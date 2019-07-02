import javascript
import semmle.javascript.frameworks.EventEmitter
import semmle.javascript.dataflow.Portals

//string queryResult() {
//	result = concat( SocketIOReservedListenNode ln, DataFlow::FunctionNode fn |
// ln.asExpr().getFile().toString().regexpMatch(".*socket.io.js.*")
//and fn = ln.getListener() |
// ln + " ! " + ln.getCalleeName() + " ! " + ln.getBase() + " ! " +  ln.getEventName()+ " ! " +  ln.getReceiver()+ " ! " +
// fn + " ! " +  fn.getNumParameter() + " ! " +  getListOfParams_FunctionNode(fn), "\n")
//}
string queryResult() {
  result = concat(Portal p, ListenNode ln, DataFlow::FunctionNode fn, DataFlow::Node pen |
      //ln.asExpr().getFile().toString().regexpMatch(".*fs.*") and
      fn = ln.getListener() and
      ln.getBase*() = pen and
      pen = p.getAnExitNode(_)
    |
      p + " ! " + pen + " ! " + ln + " ! " + ln.getCalleeName() + " ! " + ln.getBase() + " ! " +
          ln.getEventName(), "\n" //+ " ! " + ln.getReceiver() + " ! " + fn + " ! " + fn.getNumParameter() +
          //" ! " + getListOfParams_FunctionNode(fn), "\n"
    )
}

//
//from TopLevel t1
select queryResult()
//from Portal p, ListenNode ln, DataFlow::FunctionNode fn, DataFlow::Node pen
//where
//  ln.asExpr().getFile().toString().regexpMatch(".*fs.*") and
//  fn = ln.getListener() and
//  ln.getBase*() = pen and
//  pen = p.getAnExitNode(_)
//select p,pen , ln ,ln.getCalleeName(),ln.getBase() ,
//    ln.getEventName() , ln.getReceiver(),fn, fn.getNumParameter() , getListOfParams_FunctionNode(fn)
external predicate portalWithEventNameOK(string p, string en);

// this predicate works under the assumption that the string is a portal.toString, and might
// return unexpected results if the formatting doesn't match
string getPortalRoot(string p) {
  result = p.substring(p.indexOf("root"), p.indexOf(")", 0, 0)) and
  (exists(Portal pp | pp.toString() = p) or portalWithEventNameOK(p, _))
  // result = p.toString().substring(p.toString().indexOf("root"), p.toString().indexOf(")", 0, 0))
}

string incorrectAPIUse(Portal p, ListenNode ln) {
  // string eventName) {
  not portalWithEventNameOK(p.toString(), ln.getEventName()) and
  ln.getBase*() = p.getAnExitNode(_) and
  //exists(string pc |
  getPortalRoot(p.toString()) = getPortalRoot(result) and
  portalWithEventNameOK(result, ln.getEventName()) and
  not result = p.toString() //and
  //result = pc
  // )
}

predicate knownCorrectAPIUse(Portal p, ListenNode ln) {
  // string eventName) {
  portalWithEventNameOK(p.toString(), ln.getEventName()) and ln.getBase*() = p.getAnExitNode(_)
}

predicate unknownAPIUse(Portal p, ListenNode ln) {
  // string eventName) {
  not exists(incorrectAPIUse(p, ln)) and
  not knownCorrectAPIUse(p, ln) and
  ln.getBase*() = p.getAnExitNode(_)
}

// should return a list of (correctRoot, incorrectUseSeen pairs)
string aggregateListOfBrokenAPIUses(ListenNode ln) {
  result = concat(Portal p, string s | s = incorrectAPIUse(p, ln) | "[ " + p + ", " + s + " ]\n")
}

string aggregateListOfCorrectAPIUses(ListenNode ln) {
  result = concat(Portal p | knownCorrectAPIUse(p, ln) | "[ " + p + " ]")
}

string aggregateListOfUnknownAPIUses(ListenNode ln) {
  result = concat(Portal p |
      ln.getBase*() = p.getAnExitNode(_) and unknownAPIUse(p, ln)
    |
      "[ " + p + " ]"
    )
}

predicate weHaveAProblem(ListenNode ln) {
  not exists(Portal p | ln.getBase*() = p.getAnExitNode(_))
}

string whatIsGoingOn(ListenNode ln) {
  aggregateListOfBrokenAPIUses(ln) = "" and
  aggregateListOfCorrectAPIUses(ln) = "" and
  aggregateListOfUnknownAPIUses(ln) = "" and
  not weHaveAProblem(ln) and
  result = "This should never happen"
}

//class ImplicitIOImport extends DataFlow::ModuleImportNode::Range {
//  ImplicitIOImport() {
//    this = DataFlow::globalVarRef("io") //and this.getTopLevel() instanceof NodeModule
//  }
//
//  override string getPath() { result = "socket.io" }
//}

class TSGlobalDeclImport extends DataFlow::ModuleImportNode::Range {
  string path;

  TSGlobalDeclImport() {
    exists(LocalVarTypeAccess q, ImportDeclaration i |
      q.getContainer() instanceof GlobalAugmentationDeclaration and
      i.(BulkImportDeclaration).getLocal().getVariable() = q.getVariable() and
      path = i.getImportedPath().getValue() and
      this = DataFlow::globalVarRef(q
              .getEnclosingStmt()
              .(VarDeclStmt)
              .getADecl()
              .getBindingPattern()
              .getAVariable()
              .getName())
    )
  }

  override string getPath() { result = path }
}

//from ListenNode ln, string s
//where s = aggregateListOfBrokenAPIUses(ln) and not s = ""
//select ln.getEventName(), ln.asExpr().getLocation(), ln, s

//from ListenNode ln, string s
//where s = aggregateListOfCorrectAPIUses(ln) and not s = ""
//select ln.getEventName(), ln.asExpr().getLocation(), ln, s

//from ListenNode ln, string s
//where s = aggregateListOfUnknownAPIUses(ln) and not s = ""
//select ln.getEventName(), ln.asExpr().getLocation(), ln, s


//from Portal p
//where p.getAnExitNode(_).asExpr().getFile().toString().regexpMatch(".*SE1034.*")
//from Variable p
//where p.getName() = "io" and p.getADeclaration().getFile().toString().regexpMatch(".*SE1034.*")
//select p, p.getADeclaration()

//from LocalVarTypeAccess q, string s, Variable v
//where
//  q.getContainer() instanceof GlobalAugmentationDeclaration and
//  exists(ImportDeclaration i |
//    i.(BulkImportDeclaration).getLocal().getVariable() = q.getVariable() and
//    s = i.getImportedPath().toString()
//  ) and
//  q.getEnclosingStmt().(VarDeclStmt).getADecl().getBindingPattern().getAVariable() = v
//select q, s, v.getAReference()

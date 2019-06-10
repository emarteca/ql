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
  result = concat(Portal p, ListenNode ln, DataFlow::FunctionNode fn,
      DataFlow::Node pen |
      ln.asExpr().getFile().toString().regexpMatch(".*fs.*") and
      fn = ln.getListener() and
      ln.getBase*() = pen and
      pen = p.getAnExitNode(_)
    |
      p + " ! " + pen + " ! " + ln + " ! " + ln.getCalleeName() + " ! " + ln.getBase() + " ! " +
          ln.getEventName() + " ! " + ln.getReceiver() + " ! " + fn + " ! " + fn.getNumParameter() +
          " ! " + getListOfParams_FunctionNode(fn), "\n"
    )
}
//
//from TopLevel t1
//select queryResult()


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
	(exists( Portal pp | pp.toString() = p) or portalWithEventNameOK(p, _))
	// result = p.toString().substring(p.toString().indexOf("root"), p.toString().indexOf(")", 0, 0))
}


string incorrectAPIUse(Portal p, string eventName) {
	not portalWithEventNameOK(p.toString(), eventName) and
	exists(string pc | getPortalRoot(p.toString()) = getPortalRoot(pc) and portalWithEventNameOK(pc, eventName) and not pc = p.toString()
			and result = pc.toString())
}

from Portal p, ListenNode ln, DataFlow::FunctionNode fn, string s
where
  //ln.asExpr().getFile().toString().regexpMatch(".*fs.*") and
  fn = ln.getListener() and
  ln.getBase*() = p.getAnExitNode(_) and
  s = incorrectAPIUse(p, ln.getEventName())
select s, p, ln.getEventName() //, ln.getReceiver(),fn, fn.getNumParameter() , getListOfParams_FunctionNode(fn)


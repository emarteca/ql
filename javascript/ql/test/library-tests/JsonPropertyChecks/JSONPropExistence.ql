/**
 * @name JSONPropExistence
 * @description Insert description here...
 * @ kind path-problem
 * @problem.severity warning
 */

import javascript
import semmle.javascript.RestrictedLocations
private import semmle.javascript.dataflow.internal.AccessPaths
import semmle.javascript.frameworks.Testing

//import DataFlow::PathGraph
/**
 * Custom configuration for JsonParserCall outputs flowing to property accesses.
 */
class JsonParserCallConfig extends DataFlow::Configuration {
  JsonParserCallConfig() { this = "JsonParserCallConfig" }

  override predicate isSource(DataFlow::Node node) { node instanceof DataFlow::JsonParserCall }

  override predicate isSink(DataFlow::Node node) {
    exists(DataFlow::PropRef prn | node = prn.getBase())
  }

  override predicate isBarrierGuard(DataFlow::BarrierGuardNode sgn) {
    sgn instanceof ImplicitNullCheckBarrier or
    sgn instanceof PropCheckBarrier or
    sgn instanceof ExplicitPropCheckBarrier or
    sgn instanceof InPropCheckBarrier or
    sgn instanceof ExplicitUndefinedPropCheckBarrier or
    sgn instanceof AdHocIsCheckBarrier or
    sgn instanceof AdHocHasCheckBarrier or
    sgn instanceof ExplicitNullCheckBarrier
  }

  // this used to be the AdHocAssertSanitizer
  // didn't work since it's not a SanitizerGuardNode (since it's not a guard node, sanitize from asserts
  // outside of conditionals)
  override predicate isBarrier(DataFlow::Node toSanitize) {
    // dfn is a sanitizer if it's an assert call, and if there exists a var access later (i.e. in a basic
    // block dominated by the basic block of dfn) which accesses the same variable.
    exists(DataFlow::CallNode dfn |
      (
        dfn.getCalleeName().regexpMatch(".*[a|A]ssert.*") or
        dfn.getCalleeName().regexpMatch(".*[v|V]alidate.*")
      ) and
      (
        //dfn.getBasicBlock().(ReachableBasicBlock).dominates(toSanitize.getBasicBlock()) and
        strictlyDominates(dfn, toSanitize) and
        toSanitize.asExpr() = dfn
              .getAnArgument()
              .asExpr()
              .getAChildExpr*()
              .(VarAccess)
              .getVariable()
              .(LocalVariable)
              .getAnAccess()
        or
        toSanitize.asExpr() = dfn.asExpr()
      )
    )

    or 
    // one prop access sanitizes later prop accesses which have the same base
    // i.e. x.f sanitizes x.f', since a successful access to x.f means that x is not null
    // then, if x.f.g is accessed, this will still have to be checked since we have no guarantee
    // on the non-nullity of the field
    exists( DataFlow::Node prn, AccessPath bap, ReachableBasicBlock bb1, ReachableBasicBlock bb2 |
		bap.getAnInstanceIn(bb2) = prn.(DataFlow::PropRef).getBase().asExpr() and
		bap.getAnInstanceIn(bb1) = toSanitize.asExpr() //.(PropAccess).getBase() 
		//and not prn.(DataFlow::PropRef).getBase().asExpr() = toSanitize.asExpr().(PropAccess).getBase() // don't sanitize yourself
		//and bb2.dominates(bb1)
		and strictlyDominates(prn, toSanitize)
	)
	
	//or toSanitize.asExpr().(VarAccess).getVariable().isGlobal()
	
  }
}

/**
 * Null check sanitizer is any access (for now, just keep it just variable accesses, but could be more general).
 *
 * For example: if(x) sanitizes 'x' in the body of the "then".
 */
class ImplicitNullCheckBarrier extends DataFlow::BarrierGuardNode, DataFlow::Node {
  ImplicitNullCheckBarrier() { this.asExpr() instanceof VarAccess }
  	
  // no condition on e here, since we're just sanitizing e
  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
//    (e = this.asExpr().(VarAccess).getVariable().getAnAccess() or
//     e.(PropAccess).getBase() = this.asExpr().(VarAccess).getVariable().getAnAccess()
//    ) 
 	exists(AccessPath bap, BasicBlock bb, ConditionGuardNode cgn |
      (bap.getAnInstanceIn(bb) = e.(PropAccess).getBase() or 
       bap.getAnInstanceIn(bb) = e
      ) and
      bap.getAnInstance() = this.asExpr().(VarAccess).getVariable().getAnAccess() and
      // we need to make sure that the current sanitizer dominates the basic block containing the expression
      // but how to check this? since the sanitizer is not a control flow node
      cgn.getTest() = this.asExpr() and
      cgn.dominates(bb)
    )
  }
  //override predicate appliesTo( TaintTracking::Configuration cfg) { any() }
}

class ExplicitNullCheckBarrier extends DataFlow::BarrierGuardNode,
  DataFlow::ValueNode {
  
  override EqualityTest astNode;

  override predicate blocks(boolean outcome, Expr e) {
    outcome = astNode.getPolarity().booleanNot() and
    
    exists(AccessPath bap, BasicBlock bb, ConditionGuardNode cgn |
      (bap.getAnInstanceIn(bb) = e.(PropAccess).getBase() or bap.getAnInstanceIn(bb) = e) and
      bap.getAnInstance() = astNode.getAnOperand().(VarAccess).getVariable().getAnAccess() and
      // we need to make sure that the current sanitizer dominates the basic block containing the expression
      // but how to check this? since the sanitizer is not a control flow node
      cgn.getTest() = this.asExpr() and
      cgn.dominates(bb)
    ) 
  }
}


/**
 * Param check sanitizer:
 *
 * For example: if(x.p) sanitizes 'x.p' in the body of the "then".
 * But, this also needs to take into account checks of the form 'x.hasOwnProperty("p")', and such things.
 * We might be able to use an existing SG for this (WhitelistContainmentCallSanitizer in TaintTracking.qll)
 */
class PropCheckBarrier extends DataFlow::BarrierGuardNode, DataFlow::ValueNode {
  PropCheckBarrier() { 
  	this.asExpr() instanceof PropAccess 
  	//exists( AccessPath ap | this.asExpr() = ap.getAnInstance())
  }

  // here we need a parameter access and we're going to sanitize the parameter on the object (not the whole object)
  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    this.asExpr() = e
  }
}

// here we have something like jsonObj.hasOwnProperty("p")
class ExplicitPropCheckBarrier extends DataFlow::BarrierGuardNode, DataFlow::MethodCallNode {
  ExplicitPropCheckBarrier() { 
  	exists(string name |
        name = "contains" or
        name = "has" or
        name = "hasOwnProperty"
      |
        getMethodName() = name
      )
  }

  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    e instanceof PropAccess and
    exists(AccessPath bap, BasicBlock bb, ConditionGuardNode cgn |
      bap.getAnInstanceIn(bb) = e.(PropAccess).getBase() and
      bap.getAnInstance() = this.getReceiver().asExpr() and
      // we need to make sure that the current sanitizer dominates the basic block containing the expression
      // but how to check this? since the sanitizer is not a control flow node
      cgn.getTest() = this.asExpr() and
      cgn.dominates(bb)
    ) and
    e.(PropAccess).getPropertyName() = this.getArgument(0).getStringValue()
  }
}

// here we have something like 'f' in jsonObj
class InPropCheckBarrier extends DataFlow::BarrierGuardNode, DataFlow::ValueNode {
  override InExpr astNode;
  
  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    e instanceof PropAccess and
    exists(AccessPath bap, BasicBlock bb, ConditionGuardNode cgn |
      bap.getAnInstanceIn(bb) = e.(PropAccess).getBase() and
      bap.getAnInstance() = astNode.(InExpr).getRightOperand() and
      // we need to make sure that the current sanitizer dominates the basic block containing the expression
      // but how to check this? since the sanitizer is not a control flow node
      cgn.getTest() = this.asExpr() and
      cgn.dominates(bb)
    ) and
    e.(PropAccess).getPropertyName() = astNode.(InExpr).getLeftOperand().getStringValue()
  }
}

// here we have something like jsonObj[ 'f'] != undefined
class ExplicitUndefinedPropCheckBarrier extends DataFlow::BarrierGuardNode,
  DataFlow::ValueNode {
  Expr x;

  override EqualityTest astNode;

  override predicate blocks(boolean outcome, Expr e) {
    outcome = astNode.(EqualityTest).getPolarity().booleanNot() and
    e instanceof PropAccess and
    exists(AccessPath bap, BasicBlock bb, ConditionGuardNode cgn |
      bap.getAnInstanceIn(bb) = e.(PropAccess).getBase() and
      bap.getAnInstance() = astNode.(EqualityTest).getAnOperand().(PropAccess).getBase() and
      // we need to make sure that the current sanitizer dominates the basic block containing the expression
      // but how to check this? since the sanitizer is not a control flow node
      cgn.getTest() = this.asExpr() and
      cgn.dominates(bb)
    ) and
    e.(PropAccess).getPropertyName() = astNode
          .(EqualityTest)
          .getAnOperand()
          .(PropAccess)
          .getPropertyNameExpr()
          .getStringValue()
  }
}

PropAccess getAPropAccessOnParamInAFunction(Function f) {
  result.getEnclosingFunction() = f and
  result.getBase().getAChildExpr*().(VarAccess).getAVariable() = f.getParameter(0).getAVariable()
}

// we're sanitizing objects passed into a single argument function that starts with "is"
class AdHocIsCheckBarrier extends DataFlow::BarrierGuardNode, DataFlow::CallNode {
  AdHocIsCheckBarrier() {
    getCalleeName().regexpMatch("is.*") and
    getNumArgument() = 1
  }

  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    e = getArgument(0).asExpr()
    //e.(PropAccess).getBase() = getArgument(0).asExpr().(VarAccess).getVariable().getAnAccess() //and
    //e.(PropAccess).getPropertyName() = getAPropAccessOnParamInAFunction( getACallee()).getPropertyName()
  }
}

// we're sanitizing parameter p accesses objects passed into a 2 argument function that starts with "has"
class AdHocHasCheckBarrier extends DataFlow::BarrierGuardNode, DataFlow::CallNode {
  AdHocHasCheckBarrier() {
    getCalleeName().regexpMatch("has.*") and
    getNumArgument() = 2
  }

  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    //e = getArgument(0).asExpr()
    e instanceof PropAccess and
    exists(AccessPath bap, BasicBlock bb, ConditionGuardNode cgn |
      bap.getAnInstanceIn(bb) = e.(PropAccess).getBase() and
      bap.getAnInstance() = getArgument(0).asExpr() and
      // we need to make sure that the current sanitizer dominates the basic block containing the expression
      // but how to check this? since the sanitizer is not a control flow node
      cgn.getTest() = this.asExpr() and
      cgn.dominates(bb)
    ) and
    (
      e.(PropAccess).getPropertyName() = getArgument(1).asExpr().getStringValue()
//      or
//      e.(PropAccess).getPropertyNameExpr() = getArgument(1)
//            .asExpr()
//            .(VarAccess)
//            .getVariable()
//            .getAnAccess()
    )
  }
}

// hack: introduce a "correspondence" between DF and CF nodes
int getNodeIndexOfDFNode(DataFlow::Node dfn, BasicBlock bb) {
	bb.getNode(result) = dfn.getAstNode().getFirstControlFlowNode()
}

pragma[inline]
predicate strictlyDominates(DataFlow::Node a, DataFlow::Node b) {
  a.getBasicBlock().(ReachableBasicBlock).strictlyDominates(b.getBasicBlock())
  or
  exists( BasicBlock bb |
  	getNodeIndexOfDFNode(a, bb) < getNodeIndexOfDFNode(b, bb)
  )
}

predicate isDirectUseOfEnhancedFor(Expr e) {
  exists(EnhancedForLoop efl |
    e.(PropAccess).getPropertyNameExpr() = efl.getAnIterationVariable().getAnAccess() //and
    //e.(PropAccess).getBase() = efl.getIterationDomain().
  )
}

predicate isBlanketWhitelistedAccess(PropAccess pe) {
  exists(string n |
    n = pe.getPropertyName() and
    (
      n = "length"
      or
      // methods ... should we pay attention to ensure that these are actually method calls and not
      // just properties with the same name?
      (
        n = "forEach" or
        n = "map" or
        n = "push" or
        n = "match" or
        n = "filter" or
        n = "find" or
        n = "then" or
        n = "toString" or
        n = "catch" or
        n = "slice" or
        n = "charAt" or
        n = "indexOf" or
        n = "split" or
        n = "join" or
        n = "substring" or
        n = "toLowerCase" or
        n = "toUpperCase" or
        n = "replace"
      )
    )
  )
}

predicate res(JsonParserCallConfig cfg, DataFlow::Node src, DataFlow::Node sink, Expr sink2) {
  cfg.hasFlow(src, sink) and
 // not src = sink and
  sink.asExpr().getParentExpr() = sink2 
//    not (
//      cfg.isSanitizerGuard(sink) and
//      exists(ConditionGuardNode cgn | sink.asExpr() = cgn.getTest().getAChildExpr*())
//    ) and
//    (
//      sink.asExpr().getParentExpr() = sink2 and
//      not (
//        (sink2 instanceof AssignExpr or sink2 instanceof VariableDeclarator) and
//        exists(ConditionGuardNode cgn |
//          sink.getASuccessor*().asExpr() = cgn.getTest().getAChildExpr*()
//        )
//        or
//        sink2 instanceof LogicalBinaryExpr
//      )
//    ) and
//    //sink.asExpr() instanceof PropAccess and
//  not isDirectUseOfEnhancedFor(sink.asExpr()) and
//  not isBlanketWhitelistedAccess(sink.asExpr().(PropAccess))
}

//
//from JsonParserCallConfig cfg, DataFlow::PathNode src, DataFlow::PathNode sink, Expr sink2 //DataFlow::Node sink2
//where
//  not exists(Test t | src.getNode().asExpr().getFile() = t.getFile() or sink.getNode().asExpr().getFile() = t.getFile()) and
//  //sink.asExpr().getFile().toString().regexpMatch(".*nameframe.max.html.*") and
//  res(cfg, src, sink, sink2)// and
//  and sink2.getFile().toString().regexpMatch(".*imaVideo.*") 
////  and not cfg.isSanitizer(sink)
////  not sink2 instanceof AssignExpr and
////  not sink2 instanceof ObjectExpr
////sink.asExpr().getFile().toString().regexpMatch(".*JsonInteropRegistryProvider.*")
////select sink.getNode(), src, sink, "y $@", src.getNode(), "aaa"
//select sink, src, sink, "weee" //, sink2 //, sink2.getAQlClass() //, sink.asExpr().getAQlClass() //, sink.getASuccessor() //.asExpr()

//
//from JsonParserCallConfig cfg, DataFlow::Node src, DataFlow::Node sink, Expr sink2 //DataFlow::Node sink2
//where
//  not exists(Test t | src.asExpr().getFile() = t.getFile() or sink.asExpr().getFile() = t.getFile()) and
//  //sink.asExpr().getFile().toString().regexpMatch(".*nameframe.max.html.*") and
//  res(cfg, src, sink, sink2)// and
//  and sink2.getFile().toString().regexpMatch(".*simple.*") 
////  and not cfg.isSanitizer(sink)
////  not sink2 instanceof AssignExpr and
////  not sink2 instanceof ObjectExpr
////sink.asExpr().getFile().toString().regexpMatch(".*JsonInteropRegistryProvider.*")
////select sink.getNode(), src, sink, "y $@", src.getNode(), "aaa"
//select src, sink.asExpr(), sink2 //, sink2.getAQlClass(), sink.asExpr().getAQlClass()

//e = this.asExpr().(VarAccess).getVariable().getAnAccess() or
//     e.(PropAccess).getBase() = this.asExpr().(VarAccess).getVariable().getAnAccess()

//from VarAccess va, Expr e
//where va.getFile().toString().regexpMatch(".*imaVideo.*") 
//and va.getVariable().getName() = "imaSettings"
//and (e.(PropAccess).getBase() = va.getVariable().getAnAccess() or e = va.getVariable().getAnAccess())
//select va, va.getVariable(), e //, va.getVariable().getAnAccess()

//from DataFlow::PropRef prn, DataFlow::Node toSanitize
//where
//	exists( AccessPath bap, BasicBlock bb |
//		bap.getAnInstance() = prn.getBase().asExpr() and
//		bap.getAnInstanceIn(bb) = toSanitize.asExpr().(PropAccess).getBase()
//		and prn.getBasicBlock().(ReachableBasicBlock).dominates(bb)
//	) 
//     and 
//    	prn.getFile().toString().regexpMatch(".*tst.js.*")
//select prn, toSanitize


from ExplicitNullCheckBarrier jvincs, Expr e
where jvincs.blocks(e.flow()) and
//e instanceof PropAccess and
e.getFile().toString().regexpMatch(".*simple.*")
select jvincs, e //jvincs.getAnArgument().asExpr().getAChildExpr*()//, e//, e.(PropAccess).getPropertyNameExpr().getUnderlyingValue()


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
 
 class JsonParserCallConfig extends TaintTracking::Configuration {
 	JsonParserCallConfig() { this = "JsonParserCallConfig" }
 	
 	override predicate isSource( DataFlow::Node node) {
		node instanceof DataFlow::JsonParserCall
 	}
 	
 	override predicate isSink( DataFlow::Node node) {
 		node instanceof DataFlow::ValueNode
 	}
  	
 	override predicate isSanitizerGuard( TaintTracking::SanitizerGuardNode sgn) {
 		sgn instanceof ImplicitNullCheckSanitizer or
 		sgn instanceof PropCheckSanitizer or 
 		sgn instanceof ExplicitPropCheckSanitizer or
 		sgn instanceof InPropCheckSanitizer or
 		sgn instanceof ExplicitUndefinedPropCheckSanitizer or
 		sgn instanceof AdHocIsCheckSanitizer or
 		sgn instanceof AdHocHasCheckSanitizer 
 	}
 	
 	// this used to be the AdHocAssertSanitizer
 	// didn't work since it's not a SanitizerGuardNode (since it's not a guard node, sanitize from asserts
 	// outside of conditionals)
 	override predicate isSanitizer( DataFlow::Node toSanitize) {
 		// dfn is a sanitizer if it's an assert call, and if there exists a var access later (i.e. in a basic
 		// block dominated by the basic block of dfn) which accesses the same variable.
 		
 		exists( DataFlow::CallNode dfn | 
 			dfn.getCalleeName().regexpMatch("assert.*")  and
 			dfn.getBasicBlock().(ReachableBasicBlock).dominates( toSanitize.getBasicBlock()) and
 			toSanitize.asExpr() = dfn.getAnArgument().asExpr().getAChildExpr*().(VarAccess).getVariable().(LocalVariable).getAnAccess() 
 		)
 	}
 }

/**
 * Null check sanitizer is any access (for now, just keep it just variable accesses, but could be more general).
 * 
 * For example: if(x) sanitizes 'x' in the body of the "then".
 */
class ImplicitNullCheckSanitizer extends TaintTracking::SanitizerGuardNode, DataFlow::ValueNode {
	
	// no condition on e here, since we're just sanitizing e 
	override predicate sanitizes( boolean outcome, Expr e) {
		outcome = true and
		e = this.asExpr().(VarAccess).getVariable().getAnAssignedExpr()
	}
	
	//override predicate appliesTo( TaintTracking::Configuration cfg) { any() }
}

/**
 * Param check sanitizer: 
 * 
 * For example: if(x.p) sanitizes 'x.p' in the body of the "then".
 * But, this also needs to take into account checks of the form 'x.hasOwnProperty("p")', and such things.
 * We might be able to use an existing SG for this (WhitelistContainmentCallSanitizer in TaintTracking.qll)
 */
class PropCheckSanitizer extends TaintTracking::SanitizerGuardNode, DataFlow::ValueNode {
	
	PropCheckSanitizer() {
		this.asExpr() instanceof PropAccess
	}
	
	// here we need a parameter access and we're going to sanitize the parameter on the object (not the whole object) 
	override predicate sanitizes( boolean outcome, Expr e) {
		outcome = true and
		this.asExpr() = e
	}
	
}

// here we have something like jsonObj.hasOwnProperty("p")
class ExplicitPropCheckSanitizer extends TaintTracking::SanitizerGuardNode, DataFlow::MethodCallNode {
	
	ExplicitPropCheckSanitizer() { this instanceof TaintTracking::WhitelistContainmentCallSanitizer }
	
	override predicate sanitizes( boolean outcome, Expr e) {
		outcome = true and
		e instanceof PropAccess and 
		exists( AccessPath bap, BasicBlock bb, ConditionGuardNode cgn | 
				bap.getAnInstanceIn( bb) = e.(PropAccess).getBase() and
				bap.getAnInstance() = this.getReceiver().asExpr() and
				// we need to make sure that the current sanitizer dominates the basic block containing the expression
				// but how to check this? since the sanitizer is not a control flow node
				cgn.getTest() = this.asExpr() and
				cgn.dominates( bb)
		) and
		e.(PropAccess).getPropertyName() = this.getArgument(0).getStringValue() 
	}
	
}

// here we have something like 'f' in jsonObj
class InPropCheckSanitizer extends TaintTracking::SanitizerGuardNode, DataFlow::ValueNode {
	
	InPropCheckSanitizer() { this instanceof TaintTracking::InSanitizer }
	
	override predicate sanitizes( boolean outcome, Expr e) {
		outcome = true and
		e instanceof PropAccess and 
		exists( AccessPath bap, BasicBlock bb, ConditionGuardNode cgn | 
				bap.getAnInstanceIn( bb) = e.(PropAccess).getBase() and
				bap.getAnInstance() = astNode.(InExpr).getRightOperand() and
				// we need to make sure that the current sanitizer dominates the basic block containing the expression
				// but how to check this? since the sanitizer is not a control flow node
				cgn.getTest() = this.asExpr() and
				cgn.dominates( bb)
		) and
		e.(PropAccess).getPropertyName() = astNode.(InExpr).getLeftOperand().getStringValue() 
	}
	
}

// here we have something like jsonObj[ 'f'] != undefined
class ExplicitUndefinedPropCheckSanitizer extends TaintTracking::SanitizerGuardNode, DataFlow::ValueNode {
	
	ExplicitUndefinedPropCheckSanitizer() { this instanceof TaintTracking::UndefinedCheckSanitizer }
	
	override predicate sanitizes( boolean outcome, Expr e) {
		outcome = astNode.(EqualityTest).getPolarity().booleanNot() and
		e instanceof PropAccess and 
		exists( AccessPath bap, BasicBlock bb, ConditionGuardNode cgn | 
				bap.getAnInstanceIn( bb) = e.(PropAccess).getBase() and
				bap.getAnInstance() = astNode.(EqualityTest).getAnOperand().(PropAccess).getBase() and
				// we need to make sure that the current sanitizer dominates the basic block containing the expression
				// but how to check this? since the sanitizer is not a control flow node
				cgn.getTest() = this.asExpr() and
				cgn.dominates( bb)
		) and
		e.(PropAccess).getPropertyName() = astNode.(EqualityTest).getAnOperand().(PropAccess).getPropertyNameExpr().getStringValue() 
	}
	
}

PropAccess getAPropAccessOnParamInAFunction( Function f) {
	result.getEnclosingFunction() = f and 
	result.getBase().getAChildExpr*().(VarAccess).getAVariable() = f.getParameter(0).getAVariable()
}

// we're sanitizing objects passed into a single argument function that starts with "is"
class AdHocIsCheckSanitizer extends TaintTracking::SanitizerGuardNode, DataFlow::CallNode {
    AdHocIsCheckSanitizer() {
      getCalleeName().regexpMatch("is.*") and
      getNumArgument() = 1
    }

    override predicate sanitizes(boolean outcome, Expr e) {
      outcome = true and
      e = getArgument(0).asExpr()
      //e.(PropAccess).getBase() = getArgument(0).asExpr().(VarAccess).getVariable().getAnAccess() //and 
      //e.(PropAccess).getPropertyName() = getAPropAccessOnParamInAFunction( getACallee()).getPropertyName()
    }
}

// we're sanitizing parameter p accesses objects passed into a 2 argument function that starts with "has"
class AdHocHasCheckSanitizer extends TaintTracking::SanitizerGuardNode, DataFlow::CallNode {
    AdHocHasCheckSanitizer() {
      getCalleeName().regexpMatch("has.*") and
      getNumArgument() = 2
    }

    override predicate sanitizes(boolean outcome, Expr e) {
        outcome = true and
        //e = getArgument(0).asExpr()
		e instanceof PropAccess and 
		exists( AccessPath bap, BasicBlock bb, ConditionGuardNode cgn | 
				bap.getAnInstanceIn( bb) = e.(PropAccess).getBase() and
				bap.getAnInstance() = getArgument(0).asExpr() and
				// we need to make sure that the current sanitizer dominates the basic block containing the expression
				// but how to check this? since the sanitizer is not a control flow node
				cgn.getTest() = this.asExpr() and
				cgn.dominates( bb)
		) and
		(e.(PropAccess).getPropertyName() = getArgument(1).asExpr().getStringValue() 
		or
		e.(PropAccess).getPropertyNameExpr() = getArgument(1).asExpr().(VarAccess).getVariable().getAnAccess())
    }
}

//
//from AdHocAssertSanitizer jvincs, Expr e
//where jvincs.sanitizes(true, e) //and
////e instanceof PropAccess and
////e.getFile().toString().regexpMatch(".*JsonInteropRegistryProvider.*") 
//select jvincs, e //jvincs.getAnArgument().asExpr().getAChildExpr*()//, e//, e.(PropAccess).getPropertyNameExpr().getUnderlyingValue()

predicate isDirectUseOfEnhancedFor( Expr e) {
	exists( EnhancedForLoop efl | 
					e.(PropAccess).getPropertyNameExpr() = efl.getAnIterationVariable().getAnAccess() //and
					//e.(PropAccess).getBase() = efl.getIterationDomain().
	)
}

predicate isBlanketWhitelistedAccess( PropAccess pe) {
	exists( string n |
			n = pe.getPropertyName() and
			(
				n = "length" or
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
					n = "toLowerCase" or n = "toUpperCase"
				)
			)
	)
}

predicate res( JsonParserCallConfig cfg, DataFlow::Node src, DataFlow::Node sink, Expr sink2) {
	cfg.hasFlow(src, sink) and
	not src = sink and 
	not (cfg.isSanitizerGuard( sink) and 
		exists( ConditionGuardNode cgn | sink.asExpr() =  cgn.getTest().getAChildExpr*())) and

(sink.asExpr().getParentExpr() = sink2 and 
	not ((sink2 instanceof AssignExpr or sink2 instanceof VariableDeclarator) and
		exists( ConditionGuardNode cgn | sink.getASuccessor*().asExpr() = cgn.getTest().getAChildExpr*() 
	    ) 
	    or sink2 instanceof LogicalBinaryExpr
		)
)  
and
sink.asExpr() instanceof PropAccess and 
not isDirectUseOfEnhancedFor( sink.asExpr()) and
not isBlanketWhitelistedAccess( sink.asExpr().(PropAccess))
}
//
from JsonParserCallConfig cfg, DataFlow::Node src, DataFlow::Node sink, Expr sink2//DataFlow::Node sink2
where not exists( Test t | src.asExpr().getFile() = t.getFile() or sink.asExpr().getFile() = t.getFile()) and
//sink.asExpr().getFile().toString().regexpMatch(".*nameframe.max.html.*") and
res( cfg, src, sink, sink2) //and
//sink.asExpr().getFile().toString().regexpMatch(".*JsonInteropRegistryProvider.*") 
//select sink.getNode(), src, sink, "y $@", src.getNode(), "aaa"
select src, sink.asExpr()//, sink2 //, sink.asExpr().getAQlClass() //, sink.getASuccessor() //.asExpr()



/**
 * @name JSONPropExistence
 * @description Insert description here...
 * @kind problem
 * @problem.severity warning
 */

import javascript
import semmle.javascript.RestrictedLocations
private import semmle.javascript.dataflow.internal.AccessPaths

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
 		sgn instanceof PropCheckSanitizer or 
 		sgn instanceof ExplicitPropCheckSanitizer or
 		sgn instanceof InPropCheckSanitizer or
 		sgn instanceof ExplicitUndefinedPropCheckSanitizer
 	}
 }

/**
 * Null check sanitizer is any access (for now, just keep it just variable accesses, but could be more general).
 * 
 * For example: if(x) sanitizes 'x' in the body of the "then".
 */
class ImplicitNullCheckSanitizer extends TaintTracking::AdditionalSanitizerGuardNode, DataFlow::ValueNode {
	
	// no condition on e here, since we're just sanitizing e 
	override predicate sanitizes( boolean outcome, Expr e) {
		outcome = true and
		e = this.asExpr().(VarAccess).getVariable().getAnAssignedExpr()
	}
	
	override predicate appliesTo( TaintTracking::Configuration cfg) { any() }
}

/**
 * Param check sanitizer: 
 * 
 * For example: if(x.p) sanitizes 'x.p' in the body of the "then".
 * But, this also needs to take into account checks of the form 'x.hasOwnProperty("p")', and such things.
 * We might be able to use an existing SG for this (WhitelistContainmentCallSanitizer in TaintTracking.qll)
 */
class PropCheckSanitizer extends TaintTracking::AdditionalSanitizerGuardNode, DataFlow::ValueNode {
	
	PropCheckSanitizer() {
		this.asExpr() instanceof PropAccess
	}
	
	// here we need a parameter access and we're going to sanitize the parameter on the object (not the whole object) 
	override predicate sanitizes( boolean outcome, Expr e) {
		outcome = true and
		this.asExpr() = e
	}
	
	override predicate appliesTo( TaintTracking::Configuration cfg) { any() }
}

// here we have something like jsonObj.hasOwnProperty("p")
class ExplicitPropCheckSanitizer extends TaintTracking::WhitelistContainmentCallSanitizer {
	
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
class InPropCheckSanitizer extends TaintTracking::InSanitizer {
	
	override predicate sanitizes( boolean outcome, Expr e) {
		outcome = true and
		e instanceof PropAccess and 
		exists( AccessPath bap, BasicBlock bb, ConditionGuardNode cgn | 
				bap.getAnInstanceIn( bb) = e.(PropAccess).getBase() and
				bap.getAnInstance() = astNode.getRightOperand() and
				// we need to make sure that the current sanitizer dominates the basic block containing the expression
				// but how to check this? since the sanitizer is not a control flow node
				cgn.getTest() = this.asExpr() and
				cgn.dominates( bb)
		) and
		e.(PropAccess).getPropertyName() = astNode.getLeftOperand().getStringValue() 
	}
	
}

// here we have something like jsonObj[ 'f'] != undefined
class ExplicitUndefinedPropCheckSanitizer extends TaintTracking::UndefinedCheckSanitizer {
	
	override predicate sanitizes( boolean outcome, Expr e) {
		outcome = astNode.getPolarity().booleanNot() and
		e instanceof PropAccess and 
		exists( AccessPath bap, BasicBlock bb, ConditionGuardNode cgn | 
				bap.getAnInstanceIn( bb) = e.(PropAccess).getBase() and
				bap.getAnInstance() = astNode.getAnOperand().(PropAccess).getBase() and
				// we need to make sure that the current sanitizer dominates the basic block containing the expression
				// but how to check this? since the sanitizer is not a control flow node
				cgn.getTest() = this.asExpr() and
				cgn.dominates( bb)
		) and
		e.(PropAccess).getPropertyName() = astNode.getAnOperand().(PropAccess).getPropertyNameExpr().getStringValue() 
	}
	
}


//
//from ExplicitPropCheckSanitizer jvincs, Expr e
//where jvincs.sanitizes(true, e) and
//e instanceof PropAccess
//select jvincs, e//, e.(PropAccess).getPropertyName(), jvincs.getArgument(0).getStringValue() //, e.getAQlClass()

from JsonParserCallConfig cfg, DataFlow::Node src, DataFlow::Node sink
where cfg.hasFlow(src, sink) and
not src = sink and 
not (cfg.isSanitizerGuard( sink) 
	and exists( ConditionGuardNode cgn | sink.asExpr() =  cgn.getTest().getAChildExpr*())) and
//(sink.asExpr().getAChildExpr*() instanceof PropAccess or sink.asExpr() instanceof PropAccess) and
sink.asExpr() instanceof PropAccess and
sink.asExpr().getFile().toString().regexpMatch(".*JsonInteropRegistryProvider.*") 
select src, sink.asExpr()

//from RValue pa
//where pa.getFile().toString().regexpMatch(".*tst.*") 
//select pa


//from ControlStmt cs
//where cs.getFile().toString().regexpMatch(".*tst.*") 
//select cs, cs.getChildExpr( 0)



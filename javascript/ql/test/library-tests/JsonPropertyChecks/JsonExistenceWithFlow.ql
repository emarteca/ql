/**
 * @name JSON property existence checks
 * @description Accesses to properties on a JSON object should first check that the object is not null
 * @kind problem
 * @problem.severity warning
 * @id js/json-property-existence
 */

import javascript
import semmle.javascript.RestrictedLocations
private import semmle.javascript.dataflow.internal.AccessPaths
private import semmle.javascript.dataflow.InferredTypes
import semmle.javascript.frameworks.Testing

// we introduce custom dataflow labels to allow the partial sanitization of an object
// we track data from json parses (i.e. data tagged with the JsonObj label), and track
// this to sinks which perform a property read on an object with the tag MaybeNull
// this MaybeNull label is removed once a read has occured, since this indicates the base
// is not null
/**
 * Flow label to track dataflow from the result of a JSON.parse
 */
class JsonObjLabel extends DataFlow::FlowLabel {
  JsonObjLabel() { this = "JsonObj" }
}

/**
 * Flow label to track dataflow of objects which might be null
 */
class MaybeNullLabel extends DataFlow::FlowLabel {
  MaybeNullLabel() { this = "MaybeNull" }
}

/**
 * Introduce an approximation of correspondence between DataFlow and ControlFlow nodes
 * This is not exact in every case (because of phi nodes), but in most cases it is correct.
 */
int getNodeIndexOfDFNode(DataFlow::Node dfn, BasicBlock bb) {
  bb.getNode(result) = dfn.getAstNode().getFirstControlFlowNode()
}

/**
 * Predicate to determine if a DataFlow node dominates another
 * This is an adaption of the same predicate for ControlFlow nodes, using this correspondence
 * between Data/ControlFlow as determined above.
 * Strict dominance is just regular dominance except in the reflexive case where it considers
 * the relative positions of the nodes in the same basic block.
 */
pragma[inline]
predicate strictlyDominates(DataFlow::Node a, DataFlow::Node b) {
  a.getBasicBlock().(ReachableBasicBlock).strictlyDominates(b.getBasicBlock())
  or
  exists(BasicBlock bb | getNodeIndexOfDFNode(a, bb) < getNodeIndexOfDFNode(b, bb))
}

// ----------------------------------------------------------------------------------------------------------------------CONFIGURATION
/**
 * Custom DataFlow configuration: the sources and sinks are as described above.
 * Barriers are also redefined to specify cases where we can remove the MaybeNull label.
 * AdditionalFlowStep is also overriden to allow us to add the MaybeNull label on a new
 * property read.
 */
class JsonParserCallConfig extends DataFlow::Configuration {
  JsonParserCallConfig() { this = "JsonParserCallConfig" }

  /**
   * A source is the output of a JSON parser call. It has flow labels of both JsonObj
   * and MaybeNull.
   */
  override predicate isSource(DataFlow::Node node, DataFlow::FlowLabel lbl) {
    node instanceof DataFlow::JsonParserCall and
    (lbl instanceof JsonObjLabel or lbl instanceof MaybeNullLabel)
  }

  /**
   * A sink is the base of a PropRead, which has the MaybeNull label.
   * (i.e. property reads on objects which might be null)
   */
  override predicate isSink(DataFlow::Node node, DataFlow::FlowLabel lbl) {
    exists(DataFlow::PropRef prn | node = prn.getBase()) and
    lbl instanceof MaybeNullLabel
  }

  /**
   * We add new MaybeNull labels on property reads whose bases are tagged as JsonObjs.
   * (reading a property only means the base is not null, but this new access path is
   * tagged as JsonObj and could be null)
   */
  override predicate isAdditionalFlowStep(
    DataFlow::Node src, DataFlow::Node dest, DataFlow::FlowLabel srcLabel,
    DataFlow::FlowLabel destLabel
  ) {
    dest instanceof DataFlow::PropRead and
    src = dest.(DataFlow::PropRead).getBase() and
    srcLabel instanceof JsonObjLabel and
    (destLabel instanceof MaybeNullLabel or destLabel instanceof JsonObjLabel)
  }

  /**
   * List of relevant barrier guards for this configuration (described below in their
   * respective implementations)
   */
  override predicate isBarrierGuard(DataFlow::BarrierGuardNode lbgn) {
    lbgn instanceof InPropCheckBarrier or
    lbgn instanceof InstanceOfCheckBarrier or
    lbgn instanceof AdHocIsCheckBarrier or
    lbgn instanceof AdHocHasCheckBarrier or
    lbgn instanceof ExplicitUndefinedCheckBarrier or
    lbgn instanceof ImplicitNullCheckBarrier
  }

  /**
   * Helper predicate for getting a node required for the dominance check in the
   * isLabeledBarrier predicate below.
   * Required just to split up the predicate a bit, to make smaller sets to work with.
   */
  private DataFlow::Node getALBarrierDomNode() {
    // first the general prop access case
    result instanceof DataFlow::PropRef
    or
    // assert case
    (
      result.(DataFlow::CallNode).getCalleeName().regexpMatch(".*[a|A]ssert.*") or
      result.(DataFlow::CallNode).getCalleeName().regexpMatch(".*[v|V]alidate.*")
    )
  }

  /**
   * Predicate to determine barriers for the dataflow: here labeled barriers since we're working
   * over labelled flow.
   * These barriers are *in addition* to the barrier nodes specified, but they are required separately since
   * these cases do not correspond exactly to a GuardControlFlowNode.
   */
  override predicate isLabeledBarrier(DataFlow::Node dfn, DataFlow::FlowLabel lbl) {
    // only considering blocking the flow of MaybeNull; we never remove the JsonObj label
    lbl instanceof MaybeNullLabel and
    (
      exists(DataFlow::Node ddn, AccessPath bap |
        ddn = getALBarrierDomNode() and
        (
          // any property access sanitizes the base of the access path, since if the PropRef goes through we
          // know that the underlying object is not null
          bap.getAnInstance() = ddn.(DataFlow::PropRef).getBase().asExpr() or
          // a call to assert sanitizes its arguments, and itself (i.e. if the assert returns something it
          // is not considered to be MaybeNull).
          bap.getAnInstance() = ddn.(DataFlow::CallNode).getAnArgument().asExpr().getAChildExpr*() or
          bap.getAnInstance() = ddn.(DataFlow::InvokeNode).asExpr()
        ) and
        // these sanitizations persist in all subsequent (dominated) basic blocks
        bap.getAnInstance() = dfn.asExpr() and
        strictlyDominates(ddn, dfn)
      )
      or
      // in the body of an enhanced for loop (for-in or for-of) we know the iterator domain is
      // not null (i.e. in "for i in x" we know x is not null in the body)
      exists(EnhancedForLoop efl, AccessPath ap |
        ap.getAnInstance() = efl.getIterationDomain() and
        ap.getAnInstanceIn(dfn.getBasicBlock()) = dfn.asExpr() and
        efl.getBody().getBasicBlock().(ReachableBasicBlock).dominates(dfn.getBasicBlock())
      )
    )
    or
    super.isLabeledBarrier(dfn, lbl) // this ensures that the isLabeledBarrierGuard is called
  }
}


// ------------------------------------------------------------------------------------------------------------------CUSTOM SANITIZERS
/**
 * if(x) should sanitize x in the true branch.
 * Note: this applies to all access paths (i.e. if(x.k.u) would sanitize x, x.k, and x.k.u, and
 * the sanitization of x and x.k persist after the if since if either of them had been null program
 * execution would halt with an error).
 */
class ImplicitNullCheckBarrier extends DataFlow::LabeledBarrierGuardNode, DataFlow::ValueNode {
  ImplicitNullCheckBarrier() { this.asExpr() instanceof VarAccess }

  /**
   * Sanitize the condition of the guard
   */
  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    this.asExpr() = e
  }

  override DataFlow::FlowLabel getALabel() { result instanceof MaybeNullLabel }
}

/**
 * 'f' in x should sanitize x in the true branch.
 * In this case, the only thing we know is that x is not null
 * so, we sanitize x but we don't know anything about x.f itself
 */
class InPropCheckBarrier extends DataFlow::LabeledBarrierGuardNode, DataFlow::ValueNode {
  override InExpr astNode;

  /**
   * Sanitize the right side of the "in" operator (i.e. the object)
   */
  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    e = astNode.(InExpr).getRightOperand()
  }

  override DataFlow::FlowLabel getALabel() { result instanceof MaybeNullLabel }
}

/**
 * x instanceof SomeType should sanitize x in the true branch
 */
class InstanceOfCheckBarrier extends DataFlow::LabeledBarrierGuardNode, DataFlow::ValueNode {
  override InstanceofExpr astNode;

  /**
   * Sanitize the left side of the instanceof operator (i.e. the object)
   */
  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    e = astNode.(InstanceofExpr).getLeftOperand()
  }

  override DataFlow::FlowLabel getALabel() { result instanceof MaybeNullLabel }
}

/**
 * x != undefined should sanitize x in the true branch.
 * Note: like the ImplicitNullCheckBarrier, this applies to access paths of any length
 */
class ExplicitUndefinedCheckBarrier extends DataFlow::LabeledBarrierGuardNode, DataFlow::ValueNode {
  override EqualityTest astNode;

  Expr ue; // the expression we are checking is not undefined

  ExplicitUndefinedCheckBarrier() {
    exists(DataFlow::AnalyzedNode undef | astNode.hasOperands(ue, undef.asExpr()) |
      ue = astNode.getAnOperand() and
      forex(InferredType tp | tp = undef.getAType() | tp = TTUndefined()) // make sure the other operand is "undefined"
    )
  }

  /**
   * Sanitize the expression we are checking is not undefined
   */
  override predicate blocks(boolean outcome, Expr e) {
    outcome = astNode.getPolarity().booleanNot() and
    e = ue
  }

  override DataFlow::FlowLabel getALabel() { result instanceof MaybeNullLabel }
}

/**
 * Heuristic: we're sanitizing objects passed into a single argument function that starts with "is"
 */
class AdHocIsCheckBarrier extends DataFlow::LabeledBarrierGuardNode, DataFlow::CallNode {
  AdHocIsCheckBarrier() {
    getCalleeName().regexpMatch("is.*") and
    getNumArgument() = 1
  }

  /**
   * Sanitize the arg of this one-arg function
   */
  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    e = getArgument(0).asExpr()
  }

  override DataFlow::FlowLabel getALabel() { result instanceof MaybeNullLabel }
}

/**
 * Heuristic: we're sanitizing objects passed into a 2 argument function that starts with "has"
 * (example: hasProperty(x, k) will sanitize x since it is known to have property k, for instance)
 */
class AdHocHasCheckBarrier extends DataFlow::LabeledBarrierGuardNode, DataFlow::CallNode {
  AdHocHasCheckBarrier() {
    getCalleeName().regexpMatch("has.*") and
    getNumArgument() = 2
  }

  /**
   * Sanitize the first arg of this 2-arg function
   */
  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    e = getArgument(0).asExpr()
  }

  override DataFlow::FlowLabel getALabel() { result instanceof MaybeNullLabel }
}

// ------------------------------------------------------------------------------------------------------------------------------QUERY
// the query: select source, sink pairs (excluding those in test files)
from JsonParserCallConfig cfg, DataFlow::Node src, DataFlow::Node sink
where
  not exists(Test t | src.asExpr().getFile() = t.getFile() or sink.asExpr().getFile() = t.getFile()) and
  cfg.hasFlow(src, sink)
select src, sink

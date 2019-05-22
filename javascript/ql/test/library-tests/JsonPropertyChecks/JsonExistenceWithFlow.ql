import javascript
import semmle.javascript.RestrictedLocations
private import semmle.javascript.dataflow.internal.AccessPaths
private import semmle.javascript.dataflow.InferredTypes
import semmle.javascript.frameworks.Testing

class JsonObjLabel extends DataFlow::FlowLabel {
  JsonObjLabel() { this = "JsonObj" }
}

class MaybeNullLabel extends DataFlow::FlowLabel {
  MaybeNullLabel() { this = "MaybeNull" }
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

class JsonParserCallConfig extends DataFlow::Configuration {
  JsonParserCallConfig() { this = "JsonParserCallConfig" }

  override predicate isSource(DataFlow::Node node, DataFlow::FlowLabel lbl) {
    node instanceof DataFlow::JsonParserCall and
    (lbl instanceof JsonObjLabel or lbl instanceof MaybeNullLabel)
  }

  override predicate isSink(DataFlow::Node node, DataFlow::FlowLabel lbl) {
    exists(DataFlow::PropRef prn | node = prn.getBase()) and
    lbl instanceof MaybeNullLabel
  }

  override predicate isAdditionalFlowStep(
    DataFlow::Node src, DataFlow::Node dest, DataFlow::FlowLabel srcLabel,
    DataFlow::FlowLabel destLabel
  ) {
    dest instanceof DataFlow::PropRead and
    src = dest.(DataFlow::PropRead).getBase() and
    srcLabel instanceof JsonObjLabel and
    (destLabel instanceof MaybeNullLabel or destLabel instanceof JsonObjLabel)
  }

  override predicate isBarrierGuard(DataFlow::BarrierGuardNode lbgn) {
    lbgn instanceof InPropCheckBarrier or
    lbgn instanceof MethodCallBarrier or
    lbgn instanceof AdHocIsCheckBarrier or
    lbgn instanceof AdHocHasCheckBarrier or
    lbgn instanceof ExplicitUndefinedPropCheckBarrier or
    lbgn instanceof PropCheckBarrier
  }

  // this is equivalent to the isBarrier that we had before
  override predicate isLabeledBarrier(DataFlow::Node dfn, DataFlow::FlowLabel lbl) {
    lbl instanceof MaybeNullLabel and 
    exists( DataFlow::Node prn, AccessPath bap, ReachableBasicBlock bb1, ReachableBasicBlock bb2 |
    bap.getAnInstanceIn(bb2) = prn.(DataFlow::PropRef).getBase().asExpr() and
    bap.getAnInstanceIn(bb1) = dfn.asExpr() //.(PropAccess).getBase() 
    //and not prn.(DataFlow::PropRef).getBase().asExpr() = toSanitize.asExpr().(PropAccess).getBase() // don't sanitize yourself
    //and bb2.dominates(bb1)
    and strictlyDominates(prn, dfn)
  )
  or
  super.isLabeledBarrier(dfn, lbl)
  }
}

// this is probably actually the implicitnullcheck that we had before
class PropCheckBarrier extends DataFlow::LabeledBarrierGuardNode, DataFlow::ValueNode {
//  PropCheckBarrier() { 
//    this.asExpr() instanceof PropAccess 
//    //exists( AccessPath ap | this.asExpr() = ap.getAnInstance())
//  }

  // here we need a parameter access and we're going to sanitize the parameter on the object (not the whole object)
  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    this.asExpr() = e
  }
  
  override DataFlow::FlowLabel getALabel() { result instanceof MaybeNullLabel }
}

// here, we're looking at conditions of the form 'f' in x
// in this case, the only thing we know is that x is not null
// so, we sanitize x but we don't know anything about x.f itself
class InPropCheckBarrier extends DataFlow::LabeledBarrierGuardNode, DataFlow::ValueNode {
  override InExpr astNode;

  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    e = astNode.(InExpr).getRightOperand()
  }

  // label we're removing
  override DataFlow::FlowLabel getALabel() { result instanceof MaybeNullLabel }
}

// here we have something like jsonObj.anything -- if we have a method call on something it should be sanitized
class MethodCallBarrier extends DataFlow::LabeledBarrierGuardNode, DataFlow::MethodCallNode {
  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    e = this.getReceiver().asExpr()
  }

  override DataFlow::FlowLabel getALabel() { result instanceof MaybeNullLabel }
}

class ExplicitUndefinedPropCheckBarrier extends DataFlow::LabeledBarrierGuardNode,
  DataFlow::ValueNode {
  
  Expr x;
  override EqualityTest astNode;
  
  ExplicitUndefinedPropCheckBarrier() {
      exists(IndexExpr idx, DataFlow::AnalyzedNode undef |
        astNode.hasOperands(idx, undef.asExpr())
      |
        // one operand is of the form `o[x]`
        idx = astNode.getAnOperand() and
        idx.getPropertyNameExpr() = x and
        // and the other one is guaranteed to be `undefined`
        forex(InferredType tp | tp = undef.getAType() | tp = TTUndefined())
      )
    }

  override predicate blocks(boolean outcome, Expr e) {
    outcome = astNode.getPolarity().booleanNot() and
    //astNode.getAnOperand().(PropAccess) = e // TODO OR VAR ACCESS
    e instanceof PropAccess and
    exists(AccessPath bap, BasicBlock bb, ConditionGuardNode cgn |
      bap.getAnInstanceIn(bb) = e.(PropAccess).getBase() and
      bap.getAnInstance() = astNode.getAnOperand().(PropAccess).getBase() and
      // we need to make sure that the current sanitizer dominates the basic block containing the expression
      // but how to check this? since the sanitizer is not a control flow node
      cgn.getTest() = this.asExpr() and
      cgn.dominates(bb)
      and
      e.(PropAccess).getPropertyName() = astNode
          .(EqualityTest)
          .getAnOperand()
          .(PropAccess)
          .getPropertyNameExpr()
          .getStringValue()
    ) 
  }
  
  override DataFlow::FlowLabel getALabel() { result instanceof MaybeNullLabel }
}

// we're sanitizing objects passed into a single argument function that starts with "is"
class AdHocIsCheckBarrier extends DataFlow::LabeledBarrierGuardNode, DataFlow::CallNode {
  AdHocIsCheckBarrier() {
    getCalleeName().regexpMatch("is.*") and
    getNumArgument() = 1
  }

  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    e = getArgument(0).asExpr()
  }

  override DataFlow::FlowLabel getALabel() { result instanceof MaybeNullLabel }
}

// we're sanitizing objects passed into a 2 argument function that starts with "has"
class AdHocHasCheckBarrier extends DataFlow::LabeledBarrierGuardNode, DataFlow::CallNode {
  AdHocHasCheckBarrier() {
    getCalleeName().regexpMatch("has.*") and
    getNumArgument() = 2
  }

  override predicate blocks(boolean outcome, Expr e) {
    outcome = true and
    e = getArgument(0).asExpr()
  }

  override DataFlow::FlowLabel getALabel() { result instanceof MaybeNullLabel }
}

from JsonParserCallConfig cfg, DataFlow::Node src, DataFlow::Node sink, Expr sink2
where
  not exists(Test t | src.asExpr().getFile() = t.getFile() or sink.asExpr().getFile() = t.getFile()) and
  cfg.hasFlow(src, sink) and
  sink.asExpr().getParentExpr() = sink2
  //and sink2.getFile().toString().regexpMatch(".*updated.*")
select src, sink.asExpr(), sink2 //, sink2.getAQlClass(), sink.asExpr().getAQlClass()

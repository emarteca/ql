import javascript
import semmle.javascript.RestrictedLocations
private import semmle.javascript.dataflow.internal.AccessPaths
import semmle.javascript.frameworks.Testing

class JsonObjLabel extends DataFlow::FlowLabel {
  JsonObjLabel() { this = "JsonObj" }
}

class MaybeNullLabel extends DataFlow::FlowLabel {
  MaybeNullLabel() { this = "MaybeNull" }
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
    ( destLabel instanceof MaybeNullLabel or destLabel instanceof JsonObjLabel)
  }
}

from JsonParserCallConfig cfg, DataFlow::Node src, DataFlow::Node sink, Expr sink2
where
  not exists(Test t | src.asExpr().getFile() = t.getFile() or sink.asExpr().getFile() = t.getFile()) and
  cfg.hasFlow(src, sink) and
  sink.asExpr().getParentExpr() = sink2
//  and sink2.getFile().toString().regexpMatch(".*simple.*")
select src, sink.asExpr(), sink2 //, sink2.getAQlClass(), sink.asExpr().getAQlClass()

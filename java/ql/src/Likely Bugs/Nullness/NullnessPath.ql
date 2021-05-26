/**
 * @kind path-problem
 */

import java
private import semmle.code.java.dataflow.SSA
import semmle.code.java.dataflow.Nullness
private import semmle.code.java.dataflow.NullGuards
import semmle.code.java.controlflow.ControlFlow
private import semmle.code.java.controlflow.ControlFlowSpecific
import ControlFlow::PathGraph

/** A variable suspected of being `null`. */
private predicate varMaybeNull(SsaVariable v, string msg, Expr reason) {
  // A variable compared to null might be null.
  exists(Expr e |
    reason = e and
    msg = "as suggested by $@ null guard" and
    guardSuggestsVarMaybeNull(e, v) and
    not v instanceof SsaPhiNode and
    not clearlyNotNull(v) and
    // Comparisons in finally blocks are excluded since missing exception edges in the CFG could otherwise yield FPs.
    not exists(TryStmt try | try.getFinally() = e.getEnclosingStmt().getEnclosingStmt*()) and
    (
      e = any(ConditionalExpr c).getCondition().getAChildExpr*() or
      not exists(MethodAccess ma | ma.getAnArgument().getAChildExpr*() = e)
    ) and
    // Don't use a guard as reason if there is a null assignment.
    not v.(SsaExplicitUpdate).getDefiningExpr().(VariableAssign).getSource() = nullExpr()
  )
  or
  // A parameter might be null if there is a null argument somewhere.
  exists(Parameter p, Expr arg |
    v.(SsaImplicitInit).isParameterDefinition(p) and
    p.getAnArgument() = arg and
    reason = arg and
    msg = "because of $@ null argument" and
    arg = nullExpr() and
    not arg.getEnclosingCallable().getEnclosingCallable*() instanceof TestMethod
  )
  or
  // If the source of a variable is null then the variable may be null.
  exists(VariableAssign def |
    v.(SsaExplicitUpdate).getDefiningExpr() = def and
    def.getSource() = nullExpr() and
    reason = def and
    msg = "because of $@ assignment"
  )
}

class NullnessConfiguration extends ControlFlow::Configuration {
  NullnessConfiguration() { this = "NullnessConfiguration" }

  override predicate isSource(ControlFlow::Node src, ControlFlow::Label l) {
    exists(SsaVariable v |
      src = v.getCFGNode() and
      l.(LabelVar).getVar() = v.getSourceVariable().getVariable() and
      varMaybeNull(v, _, _)
    )
  }

  override predicate isSink(ControlFlow::Node sink, ControlFlow::Label l) {
    dereference(sink) and
    sink.(VarAccess).getVariable() = l.(LabelVar).getVar()
  }
}

from ControlFlow::PathNode src, ControlFlow::PathNode sink, NullnessConfiguration conf
where conf.hasFlow(src, sink)
select sink, src, sink, "null-flow: " + src.getLabel()

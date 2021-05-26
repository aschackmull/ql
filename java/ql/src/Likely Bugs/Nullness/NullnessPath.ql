/**
 * @kind path-problem
 */

import java
private import semmle.code.java.dataflow.SSA
import semmle.code.java.dataflow.NullGuards
import semmle.code.java.controlflow.ControlFlow
import ControlFlow::PathGraph

/** Helpers copied from semmle.code.java.dataflow.Nullness */
module NullHelpers {
  private import semmle.code.java.dataflow.Nullness as N
  private import semmle.code.java.frameworks.Assertions

  /**
   * Gets the `ControlFlowNode` in which the given SSA variable is being dereferenced.
   *
   * The `VarAccess` is included for nicer error reporting.
   */
  private ControlFlowNode varDereference(SsaVariable v, VarAccess va) {
    dereference(result) and
    result = sameValue(v, va)
  }

  /**
   * A `ControlFlowNode` that ensures that the SSA variable is not null in any
   * subsequent use, either by dereferencing it or by an assertion.
   */
  ControlFlowNode ensureNotNull(SsaVariable v) {
    result = varDereference(v, _)
    or
    result.(AssertStmt).getExpr() = nullGuard(v, true, false)
    or
    exists(AssertTrueMethod m | result = m.getACheck(nullGuard(v, true, false)))
    or
    exists(AssertFalseMethod m | result = m.getACheck(nullGuard(v, false, false)))
    or
    exists(AssertNotNullMethod m | result = m.getACheck(v.getAUse()))
    or
    exists(AssertThatMethod m, MethodAccess ma |
      result = m.getACheck(v.getAUse()) and ma.getControlFlowNode() = result
    |
      ma.getAnArgument().(MethodAccess).getMethod().getName() = "notNullValue"
    )
  }

  /** A variable suspected of being `null`. */
  predicate varMaybeNull(SsaVariable v, string msg, Expr reason) {
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
      not v.(SsaExplicitUpdate).getDefiningExpr().(VariableAssign).getSource() = N::nullExpr()
    )
    or
    // A parameter might be null if there is a null argument somewhere.
    exists(Parameter p, Expr arg |
      v.(SsaImplicitInit).isParameterDefinition(p) and
      p.getAnArgument() = arg and
      reason = arg and
      msg = "because of $@ null argument" and
      arg = N::nullExpr() and
      not arg.getEnclosingCallable().getEnclosingCallable*() instanceof TestMethod
    )
    or
    // If the source of a variable is null then the variable may be null.
    exists(VariableAssign def |
      v.(SsaExplicitUpdate).getDefiningExpr() = def and
      def.getSource() = N::nullExpr() and
      reason = def and
      msg = "because of $@ assignment"
    )
  }

  predicate dereference = N::dereference/1;
}

private import NullHelpers

class NullnessConfiguration extends ControlFlow::Configuration {
  NullnessConfiguration() { this = "NullnessConfiguration" }

  override predicate isSource(ControlFlow::Node src, ControlFlow::Label l) {
    exists(SsaVariable v |
      src = v.getCFGNode() and
      l.(ControlFlow::LabelVar).getVar() = v.getSourceVariable().getVariable() and
      varMaybeNull(v, _, _)
    )
  }

  override predicate isSink(ControlFlow::Node sink, ControlFlow::Label l) {
    dereference(sink) and
    sink.(VarAccess).getVariable() = l.(ControlFlow::LabelVar).getVar()
  }

  override predicate isBarrierEdge(ControlFlow::Node n1, ControlFlow::Node n2, ControlFlow::Label l) {
    exists(SsaVariable v |
      v.getSourceVariable().getVariable() = l.(ControlFlow::LabelVar).getVar()
    |
      n1 = ensureNotNull(v) and
      n2 = n1.getASuccessor()
    )
    or
    exists(SsaVariable v, BasicBlock b1, BasicBlock b2, boolean branch |
      v.getSourceVariable().getVariable() = l.(ControlFlow::LabelVar).getVar() and
      n1 = b1.getLastNode() and
      n2 = b2.getFirstNode() and
      nullGuard(v, branch, false).hasBranchEdge(b1, b2, branch)
    )
  }

  override predicate isBarrier(ControlFlow::Node n, ControlFlow::Label l) {
    n.(Assignment).getDest().(VarAccess).getVariable() = l.(ControlFlow::LabelVar).getVar()
  }
}

from ControlFlow::PathNode src, ControlFlow::PathNode sink, NullnessConfiguration conf
where conf.hasFlow(src, sink)
select sink, src, sink, "variable " + src.getLabel() + " might be null"

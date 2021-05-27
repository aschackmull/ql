private import java as J
private import semmle.code.java.dispatch.VirtualDispatch as VD

module Private {
  predicate edge(Node n1, Node n2) { n1.getASuccessor() = n2 }

  class Callable = J::Callable;

  predicate callTarget(CallNode call, Callable target) { VD::viableCallable(call) = target }

  predicate flowEntry(Callable c, Node entry) { c.getBody() = entry }

  predicate flowExit(Callable c, Node exitNode) {
    exists(Node n | n.getASuccessor() = exitNode and exitNode = c)
  }

  Callable getEnclosingCallable(Node n) { n.getEnclosingCallable() = result }

  class Split extends TSplit {
    abstract string toString();

    abstract predicate entry(Node n1, Node n2);

    abstract predicate exit(Node n1, Node n2);

    abstract predicate blocked(Node n1, Node n2);
  }
}

private import Private

private newtype TSplit =
  TSplitFinally(J::BlockStmt finally) { exists(J::TryStmt try | try.getFinally() = finally) }

private class SplitFinally extends Split, TSplitFinally {
  J::BlockStmt finally;

  SplitFinally() { this = TSplitFinally(finally) }

  override string toString() { result = "split finally" }

  override predicate entry(Node n1, Node n2) {
    n1.getAnExceptionSuccessor() = n2 and
    n2 = finally
  }

  private predicate leaving(Node n1, Node n2, boolean exceptionedge) {
    n1.getASuccessor() = n2 and
    n1.getEnclosingStmt().getEnclosingStmt*() = finally and
    not n2.getEnclosingStmt().getEnclosingStmt*() = finally and
    if n1.getAnExceptionSuccessor() = n2 then exceptionedge = true else exceptionedge = false
  }

  override predicate exit(Node n1, Node n2) { this.leaving(n1, n2, _) }

  override predicate blocked(Node n1, Node n2) { this.leaving(n1, n2, false) }
}

private newtype TLabel =
  TLabelUnit() or
  TLabelVar(J::Variable var)

module Public {
  class Node = J::ControlFlowNode;

  class CallNode extends Node {
    CallNode() { this instanceof J::Call }
  }

  abstract class Label extends TLabel {
    abstract string toString();
  }

  class Position extends int {
    Position() { any(J::Parameter p).getPosition() = this }
  }

  class LabelUnit extends Label, TLabelUnit {
    override string toString() { result = "labelunit" }
  }

  class LabelVar extends Label, TLabelVar {
    J::Variable var;

    LabelVar() { this = TLabelVar(var) }

    J::Variable getVar() { result = var }

    override string toString() { result = var.toString() }
  }
}

private import Public

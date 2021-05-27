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
}

private import Private

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

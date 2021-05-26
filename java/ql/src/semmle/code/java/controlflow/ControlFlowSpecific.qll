private import java

module Private {
  predicate edge(Node n1, Node n2) { n1.getASuccessor() = n2 }
}

private import Private

private newtype TLabel =
  TLabelUnit() or
  TLabelVar(Variable var)

module Public {
  class Node = ControlFlowNode;

  abstract class Label extends TLabel {
    abstract string toString();
  }
}

private import Public

class LabelUnit extends Label, TLabelUnit {
  override string toString() { result = "labelunit" }
}

class LabelVar extends Label, TLabelVar {
  Variable var;

  LabelVar() { this = TLabelVar(var) }

  Variable getVar() { result = var }

  override string toString() { result = var.toString() }
}

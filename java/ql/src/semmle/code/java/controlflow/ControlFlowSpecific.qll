private import java

module Private {
  predicate edge(Node n1, Node n2) { n1.getASuccessor() = n2 }
}

private import Private

private newtype TLabel = TLabelUnit()

module Public {
  class Node = ControlFlowNode;

  abstract class Label extends TLabel {
    abstract string toString();
  }
}

private import Public

private class LabelUnit extends Label, TLabelUnit {
  override string toString() { result = "labelunit" }
}

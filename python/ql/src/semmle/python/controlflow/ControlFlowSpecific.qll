private import python

module Private {
  predicate edge(Node n1, Node n2) { n1.getASuccessor() = n2 }
}

private import Private

private newtype TLabel =
  TLabelUnit() or
  TLabelVar(Variable var)

module Public {
  class Node extends ControlFlowNode {
    predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      this.getLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }
  }

  abstract class Label extends TLabel {
    abstract string toString();
  }

  class LabelUnit extends Label, TLabelUnit {
    override string toString() { result = "labelunit" }
  }

  class LabelVar extends Label, TLabelVar {
    Variable var;

    LabelVar() { this = TLabelVar(var) }

    Variable getVar() { result = var }

    override string toString() { result = var.toString() }
  }
}

private import Public

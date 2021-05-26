private import ControlFlowSpecific::Private

module ControlFlow {
  import ControlFlowSpecific::Public

  private predicate bbFirst(Node bb) {
    not edge(_, bb) and edge(bb, _)
    or
    strictcount(Node pred | edge(pred, bb)) > 1
    or
    exists(Node pred | edge(pred, bb) | strictcount(Node succ | edge(pred, succ)) > 1)
  }

  private newtype TBasicBlock = TMkBlock(Node bb) { bbFirst(bb) }

  class BasicBlock extends TBasicBlock {
    Node first;

    BasicBlock() { this = TMkBlock(first) }

    string toString() { result = first.toString() }

    /**
     * Holds if this element is at the specified location.
     * The location spans column `startcolumn` of line `startline` to
     * column `endcolumn` of line `endline` in file `filepath`.
     * For more information, see
     * [Locations](https://help.semmle.com/QL/learn-ql/ql/locations.html).
     */
    predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      first.hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }

    /** Gets an immediate successor of this basic block. */
    cached
    BasicBlock getASuccessor() { edge(this.getLastNode(), result.getFirstNode()) }

    /** Gets an immediate predecessor of this basic block. */
    BasicBlock getAPredecessor() { result.getASuccessor() = this }

    /** Gets a control-flow node contained in this basic block. */
    Node getANode() { result = getNode(_) }

    /** Gets the control-flow node at a specific (zero-indexed) position in this basic block. */
    cached
    Node getNode(int pos) {
      result = first and pos = 0
      or
      exists(Node mid, int mid_pos | pos = mid_pos + 1 |
        getNode(mid_pos) = mid and
        edge(mid, result) and
        not bbFirst(result)
      )
    }

    /** Gets the first control-flow node in this basic block. */
    Node getFirstNode() { result = first }

    /** Gets the last control-flow node in this basic block. */
    Node getLastNode() { result = getNode(length() - 1) }

    /** Gets the number of control-flow nodes contained in this basic block. */
    cached
    int length() { result = strictcount(getANode()) }
  }

  abstract class Configuration extends string {
    bindingset[this]
    Configuration() { any() }

    abstract predicate isSource(Node src, Label l);

    abstract predicate isSink(Node sink, Label l);

    predicate isBarrierEdge(Node n1, Node n2, Label l) { none() }

    predicate isBarrier(Node n, Label l) { none() }

    final predicate hasFlow(PathNode src, PathNode sink) { hasFlow(src, sink, this) }
  }

  private predicate srcBlock(BasicBlock b, int i, Node src, Label l, Configuration conf) {
    src = b.getNode(i) and
    conf.isSource(src, l)
  }

  private predicate sinkBlock(BasicBlock b, int i, Node sink, Label l, Configuration conf) {
    sink = b.getNode(i) and
    conf.isSink(sink, l)
  }

  private predicate barrierBlock(BasicBlock b, int i, Label l, Configuration conf) {
    conf.isBarrier(b.getNode(i), l)
    or
    conf.isBarrierEdge(b.getNode(i - 1), b.getNode(i), l)
  }

  private predicate barrierEdge(BasicBlock b1, BasicBlock b2, Label l, Configuration conf) {
    conf.isBarrierEdge(b1.getLastNode(), b2.getFirstNode(), l)
  }

  private predicate flowFwdEntry(BasicBlock b, Label l, Configuration conf) {
    exists(BasicBlock mid |
      flowFwdExit(mid, l, conf) and
      mid.getASuccessor() = b and
      not barrierEdge(mid, b, l, conf)
    )
  }

  private predicate flowFwdExit(BasicBlock b, Label l, Configuration conf) {
    exists(int i |
      srcBlock(b, i, _, l, conf) and
      not exists(int j | barrierBlock(b, j, l, conf) and i <= j)
    )
    or
    flowFwdEntry(b, l, conf) and
    not barrierBlock(b, _, l, conf)
  }

  private predicate flowRevEntry(BasicBlock b, Label l, Configuration conf) {
    flowFwdEntry(b, l, conf) and
    (
      exists(int i |
        sinkBlock(b, i, _, l, conf) and
        not exists(int j | barrierBlock(b, j, l, conf) and j <= i)
      )
      or
      flowRevExit(b, l, conf) and
      not barrierBlock(b, _, l, conf)
    )
  }

  private predicate flowRevExit(BasicBlock b, Label l, Configuration conf) {
    flowFwdExit(b, l, conf) and
    exists(BasicBlock mid |
      flowRevEntry(mid, l, conf) and
      mid.getAPredecessor() = b and
      not barrierEdge(b, mid, l, conf)
    )
  }

  private newtype TPathNode =
    TPathNodeSrc(Node src, Label l, Configuration conf) { srcBlock(_, _, src, l, conf) } or
    TPathNodeSink(Node sink, Label l, Configuration conf) { sinkBlock(_, _, sink, l, conf) } or
    TPathNodeMidEntry(BasicBlock b, Label l, Configuration conf) { flowRevEntry(b, l, conf) } or
    TPathNodeMidExit(BasicBlock b, Label l, Configuration conf) { flowRevExit(b, l, conf) }

  class PathNode extends TPathNode {
    abstract Node getNode();

    abstract Configuration getConfiguration();

    abstract Label getLabel();

    abstract PathNode getASuccessor();

    string toString() { result = this.getNode().toString() }

    /**
     * Holds if this element is at the specified location.
     * The location spans column `startcolumn` of line `startline` to
     * column `endcolumn` of line `endline` in file `filepath`.
     * For more information, see
     * [Locations](https://help.semmle.com/QL/learn-ql/ql/locations.html).
     */
    predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      this.getNode().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    }
  }

  class PathNodeSrc extends PathNode, TPathNodeSrc {
    Node src;
    Label l;
    Configuration conf;

    PathNodeSrc() { this = TPathNodeSrc(src, l, conf) }

    override Node getNode() { result = src }

    override Configuration getConfiguration() { result = conf }

    override Label getLabel() { result = l }

    override PathNode getASuccessor() {
      exists(BasicBlock b | b.getANode() = src | result = TPathNodeMidExit(b, l, conf))
      or
      exists(BasicBlock b, Node sink, int i, int j |
        srcBlock(b, i, src, l, conf) and
        sinkBlock(b, j, sink, l, conf) and
        i <= j and
        result = TPathNodeSink(sink, l, conf)
      )
    }
  }

  class PathNodeSink extends PathNode, TPathNodeSink {
    Node sink;
    Label l;
    Configuration conf;

    PathNodeSink() { this = TPathNodeSink(sink, l, conf) }

    override Node getNode() { result = sink }

    override Configuration getConfiguration() { result = conf }

    override Label getLabel() { result = l }

    override PathNode getASuccessor() { none() }
  }

  private class PathNodeMidEntry extends PathNode, TPathNodeMidEntry {
    BasicBlock b;
    Label l;
    Configuration conf;

    PathNodeMidEntry() { this = TPathNodeMidEntry(b, l, conf) }

    override Node getNode() { result = b.getFirstNode() }

    override Configuration getConfiguration() { result = conf }

    override Label getLabel() { result = l }

    override PathNode getASuccessor() {
      result = TPathNodeMidExit(b, l, conf)
      or
      result = TPathNodeSink(b.getANode(), l, conf)
    }
  }

  private class PathNodeMidExit extends PathNode, TPathNodeMidExit {
    BasicBlock b;
    Label l;
    Configuration conf;

    PathNodeMidExit() { this = TPathNodeMidExit(b, l, conf) }

    override Node getNode() { result = b.getFirstNode() }

    override Configuration getConfiguration() { result = conf }

    override Label getLabel() { result = l }

    override PathNode getASuccessor() { result = TPathNodeMidEntry(b.getASuccessor(), l, conf) }
  }

  module PathGraph {
    query predicate edges(PathNode n1, PathNode n2) { n1.getASuccessor() = n2 }
  }

  private predicate hasFlow(PathNodeSrc src, PathNodeSink sink, Configuration conf) {
    src.getASuccessor+() = sink and
    conf = src.getConfiguration()
  }
}

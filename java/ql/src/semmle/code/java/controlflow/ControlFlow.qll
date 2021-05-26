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

  private predicate flowFwd(BasicBlock b, Label l, Configuration conf) {
    srcBlock(b, _, _, l, conf)
    or
    exists(BasicBlock mid |
      flowFwd(mid, l, conf) and
      mid.getASuccessor() = b
    )
  }

  private predicate flowRev(BasicBlock b, Label l, Configuration conf) {
    flowFwd(b, l, conf) and
    (
      sinkBlock(b, _, _, l, conf)
      or
      exists(BasicBlock mid |
        flowRev(mid, l, conf) and
        mid.getAPredecessor() = b
      )
    )
  }

  private newtype TPathNode =
    TPathNodeSrc(Node src, Label l, Configuration conf) { srcBlock(_, _, src, l, conf) } or
    TPathNodeSink(Node sink, Label l, Configuration conf) { sinkBlock(_, _, sink, l, conf) } or
    TPathNodeMid(BasicBlock b, Label l, Configuration conf) { flowRev(b, l, conf) }

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
      exists(BasicBlock b | b.getANode() = src | result = TPathNodeMid(b.getASuccessor(), l, conf))
      or
      exists(BasicBlock b | b.getANode() = src |
        result = TPathNodeSink(b.getASuccessor().getANode(), l, conf)
      )
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

  private class PathNodeMid extends PathNode, TPathNodeMid {
    BasicBlock b;
    Label l;
    Configuration conf;

    PathNodeMid() { this = TPathNodeMid(b, l, conf) }

    override Node getNode() { result = b.getFirstNode() }

    override Configuration getConfiguration() { result = conf }

    override Label getLabel() { result = l }

    override PathNode getASuccessor() {
      result = TPathNodeMid(b.getASuccessor(), l, conf)
      or
      exists(BasicBlock succ | succ = b.getASuccessor() |
        result = TPathNodeSink(succ.getANode(), l, conf)
      )
    }
  }

  module PathGraph {
    query predicate edges(PathNode n1, PathNode n2) { n1.getASuccessor() = n2 }
  }

  private predicate hasFlow(PathNodeSrc src, PathNodeSink sink, Configuration conf) {
    src.getASuccessor+() = sink and
    conf = src.getConfiguration()
  }
}

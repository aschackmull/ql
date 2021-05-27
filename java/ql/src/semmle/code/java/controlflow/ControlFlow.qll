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

    predicate callLabel(CallNode c, Label l, Position p) { none() }

    predicate callableLabel(Callable c, Label l, Position p) { none() }

    final predicate hasFlow(PathNode src, PathNode sink) { hasFlow(src, sink, this) }
  }

  private predicate barrierBlock(BasicBlock b, int i, Label l, Configuration conf) {
    conf.isBarrier(b.getNode(i), l)
    or
    conf.isBarrierEdge(b.getNode(i - 1), b.getNode(i), l)
  }

  private predicate barrierEdge(BasicBlock b1, BasicBlock b2, Label l, Configuration conf) {
    conf.isBarrierEdge(b1.getLastNode(), b2.getFirstNode(), l)
  }

  private predicate callTargetUniq(CallNode call, Callable target) {
    target = unique(Callable tgt | callTarget(call, tgt))
  }

  private predicate callTargetUniq(
    Callable c1, Label l1, CallNode call, Callable c2, Label l2, Configuration conf
  ) {
    exists(Position p |
      c1 = getEnclosingCallable(call) and
      callTargetUniq(call, c2) and
      conf.callLabel(call, l1, p) and
      conf.callableLabel(c2, l2, p)
    )
  }

  private predicate callTarget(
    Callable c1, Label l1, CallNode call, Callable c2, Label l2, Configuration conf
  ) {
    exists(Position p |
      c1 = getEnclosingCallable(call) and
      callTarget(call, c2) and
      conf.callLabel(call, l1, p) and
      conf.callableLabel(c2, l2, p)
    )
  }

  private predicate candScopeFwd(Callable c, Label l, boolean cc, Configuration conf) {
    exists(Node src |
      conf.isSource(src, l) and
      c = getEnclosingCallable(src) and
      cc = false
    )
    or
    exists(Callable mid, CallNode call, Label lmid |
      candScopeFwd(mid, lmid, _, conf) and
      callTarget(mid, lmid, call, c, l, conf) and
      cc = true
    )
    or
    exists(Callable mid, CallNode call, Label lmid |
      candScopeFwd(mid, lmid, cc, conf) and
      callTarget(c, l, call, mid, lmid, conf) and
      cc = false
    )
  }

  private predicate candScopeRev(Callable c, Label l, boolean cc, Configuration conf) {
    candScopeFwd(c, l, _, conf) and
    (
      exists(Node sink |
        conf.isSink(sink, l) and
        c = getEnclosingCallable(sink) and
        cc = false
      )
      or
      exists(Callable mid, Label lmid |
        candScopeRev(mid, lmid, _, conf) and
        callTarget(mid, lmid, _, c, l, conf) and
        cc = true
      )
      or
      exists(Callable mid, Label lmid |
        candScopeRev(mid, lmid, cc, conf) and
        callTarget(c, l, _, mid, lmid, conf) and
        cc = false
      )
    )
  }

  private predicate callTarget2(
    Callable c1, Label l1, CallNode call, Callable c2, Label l2, Configuration conf
  ) {
    callTarget(c1, l1, call, c2, l2, conf) and
    candScopeRev(c1, l1, _, pragma[only_bind_into](conf)) and
    candScopeRev(c2, l2, _, pragma[only_bind_into](conf))
  }

  private predicate candScopeBarrierFwd(Callable c, Label l, Configuration conf) {
    candScopeRev(c, l, _, conf)
    or
    exists(Callable mid, Label lmid |
      candScopeBarrierFwd(mid, lmid, conf) and
      callTargetUniq(mid, lmid, _, c, l, conf)
    )
  }

  private predicate candScopeBarrierRev(Callable c, Label l, Configuration conf) {
    candScopeBarrierFwd(c, l, conf) and
    (
      exists(BasicBlock b |
        barrierBlock(b, _, l, conf) and
        c = getEnclosingCallable(b.getFirstNode())
      )
      or
      exists(BasicBlock b |
        barrierEdge(b, _, l, conf) and
        c = getEnclosingCallable(b.getFirstNode())
      )
      or
      exists(Callable mid, Label lmid |
        candScopeBarrierRev(mid, lmid, conf) and
        callTargetUniq(c, l, _, mid, lmid, conf)
      )
    )
  }

  private predicate candLabel(BasicBlock b, Label l, Configuration conf) {
    candScopeRev(getEnclosingCallable(b.getFirstNode()), l, _, conf)
  }

  private predicate candNode(BasicBlock b, int i, Node n, Label l, Configuration conf) {
    (
      conf.isSource(n, l) or
      conf.isSink(n, l) or
      callTarget2(_, l, n, _, _, conf)
    ) and
    b.getNode(i) = n and
    not n = b.getFirstNode() and
    not n = b.getLastNode()
  }

  private predicate step(Node n1, Node n2, Label l, Configuration conf) {
    n1 != n2 and
    (
      // intra-block step
      exists(BasicBlock b, int i, int j |
        candNode(b, i, n1, l, conf) and
        candNode(b, j, n2, l, conf) and
        i <= j and
        not exists(int k | barrierBlock(b, k, l, conf) and i <= k and k <= j)
      )
      or
      // block entry -> node
      exists(BasicBlock b, int i |
        n1 = b.getFirstNode() and
        candNode(b, i, n2, l, conf) and
        not exists(int j | barrierBlock(b, j, l, conf) and j <= i)
      )
      or
      // node -> block end
      exists(BasicBlock b, int i |
        candNode(b, i, n1, l, conf) and
        n2 = b.getLastNode() and
        not exists(int j | barrierBlock(b, j, l, conf) and i <= j)
      )
      or
      // block entry -> block end
      exists(BasicBlock b |
        n1 = b.getFirstNode() and
        n2 = b.getLastNode() and
        candLabel(b, l, conf) and
        not barrierBlock(b, _, l, conf)
      )
      or
      // block end -> block entry
      exists(BasicBlock b1, BasicBlock b2 |
        b1.getASuccessor() = b2 and
        n1 = b1.getLastNode() and
        n2 = b2.getFirstNode() and
        candLabel(b1, l, conf) and
        not barrierEdge(b1, b2, l, conf)
      )
    )
  }

  private predicate flowFwd(Node n, Label l, Configuration conf) {
    candScopeRev(getEnclosingCallable(n), l, _, conf) and
    (
      conf.isSource(n, l)
      or
      exists(Node mid | flowFwd(mid, l, conf) and step(mid, n, l, conf))
      or
      exists(Node call, Label lmid, Callable c |
        flowFwd(call, lmid, conf) and
        callTarget2(_, lmid, call, c, l, conf) and
        flowEntry(c, n)
      )
    )
  }

  private predicate flowRev(Node n, Label l, Configuration conf) {
    flowFwd(n, l, conf) and
    (
      conf.isSink(n, l)
      or
      exists(Node mid | flowRev(mid, l, conf) and step(n, mid, l, conf))
      or
      exists(Node entry, Label lmid, Callable c |
        flowRev(entry, lmid, conf) and
        flowEntry(c, entry) and
        callTarget2(_, l, n, c, lmid, conf)
      )
    )
  }

  private newtype TPathNode =
    TPathNodeMk(Node n, Label l, Configuration conf) { flowRev(n, l, conf) }

  class PathNode extends TPathNode {
    Node n;
    Label l;
    Configuration conf;

    PathNode() { this = TPathNodeMk(n, l, conf) }

    Node getNode() { result = n }

    Label getLabel() { result = l }

    Configuration getConfiguration() { result = conf }

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

    PathNode getASuccessor() {
      exists(Node succ |
        step(n, succ, l, conf) and
        result = TPathNodeMk(succ, l, conf)
      )
      or
      exists(Node succ, Label lsucc, Callable c |
        callTarget2(_, l, n, c, lsucc, conf) and
        flowEntry(c, succ) and
        result = TPathNodeMk(succ, lsucc, conf)
      )
    }

    predicate isSource() { conf.isSource(n, l) }

    predicate isSink() { conf.isSink(n, l) }
  }

  module PathGraph {
    query predicate edges(PathNode n1, PathNode n2) { n1.getASuccessor() = n2 }
  }

  private predicate hasFlow(PathNode src, PathNode sink, Configuration conf) {
    src.isSource() and
    sink.isSink() and
    src.getASuccessor+() = sink and
    conf = src.getConfiguration()
  }
}

private import codeql.util.Location

signature class NodeSig {
  string toString();
}

signature module SplittingSig<LocationSig Location> {
  class Node {
    string toString();

    Location getLocation();
  }

  class SplitKind {
    string toString();

    Location getLocation();

    predicate inScope(Node n);
  }

  class Split {
    string toString();

    Location getLocation();

    SplitKind getKind();

    predicate holds(Node n);
  }
}

signature module GraphSig<NodeSig Node> {
  predicate entry(Node n);

  predicate exit(Node n);

  predicate step(Node n1, Node n2);
}

module Splitting<LocationSig Location, SplittingSig<Location> S, GraphSig<S::Node> G> {
  private import S
  private import G

  pragma[nomagic]
  private predicate splitHolds(Split s, SplitKind k, Node n) {
    s.holds(n) and
    s.getKind() = k
  }

  // k is in scope at n, but no specific Split holds at n
  private predicate noInfoNode(Node n, SplitKind k) {
    k.inScope(n) and
    not splitHolds(_, k, n)
  }

  // k is in scope at n, and n is not dominated by a Split of kind k
  private predicate noSplitFwd(Node n, SplitKind k) {
    noInfoNode(n, k) and
    (
      entry(n)
      or
      exists(Node pred |
        step(pred, n) and
        not k.inScope(pred) and
        not splitHolds(_, k, pred)
      )
    )
    or
    exists(Node mid |
      step(mid, n) and
      noInfoNode(n, k) and
      noSplitFwd(mid, k)
    )
  }

  private predicate noSplitRev(Node n, SplitKind k) {
    noInfoNode(n, k) and
    (
      exit(n)
      or
      exists(Node succ |
        step(n, succ) and
        not k.inScope(succ) and
        not splitHolds(_, k, succ)
      )
    )
    or
    exists(Node mid |
      step(n, mid) and
      noInfoNode(n, k) and
      noSplitRev(mid, k)
    )
  }

  // predicate revReach(Node n, string ent) {
  //   exists(Node ex |
  //     splitExit(_, ex, _, _) and
  //     step*(n, ex) and
  //     ex.toString() = "conf" and
  //     if entry(n) then ent = "entry" else ent = ""
  //   )
  // }
  // n is dominated by one or more Splits of kind k, but no specific Split of kind k holds at n
  private predicate canHaveSplitFwd(Node n, SplitKind k) {
    noInfoNode(n, k) and
    not noSplitFwd(n, k)
  }

  private predicate canHaveSplitRev(Node n, SplitKind k) {
    noInfoNode(n, k) and
    not noSplitRev(n, k)
  }

  private predicate splitEntryStep(Node n1, Node n2, Split s, SplitKind k) {
    step(n1, n2) and
    splitHolds(s, k, n1) and
    noInfoNode(n2, k)
  }

  private predicate splitExitStep(Node n1, Node n2, Split s, SplitKind k) {
    step(n1, n2) and
    splitHolds(s, k, n2) and
    noInfoNode(n1, k)
  }

  private predicate hasSplitFwd(Node n, Split s, SplitKind k) {
    splitEntryStep(_, n, s, k) and
    canHaveSplitFwd(n, k)
    or
    exists(Node mid |
      hasSplitFwd(mid, s, k) and
      step(mid, n) and
      canHaveSplitFwd(n, k)
    )
  }

  private predicate hasSplitRev(Node n, Split s, SplitKind k) {
    splitExitStep(n, _, s, k) and
    canHaveSplitRev(n, k) and
    s.getKind() = k
    or
    exists(Node mid |
      hasSplitRev(mid, s, k) and
      step(n, mid) and
      canHaveSplitRev(n, k)
    )
  }

  predicate barrier1(Node n1, Node n2) {
    exists(Split s1, Split s2, SplitKind k |
      step(n1, n2) and
      splitHolds(s1, pragma[only_bind_into](k), n1) and
      splitHolds(s2, pragma[only_bind_into](k), n2) and
      s1 != s2
    )
  }

  predicate barrier2(Node n1, Node n2) {
    exists(Split s1, Split s2, SplitKind k |
      splitExitStep(n1, n2, s1, k) and
      hasSplitFwd(n1, s2, k) and
      s1 != s2 and
      not hasSplitFwd(n1, s1, k)
    )
  }

  predicate barrier3(Node n1, Node n2) {
    exists(Split s1, Split s2, SplitKind k |
      splitEntryStep(n1, n2, s1, k) and
      hasSplitRev(n2, s2, k) and
      s1 != s2 and
      not hasSplitRev(n2, s1, k)
    )
  }
}

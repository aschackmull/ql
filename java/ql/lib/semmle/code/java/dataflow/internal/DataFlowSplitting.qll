private import java
private import semmle.code.java.dataflow.NullGuards
private import semmle.code.java.dataflow.SSA
private import semmle.code.java.controlflow.Guards
private import semmle.code.java.controlflow.internal.GuardsLogic
private import DataFlowNodes
private import codeql.util.Boolean
private import DataFlowNodes::Public

private newtype TValueProperty =
  TBoolTrueValProp() or
  TNullValProp() or
  TEnumValProp(EnumConstant val) or
  //   TInstanceOfValProp(RefType type) or
  TEqValProp(SsaVariable other)

private class ValueProperty extends TValueProperty {
  string toString() {
    result = "==true" and this = TBoolTrueValProp()
    or
    result = "==null" and this = TNullValProp()
    or
    exists(EnumConstant val | result = "==" + val.toString() and this = TEnumValProp(val))
    or
    // exists(RefType type |
    //   result = "instanceof " + type.toString() and this = TInstanceOfValProp(type)
    // )
    // or
    exists(SsaVariable other | result = "==" + other.toString() and this = TEqValProp(other))
  }
}

private predicate isValPropGuard(
  SsaVariable flag, Guard g, ValueProperty p, Boolean iseq, boolean branch
) {
  sameValue(flag, _) = g and p = TBoolTrueValProp() and branch = iseq
  or
  g = directNullGuard(flag, branch, iseq) and p = TNullValProp()
  or
  exists(EnumConstant val, boolean polarity |
    g.isEquality(sameValue(flag, _), val.getAnAccess(), polarity) and
    p = TEnumValProp(val) and
    branch = polarity.booleanXor(iseq).booleanNot()
  )
  or
  exists(SsaVariable other, boolean polarity |
    // In order for this property to be meaningful throughout the scope of the
    // flag, we need to ensure that the other variable is equally meaningful
    // and constant throughout the same scope.
    other.getBasicBlock().bbDominates(flag.getBasicBlock()) and
    g.isEquality(sameValue(flag, _), sameValue(other, _), polarity) and
    p = TEqValProp(other) and
    branch = polarity.booleanXor(iseq).booleanNot()
  )
  or
  exists(Guard g0, boolean branch0 |
    isValPropGuard(flag, g0, p, iseq, branch0) and
    implies_v3(g, branch, g0, branch0)
  )
}

private predicate valPropGuardControls(
  SsaVariable flag, Guard g, BasicBlock bb, ValueProperty p, boolean iseq
) {
  exists(boolean branch |
    isValPropGuard(flag, g, p, iseq, branch) and g.directlyControls(bb, branch)
  )
}

pragma[nomagic]
private predicate flagCandidate(SsaVariable flag, ValueProperty p) {
  2 <= strictcount(Guard g | valPropGuardControls(flag, g, _, p, _)) and
  not flag.getCfgNode().getEnclosingStmt().getEnclosingStmt*() instanceof LoopStmt
}

private predicate controlReachRev(SsaVariable flag, ValueProperty p, BasicBlock bb) {
  exists(BasicBlock controlled |
    flagCandidate(flag, p) and
    valPropGuardControls(flag, _, controlled, p, _) and
    bb.getABBSuccessor() = controlled and
    not valPropGuardControls(flag, _, bb, p, _)
  )
  or
  exists(BasicBlock succ |
    bb.getABBSuccessor() = succ and
    controlReachRev(flag, p, succ) and
    not succ = flag.getBasicBlock()
  )
}

private predicate flagRelevant(SsaVariable flag, ValueProperty p, BasicBlock bb) {
  exists(BasicBlock prev |
    prev = bb.getABBPredecessor() and
    valPropGuardControls(flag, _, prev, p, _) and
    not valPropGuardControls(flag, _, bb, p, _) and
    controlReachRev(flag, p, bb)
  )
  or
  exists(BasicBlock pred |
    flagRelevant(flag, p, pred) and
    pred.getABBSuccessor() = bb and
    controlReachRev(flag, p, bb)
  )
}

private newtype TSplitKind =
  TValuePropSplitKind(SsaVariable flag, ValueProperty p) { flagRelevant(flag, p, _) }

private newtype TSplit =
  TValuePropSplit(SsaVariable flag, ValueProperty p, Boolean iseq) { flagRelevant(flag, p, _) }

abstract class SplitKind extends TSplitKind {
  abstract string toString();

  abstract Location getLocation();

  abstract predicate inScope(Node n);
}

class ValuePropSplitKind extends SplitKind {
  private SsaVariable flag;
  private ValueProperty p;

  ValuePropSplitKind() { this = TValuePropSplitKind(flag, p) }

  override string toString() { result = flag.toString() + " " + p.toString() }

  override Location getLocation() { result = flag.getLocation() }

  override predicate inScope(Node n) {
    exists(BasicBlock bb |
      flagRelevant(flag, p, bb) and
      bb = getNodeBasicBlock(n)
    )
  }
}

abstract class Split extends TSplit {
  abstract string toString();

  abstract Location getLocation();

  abstract SplitKind getKind();

  abstract predicate holds(Node n);
}

class ValuePropSplit extends Split {
  private SsaVariable flag;
  private ValueProperty p;
  private boolean iseq;

  ValuePropSplit() { this = TValuePropSplit(flag, p, iseq) }

  override string toString() { result = this.getKind().toString() + " is " + iseq }

  override Location getLocation() { result = flag.getLocation() }

  override SplitKind getKind() { result = TValuePropSplitKind(flag, p) }

  override predicate holds(Node n) {
    exists(BasicBlock bb |
      valPropGuardControls(flag, _, bb, p, iseq) and
      bb = getNodeBasicBlock(n)
    )
  }
}

/**
 * INTERNAL: This is part of the virtual dispatch computation.
 *
 * Provides a strengthening of the virtual dispatch relation using a dedicated
 * data flow check for lambdas, anonymous classes, and other sufficiently
 * private classes where all object instantiations are accounted for.
 */

import java
private import VirtualDispatch
private import semmle.code.java.dataflow.internal.BaseSSA
private import semmle.code.java.dataflow.internal.DataFlowUtil as DataFlow
private import semmle.code.java.dataflow.internal.DataFlowPrivate as DataFlowPrivate
private import semmle.code.java.dataflow.InstanceAccess
private import semmle.code.java.Collections
private import semmle.code.java.Maps
private import codeql.typetracking.TypeTracking

/**
 * Gets a viable dispatch target for `ma`. This is the input dispatch relation.
 */
private Method viableImpl_inp(MethodAccess ma) { result = viableImpl_v2(ma) }

private Callable dispatchCand(Call c) {
  c instanceof ConstructorCall and result = c.getCallee().getSourceDeclaration()
  or
  result = viableImpl_inp(c) and
  not dispatchOrigin(_, c, result)
}

/**
 * Holds if `t` and all its enclosing types are public.
 */
pragma[assume_small_delta]
private predicate veryPublic(RefType t) {
  t.isPublic() and
  (
    not t instanceof NestedType or
    veryPublic(t.(NestedType).getEnclosingType())
  )
}

/**
 * Holds if `cie` occurs as the initializer of a public static field.
 */
private predicate publicStaticFieldInit(ClassInstanceExpr cie) {
  exists(Field f |
    f.isStatic() and
    f.isPublic() and
    veryPublic(f.getDeclaringType()) and
    f.getInitializer() = cie
  )
}

/**
 * Holds if a `ClassInstanceExpr` constructing `t` occurs as the initializer of
 * a public static field.
 */
private predicate publicThroughField(RefType t) {
  exists(ClassInstanceExpr cie |
    cie.getConstructedType() = t and
    publicStaticFieldInit(cie)
  )
}

/**
 * Holds if `t` and its subtypes are private or anonymous.
 */
private predicate privateConstruction(RefType t) {
  (t.isPrivate() or t instanceof AnonymousClass) and
  not publicThroughField(t) and
  forall(SrcRefType sub | sub.getASourceSupertype+() = t.getSourceDeclaration() |
    (sub.isPrivate() or sub instanceof AnonymousClass) and
    not publicThroughField(sub)
  )
}

/**
 * Holds if `m` is declared on a type that we will track all instantiations of
 * for the purpose of virtual dispatch to `m`. This holds in particular for
 * lambda methods and methods on other anonymous classes.
 */
private predicate trackedMethod(Method m) {
  privateConstruction(m.getDeclaringType().getSourceDeclaration())
}

/**
 * Holds if `t` declares or inherits the tracked method `m`.
 */
private predicate trackedMethodOnType(Method m, SrcRefType t) {
  exists(Method m0 |
    t.hasMethod(m0, _, _) and
    m = m0.getSourceDeclaration() and
    trackedMethod(m)
  )
}

/**
 * Holds if `ma` may dispatch to the tracked method `m` declared or inherited
 * by the type constructed by `cie`. Thus the dispatch from `ma` to `m` will
 * only be included if `cie` flows to the qualifier of `ma`.
 */
private predicate dispatchOrigin(ClassInstanceExpr cie, MethodAccess ma, Method m) {
  m = viableImpl_inp(ma) and
  not m = ma.getMethod().getSourceDeclaration() and
  trackedMethodOnType(m, cie.getConstructedType().getSourceDeclaration())
}

/** Holds if `t` is a type that is relevant for dispatch flow. */
private predicate relevant(RefType t) {
  exists(ClassInstanceExpr cie |
    dispatchOrigin(cie, _, _) and t = cie.getConstructedType().getSourceDeclaration()
  )
  or
  relevant(t.getErasure())
  or
  exists(RefType r | relevant(r) and t = r.getASourceSupertype())
  or
  relevant(t.(Array).getComponentType())
  or
  t instanceof MapType
  or
  t instanceof CollectionType
}

/** A node with a type that is relevant for dispatch flow. */
private class RelevantNode extends DataFlow::Node {
  RelevantNode() { relevant(this.getType()) }
}

/**
 * Holds if `p` is the `i`th parameter of a viable dispatch target of `call`.
 * The instance parameter is considered to have index `-1`.
 */
pragma[nomagic]
private predicate viableParamCand(Call call, int i, DataFlow::ParameterNode p) {
  exists(DataFlowPrivate::DataFlowCallable callable |
    callable.asCallable() = dispatchCand(call) and
    p.isParameterOf(callable, i) and
    p instanceof RelevantNode
  )
}

/**
 * Holds if `arg` is a possible argument to `p` taking virtual dispatch into account.
 */
private predicate viableArgParamCand(DataFlowPrivate::ArgumentNode arg, DataFlow::ParameterNode p) {
  exists(int i, DataFlowPrivate::DataFlowCall call |
    viableParamCand(call.asCall(), i, p) and
    arg.argumentOf(call, i)
  )
}

/**
 * Holds if data may flow from `n1` to `n2` in a single step through a call or a return.
 */
private predicate callFlowStepCand(RelevantNode n1, RelevantNode n2) {
  exists(ReturnStmt ret, Method m |
    ret.getEnclosingCallable() = m and
    ret.getResult() = n1.asExpr() and
    m = dispatchCand(n2.asExpr())
  )
  or
  viableArgParamCand(n1, n2)
}

/**
 * Holds if data may flow from `n1` to `n2` in a single step that does not go
 * through a call or a return.
 */
private predicate flowStep(RelevantNode n1, RelevantNode n2) {
  exists(BaseSsaVariable v, BaseSsaVariable def |
    def.(BaseSsaUpdate).getDefiningExpr().(VariableAssign).getSource() = n1.asExpr()
    or
    def.(BaseSsaImplicitInit).isParameterDefinition(n1.asParameter())
    or
    exists(EnhancedForStmt for |
      for.getVariable() = def.(BaseSsaUpdate).getDefiningExpr() and
      for.getExpr() = n1.asExpr() and
      n1.getType() instanceof Array
    )
  |
    v.getAnUltimateDefinition() = def and
    v.getAUse() = n2.asExpr()
  )
  or
  exists(Callable c | n1.(DataFlow::InstanceParameterNode).getCallable() = c |
    exists(InstanceAccess ia |
      ia = n2.asExpr() and ia.getEnclosingCallable() = c and ia.isOwnInstanceAccess()
    )
    or
    n2.(DataFlow::ImplicitInstanceAccess)
        .getInstanceAccess()
        .(OwnInstanceAccess)
        .getEnclosingCallable() = c
  )
  or
  n2.(DataFlow::FieldValueNode).getField().getAnAssignedValue() = n1.asExpr()
  or
  n2.asExpr().(FieldRead).getField() = n1.(DataFlow::FieldValueNode).getField()
  or
  exists(EnumType enum, Method getValue |
    enum.getAnEnumConstant().getAnAssignedValue() = n1.asExpr() and
    getValue.getDeclaringType() = enum and
    (getValue.hasName("values") or getValue.hasName("valueOf")) and
    n2.asExpr().(MethodAccess).getMethod() = getValue
  )
  or
  n2.asExpr().(CastingExpr).getExpr() = n1.asExpr()
  or
  n2.asExpr().(ChooseExpr).getAResultExpr() = n1.asExpr()
  or
  n2.asExpr().(AssignExpr).getSource() = n1.asExpr()
  or
  n2.asExpr().(ArrayInit).getAnInit() = n1.asExpr()
  or
  n2.asExpr().(ArrayCreationExpr).getInit() = n1.asExpr()
  or
  n2.asExpr().(ArrayAccess).getArray() = n1.asExpr()
  or
  exists(Argument arg |
    n1.asExpr() = arg and
    arg.isVararg() and
    n2.(DataFlow::ImplicitVarargsArray).getCall() = arg.getCall()
  )
  or
  exists(AssignExpr a, Variable v |
    a.getSource() = n1.asExpr() and
    a.getDest().(ArrayAccess).getArray() = v.getAnAccess() and
    n2.asExpr() = v.getAnAccess().(RValue)
  )
  or
  exists(Variable v, MethodAccess put, MethodAccess get |
    put.getArgument(1) = n1.asExpr() and
    put.getMethod().(MapMethod).hasName("put") and
    put.getQualifier() = v.getAnAccess() and
    get.getQualifier() = v.getAnAccess() and
    get.getMethod().(MapMethod).hasName("get") and
    n2.asExpr() = get
  )
  or
  exists(Variable v, MethodAccess add |
    add.getAnArgument() = n1.asExpr() and
    add.getMethod().(CollectionMethod).hasName("add") and
    add.getQualifier() = v.getAnAccess()
  |
    exists(MethodAccess get |
      get.getQualifier() = v.getAnAccess() and
      get.getMethod().(CollectionMethod).hasName("get") and
      n2.asExpr() = get
    )
    or
    exists(EnhancedForStmt for, BaseSsaVariable ssa, BaseSsaVariable def |
      for.getVariable() = def.(BaseSsaUpdate).getDefiningExpr() and
      for.getExpr() = v.getAnAccess() and
      ssa.getAnUltimateDefinition() = def and
      ssa.getAUse() = n2.asExpr()
    )
  )
}

private module TypeTrackingSteps {
  class Node = RelevantNode;

  class LocalSourceNode extends RelevantNode {
    LocalSourceNode() {
      this.asExpr() instanceof Call or
      this.asExpr() instanceof RValue or
      this instanceof DataFlow::ParameterNode or
      this instanceof DataFlow::ImplicitVarargsArray or
      this.asExpr() instanceof ArrayInit or
      this.asExpr() instanceof ArrayAccess or
      this instanceof DataFlow::FieldValueNode
    }
  }

  private newtype TContent =
    ContentArray() or
    ContentArrayArray()

  class Content extends TContent {
    string toString() {
      this = ContentArray() and result = "array"
      or
      this = ContentArrayArray() and result = "array array"
    }
  }

  class ContentFilter extends Content {
    Content getAMatchingContent() { result = this }
  }

  predicate compatibleContents(Content storeContents, Content loadContents) {
    storeContents = loadContents
  }

  predicate simpleLocalSmallStep(Node n1, Node n2) {
    exists(BaseSsaVariable v, BaseSsaVariable def |
      def.(BaseSsaUpdate).getDefiningExpr().(VariableAssign).getSource() = n1.asExpr()
      or
      def.(BaseSsaImplicitInit).isParameterDefinition(n1.asParameter())
    |
      v.getAnUltimateDefinition() = def and
      v.getAUse() = n2.asExpr()
    )
    or
    exists(Callable c | n1.(DataFlow::InstanceParameterNode).getCallable() = c |
      exists(InstanceAccess ia |
        ia = n2.asExpr() and ia.getEnclosingCallable() = c and ia.isOwnInstanceAccess()
      )
      or
      n2.(DataFlow::ImplicitInstanceAccess)
          .getInstanceAccess()
          .(OwnInstanceAccess)
          .getEnclosingCallable() = c
    )
    or
    n2.asExpr().(CastingExpr).getExpr() = n1.asExpr()
    or
    n2.asExpr().(ChooseExpr).getAResultExpr() = n1.asExpr()
    or
    n2.asExpr().(AssignExpr).getSource() = n1.asExpr()
    or
    n2.asExpr().(ArrayCreationExpr).getInit() = n1.asExpr()
  }

  predicate levelStepNoCall(Node n1, LocalSourceNode n2) {
    exists(EnumType enum, Method getValue |
      enum.getAnEnumConstant().getAnAssignedValue() = n1.asExpr() and
      getValue.getDeclaringType() = enum and
      getValue.hasName("valueOf") and
      n2.asExpr().(MethodAccess).getMethod() = getValue
    )
    or
    exists(Variable v, MethodAccess put, MethodAccess get |
      put.getArgument(1) = n1.asExpr() and
      put.getMethod().(MapMethod).hasName("put") and
      put.getQualifier() = v.getAnAccess() and
      get.getQualifier() = v.getAnAccess() and
      get.getMethod().(MapMethod).hasName("get") and
      n2.asExpr() = get
    )
    or
    exists(Variable v, MethodAccess add |
      add.getAnArgument() = n1.asExpr() and
      add.getMethod().(CollectionMethod).hasName("add") and
      add.getQualifier() = v.getAnAccess()
    |
      exists(MethodAccess get |
        get.getQualifier() = v.getAnAccess() and
        get.getMethod().(CollectionMethod).hasName("get") and
        n2.asExpr() = get
      )
      or
      exists(EnhancedForStmt for, BaseSsaVariable ssa, BaseSsaVariable def |
        for.getVariable() = def.(BaseSsaUpdate).getDefiningExpr() and
        for.getExpr() = v.getAnAccess() and
        ssa.getAnUltimateDefinition() = def and
        ssa.getAUse() = n2.asExpr()
      )
    )
  }

  predicate levelStepCall(Node n1, LocalSourceNode n2) { none() }

  predicate storeStep(Node n1, Node n2, Content f) {
    exists(EnumType enum, Method getValue |
      enum.getAnEnumConstant().getAnAssignedValue() = n1.asExpr() and
      getValue.getDeclaringType() = enum and
      getValue.hasName("values") and
      n2.asExpr().(MethodAccess).getMethod() = getValue and
      f = ContentArray()
    )
    or
    n2.asExpr().(ArrayInit).getAnInit() = n1.asExpr() and
    f = ContentArray()
    or
    exists(Argument arg |
      n1.asExpr() = arg and
      arg.isVararg() and
      n2.(DataFlow::ImplicitVarargsArray).getCall() = arg.getCall() and
      f = ContentArray()
    )
    or
    exists(AssignExpr a, Variable v |
      a.getSource() = n1.asExpr() and
      a.getDest().(ArrayAccess).getArray() = v.getAnAccess() and
      n2.asExpr() = v.getAnAccess().(RValue) and
      f = ContentArray()
    )
  }

  predicate loadStep(Node n1, LocalSourceNode n2, Content f) {
    exists(BaseSsaVariable v, BaseSsaVariable def |
      exists(EnhancedForStmt for |
        for.getVariable() = def.(BaseSsaUpdate).getDefiningExpr() and
        for.getExpr() = n1.asExpr() and
        n1.getType() instanceof Array and
        f = ContentArray()
      )
    |
      v.getAnUltimateDefinition() = def and
      v.getAUse() = n2.asExpr()
    )
    or
    n2.asExpr().(ArrayAccess).getArray() = n1.asExpr()
  }

  predicate loadStoreStep(Node nodeFrom, Node nodeTo, Content f1, Content f2) {
    loadStep(nodeFrom, nodeTo, ContentArray()) and
    f1 = ContentArrayArray() and
    f2 = ContentArray()
    or
    storeStep(nodeFrom, nodeTo, ContentArray()) and
    f1 = ContentArray() and
    f2 = ContentArrayArray()
  }

  predicate withContentStep(Node nodeFrom, LocalSourceNode nodeTo, ContentFilter f) { none() }

  predicate withoutContentStep(Node nodeFrom, LocalSourceNode nodeTo, ContentFilter f) { none() }

  predicate jumpStep(Node n1, LocalSourceNode n2) {
    n2.(DataFlow::FieldValueNode).getField().getAnAssignedValue() = n1.asExpr()
    or
    n2.asExpr().(FieldRead).getField() = n1.(DataFlow::FieldValueNode).getField()
  }

  predicate hasFeatureBacktrackStoreTarget() { none() }
}

private predicate lambdaSource(RelevantNode n) { dispatchOrigin(n.asExpr(), _, _) }

private predicate lambdaSink(RelevantNode n) {
  exists(MethodAccess ma | dispatchOrigin(_, ma, _) | n = DataFlow::getInstanceArgument(ma))
}

private signature Method methodDispatchSig(MethodAccess ma);

private module TrackLambda<methodDispatchSig/1 lambdaDispatch0> {
  private Callable dispatch(Call c) {
    result = dispatchCand(c) or
    result = lambdaDispatch0(c)
  }

  /**
   * Holds if `p` is the `i`th parameter of a viable dispatch target of `call`.
   * The instance parameter is considered to have index `-1`.
   */
  pragma[nomagic]
  private predicate paramCand(Call call, int i, DataFlow::ParameterNode p) {
    exists(DataFlowPrivate::DataFlowCallable callable |
      callable.asCallable() = dispatch(call) and
      p.isParameterOf(callable, i) and
      p instanceof RelevantNode
    )
  }

  /**
   * Holds if `arg` is a possible argument to `p` taking virtual dispatch into account.
   */
  private predicate argParamCand(DataFlowPrivate::ArgumentNode arg, DataFlow::ParameterNode p) {
    exists(int i, DataFlowPrivate::DataFlowCall call |
      paramCand(call.asCall(), i, p) and
      arg.argumentOf(call, i)
    )
  }

  private module TtInput implements TypeTrackingInput {
    import TypeTrackingSteps

    predicate callStep(Node n1, LocalSourceNode n2) { argParamCand(n1, n2) }

    predicate returnStep(Node n1, LocalSourceNode n2) {
      exists(ReturnStmt ret, Method m |
        ret.getEnclosingCallable() = m and
        ret.getResult() = n1.asExpr() and
        m = dispatch(n2.asExpr())
      )
    }
  }

  private import TypeTracking<TtInput>::TypeTrack<lambdaSource/1>::Graph<lambdaSink/1>

  private predicate edgePlus(PathNode n1, PathNode n2) = fastTC(edges/2)(n1, n2)

  private predicate pairCand(PathNode p1, PathNode p2, Method m, MethodAccess ma) {
    exists(ClassInstanceExpr cie |
      dispatchOrigin(cie, ma, m) and
      p1.getNode() = DataFlow::exprNode(cie) and
      p2.getNode() = DataFlow::getInstanceArgument(ma) and
      p1.isSource() and
      p2.isSink()
    )
  }

  Method lambdaDispatch(MethodAccess ma) {
    exists(PathNode p1, PathNode p2 |
      (p1 = p2 or edgePlus(p1, p2)) and
      pairCand(p1, p2, result, ma)
    )
  }

  predicate flow(PathNode p1, PathNode p2, Method m, MethodAccess ma, int grp2) {
    (p1 = p2 or edgePlus(p1, p2)) and
    pairCand(p1, p2, m, ma) and
    // grp1 = clls(m) and
    grp2 = tgts(ma)
  }

  // predicate flow62_2(PathNode p1, PathNode p2, Method m, MethodAccess ma) {
  //   flow(p1, p2, m, ma, 62, 2)
  // }


  /*
  lam ---> qual.m

  disp: qual.m -> lam

  */

  int tgts(MethodAccess ma) { result = strictcount(Method m | m = lambdaDispatch(ma)) }

  int clls(Method m) { result = strictcount(MethodAccess ma | m = lambdaDispatch(ma)) }

  module PathProp2 {
    newtype TNode2 =
      TN(PathNode n) or
      TCall(MethodAccess ma)
      // TCall(MethodAccess ma) { flow(_, _, _, ma, _) }
  // //     TGrpSrc(int grp) { flow(_, _, _, _, grp, _) } or
  // //     TGrpSink(int grp) { flow(_, _, _, _, _, grp) }

  //   class Node2 extends TNode2 {
  //     PathNode getANode() { this = TN(result) }
  //     MethodAccess getACall() { this = TCall(result) }

  // //     int getGrpSrc() { this = TGrpSrc(result) }

  // //     int getGrpSink() { this = TGrpSink(result) }

  //     string toString() {
  //       result = getANode().toString() or
  //       result = getACall().toString()
  //       // result = "src" + getGrpSrc() or
  //       // result = "sink" + getGrpSink()
  //     }

  //     predicate hasLocationInfo(
  //       string filepath, int startline, int startcolumn, int endline, int endcolumn
  //     ) {
  //       getANode().getNode().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  //       or
  //       getACall().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  // //       (exists(getGrpSrc()) or exists(getGrpSink())) and
  // //       filepath = "" and
  // //       startline = 0 and
  // //       startcolumn = 0 and
  // //       endline = 0 and
  // //       endcolumn = 0
  //     }
  //   }

  //   predicate edge(Node2 a, Node2 b) {
  //     edges(a.getANode(), b.getANode()) or
  //     flow(b.getANode(), _, _, a.getACall(), _)
  // //     flow(_, a.getANode(), _, _, _, b.getGrpSink()) or
  // //     flow(b.getANode(), _, _, _, a.getGrpSrc(), _)
  //   }

  //   predicate flow2(Node2 src, Node2 sink, Method m, MethodAccess ma, int tgts) {
  //     flow(_, sink.getANode(), m, ma, tgts) and ma = src.getACall()
  // //     flow(_, _, m, ma, src.getGrpSrc(), sink.getGrpSink())
  //   }
  }
}

/**
 * Holds if `n` is forward-reachable from a relevant `ClassInstanceExpr`.
 */
private predicate nodeCandFwd(DataFlow::Node n) {
  dispatchOrigin(n.asExpr(), _, _)
  or
  exists(DataFlow::Node mid | nodeCandFwd(mid) | flowStep(mid, n) or callFlowStepCand(mid, n))
}

/**
 * Holds if `n` may occur on a dispatch flow path. That is, a path from a
 * relevant `ClassInstanceExpr` to a qualifier of a relevant `MethodAccess`.
 */
private predicate nodeCand(DataFlow::Node n) {
  exists(MethodAccess ma |
    dispatchOrigin(_, ma, _) and
    n = DataFlow::getInstanceArgument(ma) and
    nodeCandFwd(n)
  )
  or
  exists(DataFlow::Node mid | nodeCand(mid) | flowStep(n, mid) or callFlowStepCand(n, mid)) and
  nodeCandFwd(n)
}

/**
 * Holds if `n1 -> n2` is a relevant dispatch flow step.
 */
private predicate step(DataFlow::Node n1, DataFlow::Node n2) {
  (flowStep(n1, n2) or callFlowStepCand(n1, n2)) and
  nodeCand(n1) and
  nodeCand(n2)
}

private predicate stepPlus(DataFlow::Node n1, DataFlow::Node n2) = fastTC(step/2)(n1, n2)

/**
 * Holds if there is flow from a `ClassInstanceExpr` instantiating a type that
 * declares or inherits the tracked method `m` to the qualifier of `ma` such
 * that `ma` may dispatch to `m`.
 */
pragma[inline]
private predicate hasDispatchFlow(MethodAccess ma, Method m) {
  exists(ClassInstanceExpr cie |
    dispatchOrigin(cie, ma, m) and
    stepPlus(DataFlow::exprNode(cie), DataFlow::getInstanceArgument(ma))
  )
}

// pragma[inline]
// private predicate tt1_hasDispatchFlow(MethodAccess ma, Method m) {
//   exists(ClassInstanceExpr cie |
//     dispatchOrigin(cie, ma, m) and
//     TT1::flowPair(exprNode(cie), getInstanceArgument(ma))
//   )
// }
// module TT1 {
// Method noDisp(MethodAccess ma) { none() }
Method n(MethodAccess ma) { none() }

// module TTI1 = TrackLambda<noDisp/1>;
module Disp1 {
  import TrackLambda<n/1>

  pragma[nomagic]
  Method d(MethodAccess ma) { result = lambdaDispatch(ma) }
}

module Disp2 {
  import TrackLambda<Disp1::d/1>

  pragma[nomagic]
  Method d(MethodAccess ma) { result = lambdaDispatch(ma) }
}

module Disp3 {
  import TrackLambda<Disp2::d/1>

  pragma[nomagic]
  Method d(MethodAccess ma) { result = lambdaDispatch(ma) }
}

module Disp4 {
  import TrackLambda<Disp3::d/1>

  pragma[nomagic]
  Method d(MethodAccess ma) { result = lambdaDispatch(ma) }

  // predicate fff = flow62_2/4;
}

module Disp5 {
  import TrackLambda<Disp4::d/1>
  pragma[nomagic]
  Method d(MethodAccess ma) { result = lambdaDispatch(ma) }
}
module Disp6 {
  import TrackLambda<Disp5::d/1>
  pragma[nomagic]
  Method d(MethodAccess ma) { result = lambdaDispatch(ma) }
}
// predicate disp1 = TrackLambda<noDisp/1>::lambdaDispatch/1;
// predicate disp2 = TrackLambda<disp1/1>::lambdaDispatch/1;
// predicate disp3 = TrackLambda<disp2/1>::lambdaDispatch/1;
// predicate disp4 = TrackLambda<disp3/1>::lambdaDispatch/1;
// predicate disp5 = TrackLambda<disp4/1>::lambdaDispatch/1;
// predicate disp6 = TrackLambda<disp5/1>::lambdaDispatch/1;
predicate disp1 = Disp1::d/1;

predicate disp2 = Disp2::d/1;

predicate disp3 = Disp3::d/1;

predicate disp4 = Disp4::d/1;

predicate disp5 = Disp5::d/1;
predicate disp6 = Disp6::d/1;
predicate countdisp(int d1, int d2, int d3, int d4
  , int d5, int d6) {
  d1 = strictcount(MethodAccess ma, Method m | m = disp1(ma)) and
  d2 = strictcount(MethodAccess ma, Method m | m = disp2(ma)) and
  d3 = strictcount(MethodAccess ma, Method m | m = disp3(ma)) and
  d4 = strictcount(MethodAccess ma, Method m | m = disp4(ma))
  and
  d5 = strictcount(MethodAccess ma, Method m | m = disp5(ma)) and
  d6 = strictcount(MethodAccess ma, Method m | m = disp6(ma))
}

// Method tt1_disp(MethodAccess ma) {
//   result = TTI1::lambdaDispatch(ma)
// }
// predicate countdispatch(int i, int notok) {
//   i = strictcount(MethodAccess ma, Method m | m = tt1_disp(ma)) and
//   notok = count(MethodAccess ma, Method m | m = tt1_disp(ma) and not m = lamDisp(ma))
// }
predicate hist_(int calls, int tgts) {
  calls = strictcount(MethodAccess ma | tgts = strictcount(Method m | m = disp4(ma)))
}

// }
// module TT2 {
//   Method disp(MethodAccess ma) { result = TT1::tt1_disp(ma) }
//   module TTI2 = MkTypeTrackingSteps<disp/1>;
//   import TypeTracking<TTI2>::TypeTrack<ttSource/1>::Graph<ttSink/1>
//   predicate flow(PathNode p1, PathNode p2, MethodAccess ma, Method m) {
//     hasFlow(p1, p2) and
//     exists(ClassInstanceExpr cie |
//       dispatchOrigin(cie, ma, m) and
//       p1.getNode() = DataFlow::exprNode(cie) and
//       p2.getNode() = DataFlow::getInstanceArgument(ma)
//     )
//   }
//   Method tt2_disp(MethodAccess ma) {
//     result = viableImpl_inp(ma) and
//     flow(_, _, ma, result)
//   }
//   predicate countdispatch(int i, int notok) {
//     i = strictcount(MethodAccess ma, Method m | m = tt2_disp(ma)) and
//     notok = count(MethodAccess ma, Method m | m = tt2_disp(ma) and not m = lamDisp(ma))
//   }
//   predicate hist_(int calls, int tgts) {
//     calls = strictcount(MethodAccess ma | tgts = strictcount(Method m | m = tt2_disp(ma)))
//   }
// }
predicate countdisp_0(int inp, int out, int removed, int irr, int has, int has2) {
  inp = strictcount(Method m, MethodAccess ma | m = viableImpl_inp(ma)) and
  out = strictcount(Method m, MethodAccess ma | m = viableImpl_out(ma)) and
  removed = inp - out and
  irr =
    strictcount(Method m, MethodAccess ma | m = viableImpl_out(ma) and not dispatchOrigin(_, ma, m)) and
  has = out - irr and
  has2 =
    strictcount(Method m, MethodAccess ma | m = viableImpl_out(ma) and dispatchOrigin(_, ma, m))
  // has = strictcount(Method m, MethodAccess ma | m = viableImpl_inp(ma) and hasDispatchFlow(ma, m))
}
Method lamDisp(MethodAccess ma) {
  result = viableImpl_out(ma) and
  dispatchOrigin(_, ma, result)
}

int targets(MethodAccess ma) { result = strictcount(Method m | m = lamDisp(ma)) }

int calls(Method m) { result = strictcount(MethodAccess ma | m = lamDisp(ma)) }

Method lamDispLarge(MethodAccess ma) {
  result = lamDisp(ma) and
  targets(ma) > 1 and
  calls(result) > 1
}

predicate countProject(int mas, int ms, int mas2, int ms2) {
  mas = strictcount(MethodAccess ma | exists(lamDisp(ma))) and
  ms = strictcount(Method m | m = lamDisp(_)) and
  mas2 = strictcount(MethodAccess ma | exists(lamDispLarge(ma))) and
  ms2 = strictcount(Method m | m = lamDispLarge(_))
}

predicate hist(int calls, int tgts) {
  calls =
    strictcount(MethodAccess ma |
      tgts = strictcount(Method m | m = viableImpl_out(ma) and dispatchOrigin(_, ma, m))
    )
}

predicate hist2(int calls, int tgts) {
  tgts =
    strictcount(Method m |
      calls = strictcount(MethodAccess ma | m = viableImpl_out(ma) and dispatchOrigin(_, ma, m))
    )
}

module PathProb {
  predicate edges1(DataFlow::Node a, DataFlow::Node b) { step(a, b) }

  predicate flow(
    DataFlow::Node src, DataFlow::Node sink, MethodAccess ma, Method m, int srcGroup, int sinkGroup
  ) {
    m = viableImpl_out(ma) and
    dispatchOrigin(src.asExpr(), ma, m) and
    sink = DataFlow::getInstanceArgument(ma) and
    srcGroup = calls(m) and
    sinkGroup = targets(ma)
  }

  predicate countflow(int flow, int groupPairs) {
    flow = strictcount(DataFlow::Node src, DataFlow::Node sink | flow(src, sink, _, _, _, _)) and
    groupPairs = strictcount(int src, int sink | flow(_, _, _, _, src, sink))
  }

  newtype TNode2 =
    TN(DataFlow::Node n) { nodeCand(n) } or
    TGrpSrc(int grp) { flow(_, _, _, _, grp, _) } or
    TGrpSink(int grp) { flow(_, _, _, _, _, grp) }

  class Node2 extends TNode2 {
    DataFlow::Node getANode() { this = TN(result) }

    int getGrpSrc() { this = TGrpSrc(result) }

    int getGrpSink() { this = TGrpSink(result) }

    string toString() {
      result = getANode().toString() or
      result = "src" + getGrpSrc() or
      result = "sink" + getGrpSink()
    }

    predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    ) {
      getANode().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
      or
      (exists(getGrpSrc()) or exists(getGrpSink())) and
      filepath = "" and
      startline = 0 and
      startcolumn = 0 and
      endline = 0 and
      endcolumn = 0
    }
  }

  query predicate edges(Node2 a, Node2 b) {
    edges1(a.getANode(), b.getANode()) or
    flow(_, a.getANode(), _, _, _, b.getGrpSink()) or
    flow(b.getANode(), _, _, _, a.getGrpSrc(), _)
  }

  predicate flow2(Node2 src, Node2 sink, MethodAccess ma, Method m) {
    flow(_, _, ma, m, src.getGrpSrc(), sink.getGrpSink())
  }
}

// Method tt1_viableImpl_out(MethodAccess ma) {
//   result = viableImpl_inp(ma) and
//   (tt1_hasDispatchFlow(ma, result) or not dispatchOrigin(_, ma, result))
// }
/**
 * Gets a viable dispatch target for `ma`. This is the output dispatch relation.
 */
Method viableImpl_out(MethodAccess ma) {
  result = viableImpl_inp(ma) and
  (hasDispatchFlow(ma, result) or not dispatchOrigin(_, ma, result))
}

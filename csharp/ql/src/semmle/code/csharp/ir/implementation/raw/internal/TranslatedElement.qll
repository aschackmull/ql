import csharp
import semmle.code.csharp.ir.implementation.raw.IR
private import semmle.code.csharp.ir.IRConfiguration
private import semmle.code.csharp.ir.implementation.Opcode
private import semmle.code.csharp.ir.implementation.internal.OperandTag
private import semmle.code.csharp.ir.internal.TempVariableTag
private import InstructionTag
private import TranslatedCondition
private import TranslatedFunction
private import TranslatedStmt
private import IRConstruction
private import semmle.code.csharp.ir.Util
private import semmle.code.csharp.ir.internal.IRCSharpLanguage as Language

/**
 * Gets the built-in `int` type.
 */
IntType getIntType() { any() }

ArrayType getArrayOfDim(int dim, Type type) {
  result.getRank() = dim and
  result.getElementType() = type
}

/**
 * Gets the "real" parent of `expr`. This predicate treats conversions as if
 * they were explicit nodes in the expression tree, rather than as implicit
 * nodes as in the regular AST representation.
 */
private Element getRealParent(Expr expr) { result = expr.getParent() }

/**
 * Holds if `expr` is a constant of a type that can be replaced directly with
 * its value in the IR. This does not include address constants as we have no
 * means to express those as QL values.
 */
predicate isIRConstant(Expr expr) { exists(expr.getValue()) }

// Pulled out to work around QL-796
private predicate isOrphan(Expr expr) { not exists(getRealParent(expr)) }

/**
 * Holds if `expr` should be ignored for the purposes of IR generation due to
 * some property of `expr` or one of its ancestors.
 */
private predicate ignoreExprAndDescendants(Expr expr) {
  // Ignore parentless expressions
  isOrphan(expr)
  or
  // Ignore the constants in SwitchCase, since their values are embedded in the
  // CaseEdge.
  getRealParent(expr) instanceof CaseStmt
  or
  // Ignore descendants of constant expressions, since we'll just substitute the
  // constant value.
  isIRConstant(getRealParent(expr))
  or
  ignoreExprAndDescendants(getRealParent(expr)) // recursive case
}

/**
 * Holds if `expr` (not including its descendants) should be ignored for the
 * purposes of IR generation.
 */
private predicate ignoreExprOnly(Expr expr) {
  not translateFunction(expr.getEnclosingCallable())
  or
  // Ignore size of arrays when translating
  expr.getParent() instanceof ArrayCreation and expr.hasValue()
  or
  // Ignore the child expression of a goto case stmt
  expr.getParent() instanceof GotoCaseStmt
}

/**
 * Holds if `expr` should be ignored for the purposes of IR generation.
 */
private predicate ignoreExpr(Expr expr) {
  ignoreExprOnly(expr) or
  ignoreExprAndDescendants(expr)
}

/**
 * Holds if `func` should be translated to IR.
 */
private predicate translateFunction(Callable callable) {
  // not isInvalidFunction(callable)
  exists(callable.getEntryPoint()) and
  exists(IRConfiguration config | config.shouldCreateIRForFunction(callable))
}

/**
 * Holds if `stmt` should be translated to IR.
 */
private predicate translateStmt(Stmt stmt) { translateFunction(stmt.getEnclosingCallable()) }

/**
 * Holds if `expr` is most naturally evaluated as control flow, rather than as
 * a value.
 */
private predicate isNativeCondition(Expr expr) {
  expr instanceof BinaryLogicalOperation and
  not isIRConstant(expr)
}

/**
 * Holds if `expr` can be evaluated as either a condition or a value expression,
 * depending on context.
 */
private predicate isFlexibleCondition(Expr expr) {
  (
    expr instanceof ParenthesizedExpr or
    expr instanceof LogicalNotExpr
  ) and
  usedAsCondition(expr) and
  not isIRConstant(expr)
}

/**
 * Holds if `expr` is used in a condition context, i.e. the Boolean result of
 * the expression is directly used to determine control flow.
 */
private predicate usedAsCondition(Expr expr) {
  exists(BinaryLogicalOperation op |
    op.getLeftOperand() = expr or
    op.getRightOperand() = expr
  )
  or
  exists(LoopStmt loop | loop.getCondition() = expr)
  or
  exists(IfStmt ifStmt | ifStmt.getCondition() = expr)
  or
  exists(ConditionalExpr condExpr | condExpr.getCondition() = expr)
  or
  exists(LogicalNotExpr notExpr |
    notExpr.getOperand() = expr and
    usedAsCondition(notExpr)
  )
  or
  exists(ParenthesizedExpr paren |
    paren.getExpr() = expr and
    usedAsCondition(paren)
  )
}

newtype TTranslatedElement =
  // An expression that is not being consumed as a condition
  TTranslatedValueExpr(Expr expr) {
    not ignoreExpr(expr) and
    not isNativeCondition(expr) and
    not isFlexibleCondition(expr)
  } or
  // A separate element to handle the lvalue-to-rvalue conversion step of an
  // expression.
  TTranslatedLoad(Expr expr) {
    // TODO: Revisit and make sure Loads are only used when needed
    expr instanceof AssignableRead and
    not expr.getParent() instanceof ArrayAccess and
    not (
      expr.getParent() instanceof Assignment and
      expr.getType() instanceof RefType
    ) and
    // Ignore loads for reads in `++` and `--` since their
    // translated elements handle them
    not expr.getParent() instanceof MutatorOperation
  } or
  // An expression most naturally translated as control flow.
  TTranslatedNativeCondition(Expr expr) {
    not ignoreExpr(expr) and
    isNativeCondition(expr)
  } or
  // An expression that can best be translated as control flow given the context
  // in which it is used.
  TTranslatedFlexibleCondition(Expr expr) {
    not ignoreExpr(expr) and
    isFlexibleCondition(expr)
  } or
  // An expression that is not naturally translated as control flow, but is
  // consumed in a condition context. This element adapts the original element
  // to the condition context.
  TTranslatedValueCondition(Expr expr) {
    not ignoreExpr(expr) and
    not isNativeCondition(expr) and
    not isFlexibleCondition(expr) and
    usedAsCondition(expr)
  } or
  // An expression that is naturally translated as control flow, but is used in
  // a context where a simple value is expected. This element adapts the
  // original condition to the value context.
  TTranslatedConditionValue(Expr expr) {
    not ignoreExpr(expr) and
    isNativeCondition(expr) and
    not usedAsCondition(expr)
  } or
  // An expression used as an initializer.
  TTranslatedInitialization(Expr expr) {
    not ignoreExpr(expr) and
    (
      // Because of their implementation in C#,
      // we deal with all the types of initialization separately.
      // First only simple local variable initialization (ie. `int x = 0`)
      exists(LocalVariableDeclAndInitExpr lvInit |
        lvInit.getInitializer() = expr and
        not expr instanceof ArrayCreation and
        not expr instanceof ObjectCreation
      )
      or
      // Then treat more complex ones
      expr instanceof ObjectCreation
      or
      expr instanceof ArrayInitializer
      or
      expr instanceof ObjectInitializer
      or
      expr = any(ThrowExpr throw).getExpr()
      or
      expr = any(CollectionInitializer colInit).getAnElementInitializer()
      or
      expr = any(ReturnStmt returnStmt).getExpr()
      or
      expr = any(ArrayInitializer arrInit).getAnElement()
      or
      expr = any(LambdaExpr lambda).getSourceDeclaration()
      or
      expr = any(AnonymousMethodExpr anonMethExpr).getSourceDeclaration()
    )
  } or
  // The initialization of an array element via a member of an initializer list.
  TTranslatedExplicitElementInitialization(ArrayInitializer initList, int elementIndex) {
    not ignoreExpr(initList) and
    exists(initList.getElement(elementIndex))
  } or
  // The value initialization of a range of array elements that were omitted
  // from an initializer list.
  TTranslatedElementValueInitialization(
    ArrayInitializer initList, int elementIndex, int elementCount
  ) {
    not ignoreExpr(initList) and
    isFirstValueInitializedElementInRange(initList, elementIndex) and
    elementCount = getEndOfValueInitializedRange(initList, elementIndex) - elementIndex
  } or
  // The initialization of a base class from within a constructor.
  TTranslatedConstructorInitializer(ConstructorInitializer init) { not ignoreExpr(init) } or
  // A statement
  TTranslatedStmt(Stmt stmt) { translateStmt(stmt) } or
  // A function
  TTranslatedFunction(Callable callable) { translateFunction(callable) } or
  // A function parameter
  TTranslatedParameter(Parameter param) {
    exists(Callable func |
      func = param.getCallable() and
      translateFunction(func)
    )
  } or
  // A local declaration
  TTranslatedDeclaration(LocalVariableDeclExpr entry)

/**
 * Gets the index of the first explicitly initialized element in `initList`
 * whose index is greater than `afterElementIndex`, where `afterElementIndex`
 * is a first value-initialized element in a value-initialized range in
 * `initList`. If there are no remaining explicitly initialized elements in
 * `initList`, the result is the total number of elements in the array being
 * initialized.
 */
private int getEndOfValueInitializedRange(ArrayInitializer initList, int afterElementIndex) {
  result = getNextExplicitlyInitializedElementAfter(initList, afterElementIndex)
  or
  isFirstValueInitializedElementInRange(initList, afterElementIndex) and
  not exists(getNextExplicitlyInitializedElementAfter(initList, afterElementIndex)) and
  result = initList.getNumberOfElements()
}

/**
 * Gets the index of the first explicitly initialized element in `initList`
 * whose index is greater than `afterElementIndex`, where `afterElementIndex`
 * is a first value-initialized element in a value-initialized range in
 * `initList`.
 */
private int getNextExplicitlyInitializedElementAfter(
  ArrayInitializer initList, int afterElementIndex
) {
  isFirstValueInitializedElementInRange(initList, afterElementIndex) and
  result = min(int i | exists(initList.getElement(i)) and i > afterElementIndex)
}

/**
 * Holds if element `elementIndex` is the first value-initialized element in a
 * range of one or more consecutive value-initialized elements in `initList`.
 */
private predicate isFirstValueInitializedElementInRange(ArrayInitWithMod initList, int elementIndex) {
  initList.isValueInitialized(elementIndex) and
  (
    elementIndex = 0 or
    not initList.isValueInitialized(elementIndex - 1)
  )
}

/**
 * Represents an AST node for which IR needs to be generated.
 *
 * In most cases, there is a single `TranslatedElement` for each AST node.
 * However, when a single AST node performs two separable operations (e.g.
 * a `VariableAccess` that is also a load), there may be multiple
 * `TranslatedElement` nodes for a single AST node.
 */
abstract class TranslatedElement extends TTranslatedElement {
  abstract string toString();

  /**
   * Gets the AST node being translated.
   */
  abstract Language::AST getAST();

  /**
   * Get the first instruction to be executed in the evaluation of this element.
   */
  abstract Instruction getFirstInstruction();

  /**
   * Get the immediate child elements of this element.
   */
  final TranslatedElement getAChild() { result = this.getChild(_) }

  /**
   * Gets the immediate child element of this element. The `id` is unique
   * among all children of this element, but the values are not necessarily
   * consecutive.
   */
  abstract TranslatedElement getChild(int id);

  /**
   * Gets the an identifier string for the element. This string is unique within
   * the scope of the element's function.
   */
  final string getId() { result = this.getUniqueId().toString() }

  private TranslatedElement getChildByRank(int rankIndex) {
    result = rank[rankIndex + 1](TranslatedElement child, int id |
        child = this.getChild(id)
      |
        child order by id
      )
  }

  language[monotonicAggregates]
  private int getDescendantCount() {
    result = 1 +
        sum(TranslatedElement child | child = this.getChildByRank(_) | child.getDescendantCount())
  }

  private int getUniqueId() {
    if not exists(this.getParent())
    then result = 0
    else
      exists(TranslatedElement parent |
        parent = this.getParent() and
        if this = parent.getChildByRank(0)
        then result = 1 + parent.getUniqueId()
        else
          exists(int childIndex, TranslatedElement previousChild |
            this = parent.getChildByRank(childIndex) and
            previousChild = parent.getChildByRank(childIndex - 1) and
            result = previousChild.getUniqueId() + previousChild.getDescendantCount()
          )
      )
  }

  /**
   * Holds if this element generates an instruction with opcode `opcode` and
   * result type `resultType`. `tag` must be unique for each instruction
   * generated from the same AST node (not just from the same
   * `TranslatedElement`).
   * If the instruction does not return a result, `resultType` should be
   * `VoidType`.
   */
  abstract predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  );

  /**
   * Gets the `Function` that contains this element.
   */
  abstract Callable getFunction();

  /**
   * Gets the successor instruction of the instruction that was generated by
   * this element for tag `tag`. The successor edge kind is specified by `kind`.
   */
  abstract Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind);

  /**
   * Gets the successor instruction to which control should flow after the
   * child element specified by `child` has finished execution.
   */
  abstract Instruction getChildSuccessor(TranslatedElement child);

  /**
   * Gets the instruction to which control should flow if an exception is thrown
   * within this element. This will generally return first `catch` block of the
   * nearest enclosing `try`, or the `Unwind` instruction for the function if
   * there is no enclosing `try`.
   */
  Instruction getExceptionSuccessorInstruction() {
    result = getParent().getExceptionSuccessorInstruction()
  }

  /**
   * Gets the primary instruction for the side effect instruction that was
   * generated by this element for tag `tag`.
   */
  Instruction getPrimaryInstructionForSideEffect(InstructionTag tag) { none() }

  /**
   * Holds if this element generates a temporary variable with type `type`.
   * `tag` must be unique for each variable generated from the same AST node
   * (not just from the same `TranslatedElement`).
   */
  predicate hasTempVariable(TempVariableTag tag, Type type) { none() }

  /**
   * If the instruction specified by `tag` is a `FunctionInstruction`, gets the
   * `Function` for that instruction.
   */
  Callable getInstructionFunction(InstructionTag tag) { none() }

  /**
   * If the instruction specified by `tag` is a `VariableInstruction`, gets the
   * `IRVariable` for that instruction.
   */
  IRVariable getInstructionVariable(InstructionTag tag) { none() }

  /**
   * If the instruction specified by `tag` is a `FieldInstruction`, gets the
   * `Field` for that instruction.
   */
  Field getInstructionField(InstructionTag tag) { none() }

  /**
   * If the instruction specified by `tag` is an `IndexedElementInstruction`,
   * gets the `ArrayAccess` of that instruction.
   */
  ArrayAccess getInstructionArrayAccess(InstructionTag tag) { none() }

  /**
   * If the instruction specified by `tag` is a `ConstantValueInstruction`, gets
   * the constant value for that instruction.
   */
  string getInstructionConstantValue(InstructionTag tag) { none() }

  /**
   * If the instruction specified by `tag` is a `PointerArithmeticInstruction`,
   * gets the size of the type pointed to by the pointer.
   */
  int getInstructionElementSize(InstructionTag tag) { none() }

  /**
   * If the instruction specified by `tag` has a result of type `UnknownType`,
   * gets the size of the result in bytes. If the result does not have a knonwn
   * constant size, this predicate does not hold.
   */
  int getInstructionResultSize(InstructionTag tag) { none() }

  /**
   * If the instruction specified by `tag` is a `StringConstantInstruction`,
   * gets the `StringLiteral` for that instruction.
   */
  StringLiteral getInstructionStringLiteral(InstructionTag tag) { none() }

  /**
   * If the instruction specified by `tag` is a `CatchByTypeInstruction`,
   * gets the type of the exception to be caught.
   */
  Type getInstructionExceptionType(InstructionTag tag) { none() }

  /**
   * If the instruction specified by `tag` is an `InheritanceConversionInstruction`,
   * gets the inheritance relationship for that instruction.
   */
  predicate getInstructionInheritance(InstructionTag tag, Class baseClass, Class derivedClass) {
    none()
  }

  /**
   * Gets the instruction whose result is consumed as an operand of the
   * instruction specified by `tag`, with the operand specified by `operandTag`.
   */
  Instruction getInstructionOperand(InstructionTag tag, OperandTag operandTag) { none() }

  /**
   * Gets the type of the memory operand specified by `operandTag` on the the instruction specified by `tag`.
   */
  Type getInstructionOperandType(InstructionTag tag, TypedOperandTag operandTag) { none() }

  /**
   * Gets the size of the memory operand specified by `operandTag` on the the instruction specified by `tag`.
   * Only holds for operands whose type is `UnknownType`.
   */
  int getInstructionOperandSize(InstructionTag tag, SideEffectOperandTag operandTag) { none() }

  /**
   * Gets the instruction generated by this element with tag `tag`.
   */
  final Instruction getInstruction(InstructionTag tag) {
    getInstructionTranslatedElement(result) = this and
    getInstructionTag(result) = tag
  }

  /**
   * Gets the temporary variable generated by this element with tag `tag`.
   */
  final IRTempVariable getTempVariable(TempVariableTag tag) {
    result.getAST() = getAST() and
    result.getTag() = tag and
    this.hasTempVariable(tag, _)
  }

  /**
   * Gets the parent element of this element.
   */
  final TranslatedElement getParent() { result.getAChild() = this }
}

import csharp
private import semmle.code.csharp.ir.internal.TempVariableTag
private import semmle.code.csharp.ir.implementation.internal.OperandTag
private import InstructionTag
private import TranslatedCondition
private import TranslatedDeclaration
private import TranslatedElement
private import TranslatedExpr
private import TranslatedFunction
private import TranslatedInitialization
private import IRInternal
private import semmle.code.csharp.ir.internal.IRUtilities

TranslatedStmt getTranslatedStmt(Stmt stmt) { result.getAST() = stmt }

abstract class TranslatedStmt extends TranslatedElement, TTranslatedStmt {
  Stmt stmt;

  TranslatedStmt() { this = TTranslatedStmt(stmt) }

  final override string toString() { result = stmt.toString() }

  final override Language::AST getAST() { result = stmt }

  final override Callable getFunction() { result = stmt.getEnclosingCallable() }
}

class TranslatedEmptyStmt extends TranslatedStmt {
  TranslatedEmptyStmt() {
    stmt instanceof EmptyStmt or
    stmt instanceof LabelStmt or
    stmt instanceof CaseStmt
  }

  override TranslatedElement getChild(int id) { none() }

  override Instruction getFirstInstruction() { result = this.getInstruction(OnlyInstructionTag()) }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    tag = OnlyInstructionTag() and
    opcode instanceof Opcode::NoOp and
    resultType instanceof VoidType and
    isLValue = false
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = OnlyInstructionTag() and
    result = this.getParent().getChildSuccessor(this) and
    kind instanceof GotoEdge
  }

  override Instruction getChildSuccessor(TranslatedElement child) { none() }
}

class TranslatedDeclStmt extends TranslatedStmt {
  override LocalVariableDeclStmt stmt;

  override TranslatedElement getChild(int id) { result = this.getLocalDeclaration(id) }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    none()
  }

  override Instruction getFirstInstruction() {
    result = this.getLocalDeclaration(0).getFirstInstruction()
  }

  private int getChildCount() { result = count(stmt.getAVariableDeclExpr()) }

  private TranslatedLocalDeclaration getLocalDeclaration(int index) {
    result = getTranslatedLocalDeclaration(stmt.getVariableDeclExpr(index))
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  override Instruction getChildSuccessor(TranslatedElement child) {
    exists(int index |
      child = this.getLocalDeclaration(index) and
      if index = (getChildCount() - 1)
      then result = this.getParent().getChildSuccessor(this)
      else result = this.getLocalDeclaration(index + 1).getFirstInstruction()
    )
  }
}

class TranslatedExprStmt extends TranslatedStmt {
  override ExprStmt stmt;

  TranslatedExpr getExpr() { result = getTranslatedExpr(stmt.(ExprStmt).getExpr()) }

  override TranslatedElement getChild(int id) { id = 0 and result = this.getExpr() }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    none()
  }

  override Instruction getFirstInstruction() { result = this.getExpr().getFirstInstruction() }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  override Instruction getChildSuccessor(TranslatedElement child) {
    child = this.getExpr() and
    result = this.getParent().getChildSuccessor(this)
  }
}

/**
 * Class that deals with an `ExprStmt` whose child is an `AssignExpr` whose
 * lvalue is an accessor call.
 * Since we desugar such an expression to function call,
 * we ignore the assignment and make the only child of the translated statement
 * the accessor call.
 */
class TranslatedExprStmtAccessorSet extends TranslatedExprStmt {
  override ExprStmt stmt;

  TranslatedExprStmtAccessorSet() {
    stmt.getExpr() instanceof AssignExpr and
    stmt.getExpr().(AssignExpr).getLValue() instanceof AccessorCall
  }

  override TranslatedExpr getExpr() {
    result = getTranslatedExpr(stmt.(ExprStmt).getExpr().(AssignExpr).getLValue())
  }

  override TranslatedElement getChild(int id) { id = 0 and result = this.getExpr() }

  override Instruction getFirstInstruction() { result = this.getExpr().getFirstInstruction() }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  override Instruction getChildSuccessor(TranslatedElement child) {
    child = this.getExpr() and
    result = this.getParent().getChildSuccessor(this)
  }
}

abstract class TranslatedReturnStmt extends TranslatedStmt {
  override ReturnStmt stmt;

  final TranslatedFunction getEnclosingFunction() {
    result = getTranslatedFunction(stmt.getEnclosingCallable())
  }
}

class TranslatedReturnValueStmt extends TranslatedReturnStmt, InitializationContext {
  TranslatedReturnValueStmt() { exists(stmt.getExpr()) }

  override TranslatedElement getChild(int id) { id = 0 and result = this.getInitialization() }

  override Instruction getFirstInstruction() {
    result = this.getInstruction(InitializerVariableAddressTag())
  }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    tag = InitializerVariableAddressTag() and
    opcode instanceof Opcode::VariableAddress and
    resultType = this.getEnclosingFunction().getReturnVariable().getType() and
    isLValue = true
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = InitializerVariableAddressTag() and
    result = this.getInitialization().getFirstInstruction() and
    kind instanceof GotoEdge
  }

  override Instruction getChildSuccessor(TranslatedElement child) {
    child = this.getInitialization() and
    result = this.getEnclosingFunction().getReturnSuccessorInstruction()
  }

  override IRVariable getInstructionVariable(InstructionTag tag) {
    tag = InitializerVariableAddressTag() and
    result = this.getEnclosingFunction().getReturnVariable()
  }

  override Instruction getTargetAddress() {
    result = this.getInstruction(InitializerVariableAddressTag())
  }

  override Type getTargetType() {
    result = this.getEnclosingFunction().getReturnVariable().getType()
  }

  TranslatedInitialization getInitialization() {
    result = getTranslatedInitialization(stmt.getExpr())
  }
}

class TranslatedReturnVoidStmt extends TranslatedReturnStmt {
  TranslatedReturnVoidStmt() { not exists(stmt.getExpr()) }

  override TranslatedElement getChild(int id) { none() }

  override Instruction getFirstInstruction() { result = this.getInstruction(OnlyInstructionTag()) }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    tag = OnlyInstructionTag() and
    opcode instanceof Opcode::NoOp and
    resultType instanceof VoidType and
    isLValue = false
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = OnlyInstructionTag() and
    result = this.getEnclosingFunction().getReturnSuccessorInstruction() and
    kind instanceof GotoEdge
  }

  override Instruction getChildSuccessor(TranslatedElement child) { none() }
}

/**
 * The IR translation of a C++ `try` statement.
 */
// TODO: Make sure that if the exception is uncaught or rethrown
//       finally is still executed.
class TranslatedTryStmt extends TranslatedStmt {
  override TryStmt stmt;

  override TranslatedElement getChild(int id) {
    id = 0 and result = this.getBody()
    or
    id = 1 and result = this.getFinally()
    or
    result = this.getCatchClause(id - 2)
  }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    none()
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  override Instruction getFirstInstruction() { result = this.getBody().getFirstInstruction() }

  override Instruction getChildSuccessor(TranslatedElement child) {
    child = this.getCatchClause(_) and result = this.getFinally().getFirstInstruction()
    or
    child = this.getBody() and result = this.getFinally().getFirstInstruction()
    or
    child = this.getFinally() and result = this.getParent().getChildSuccessor(this)
  }

  final Instruction getNextHandler(TranslatedClause clause) {
    exists(int index |
      clause = this.getCatchClause(index) and
      result = this.getCatchClause(index + 1).getFirstInstruction()
    )
    or
    // The last catch clause flows to the exception successor of the parent
    // of the `try`, because the exception successor of the `try` itself is
    // the first catch clause.
    clause = this.getCatchClause(count(stmt.getACatchClause()) - 1) and
    result = this.getParent().getExceptionSuccessorInstruction()
  }

  final override Instruction getExceptionSuccessorInstruction() {
    result = this.getCatchClause(0).getFirstInstruction()
  }

  private TranslatedClause getCatchClause(int index) {
    result = getTranslatedStmt(stmt.getCatchClause(index))
  }

  private TranslatedStmt getFinally() { result = getTranslatedStmt(stmt.getFinally()) }

  private TranslatedStmt getBody() { result = getTranslatedStmt(stmt.getBlock()) }
}

class TranslatedBlock extends TranslatedStmt {
  override BlockStmt stmt;

  override TranslatedElement getChild(int id) { result = this.getStmt(id) }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    isEmpty() and
    opcode instanceof Opcode::NoOp and
    tag = OnlyInstructionTag() and
    resultType instanceof VoidType and
    isLValue = false
  }

  override Instruction getFirstInstruction() {
    if isEmpty()
    then result = this.getInstruction(OnlyInstructionTag())
    else result = this.getStmt(0).getFirstInstruction()
  }

  private predicate isEmpty() { stmt.isEmpty() }

  private TranslatedStmt getStmt(int index) { result = getTranslatedStmt(stmt.getStmt(index)) }

  private int getStmtCount() { result = count(stmt.getAStmt()) }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = OnlyInstructionTag() and
    result = this.getParent().getChildSuccessor(this) and
    kind instanceof GotoEdge
  }

  override Instruction getChildSuccessor(TranslatedElement child) {
    exists(int index |
      child = this.getStmt(index) and
      if index = (getStmtCount() - 1)
      then result = this.getParent().getChildSuccessor(this)
      else result = this.getStmt(index + 1).getFirstInstruction()
    )
  }
}

/**
 * The IR translation of a C# `catch` clause.
 */
abstract class TranslatedClause extends TranslatedStmt {
  override CatchClause stmt;

  override TranslatedElement getChild(int id) { id = 1 and result = this.getBlock() }

  override Instruction getFirstInstruction() { result = this.getInstruction(CatchTag()) }

  override Instruction getChildSuccessor(TranslatedElement child) {
    child = this.getBlock() and result = this.getParent().getChildSuccessor(this)
  }

  override Instruction getExceptionSuccessorInstruction() {
    // A throw from within a `catch` block flows to the handler for the parent of
    // the `try`.
    result = this.getParent().getParent().getExceptionSuccessorInstruction()
  }

  TranslatedStmt getBlock() { result = getTranslatedStmt(stmt.getBlock()) }
}

/**
 * The IR translation of a C# `catch` block that catches an exception with a
 * specific type (e.g. `catch (Exception ex) { ... }`).
 */
class TranslatedCatchByTypeClause extends TranslatedClause {
  TranslatedCatchByTypeClause() { stmt instanceof SpecificCatchClause }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    tag = CatchTag() and
    opcode instanceof Opcode::CatchByType and
    resultType instanceof VoidType and
    isLValue = false
  }

  override TranslatedElement getChild(int id) {
    id = 0 and result = getParameter()
    or
    result = super.getChild(id)
  }

  override Instruction getChildSuccessor(TranslatedElement child) {
    result = super.getChildSuccessor(child)
    or
    child = getParameter() and result = this.getBlock().getFirstInstruction()
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = CatchTag() and
    (
      kind instanceof GotoEdge and
      result = getParameter().getFirstInstruction()
      or
      kind instanceof ExceptionEdge and
      result = this.getParent().(TranslatedTryStmt).getNextHandler(this)
    )
  }

  override Type getInstructionExceptionType(InstructionTag tag) {
    tag = CatchTag() and
    result = stmt.(SpecificCatchClause).getVariable().getType()
  }

  private TranslatedLocalDeclaration getParameter() {
    result = getTranslatedLocalDeclaration(stmt.(SpecificCatchClause).getVariableDeclExpr())
  }
}

/**
 * The IR translation of catch block with no parameters.
 */
class TranslatedGeneralCatchClause extends TranslatedClause {
  TranslatedGeneralCatchClause() { stmt instanceof GeneralCatchClause }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    tag = CatchTag() and
    opcode instanceof Opcode::CatchAny and
    resultType instanceof VoidType and
    isLValue = false
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = CatchTag() and
    kind instanceof GotoEdge and
    result = this.getBlock().getFirstInstruction()
  }
}

/**
 * The IR translation of a throw statement that throws an exception,
 * as oposed to just rethrowing one.
 */
class TranslatedThrowExceptionStmt extends TranslatedStmt, InitializationContext {
  override ThrowStmt stmt;

  TranslatedThrowExceptionStmt() {
    // Must throw an exception
    exists(stmt.getExpr())
  }

  override TranslatedElement getChild(int id) { id = 0 and result = this.getInitialization() }

  override Instruction getFirstInstruction() {
    result = this.getInstruction(InitializerVariableAddressTag())
  }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    tag = ThrowTag() and
    opcode instanceof Opcode::ThrowValue and
    resultType instanceof VoidType and
    isLValue = false
    or
    tag = InitializerVariableAddressTag() and
    opcode instanceof Opcode::VariableAddress and
    resultType = this.getExceptionType() and
    isLValue = true
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = ThrowTag() and
    kind instanceof ExceptionEdge and
    result = this.getParent().getExceptionSuccessorInstruction()
    or
    tag = InitializerVariableAddressTag() and
    result = this.getInitialization().getFirstInstruction() and
    kind instanceof GotoEdge
  }

  override Instruction getChildSuccessor(TranslatedElement child) {
    child = this.getInitialization() and
    result = this.getInstruction(ThrowTag())
  }

  override IRVariable getInstructionVariable(InstructionTag tag) {
    tag = InitializerVariableAddressTag() and
    result = getIRTempVariable(stmt, ThrowTempVar())
  }

  final override predicate hasTempVariable(TempVariableTag tag, Type type) {
    tag = ThrowTempVar() and
    type = this.getExceptionType()
  }

  final override Instruction getInstructionOperand(InstructionTag tag, OperandTag operandTag) {
    tag = ThrowTag() and
    (
      operandTag instanceof AddressOperandTag and
      result = this.getInstruction(InitializerVariableAddressTag())
      or
      operandTag instanceof LoadOperandTag and
      result = getTranslatedFunction(stmt.getEnclosingCallable())
            .getUnmodeledDefinitionInstruction()
    )
  }

  final override Type getInstructionOperandType(InstructionTag tag, TypedOperandTag operandTag) {
    tag = ThrowTag() and
    operandTag instanceof LoadOperandTag and
    result = this.getExceptionType()
  }

  override Instruction getTargetAddress() {
    result = this.getInstruction(InitializerVariableAddressTag())
  }

  override Type getTargetType() { result = this.getExceptionType() }

  TranslatedInitialization getInitialization() {
    result = getTranslatedInitialization(stmt.getExpr())
  }

  private Type getExceptionType() { result = stmt.getExpr().getType() }
}

/**
 * The IR translation of a simple throw statement, ie. one that just
 * rethrows an exception.
 */
class TranslatedEmptyThrowStmt extends TranslatedStmt {
  override ThrowStmt stmt;

  TranslatedEmptyThrowStmt() { not exists(stmt.getExpr()) }

  override TranslatedElement getChild(int id) { none() }

  override Instruction getFirstInstruction() { result = this.getInstruction(ThrowTag()) }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    tag = ThrowTag() and
    opcode instanceof Opcode::ReThrow and
    resultType instanceof VoidType and
    isLValue = false
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = ThrowTag() and
    kind instanceof ExceptionEdge and
    result = this.getParent().getExceptionSuccessorInstruction()
  }

  override Instruction getChildSuccessor(TranslatedElement child) { none() }
}

class TranslatedIfStmt extends TranslatedStmt, ConditionContext {
  override IfStmt stmt;

  override Instruction getFirstInstruction() { result = this.getCondition().getFirstInstruction() }

  override TranslatedElement getChild(int id) {
    id = 0 and result = this.getCondition()
    or
    id = 1 and result = this.getThen()
    or
    id = 2 and result = this.getElse()
  }

  private TranslatedCondition getCondition() {
    result = getTranslatedCondition(stmt.getCondition())
  }

  private TranslatedStmt getThen() { result = getTranslatedStmt(stmt.getThen()) }

  private TranslatedStmt getElse() { result = getTranslatedStmt(stmt.getElse()) }

  private predicate hasElse() { exists(stmt.getElse()) }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  override Instruction getChildTrueSuccessor(TranslatedCondition child) {
    child = this.getCondition() and
    result = this.getThen().getFirstInstruction()
  }

  override Instruction getChildFalseSuccessor(TranslatedCondition child) {
    child = this.getCondition() and
    if this.hasElse()
    then result = this.getElse().getFirstInstruction()
    else result = this.getParent().getChildSuccessor(this)
  }

  override Instruction getChildSuccessor(TranslatedElement child) {
    (child = this.getThen() or child = this.getElse()) and
    result = this.getParent().getChildSuccessor(this)
  }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    none()
  }
}

abstract class TranslatedLoop extends TranslatedStmt, ConditionContext {
  override LoopStmt stmt;

  final TranslatedCondition getCondition() { result = getTranslatedCondition(stmt.getCondition()) }

  final TranslatedStmt getBody() { result = getTranslatedStmt(stmt.getBody()) }

  final Instruction getFirstConditionInstruction() {
    if hasCondition()
    then result = getCondition().getFirstInstruction()
    else result = this.getBody().getFirstInstruction()
  }

  final predicate hasCondition() { exists(stmt.getCondition()) }

  override TranslatedElement getChild(int id) {
    id = 0 and result = this.getCondition()
    or
    id = 1 and result = this.getBody()
  }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    none()
  }

  final override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  final override Instruction getChildTrueSuccessor(TranslatedCondition child) {
    child = this.getCondition() and result = this.getBody().getFirstInstruction()
  }

  final override Instruction getChildFalseSuccessor(TranslatedCondition child) {
    child = this.getCondition() and result = this.getParent().getChildSuccessor(this)
  }
}

class TranslatedWhileStmt extends TranslatedLoop {
  TranslatedWhileStmt() { stmt instanceof WhileStmt }

  override Instruction getFirstInstruction() { result = this.getFirstConditionInstruction() }

  override Instruction getChildSuccessor(TranslatedElement child) {
    child = this.getBody() and result = this.getFirstConditionInstruction()
  }
}

class TranslatedDoStmt extends TranslatedLoop {
  TranslatedDoStmt() { stmt instanceof DoStmt }

  override Instruction getFirstInstruction() { result = this.getBody().getFirstInstruction() }

  override Instruction getChildSuccessor(TranslatedElement child) {
    child = this.getBody() and result = this.getFirstConditionInstruction()
  }
}

class TranslatedForStmt extends TranslatedLoop {
  override ForStmt stmt;

  override TranslatedElement getChild(int id) {
    id = 0 and result = this.getDeclAndInit()
    or
    id = 1 and result = this.getCondition()
    or
    id = 2 and result = this.getUpdate()
    or
    id = 3 and result = this.getBody()
  }

  private TranslatedLocalDeclaration getDeclAndInit() {
    result = getTranslatedLocalDeclaration(stmt.getAnInitializer())
  }

  private predicate hasInitialization() { exists(stmt.getAnInitializer()) }

  TranslatedExpr getUpdate() { result = getTranslatedExpr(stmt.getAnUpdate()) }

  private predicate hasUpdate() { exists(stmt.getAnUpdate()) }

  override Instruction getFirstInstruction() {
    if this.hasInitialization()
    then result = this.getDeclAndInit().getFirstInstruction()
    else result = this.getFirstConditionInstruction()
  }

  override Instruction getChildSuccessor(TranslatedElement child) {
    child = this.getDeclAndInit() and
    result = this.getFirstConditionInstruction()
    or
    (
      child = this.getBody() and
      if this.hasUpdate()
      then result = this.getUpdate().getFirstInstruction()
      else result = this.getFirstConditionInstruction()
    )
    or
    child = this.getUpdate() and result = this.getFirstConditionInstruction()
  }
}

/**
 * Base class for the translation of `BreakStmt`s and `GotoStmt`s.
 */
abstract class TranslatedSpecificJump extends TranslatedStmt {
  override Instruction getFirstInstruction() { result = this.getInstruction(OnlyInstructionTag()) }

  override TranslatedElement getChild(int id) { none() }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    tag = OnlyInstructionTag() and
    opcode instanceof Opcode::NoOp and
    resultType instanceof VoidType and
    isLValue = false
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  override Instruction getChildSuccessor(TranslatedElement child) { none() }
}

class TranslatedBreakStmt extends TranslatedSpecificJump {
  override BreakStmt stmt;

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = OnlyInstructionTag() and
    kind instanceof GotoEdge and
    result = this.getEnclosingLoopOrSwitchNextInstr(stmt)
  }

  private Instruction getEnclosingLoopOrSwitchNextInstr(Stmt crtStmt) {
    if crtStmt instanceof LoopStmt or crtStmt instanceof SwitchStmt
    then
      result = getTranslatedStmt(crtStmt).getParent().getChildSuccessor(getTranslatedStmt(crtStmt))
    else result = this.getEnclosingLoopOrSwitchNextInstr(crtStmt.getParent())
  }
}

class TranslatedGotoLabelStmt extends TranslatedSpecificJump {
  override GotoLabelStmt stmt;

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = OnlyInstructionTag() and
    kind instanceof GotoEdge and
    result = getTranslatedStmt(stmt.getTarget()).getFirstInstruction()
  }
}

class TranslatedGotoCaseStmt extends TranslatedSpecificJump {
  override GotoCaseStmt stmt;

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = OnlyInstructionTag() and
    kind instanceof GotoEdge and
    result = this.getCase(stmt, stmt.getExpr()).getFirstInstruction()
  }

  private TranslatedStmt getCase(Stmt crtStmt, Expr expr) {
    if crtStmt instanceof SwitchStmt
    then
      exists(CaseStmt caseStmt |
        caseStmt = crtStmt.(SwitchStmt).getACase() and
        // We check for the constant value of the expression
        // since we can't check for equality between `PatternExpr` and `Expr`
        caseStmt.getPattern().getValue() = expr.getValue() and
        result = getTranslatedStmt(caseStmt)
      )
    else result = this.getCase(crtStmt.getParent(), expr)
  }
}

class TranslatedGotoDefaultStmt extends TranslatedSpecificJump {
  override GotoDefaultStmt stmt;

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = OnlyInstructionTag() and
    kind instanceof GotoEdge and
    result = getDefaultCase(stmt).getFirstInstruction()
  }

  private TranslatedStmt getDefaultCase(Stmt crtStmt) {
    if crtStmt instanceof SwitchStmt
    then
      exists(CaseStmt caseStmt |
        caseStmt = crtStmt.(SwitchStmt).getDefaultCase() and
        result = getTranslatedStmt(caseStmt)
      )
    else result = this.getDefaultCase(crtStmt.getParent())
  }
}

class TranslatedSwitchStmt extends TranslatedStmt {
  override SwitchStmt stmt;

  private TranslatedExpr getSwitchExpr() { result = getTranslatedExpr(stmt.getExpr()) }

  override Instruction getFirstInstruction() { result = this.getSwitchExpr().getFirstInstruction() }

  override TranslatedElement getChild(int id) {
    if id = -1
    then
      // The switch expression.
      result = getTranslatedExpr(stmt.getChild(0))
    else
      if id = 0
      then
        // The first case's body.
        result = getTranslatedStmt(stmt.getChild(0))
      else
        // The subsequent case's bodies.
        result = getTranslatedStmt(stmt.getChild(id))
  }

  override predicate hasInstruction(
    Opcode opcode, InstructionTag tag, Type resultType, boolean isLValue
  ) {
    tag = SwitchBranchTag() and
    opcode instanceof Opcode::Switch and
    resultType instanceof VoidType and
    isLValue = false
  }

  override Instruction getInstructionOperand(InstructionTag tag, OperandTag operandTag) {
    tag = SwitchBranchTag() and
    operandTag instanceof ConditionOperandTag and
    result = this.getSwitchExpr().getResult()
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = SwitchBranchTag() and
    exists(CaseStmt caseStmt |
      caseStmt = stmt.getACase() and
      kind = this.getCaseEdge(caseStmt) and
      result = getTranslatedStmt(caseStmt).getFirstInstruction()
    )
  }

  private EdgeKind getCaseEdge(CaseStmt caseStmt) {
    if caseStmt instanceof DefaultCase
    then result instanceof DefaultEdge
    else
      exists(CaseEdge edge |
        result = edge and
        hasCaseEdge(caseStmt, edge.getMinValue(), edge.getMinValue())
      )
  }

  override Instruction getChildSuccessor(TranslatedElement child) {
    child = this.getSwitchExpr() and result = this.getInstruction(SwitchBranchTag())
    or
    exists(int index, int numStmts |
      numStmts = count(stmt.getAChild()) and
      child = getTranslatedStmt(stmt.getChild(index)) and
      if index = (numStmts - 1)
      then result = this.getParent().getChildSuccessor(this)
      else result = getTranslatedStmt(stmt.getChild(index + 1)).getFirstInstruction()
    )
  }
}

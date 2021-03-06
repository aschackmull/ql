private import csharp

/**
 * Given a type, get the type that would result by applying "pointer decay".
 * A function type becomes a pointer to that function type, and an array type
 * becomes a pointer to the element type of the array. If the specified type
 * is not subject to pointer decay, this predicate does not hold.
 */
// TODO: Only pointer to array decay in C#?
private Type getDecayedType(Type type) {
  result.(PointerType).getReferentType() = type.(ArrayType).getElementType()
}

/**
 * Get the actual type of the specified variable, as opposed to the declared type.
 * This returns the type of the variable after any pointer decay is applied, and
 * after any unsized array type has its size inferred from the initializer.
 */
Type getVariableType(Variable v) {
  exists(Type declaredType |
    declaredType = v.getType() and
    if v instanceof Parameter
    then
      result = getDecayedType(declaredType)
      or
      not exists(getDecayedType(declaredType)) and result = declaredType
    else
      if declaredType instanceof ArrayType
      then
        // TODO: Arrays have a declared dimension in C#, so this should not be needed
        // and not declaredType.(ArrayType).hasArraySize()
        result = v.getInitializer().getType()
        or
        not exists(v.getInitializer()) and result = declaredType
      else result = declaredType
  )
}

predicate hasCaseEdge(CaseStmt caseStmt, string minValue, string maxValue) {
  minValue = caseStmt.getPattern().getValue() and
  maxValue = minValue
}

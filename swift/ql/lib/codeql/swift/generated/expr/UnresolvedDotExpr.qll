// generated by codegen/codegen.py
/**
 * This module provides the generated definition of `UnresolvedDotExpr`.
 * INTERNAL: Do not import directly.
 */

private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.ErrorElement
import codeql.swift.elements.expr.Expr

/**
 * INTERNAL: This module contains the fully generated definition of `UnresolvedDotExpr` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::UnresolvedDotExpr` class directly.
   * Use the subclass `UnresolvedDotExpr`, where the following predicates are available.
   */
  class UnresolvedDotExpr extends Synth::TUnresolvedDotExpr, Expr, ErrorElement {
    override string getAPrimaryQlClass() { result = "UnresolvedDotExpr" }

    /**
     * Gets the base of this unresolved dot expression.
     *
     * This includes nodes from the "hidden" AST. It can be overridden in subclasses to change the
     * behavior of both the `Immediate` and non-`Immediate` versions.
     */
    Expr getImmediateBase() {
      result =
        Synth::convertExprFromRaw(Synth::convertUnresolvedDotExprToRaw(this)
              .(Raw::UnresolvedDotExpr)
              .getBase())
    }

    /**
     * Gets the base of this unresolved dot expression.
     */
    final Expr getBase() {
      exists(Expr immediate |
        immediate = this.getImmediateBase() and
        if exists(this.getResolveStep()) then result = immediate else result = immediate.resolve()
      )
    }

    /**
     * Gets the name of this unresolved dot expression.
     */
    string getName() {
      result = Synth::convertUnresolvedDotExprToRaw(this).(Raw::UnresolvedDotExpr).getName()
    }
  }
}

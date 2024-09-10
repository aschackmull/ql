// generated by codegen
/**
 * This module provides the generated definition of `RecordLitField`.
 * INTERNAL: Do not import directly.
 */

private import codeql.rust.generated.Synth
private import codeql.rust.generated.Raw
import codeql.rust.elements.AstNode
import codeql.rust.elements.Expr

/**
 * INTERNAL: This module contains the fully generated definition of `RecordLitField` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::RecordLitField` class directly.
   * Use the subclass `RecordLitField`, where the following predicates are available.
   */
  class RecordLitField extends Synth::TRecordLitField, AstNode {
    override string getAPrimaryQlClass() { result = "RecordLitField" }

    /**
     * Gets the name of this record lit field.
     */
    string getName() {
      result = Synth::convertRecordLitFieldToRaw(this).(Raw::RecordLitField).getName()
    }

    /**
     * Gets the expression of this record lit field.
     */
    Expr getExpr() {
      result =
        Synth::convertExprFromRaw(Synth::convertRecordLitFieldToRaw(this)
              .(Raw::RecordLitField)
              .getExpr())
    }
  }
}

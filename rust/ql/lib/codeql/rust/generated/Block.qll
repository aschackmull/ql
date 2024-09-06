// generated by codegen
/**
 * This module provides the generated definition of `Block`.
 * INTERNAL: Do not import directly.
 */

private import codeql.rust.generated.Synth
private import codeql.rust.generated.Raw
import codeql.rust.elements.BlockBase

/**
 * INTERNAL: This module contains the fully generated definition of `Block` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::Block` class directly.
   * Use the subclass `Block`, where the following predicates are available.
   */
  class Block extends Synth::TBlock, BlockBase {
    override string getAPrimaryQlClass() { result = "Block" }

    /**
     * Gets the label of this block, if it exists.
     */
    string getLabel() { result = Synth::convertBlockToRaw(this).(Raw::Block).getLabel() }

    /**
     * Holds if `getLabel()` exists.
     */
    final predicate hasLabel() { exists(this.getLabel()) }
  }
}

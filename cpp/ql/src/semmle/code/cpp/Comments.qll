import semmle.code.cpp.Location
import semmle.code.cpp.Element

/**
 * A C/C++ comment. For example the comment in the following code:
 * ```
 * // C++ style single-line comment
 * ```
 * or a C style comment (which starts with `/*`).
 */
class Comment extends Locatable, @comment {
  override string toString() { result = this.getContents() }
  override Location getLocation() { comments(underlyingElement(this),_,result) }
  string getContents() { comments(underlyingElement(this),result,_) }
  Element getCommentedElement() { commentbinding(underlyingElement(this),unresolveElement(result)) }
}

/**
 * A C style comment (one which starts with `/*`).
 */
class CStyleComment extends Comment {
  CStyleComment() {
    this.getContents().matches("/*%")
  }
}

/**
 * A CPP style comment. For example the comment in the following code:
 * ```
 * // C++ style single-line comment
 * ```
 */
class CppStyleComment extends Comment {
  CppStyleComment() {
    this.getContents().prefix(2) = "//"
  }
}

/**
 * Provides default sources, sinks and sanitizers for detecting
 * "XML bomb"
 * vulnerabilities, as well as extension points for adding your own.
 */

private import python
private import semmle.python.dataflow.new.DataFlow
private import semmle.python.Concepts
import experimental.semmle.python.frameworks.Xml // needed until modeling have been promoted
private import semmle.python.dataflow.new.RemoteFlowSources

/**
 * Provides default sources, sinks and sanitizers for detecting "XML bomb"
 * vulnerabilities, as well as extension points for adding your own.
 */
module XmlBomb {
  /**
   * A data flow source for XML-bomb vulnerabilities.
   */
  abstract class Source extends DataFlow::Node { }

  /**
   * A data flow sink for XML-bomb vulnerabilities.
   */
  abstract class Sink extends DataFlow::Node { }

  /**
   * A sanitizer for XML-bomb vulnerabilities.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  /** A source of remote user input, considered as a flow source for XML bomb vulnerabilities. */
  class RemoteFlowSourceAsSource extends Source {
    RemoteFlowSourceAsSource() { this instanceof RemoteFlowSource }
  }

  /**
   * A call to an XML parser that performs internal entity expansion, viewed
   * as a data flow sink for XML-bomb vulnerabilities.
   */
  class XmlParsingWithEntityResolution extends Sink {
    XmlParsingWithEntityResolution() {
      exists(XML::XMLParsing parsing, XML::XMLParsingVulnerabilityKind kind |
        (kind.isBillionLaughs() or kind.isQuadraticBlowup()) and
        parsing.vulnerableTo(kind) and
        this = parsing.getAnInput()
      )
    }
  }
}

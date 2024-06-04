/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Alethe node conversion
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALETHE__ALETHE_NODE_CONVERTER_H
#define CVC5__PROOF__ALETHE__ALETHE_NODE_CONVERTER_H

#include "expr/node.h"
#include "expr/node_converter.h"
#include "proof/alf/alf_node_converter.h"

namespace cvc5::internal {
namespace proof {

/**
 * This is a helper class for the Alethe post-processor that converts nodes into
 * their expected form in Alethe.
 */
class AletheNodeConverter : public BaseAlfNodeConverter
{
 public:
  /** Constructor
   *
   * @param nm The node manager
   * @param defineSkolems Whether Skolem definitions will be saved to be printed
   * separately.
   */
  AletheNodeConverter(NodeManager* nm, bool defineSkolems = false)
      : BaseAlfNodeConverter(nm), d_defineSkolems(defineSkolems)
  {
  }
  ~AletheNodeConverter() {}

  /** convert at post-order traversal */
  Node postConvert(Node n) override;

  /** A wrapper for convert that checks whether there was an error during
   * conversion.
   *
   * @param n The node to be converted
   * @param isAssumption Whether the n is an assumption
   * @return The converted node if there was no error, otherwise Node::null().
   */
  Node maybeConvert(Node n, bool isAssumption = false);

  /** Retrieve the saved error message, if any. */
  const std::string& getError();

  /** Return original assumption, if any, for a given (converted) node. */
  Node getOriginalAssumption(Node n);

  /** Retrieve a mapping between Skolems and their converted definitions.
   *
   * Note that this mapping is ordered in a way that a Skolem whose definition
   * depends on another Skolem will come after that Skolem in the map.
   */
  const std::map<Node, Node>& getSkolemDefinitions();

  Node mkInternalSymbol(const std::string& name,
                        TypeNode tn,
                        bool useRawSym = true) override;

  Node getOperatorOfTerm(Node n, bool reqCast = false) override
  {
    return Node::null();
  };

  Node typeAsNode(TypeNode tni) override { return Node::null(); };

  Node mkInternalApp(const std::string& name,
                     const std::vector<Node>& args,
                     TypeNode ret,
                     bool useRawSym = true) override
  {
    return Node::null();
  };

 private:
  /** Error message saved during failed conversion. */
  std::string d_error;
  /** Whether Skolem definitions will be saved to be printed separately. */
  bool d_defineSkolems;

  /**
   * As above but uses the s-expression type.
   */
  Node mkInternalSymbol(const std::string& name);

  /** Maps from internally generated symbols to the built nodes. */
  std::map<std::pair<TypeNode, std::string>, Node> d_symbolsMap;

  /** Map from converted node to original (used only for assumptions). */
  std::map<Node, Node> d_convToOriginalAssumption;

  /** Map between Skolems and their converted definitions. */
  std::map<Node, Node> d_skolems;
  /** Auxiliary map for maintaining the expected order in the above map. */
  std::map<Node, Node> d_skolemsAux;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif

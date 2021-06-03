/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Conversion from ProofNode to s-expressions.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_NODE_TO_SEXPR_H
#define CVC5__PROOF__PROOF_NODE_TO_SEXPR_H

#include <map>

#include "expr/node.h"
#include "proof/proof_rule.h"

namespace cvc5 {

class ProofNode;

/** A class to convert ProofNode objects to s-expressions */
class ProofNodeToSExpr
{
 public:
  ProofNodeToSExpr();
  ~ProofNodeToSExpr() {}
  /** Convert the given proof node to an s-expression
   *
   * This is useful for operations where it is useful to view a ProofNode as
   * a Node. Printing is one such example, where a ProofNode can be printed
   * as a dag after this conversion.
   *
   * The s-expression for a ProofNode has the form:
   *   (SEXPR (VAR "<d_rule>") S1 ... Sn (VAR ":args") (SEXPR <d_args>))
   * where S1, ..., Sn are the s-expressions for its <d_children>.
   */
  Node convertToSExpr(const ProofNode* pn);

 private:
  /** map proof rules to a variable */
  std::map<PfRule, Node> d_pfrMap;
  /** Dummy ":args" marker */
  Node d_argsMarker;
  /** Dummy ":conclusion" marker */
  Node d_conclusionMarker;
  /** map proof nodes to their s-expression */
  std::map<const ProofNode*, Node> d_pnMap;
  /**
   * map nodes to a bound variable, used for nodes that have special AST status
   * like builtin operators
   */
  std::map<Node, Node> d_nodeMap;
  /** get or make pf rule variable */
  Node getOrMkPfRuleVariable(PfRule r);
  /** get or make node variable */
  Node getOrMkNodeVariable(Node n);
};

}  // namespace cvc5

#endif /* CVC5__PROOF__PROOF_RULE_H */

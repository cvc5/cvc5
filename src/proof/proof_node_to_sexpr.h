/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

#include "expr/kind.h"
#include "expr/node.h"
#include "proof/method_id.h"
#include "proof/proof_rule.h"
#include "rewriter/rewrites.h"
#include "theory/inference_id.h"
#include "theory/theory_id.h"

namespace cvc5::internal {

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
   * 
   * @param pn The proof node to print
   * @param printConclusion Whether to print conclusions
   */
  Node convertToSExpr(const ProofNode* pn, bool printConclusion = false);

 private:
  /** argument format, determines how to print an argument */
  enum class ArgFormat
  {
    // just use the argument itself
    DEFAULT,
    // print the argument as a kind
    KIND,
    // print the argument as a theory id
    THEORY_ID,
    // print the argument as a method id
    METHOD_ID,
    // print the argument as an inference id
    INFERENCE_ID,
    // print the argument as a DSL rewrite id
    DSL_REWRITE_ID,
    // print a variable whose name is the term (see getOrMkNodeVariable)
    NODE_VAR
  };
  /** map proof rules to a variable */
  std::map<PfRule, Node> d_pfrMap;
  /** map kind to a variable displaying the kind they represent */
  std::map<Kind, Node> d_kindMap;
  /** map theory ids to a variable displaying the theory id they represent */
  std::map<theory::TheoryId, Node> d_tidMap;
  /** map method ids to a variable displaying the method id they represent */
  std::map<MethodId, Node> d_midMap;
  /** map infer ids to a variable displaying the inference id they represent */
  std::map<theory::InferenceId, Node> d_iidMap;
  /** map dsl rewrite ids to a variable displaying the dsl rewrite id they
   * represent */
  std::map<rewriter::DslPfRule, Node> d_dslrMap;
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
  std::map<TNode, Node> d_nodeMap;
  /** get or make pf rule variable */
  Node getOrMkPfRuleVariable(PfRule r);
  /** get or make kind variable from the kind embedded in n */
  Node getOrMkKindVariable(TNode n);
  /** get or make theory id variable */
  Node getOrMkTheoryIdVariable(TNode n);
  /** get or make method id variable */
  Node getOrMkMethodIdVariable(TNode n);
  /** get or make inference id variable */
  Node getOrMkInferenceIdVariable(TNode n);
  /** get or make DSL rewrite id variable */
  Node getOrMkDslRewriteVariable(TNode n);
  /**
   * Get or make node variable that prints the same as n but has SEXPR type.
   * This is used to ensure the type checker does not complain when trying to
   * print e.g. builtin operators as first-class terms in the SEXPR.
   */
  Node getOrMkNodeVariable(TNode n);
  /** get argument based on the provided format */
  Node getArgument(Node arg, ArgFormat f);
  /** get argument format for proof node */
  ArgFormat getArgumentFormat(const ProofNode* pn, size_t i);
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_RULE_H */

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite database term processor
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__REWRITE_DB_TERM_PROCESS__H
#define CVC5__REWRITER__REWRITE_DB_TERM_PROCESS__H

#include <cvc5/cvc5_proof_rule.h>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * The desired AST of terms in our DSL rewrite rule proof reconstruction can be
 * different than the default representation of terms in cvc5. These
 * differences include:
 * (1) cvc5 has (word) string literals; the DSL assumes these are
 * concatenations of constants, e.g. "ABC" is the term (str.++ "A" "B" "C").
 * (2) Constant bitvectors are lifted to CONST_BITVECTOR_SYMBOLIC.
 * (3) Indexed operators are lifted to APPLY_INDEXED_SYMBOLIC.
 * (4) Quantifier patterns are dropped.
 *
 * This node converter converts from the default representation of cvc5 terms
 * to the representation of terms required by the DSL proof reconstruction
 * algorithm.
 *
 * Notice that this converter is independent of the end target proof checker,
 * and thus we do not do any target-specific processing (e.g. converting to
 * curried form).
 */
class RewriteDbNodeConverter : public NodeConverter
{
 public:
  /**
   * The latter two arguments are used internally if we are proof producing
   * via ProofRewriteDbNodeConverter.
   */
  RewriteDbNodeConverter(NodeManager* nm,
                         TConvProofGenerator* tpg = nullptr,
                         CDProof* p = nullptr);
  /**
   * This converts the node n to the internal shape that it should be in
   * for the DSL proof reconstruction algorithm.
   */
  Node postConvert(Node n) override;

 protected:
  /** A pointer to a TConvProofGenerator, if proof producing */
  TConvProofGenerator* d_tpg;
  /** A CDProof, if proof producing */
  CDProof* d_proof;
  /** Record that n ---> ret, justifiable by proof rule r. */
  void recordProofStep(const Node& n, const Node& ret, ProofRule r);
  /** Should we traverse n? */
  bool shouldTraverse(Node n) override;
};

/** A proof producing version of the above class */
class ProofRewriteDbNodeConverter : protected EnvObj
{
 public:
  ProofRewriteDbNodeConverter(Env& env);
  /**
   * Return the proof of the conversion of n based on the above class.
   * Specifically, this returns a proof of
   *   n = RewriteDbNodeConverter::convert(n).
   * The returned proof is a term conversion proof whose small steps are
   * EVALUATE, ACI_NORM and ENCODE_EQ_INTRO.
   */
  std::shared_ptr<ProofNode> convert(const Node& n);

 private:
  /** A pointer to a TConvProofGenerator, if proof producing */
  TConvProofGenerator d_tpg;
  /** A CDProof */
  CDProof d_proof;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__REWRITE_DB_TERM_PROCESS__H */

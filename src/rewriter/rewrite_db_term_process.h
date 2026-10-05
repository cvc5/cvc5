/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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
#include "expr/term_context.h"
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
 * (5) APPLY_UF is converted to HO_APPLY chains.
 * (6) Function constants are converted to lambdas.
 * (7) Annotations are applied to parametric datatype constructors.
 * (8) NONLINEAR_MULT is reverted to MULT.
 *
 * This node converter converts from the default representation of cvc5 terms
 * to the representation of terms required by the DSL proof reconstruction
 * algorithm.
 *
 * Note that (3) is applied only when liftIndexed is true, which is the case
 * for the internal search of the DSL proof reconstruction algorithm, where it
 * is required for matching against the left hand side of RARE rules. It is
 * *not* applied when this class is used to define the semantics of
 * ProofRule::ENCODE_EQ_INTRO, since APPLY_INDEXED_SYMBOLIC has no counterpart
 * in external proof formats. Instead, applications of APPLY_INDEXED_SYMBOLIC
 * are folded back to their concrete representation (see
 * IndexedOpFoldNodeConverter) when the proof is constructed.
 *
 * Notice that this converter is independent of the end target proof checker,
 * and thus we do not do any target-specific processing (e.g. converting to
 * curried form).
 */
class RewriteDbNodeConverter : public NodeConverter
{
 public:
  /**
   * @param nm The node manager.
   * @param liftIndexed Whether indexed operators are lifted to
   * APPLY_INDEXED_SYMBOLIC, see (3) above.
   * @param tpg The proof generator, if proof producing.
   * @param p The proof, if proof producing.
   *
   * The latter two arguments are used internally if we are proof producing
   * via ProofRewriteDbNodeConverter.
   */
  RewriteDbNodeConverter(NodeManager* nm,
                         bool liftIndexed = false,
                         TConvProofGenerator* tpg = nullptr,
                         CDProof* p = nullptr);
  /**
   * This converts the node n to the internal shape that it should be in
   * for the DSL proof reconstruction algorithm.
   */
  Node postConvert(Node n) override;

 protected:
  /** Whether we lift indexed operators to APPLY_INDEXED_SYMBOLIC */
  bool d_liftIndexed;
  /** A pointer to a TConvProofGenerator, if proof producing */
  TConvProofGenerator* d_tpg;
  /** A CDProof, if proof producing */
  CDProof* d_proof;
  /** Record that n ---> ret, justifiable by proof rule r. */
  void recordProofStep(const Node& n, const Node& ret, ProofRule r);
  /** Should we traverse n? */
  bool shouldTraverse(Node n) override;
};

/**
 * Folds applications of indexed operators whose indices are given as explicit
 * arguments (APPLY_INDEXED_SYMBOLIC) to their concrete representation, e.g.
 *   (APPLY_INDEXED_SYMBOLIC (extract) 3 0 x)
 * is converted to
 *   ((_ extract 3 0) x).
 * This is the inverse of the lifting performed by RewriteDbNodeConverter, see
 * (3) in its documentation above. Subterms whose indices do not evaluate to
 * numeral constants are left unchanged.
 *
 * This class is used to map the terms occurring in the internal search of the
 * DSL proof reconstruction algorithm back to their concrete representation,
 * which is the representation used in proofs. It is also used to define the
 * semantics of ProofRule::DSL_REWRITE.
 */
class IndexedOpFoldNodeConverter : public NodeConverter
{
 public:
  IndexedOpFoldNodeConverter(NodeManager* nm);
  /** Fold n, see class documentation above. */
  Node postConvert(Node n) override;
  /**
   * Convenience method, folds n using a fresh converter. Should be used only
   * when a persistent instance of this class is not available, since it does
   * not benefit from caching across calls.
   */
  static Node fold(NodeManager* nm, const Node& n);
  /**
   * Does n contain a subterm of kind APPLY_INDEXED_SYMBOLIC, i.e. is there
   * anything to fold in n? The result of this method is cached as an attribute
   * on n, since it is queried often on the same terms during DSL proof
   * reconstruction.
   */
  static bool hasIndexedSymbolic(TNode n);
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
  /** Term context matching the policy for the converter above */
  WithinKindTermContext d_wktc;
  /** A pointer to a TConvProofGenerator, if proof producing */
  TConvProofGenerator d_tpg;
  /** A CDProof */
  CDProof d_proof;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__REWRITE_DB_TERM_PROCESS__H */

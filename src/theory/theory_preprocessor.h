/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory preprocessor.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__THEORY_PREPROCESSOR_H
#define CVC5__THEORY__THEORY_PREPROCESSOR_H

#include <unordered_map>

#include "context/cdhashmap.h"
#include "context/context.h"
#include "expr/lazy_proof.h"
#include "expr/node.h"
#include "expr/tconv_seq_proof_generator.h"
#include "expr/term_conversion_proof_generator.h"
#include "smt/term_formula_removal.h"
#include "theory/skolem_lemma.h"
#include "theory/trust_node.h"

namespace cvc5 {

class LogicInfo;
class TheoryEngine;
class RemoveTermFormulas;

namespace theory {

/**
 * The preprocessor used in TheoryEngine.
 *
 * A summary of the steps taken by the method preprocess:
 *
 * [1]
 * apply rewriter
 * [2]
 * TRAVERSE(
 *   prerewrite:
 *    if theory atom {
 *      TRAVERSE(
 *        prerewrite:
 *          // nothing
 *        postrewrite:
 *          apply rewriter
 *          apply ppRewrite
 *            if changed
 *              apply rewriter
 *              REPEAT traversal
 *      )
 *      apply term formula removal
 *      apply rewriter
 *    }
 *  postrewrite: // for Boolean connectives
 *    apply rewriter
 * )
 *
 * Note that the rewriter must be applied beforehand, since the rewriter may
 * rewrite a theory atom into a formula, e.g. quantifiers miniscoping. This
 * impacts what the inner traversal is applied to.
 */
class TheoryPreprocessor
{
  typedef context::CDHashMap<Node, Node> NodeMap;

 public:
  /** Constructs a theory preprocessor */
  TheoryPreprocessor(TheoryEngine& engine,
                     context::UserContext* userContext,
                     ProofNodeManager* pnm = nullptr);
  /** Destroys a theory preprocessor */
  ~TheoryPreprocessor();
  /**
   * Preprocesses the given assertion node. It returns a TrustNode of kind
   * TrustNodeKind::REWRITE indicating the preprocessed form of node. It stores
   * additional lemmas in newLemmas, which are trust nodes of kind
   * TrustNodeKind::LEMMA. These correspond to e.g. lemmas corresponding to ITE
   * removal. For each lemma in newLemmas, we add the corresponding skolem that
   * the lemma defines.
   *
   * @param node The assertion to preprocess,
   * @param newLemmas The lemmas to add to the set of assertions,
   * @param newSkolems The skolems that newLemmas correspond to,
   * @return The (REWRITE) trust node corresponding to rewritten node via
   * preprocessing.
   */
  TrustNode preprocess(TNode node,
                       std::vector<TrustNode>& newLemmas,
                       std::vector<Node>& newSkolems);
  /**
   * Same as above, but transforms the proof of node into a proof of the
   * preprocessed node and returns the LEMMA trust node.
   *
   * @param node The assertion to preprocess,
   * @param newLemmas The lemmas to add to the set of assertions,
   * @param newSkolems The skolems that newLemmas correspond to,
   * @return The (LEMMA) trust node corresponding to the proof of the rewritten
   * form of the proven field of node.
   */
  TrustNode preprocessLemma(TrustNode node,
                            std::vector<TrustNode>& newLemmas,
                            std::vector<Node>& newSkolems);

  /** Get the term formula removal utility */
  RemoveTermFormulas& getRemoveTermFormulas();

 private:
  /**
   * Runs theory specific preprocessing (Theory::ppRewrite) on the non-Boolean
   * parts of the node.
   */
  TrustNode theoryPreprocess(TNode node,
                             std::vector<TrustNode>& newLemmas,
                             std::vector<Node>& newSkolems);
  /**
   * Internal helper for preprocess, which also optionally preprocesses the
   * new lemmas generated until a fixed point is reached based on argument
   * procLemmas.
   */
  TrustNode preprocessInternal(TNode node,
                               std::vector<TrustNode>& newLemmas,
                               std::vector<Node>& newSkolems,
                               bool procLemmas);
  /**
   * Internal helper for preprocessLemma, which also optionally preprocesses the
   * new lemmas generated until a fixed point is reached based on argument
   * procLemmas.
   */
  TrustNode preprocessLemmaInternal(TrustNode node,
                                    std::vector<TrustNode>& newLemmas,
                                    std::vector<Node>& newSkolems,
                                    bool procLemmas);
  /** Reference to owning theory engine */
  TheoryEngine& d_engine;
  /** Logic info of theory engine */
  const LogicInfo& d_logicInfo;
  /**
   * Cache for theory-preprocessing of theory atoms. The domain of this map
   * are terms that appear within theory atoms given to this class.
   */
  NodeMap d_ppCache;
  /**
   * Cache for theory-preprocessing + term formula removal of the Boolean
   * structure of assertions. The domain of this map are the Boolean
   * connectives and theory atoms given to this class.
   */
  NodeMap d_rtfCache;
  /** The term formula remover */
  RemoveTermFormulas d_tfr;
  /** The term context, which computes hash values for term contexts. */
  InQuantTermContext d_iqtc;
  /**
   * A term conversion proof generator storing preprocessing and rewriting
   * steps, which is done until fixed point in the inner traversal of this
   * class for theory atoms in step [2] above.
   */
  std::unique_ptr<TConvProofGenerator> d_tpg;
  /**
   * A term conversion proof generator storing large steps from d_tpg (results
   * of its fixed point) and term formula removal steps for the outer traversal
   * of this class for theory atoms in step [2] above.
   */
  std::unique_ptr<TConvProofGenerator> d_tpgRtf;
  /**
   * A term conversion proof generator storing rewriting steps, which is used
   * for top-level rewriting before the preprocessing pass, step [1] above.
   */
  std::unique_ptr<TConvProofGenerator> d_tpgRew;
  /**
   * A term conversion sequence generator, which applies rewriting,
   * (theory-preprocessing + rewriting + term formula removal), rewriting again
   * in sequence, given by d_tpgRew and d_tpgRtf.
   */
  std::unique_ptr<TConvSeqProofGenerator> d_tspg;
  /** A lazy proof, for additional lemmas. */
  std::unique_ptr<LazyCDProof> d_lp;
  /**
   * Helper for theoryPreprocess, which traverses the provided term and
   * applies ppRewrite and rewriting until fixed point on term using
   * the method preprocessWithProof helper below.
   */
  Node ppTheoryRewrite(TNode term, std::vector<SkolemLemma>& lems);
  /**
   * Rewrite with proof, which stores a REWRITE step in pg if necessary
   * and returns the rewritten form of term.
   *
   * @param term The term to rewrite
   * @param pg The proof generator to register to
   * @param isPre whether the rewrite is a pre-rewrite.
   */
  Node rewriteWithProof(Node term, TConvProofGenerator* pg, bool isPre);
  /**
   * Preprocess with proof, which calls the appropriate ppRewrite method,
   * stores the corresponding rewrite step in d_tpg if necessary and returns
   * the preprocessed and rewritten form of term. It should be the case that
   * term is already in rewritten form.
   */
  Node preprocessWithProof(Node term, std::vector<SkolemLemma>& lems);
  /**
   * Register rewrite trn based on trust node into term conversion generator
   * pg, which uses THEORY_PREPROCESS as a step if no proof generator is
   * provided in trn.
   *
   * @param trn The REWRITE trust node
   * @param pg The proof generator to register to
   * @param isPre whether the rewrite is a pre-rewrite.
   */
  void registerTrustedRewrite(TrustNode trn,
                              TConvProofGenerator* pg,
                              bool isPre);
  /** Proofs enabled */
  bool isProofEnabled() const;
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__THEORY_PREPROCESSOR_H */

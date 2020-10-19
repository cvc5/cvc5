/*********************                                                        */
/*! \file tconv_seq_proof_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term conversion sequence proof generator utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__TCONV_SEQ_PROOF_GENERATOR_H
#define CVC4__EXPR__TCONV_SEQ_PROOF_GENERATOR_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "expr/proof_generator.h"
#include "expr/proof_node_manager.h"
#include "theory/trust_node.h"

namespace CVC4 {

/**
 * The term conversion sequence proof generator. This is used for maintaining
 * a fixed sequence of proof generators that provide proofs for rewrites
 * (equalities). We call these the "component generators" of this sequence,
 * which are typically TConvProofGenerator.
 */
class TConvSeqProofGenerator : public ProofGenerator
{
 public:
  /**
   * @param pnm The proof node manager for constructing ProofNode objects.
   * @param ts The list of component term conversion generators that are
   * applied in sequence
   * @param c The context that this class depends on. If none is provided,
   * this class is context-independent.
   * @param name The name of this generator (for debugging).
   */
  TConvSeqProofGenerator(ProofNodeManager* pnm,
                         const std::vector<ProofGenerator*>& ts,
                         context::Context* c = nullptr,
                         std::string name = "TConvSeqProofGenerator");
  ~TConvSeqProofGenerator();
  /**
   * Indicate that the index^th proof generator converts term t to s. This
   * should be called for a unique s for each (t, index). It must be the
   * case that d_tconv[index] can provide a proof for t = s in the remainder
   * of the context maintained by this class.
   */
  void registerConvertedTerm(Node t, Node s, size_t index);
  /**
   * Get the proof for formula f. It should be the case that f is of the form
   * t_0 = t_n, where it must be the case that t_n is obtained by the following:
   * For each i=0, ... n, let t_{i+1} be the term such that
   *   registerConvertedTerm(t_i, t_{i+1}, i)
   * was called. Otherwise t_{i+1} = t_i.
   * In other words, t_n is obtained by converting t_0, in order, based on the
   * calls to registerConvertedTerm.
   *
   * @param f The equality fact to get the proof for.
   * @return The proof for f.
   */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /**
   * Get subsequence proof for f, with given start and end steps (inclusive).
   */
  std::shared_ptr<ProofNode> getSubsequenceProofFor(Node f,
                                                    size_t start,
                                                    size_t end);
  /** Identify this generator (for debugging, etc..) */
  std::string identify() const override;

  /**
   * Make trust node from a sequence of converted terms. The number of
   * terms in cterms should be 1 + the number of component proof generators
   * maintained by this class. This selects a proof generator that is capable
   * of proving cterms[0] = cterms[cterms.size()-1], which is either this
   * generator, or one of the component proof generators, if only one step
   * rewrote. In the former case, all steps are registered to this class.
   * Using a component generator is an optimization that saves having to
   * save the conversion steps or use this class. For example, if we have 2 
   * term conversion components, and call this method on:
   *   { a, b, c }
   * then this method calls:
   *   registerConvertedTerm( a, b, 0 )
   *   registerConvertedTerm( b, c, 1 )
   * and returns a trust node proving (= a c) with this class as the proof
   * generator. On the other hand, if we call this method on:
   *   { d, d, e }
   * then we return a trust node proving (= d e) with the 2nd component proof
   * generator, as it alone is capable of proving this equality.
   */
  theory::TrustNode mkTrustRewriteSequence(const std::vector<Node>& cterms);

 protected:
  using NodeIndexPairHashFunction =
      PairHashFunction<Node, size_t, NodeHashFunction>;
  typedef context::
      CDHashMap<std::pair<Node, size_t>, Node, NodeIndexPairHashFunction>
          NodeIndexNodeMap;
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** The term conversion generators */
  std::vector<ProofGenerator*> d_tconvs;
  /** the set of converted terms */
  NodeIndexNodeMap d_converted;
  /** Name identifier */
  std::string d_name;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__TCONV_SEQ_PROOF_GENERATOR_H */

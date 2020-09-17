/*********************                                                        */
/*! \file tconv_seq_proof_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

namespace CVC4 {

/**
 * The term conversion sequence proof generator.
 */
class TConvSeqProofGenerator : public ProofGenerator
{
 public:
  /**
   * @param pnm The proof node manager for constructing ProofNode objects.
   * @param ts The list of term conversion generators that are applied in
   * sequence
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
   * case that d_tconv[index] can provide a proof for t = s.
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
   * Get subsequence proof, with given start and end steps (inclusive).
   */
  std::shared_ptr<ProofNode> getSubsequenceProofFor(Node f, size_t start, size_t end);
  /** Identify this generator (for debugging, etc..) */
  std::string identify() const override;

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

/** Applies a subsequence of the steps for the above generator */
class TConvSubSeqGenerator : public ProofGenerator
{
public:
  TConvSubSeqGenerator(TConvSeqProofGenerator* tref, size_t start, size_t end, 
                         std::string name = "TConvSubSeqGenerator");
  /**
   * Get proof for, calls getSubsequenceProofFor on the referenced term
   * conversion sequence generator.
   */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Identify this generator (for debugging, etc..) */
  std::string identify() const override;
private:
  /** The conversion sequence generator */
  TConvSeqProofGenerator * d_tref;
  /** The start and end indices in the reference */
  size_t d_start;
  size_t d_end;
  /** Name identifier */
  std::string d_name;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__TERM_CONVERSION_PROOF_GENERATOR_H */

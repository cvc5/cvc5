/*********************                                                        */
/*! \file term_conversion_proof_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term conversion proof generator utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__TERM_CONVERSION_PROOF_GENERATOR_H
#define CVC4__EXPR__TERM_CONVERSION_PROOF_GENERATOR_H

#include "context/cdhashmap.h"
#include "expr/proof_generator.h"
#include "expr/proof_node_manager.h"
#include "expr/lazy_proof.h"

namespace CVC4 {

/**
 * The term conversion proof generator.
 */
class TermConversionProofGenerator : public ProofGenerator
{
 public:
  /** Constructor
   *
   * @param pnm The proof node manager for constructing ProofNode objects.
   * @param c The context that this class depends on. If none is provided,
   * this class is context-independent.
   */
  TermConversionProofGenerator(ProofNodeManager* pnm,
              context::Context* c = nullptr);
  ~TermConversionProofGenerator();
  /** 
   * Add rewrite step t --> s based on proof generator.
   */
  void addRewriteStep(Node t, Node s, ProofGenerator * pg);
  /** Same as above, for a single step */
  void addRewriteStep(Node t, Node s, ProofStep ps);
  /** 
   * Get the proof for formula f. It should be the case that f is of the form
   * t = t', where t' is the result of rewriting t based on the rewrite steps
   * registered to this class.
   *
   * @param f The fact to get the proof for.
   * @return The proof for f.
   */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
 protected:
  /** 
   * Get the proof for term t. Returns a proof of t = t' where t' is the
   * result of rewriting t based on the rewrite steps registered to this class.
   */
  std::shared_ptr<ProofNode> getProofForRewriting(Node t);
  typedef context::CDHashMap<Node, Node, NodeHashFunction>
      NodeNodeMap;
  /** A dummy context used by this class if none is provided */
  context::Context d_context;
   /** The (lazy) context dependent proof object. */
   LazyCDProof d_proof;
   /** map to rewritten forms */
   NodeNodeMap d_rewriteMap;
   /** Get rewrite step */
   Node getRewriteStep(Node t) const;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__TERM_CONVERSION_PROOF_GENERATOR_H */

/*********************                                                        */
/*! \file proof_output_channel.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Guy Katz, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF_OUTPUT_CHANNEL_H
#define CVC4__PROOF_OUTPUT_CHANNEL_H

#include <memory>
#include <set>
#include <unordered_set>

#include "expr/node.h"
#include "theory/output_channel.h"
#include "theory/theory.h"
#include "util/proof.h"

namespace CVC4 {

class ProofOutputChannel : public theory::OutputChannel {
 public:
  ProofOutputChannel();
  ~ProofOutputChannel() override {}

  /**
   * This may be called at most once per ProofOutputChannel.
   * Requires that `n` and `pf` are non-null.
   */
  void conflict(TNode n, std::unique_ptr<Proof> pf) override;
  bool propagate(TNode x) override;
  theory::LemmaStatus lemma(TNode n, ProofRule rule, bool, bool, bool) override;
  theory::LemmaStatus splitLemma(TNode, bool) override;
  void requirePhase(TNode n, bool b) override;
  void setIncomplete() override;

  /** Has conflict() has been called? */
  bool hasConflict() const { return !d_conflict.isNull(); }

  /**
   * Returns the proof passed into the conflict() call.
   * Requires hasConflict() to hold.
   */
  const Proof& getConflictProof() const;
  Node getLastLemma() const { return d_lemma; }

 private:
  Node d_conflict;
  std::unique_ptr<Proof> d_proof;
  Node d_lemma;
  std::set<Node> d_propagations;
}; /* class ProofOutputChannel */

class MyPreRegisterVisitor {
  theory::Theory* d_theory;
  std::unordered_set<TNode, TNodeHashFunction> d_visited;
public:
  typedef void return_type;
  MyPreRegisterVisitor(theory::Theory* theory);
  bool alreadyVisited(TNode current, TNode parent);
  void visit(TNode current, TNode parent);
  void start(TNode node);
  void done(TNode node);
}; /* class MyPreRegisterVisitor */

} /* CVC4 namespace */

#endif /* CVC4__PROOF_OUTPUT_CHANNEL_H */

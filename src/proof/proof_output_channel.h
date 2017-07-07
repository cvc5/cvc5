/*********************                                                        */
/*! \file proof_output_channel.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF_OUTPUT_CHANNEL_H
#define __CVC4__PROOF_OUTPUT_CHANNEL_H

#include "theory/output_channel.h"

namespace CVC4 {

class ProofOutputChannel : public theory::OutputChannel {
public:
  Node d_conflict;
  Proof* d_proof;
  Node d_lemma;
  std::set<Node> d_propagations;

  ProofOutputChannel();

  virtual ~ProofOutputChannel() throw() {}

  virtual void conflict(TNode n, Proof* pf) throw();
  virtual bool propagate(TNode x) throw();
  virtual theory::LemmaStatus lemma(TNode n, ProofRule rule, bool, bool, bool);
  virtual theory::LemmaStatus splitLemma(TNode, bool);
  virtual void requirePhase(TNode n, bool b) throw();
  virtual bool flipDecision() throw();
  virtual void setIncomplete() throw();
};/* class ProofOutputChannel */

class MyPreRegisterVisitor {
  theory::Theory* d_theory;
  __gnu_cxx::hash_set<TNode, TNodeHashFunction> d_visited;
public:
  typedef void return_type;
  MyPreRegisterVisitor(theory::Theory* theory);
  bool alreadyVisited(TNode current, TNode parent);
  void visit(TNode current, TNode parent);
  void start(TNode node);
  void done(TNode node);
}; /* class MyPreRegisterVisitor */

} /* CVC4 namespace */

#endif /* __CVC4__PROOF_OUTPUT_CHANNEL_H */

/*********************                                                        */
/*! \file proof_output_channel.h
 ** \verbatim
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

  void conflict(TNode n, Proof* pf) throw();
  bool propagate(TNode x) throw();
  theory::LemmaStatus lemma(TNode n, ProofRule rule, bool, bool, bool) throw();
  theory::LemmaStatus splitLemma(TNode, bool) throw();
  void requirePhase(TNode n, bool b) throw();
  bool flipDecision() throw();
  void setIncomplete() throw();
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

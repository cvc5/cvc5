/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Datatypes inference manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__DATATYPES__INFERENCE_MANAGER_H
#define CVC4__THEORY__DATATYPES__INFERENCE_MANAGER_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "theory/inference_manager_buffered.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

/**
 * The datatypes inference manager. The main unique features of this inference
 * manager are:
 * (1) Explicit caching of lemmas,
 * (2) A custom process() method with relies on a policy determining which
 * facts must be sent as lemmas (mustCommunicateFact).
 * (3) Methods for tracking when lemmas and facts have been processed.
 */
class InferenceManager : public InferenceManagerBuffered
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  InferenceManager(Theory& t, TheoryState& state, ProofNodeManager* pnm);
  ~InferenceManager() {}
  /**
   * Process the current lemmas and facts. This is a custom method that can
   * be seen as overriding the behavior of calling both doPendingLemmas and
   * doPendingFacts. It determines whether facts should be sent as lemmas
   * or processed internally.
   */
  void process();

 protected:
  /**
   * Must communicate fact method.
   * The datatypes decision procedure makes "internal" inferences :
   *  (1) Unification : C( t1...tn ) = C( s1...sn ) => ti = si
   *  (2) Label : ~is_C1(t) ... ~is_C{i-1}(t) ~is_C{i+1}(t) ... ~is_Cn(t) =>
   * is_Ci( t )
   *  (3) Instantiate : is_C( t ) => t = C( sel_1( t ) ... sel_n( t ) )
   *  (4) collapse selector : S( C( t1...tn ) ) = t'
   *  (5) collapse term size : size( C( t1...tn ) ) = 1 + size( t1 ) + ... +
   * size( tn )
   *  (6) non-negative size : 0 <= size(t)
   * This method returns true if the fact must be sent out as a lemma. If it
   * returns false, then we assert the fact internally. We may need to
   * communicate outwards if the conclusions involve other theories.  Also
   * communicate (6) and OR conclusions.
   */
  bool mustCommunicateFact(Node n, Node exp) const;
  /** Common node */
  Node d_true;
};

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4

#endif

/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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
 * A custom inference class. The main feature of this class is that it
 * dynamically decides whether to process itself as a fact or as a lemma,
 * based on the mustCommunicateFact method below.
 */
class DatatypesInference : public SimpleTheoryInternalFact
{
 public:
  DatatypesInference(Node conc, Node exp, ProofGenerator* pg);
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
  static bool mustCommunicateFact(Node n, Node exp);
  /**
   * Process this fact, possibly as a fact or as a lemma, depending on the
   * above method.
   */
  bool process(TheoryInferenceManager* im, bool asLemma) override;
};

/**
 * The datatypes inference manager, which uses the above class for
 * inferences.
 */
class InferenceManager : public InferenceManagerBuffered
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  InferenceManager(Theory& t, TheoryState& state, ProofNodeManager* pnm);
  ~InferenceManager() {}
  /**
   * Add pending inference, which may be processed as either a fact or
   * a lemma based on mustCommunicateFact in DatatypesInference above.
   */
  void addPendingInference(Node conc, Node exp, ProofGenerator* pg = nullptr);
  /**
   * Process the current lemmas and facts. This is a custom method that can
   * be seen as overriding the behavior of calling both doPendingLemmas and
   * doPendingFacts. It determines whether facts should be sent as lemmas
   * or processed internally.
   */
  void process();
  /**
   * Send lemmas with property NONE on the output channel immediately.
   * Returns true if any lemma was sent.
   */
  bool sendLemmas(const std::vector<Node>& lemmas);
};

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4

#endif

/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The inference manager for the theory of sets.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__INFERENCE_MANAGER_H
#define CVC4__THEORY__SETS__INFERENCE_MANAGER_H

#include "theory/sets/sets_state.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {
  
class TheorySetsPrivate;

/** Inference manager 
 * 
 * This class manages inferences produced by the theory of sets.
 */
class InferenceManager {
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
 public:
  InferenceManager(TheorySetsPrivate& p,
                       SetsState& s,
                       eq::EqualityEngine& e,
                       context::Context* c,
                       context::UserContext* u);
  /** reset 
   * 
   */
  void reset();
  /** 
   * Add inferences corresponding to ( exp => fact ).
   * 
   */
  void assertInference( Node fact, Node exp, std::vector< Node >& lemmas, const char * c, int inferType = 0 );
  void assertInference( Node fact, std::vector< Node >& exp, std::vector< Node >& lemmas, const char * c, int inferType = 0 );
  void assertInference( std::vector< Node >& conc, Node exp, std::vector< Node >& lemmas, const char * c, int inferType = 0 );
  void assertInference( std::vector< Node >& conc, std::vector< Node >& exp, std::vector< Node >& lemmas, const char * c, int inferType = 0 );
  /** Flush lemmas
   *
   * This sends lemmas on the output channel of the theory of sets.
   *
   * The argument preprocess indicates whether preprocessing should be applied
   * (by TheoryEngine) on each of lemmas.
   */
  void flushLemmas(std::vector<Node>& lemmas, bool preprocess = false);
  /** singular version of above */
  void flushLemma(Node lem, bool preprocess = false);
  /** Have we sent out a lemma during a call to a full effort check? */
  bool sentLemma() const;
  // send lemma ( n OR (NOT n) ) immediately
  void split( Node n, int reqPol=0 );
  bool hasLemmaCached( Node lem ) const;
  bool hasProcessed() const;
 private:
  /** constants */
  Node d_true;
  Node d_false;
  /** the theory of sets which owns this */
  TheorySetsPrivate& d_parent;
  /** Reference to the state object for the theory of sets */
  SetsState& d_state;
  /** Reference to the equality engine of theory of sets */
  eq::EqualityEngine& d_ee;
  /** sent lemma
   *
   * This flag is set to true during a full effort check if this theory
   * called d_out->lemma(...).
   */
  bool d_sentLemma;
  /** added fact
   *
   * This flag is set to true during a full effort check if this theory
   * added an internal fact to its equality engine.
   */
  bool d_addedFact;
  /** A user-context-dependent cache of all lemmas produced */
  NodeSet d_lemmas_produced;
  /** 
   * A set of nodes to ref-count. Nodes that are facts or are explanations of
   * facts must be added to this set since the equality engine does not
   * ref count nodes.
   */
  NodeSet d_keep;
  /** Assert fact recursive
   *
   * inferType : 1 : must send out as lemma, -1 : do internal inferences if possible, 0 : default.
   */
  bool assertFactRec( Node fact, Node exp, std::vector< Node >& lemma, int inferType = 0 );
};


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__SETS__INFERENCE_MANAGER_H */

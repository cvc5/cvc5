/*********************                                                        */
/*! \file cardinality_extension.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An extension of the theory sets for handling cardinality constraints
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__CARDINALITY_EXTENSION_H
#define CVC4__THEORY__SETS__CARDINALITY_EXTENSION_H

#include "context/cdhashset.h"
#include "context/context.h"
#include "theory/sets/inference_manager.h"
#include "theory/sets/sets_state.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySetsPrivate;

class CardinalityExtension
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  /**
   * Constructs a new instance of the cardinality solver w.r.t. the provided
   * contexts.
   */
  CardinalityExtension(TheorySetsPrivate& p,
                       SetsState& s,
                       InferenceManager& im,
                       eq::EqualityEngine& e,
                       context::Context* c,
                       context::UserContext* u);

  ~CardinalityExtension() {}
  /** reset
   * 
   * Called at the beginning of a full effort check. This resets the data
   * structures used by this class during a full effort check.
   */
  void reset();
  /** register term
   * 
   * Register that the term n exists in the current context, where n is an
   * application of CARD.
   */
  void registerTerm(Node n, std::vector<Node>& lemmas);
  /** check
   * 
   * Invoke a full effort check of the cardinality solver. At a high level,
   * this asserts inferences via the inference manager object d_im. If no
   * inferences are made, then the current set of assertions is satisfied
   * with respect to constraints involving set cardinality.
   */
  void check();
  /** Is model value basic?
   *   
   * This returns true if equivalence class eqc is a "leaf" in the cardinality
   * graph. In this case, its model value is simply 
   */
  bool isModelValueBasic(Node eqc);
  /** get model elements
   *
   * This method updates els so that it is the set of elements that occur in eqc
   * in the model we are building. Notice that els may already have elements 
   * in it (from explicit memberships from the base set solver for leaf nodes
   * of the cardinality graph). This method is used during the collectModelInfo
   * method of theory of sets.
   * 
   * The argument mvals maps set equivalence classes to their model values. 
   * Due to our model construction algorithm, it can be assumed that all
   * sets in the normal form of eqc occur in the domain of mvals by the order
   * in which sets are assigned.
   */
  void mkModelValueElementsFor(Node eqc,
                               std::vector<Node>& els,
                               const std::map<Node, Node>& mvals);
  /** get ordered sets equivalence classes
   *
   * Get the ordered set of equivalence classes computed by this class. This
   * ordering ensures the invariant mentioned above mkModelValueElementsFor.
   * 
   * This ordering ensures that all children of a node in the cardinality
   * graph computed by this class occur before it in this list.
   */
  const std::vector<Node>& getOrderedSetsEqClasses() { return d_oSetEqc; }

 private:
  /** constants */
  Node d_zero;
  /** the empty vector */
  std::vector<Node> d_emp_exp;
  /** the theory of sets which owns this */
  TheorySetsPrivate& d_parent;
  /** Reference to the state object for the theory of sets */
  SetsState& d_state;
  /** Reference to the inference manager for the theory of sets */
  InferenceManager& d_im;
  /** Reference to the equality engine of theory of sets */
  eq::EqualityEngine& d_ee;
  void checkCardBuildGraph(std::vector<Node>& lemmas);
  void registerCardinalityTerm(Node n, std::vector<Node>& lemmas);
  void checkCardCycles(std::vector<Node>& lemmas);
  void checkCardCyclesRec(Node eqc,
                          std::vector<Node>& curr,
                          std::vector<Node>& exp,
                          std::vector<Node>& lemmas);
  void checkNormalForms(std::vector<Node>& lemmas,
                        std::vector<Node>& intro_sets);
  void checkNormalForm(Node eqc, std::vector<Node>& intro_sets);
  void checkMinCard(std::vector<Node>& lemmas);
  /** element types of sets for which cardinality is enabled */
  std::map<TypeNode, bool> d_t_card_enabled;
  std::map<Node, Node> d_eqc_to_card_term;
  NodeSet d_card_processed;
  std::map<Node, std::vector<Node> > d_card_parent;
  std::map<Node, std::map<Node, std::vector<Node> > > d_ff;
  std::map<Node, std::vector<Node> > d_nf;
  std::map<Node, Node> d_card_base;
  /** the ordered set of equivalence classes */
  std::vector<Node> d_oSetEqc;
}; /* class CardinalityExtension */

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H */

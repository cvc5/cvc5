/*********************                                                        */
/*! \file solver_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver state of the theory of strings
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__SOLVER_STATE_H
#define CVC4__THEORY__STRINGS__SOLVER_STATE_H

#include <map>

#include "context/cdlist.h"
#include "context/context.h"
#include "expr/node.h"
#include "theory/strings/eqc_info.h"
#include "theory/strings/infer_info.h"
#include "theory/theory_model.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"
#include "theory/valuation.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * Solver state for strings.
 *
 * The purpose of this class is track and provide query functions for the state
 * of the assertions for the theory of strings. This includes:
 * (1) Equality queries via the equality engine,
 * (2) Whether the set of assertions is in conflict.
 * (3) Equivalence class information as in the class above.
 */
class SolverState : public TheoryState
{
  typedef context::CDList<Node> NodeList;

 public:
  SolverState(context::Context* c,
              context::UserContext* u,
              Valuation& v);
  ~SolverState();
  //-------------------------------------- disequality information
  /**
   * Get the list of disequalities that are currently asserted to the equality
   * engine.
   */
  const context::CDList<Node>& getDisequalityList() const;
  /**
   * notify the state that disequality (not (= t1 t2)) holds in the current
   * context. This will be included in the return of the above method.
   */
  void addDisequality(TNode t1, TNode t2);
  //-------------------------------------- end disequality information
  //------------------------------------------ conflicts
  /** set pending prefix conflict
   *
   * If conf is non-null, this is called when conf is a conjunction of literals
   * that hold in the current context that are unsatisfiable. It is set as the
   * "pending conflict" to be processed as a conflict lemma on the output
   * channel of this class. It is not sent out immediately since it may require
   * explanation from the equality engine, and may be called at any time, e.g.
   * during a merge operation, when the equality engine is not in a state to
   * provide explanations.
   */
  void setPendingPrefixConflictWhen(Node conf);
  /**
   * Set pending conflict, infer info version. Called when we are in conflict
   * based on the inference ii. This generalizes the above method.
   */
  void setPendingConflict(InferInfo& ii);
  /** return true if we have a pending conflict */
  bool hasPendingConflict() const;
  /** get the pending conflict, or null if none exist */
  bool getPendingConflict(InferInfo& ii) const;
  //------------------------------------------ end conflicts
  /** get length with explanation
   *
   * If possible, this returns an arithmetic term that exists in the current
   * context that is equal to the length of te, or otherwise returns the
   * length of t. It adds to exp literals that hold in the current context that
   * explain why that term is equal to the length of t. For example, if
   * we have assertions:
   *   len( x ) = 5 ^ z = x ^ x = y,
   * then getLengthExp( z, exp, y ) returns len( x ) and adds { z = x } to
   * exp. On the other hand, getLengthExp( z, exp, x ) returns len( x ) and
   * adds nothing to exp.
   */
  Node getLengthExp(Node t, std::vector<Node>& exp, Node te);
  /** shorthand for getLengthExp(t, exp, t) */
  Node getLength(Node t, std::vector<Node>& exp);
  /** explain non-empty
   *
   * This returns an explanation of why string-like term is non-empty in the
   * current context, if such an explanation exists. Otherwise, this returns
   * the null node.
   *
   * Note that an explanation is a (conjunction of) literals that currently hold
   * in the equality engine.
   */
  Node explainNonEmpty(Node s);
  /**
   * Is equal empty word? Returns true if s is equal to the empty word (of
   * its type). If this method returns true, it updates emps to be that word.
   * This is an optimization so that the relevant empty word does not need to
   * be constructed to check if s is equal to the empty word.
   */
  bool isEqualEmptyWord(Node s, Node& emps);
  /**
   * Get the above information for equivalence class eqc. If doMake is true,
   * we construct a new information class if one does not exist. The term eqc
   * should currently be a representative of the equality engine of this class.
   */
  EqcInfo* getOrMakeEqcInfo(Node eqc, bool doMake = true);
  /** Get pointer to the model object of the Valuation object */
  TheoryModel* getModel();
  /** Entailment check
   *
   * This calls entailmentCheck on the Valuation object of theory of strings.
   */
  std::pair<bool, Node> entailmentCheck(options::TheoryOfMode mode, TNode lit);
  /** Separate by length
   *
   * Separate the string representatives in argument n into a partition cols
   * whose collections have equal length. The i^th vector in cols has length
   * lts[i] for all elements in col. These vectors are furthmore separated
   * by string-like type.
   */
  void separateByLength(
      const std::vector<Node>& n,
      std::map<TypeNode, std::vector<std::vector<Node>>>& cols,
      std::map<TypeNode, std::vector<Node>>& lts);

 private:
  /** Common constants */
  Node d_zero;
  Node d_false;
  /**
   * The (SAT-context-dependent) list of disequalities that have been asserted
   * to the equality engine above.
   */
  NodeList d_eeDisequalities;
  /** The pending conflict if one exists */
  context::CDO<bool> d_pendingConflictSet;
  /** The pending conflict, valid if the above flag is true */
  InferInfo d_pendingConflict;
  /** Map from representatives to their equivalence class information */
  std::map<Node, EqcInfo*> d_eqcInfo;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__SOLVER_STATE_H */

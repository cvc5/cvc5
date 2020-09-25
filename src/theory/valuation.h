/*********************                                                        */
/*! \file valuation.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A "valuation" proxy for TheoryEngine
 **
 ** A "valuation" proxy for TheoryEngine.  This class breaks the dependence
 ** of theories' getValue() implementations on TheoryEngine.  getValue()
 ** takes a Valuation, which delegates to TheoryEngine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__VALUATION_H
#define CVC4__THEORY__VALUATION_H

#include "expr/node.h"
#include "options/theory_options.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

class TheoryModel;

/**
 * The status of an equality in the current context.
 */
enum EqualityStatus {
  /** The equality is known to be true and has been propagated */
  EQUALITY_TRUE_AND_PROPAGATED,
  /** The equality is known to be false and has been propagated */
  EQUALITY_FALSE_AND_PROPAGATED,
  /** The equality is known to be true */
  EQUALITY_TRUE,
  /** The equality is known to be false */
  EQUALITY_FALSE,
  /** The equality is not known, but is true in the current model */
  EQUALITY_TRUE_IN_MODEL,
  /** The equality is not known, but is false in the current model */
  EQUALITY_FALSE_IN_MODEL,
  /** The equality is completely unknown */
  EQUALITY_UNKNOWN
};/* enum EqualityStatus */

std::ostream& operator<<(std::ostream& os, EqualityStatus s);

/**
 * Returns true if the two statuses are compatible, i.e. both TRUE
 * or both FALSE (regardless of inmodel/propagation).
 */
bool equalityStatusCompatible(EqualityStatus s1, EqualityStatus s2);

class Valuation {
  TheoryEngine* d_engine;
public:
  Valuation(TheoryEngine* engine) :
    d_engine(engine) {
  }

  /**
   * Return true if n has an associated SAT literal
   */
  bool isSatLiteral(TNode n) const;

  /**
   * Get the current SAT assignment to the node n.
   *
   * This is only permitted if n is a theory atom that has an associated
   * SAT literal (or its negation).
   *
   * @return Node::null() if no current assignment; otherwise true or false.
   */
  Node getSatValue(TNode n) const;

  /**
   * Returns true if the node has a current SAT assignment. If yes, the
   * argument "value" is set to its value.
   *
   * This is only permitted if n is a theory atom that has an associated
   * SAT literal.
   *
   * @return true if the literal has a current assignment, and returns the
   * value in the "value" argument; otherwise false and the "value"
   * argument is unmodified.
   */
  bool hasSatValue(TNode n, bool& value) const;

  /**
   * Returns the equality status of the two terms, from the theory that owns the domain type.
   * The types of a and b must be the same.
   */
  EqualityStatus getEqualityStatus(TNode a, TNode b);

  /**
   * Returns the model value of the shared term (or null if not available).
   */
  Node getModelValue(TNode var);

  /**
   * Returns pointer to model. This model is only valid during last call effort
   * check.
   */
  TheoryModel* getModel();

  //-------------------------------------- static configuration of the model
  /**
   * Set that k is an unevaluated kind in the TheoryModel, if it exists.
   * See TheoryModel::setUnevaluatedKind for details.
   */
  void setUnevaluatedKind(Kind k);
  /**
   * Set that k is an unevaluated kind in the TheoryModel, if it exists.
   * See TheoryModel::setSemiEvaluatedKind for details.
   */
  void setSemiEvaluatedKind(Kind k);
  /**
   * Set that k is an irrelevant kind in the TheoryModel, if it exists.
   * See TheoryModel::setIrrelevantKind for details.
   */
  void setIrrelevantKind(Kind k);
  //-------------------------------------- end static configuration of the model

  /**
   * Ensure that the given node will have a designated SAT literal
   * that is definitionally equal to it.  The result of this function
   * is a Node that can be queried via getSatValue().
   *
   * @return the actual node that's been "literalized," which may
   * differ from the input due to theory-rewriting and preprocessing,
   * as well as CNF conversion
   */
  Node ensureLiteral(TNode n) CVC4_WARN_UNUSED_RESULT;

  /**
   * Returns whether the given lit (which must be a SAT literal) is a decision
   * literal or not.  Throws an exception if lit is not a SAT literal.  "lit" may
   * be in either phase; that is, if "lit" is a SAT literal, this function returns
   * true both for lit and the negation of lit.
   */
  bool isDecision(Node lit) const;

  /**
   * Get the assertion level of the SAT solver.
   */
  unsigned getAssertionLevel() const;

  /**
   * Request an entailment check according to the given theoryOfMode.
   * See theory.h for documentation on entailmentCheck().
   */
  std::pair<bool, Node> entailmentCheck(options::TheoryOfMode mode, TNode lit);

  /** need check ? */
  bool needCheck() const;

  /**
   * Is the literal lit (possibly) critical for satisfying the input formula in
   * the current context? This call is applicable only during collectModelInfo
   * or during LAST_CALL effort.
   */
  bool isRelevant(Node lit) const;
};/* class Valuation */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__VALUATION_H */

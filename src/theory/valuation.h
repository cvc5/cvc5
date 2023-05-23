/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A "valuation" proxy for TheoryEngine
 *
 * A "valuation" proxy for TheoryEngine.  This class breaks the dependence
 * of theories' getValue() implementations on TheoryEngine.  getValue()
 * takes a Valuation, which delegates to TheoryEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__VALUATION_H
#define CVC5__THEORY__VALUATION_H

#include "context/cdlist.h"
#include "expr/node.h"
#include "options/theory_options.h"

namespace cvc5::internal {

class TheoryEngine;

namespace theory {

struct Assertion;
class TheoryModel;
class SortInference;

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
   * Same as above, without setting the value.
   */
  bool hasSatValue(TNode n) const;

  /**
   * Returns the equality status of the two terms, from the theory that owns the domain type.
   * The types of a and b must be the same.
   */
  EqualityStatus getEqualityStatus(TNode a, TNode b);

  /**
   * Returns the candidate model value of the shared term (or null if not
   * available). A candidate model value is one computed at full effort,
   * prior to running theory combination and final model construction.
   */
  Node getCandidateModelValue(TNode var);

  /**
   * Returns pointer to model. This model is only valid during last call effort
   * check.
   */
  TheoryModel* getModel();
  /**
   * Returns a pointer to the sort inference module, which lives in TheoryEngine
   * and is non-null when options::sortInference is true.
   */
  SortInference* getSortInference();

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
   * Note that this call may add lemmas to the SAT solver corresponding to the
   * definition of subterms eliminated by preprocessing.
   *
   * @return the actual node that's been "literalized," which may
   * differ from the input due to theory-rewriting and preprocessing,
   * as well as CNF conversion
   */
  CVC5_WARN_UNUSED_RESULT Node ensureLiteral(TNode n);

  /**
   * This returns the theory-preprocessed form of term n. The theory
   * preprocessed form of a term t is one returned by
   * TheoryPreprocess::preprocess (see theory/theory_preprocess.h). In
   * particular, the returned term has syntax sugar symbols eliminated
   * (e.g. div, mod, partial datatype selectors), has term formulas (e.g. ITE
   * terms eliminated) and has been rewritten.
   *
   * Note that this call may add lemmas to the SAT solver corresponding to the
   * definition of subterms eliminated by preprocessing.
   *
   * @param n The node to preprocess
   * @return The preprocessed form of n
   */
  Node getPreprocessedTerm(TNode n);
  /**
   * Same as above, but also tracks the skolems and their corresponding
   * definitions in sks and skAsserts respectively.
   */
  Node getPreprocessedTerm(TNode n,
                           std::vector<Node>& skAsserts,
                           std::vector<Node>& sks);

  /**
   * Returns whether the given lit (which must be a SAT literal) is a decision
   * literal or not.  Throws an exception if lit is not a SAT literal.  "lit" may
   * be in either phase; that is, if "lit" is a SAT literal, this function returns
   * true both for lit and the negation of lit.
   */
  bool isDecision(Node lit) const;

  /**
   * Return whether lit has a fixed SAT assignment (i.e., implied by input
   * assertions).
   */
  bool isFixed(TNode lit) const;

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

  //------------------------------------------- access methods for assertions
  /**
   * The following methods are intended only to be used in limited use cases,
   * for cases where a theory (e.g. quantifiers) requires knowing about the
   * assertions from other theories.
   */
  /** The beginning iterator of facts for theory tid.*/
  context::CDList<Assertion>::const_iterator factsBegin(TheoryId tid);
  /** The beginning iterator of facts for theory tid.*/
  context::CDList<Assertion>::const_iterator factsEnd(TheoryId tid);
};/* class Valuation */

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__VALUATION_H */

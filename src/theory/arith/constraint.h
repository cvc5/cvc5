/*********************                                                        */
/*! \file constraint.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Alex Ozdemir, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Defines Constraint and ConstraintDatabase which is the internal representation of variables in arithmetic
 **
 ** This file defines Constraint and ConstraintDatabase.
 ** A Constraint is the internal representation of literals in TheoryArithmetic.
 ** Constraints are fundamentally a triple:
 **  - ArithVar associated with the constraint,
 **  - a DeltaRational value,
 **  - and a ConstraintType.
 **
 ** Literals:
 **   The constraint may also keep track of a node corresponding to the
 **   Constraint.
 **   This can be accessed by getLiteral() in O(1) if it has been set.
 **   This node must be in normal form and may be used for communication with
 **   the TheoryEngine.
 **
 ** In addition, Constraints keep track of the following:
 **  - A Constraint that is the negation of the Constraint.
 **  - An iterator into a set of Constraints for the ArithVar sorted by
 **    DeltaRational value.
 **  - A context dependent internal proof of the node that can be used for
 **    explanations.
 **  - Whether an equality/disequality has been split in the user context via a
 **    lemma.
 **  - Whether a constraint, be be used in explanations sent to the context
 **
 ** Looking up constraints:
 **  - All of the Constraints with associated nodes in the ConstraintDatabase can
 **    be accessed via a single hashtable lookup until the Constraint is removed.
 **  - Nodes that have not been associated to a constraints can be
 **    inserted/associated to existing nodes in O(log n) time.
 **
 ** Implications:
 **  - A Constraint can be used to find unate implications.
 **  - A unate implication is an implication based purely on the ArithVar matching
 **    and the DeltaRational value.
 **    (implies (<= x c) (<= x d)) given c <= d
 **  - This is done using the iterator into the sorted set of constraints.
 **  - Given a tight constraint and previous tightest constraint, this will
 **    efficiently propagate internally.
 **
 ** Additing and Removing Constraints
 **  - Adding Constraints takes O(log n) time where n is the number of
 **    constraints associated with the ArithVar.
 **  - Removing Constraints takes O(1) time.
 **
 ** Internals:
 **  - Constraints are pointers to ConstraintValues.
 **  - Undefined Constraints are NullConstraint.

 **
 ** Assumption vs. Assertion:
 ** - An assertion is anything on the theory d_fact queue.
 **   This includes any thing propagated and returned to the fact queue.
 **   These can be used in external conflicts and propagations of earlier proofs.
 ** - An assumption is anything on the theory d_fact queue that has no further
 **   explanation i.e. this theory did not propagate it.
 ** - To set something an assumption, first set it as being as assertion.
 ** - Internal assumptions have no explanations and must be regressed out of the proof.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__CONSTRAINT_H
#define CVC4__THEORY__ARITH__CONSTRAINT_H

#include <list>
#include <set>
#include <unordered_map>
#include <vector>

#include "base/configuration_private.h"
#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "context/context.h"
#include "expr/node.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/callbacks.h"
#include "theory/arith/congruence_manager.h"
#include "theory/arith/constraint_forward.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/proof_macros.h"

namespace CVC4 {
namespace theory {
namespace arith {
class Comparison;
}
}
}
namespace CVC4 {
namespace theory {
namespace arith {

/**
 * Logs the types of different proofs.
 * Current, proof types:
 * - NoAP             : This constraint is not known to be true.
 * - AssumeAP         : This is an input assertion. There is no proof.
 *                    : Something can be both asserted and have a proof.
 * - InternalAssumeAP : An internal assumption. This has no guarantee of having an external proof.
 *                    : This must be removed by regression.
 * - FarkasAP         : A proof with Farka's coefficients, i.e.
 *                    :  \sum lambda_i ( asNode(x_i) <= c_i  ) |= 0 < 0
 *                    : If proofs are on, coefficients will be logged.
 *                    : If proofs are off, coefficients will not be logged.
 *                    : A unate implication is a FarkasAP.
 * - TrichotomyAP     : This is any entailment using (x<= a and x >=a) => x = a
 *                    : Equivalently, (x > a or x < a or x = a)
 *                    : There are 3 candidate ways this can propagate:
 *                    :   !(x > a) and !(x = a) => x < a
 *                    :   !(x < a) and !(x = a) => x > a
 *                    :   !(x > a) and !(x < a) => x = a
 * - EqualityEngineAP : This is propagated by the equality engine.
 *                    : Consult this for the proof.
 * - IntTightenAP     : This is indicates that a bound involving integers was tightened.
 *                    : e.g. i < 5.5 became i <= 5, when i is an integer.
 * - IntHoleAP        : This is currently a catch-all for all integer specific reason.
 */
enum ArithProofType
  { NoAP,
    AssumeAP,
    InternalAssumeAP,
    FarkasAP,
    TrichotomyAP,
    EqualityEngineAP,
    IntTightenAP,
    IntHoleAP};

/**
 * The types of constraints.
 * The convex constraints are the constraints are LowerBound, Equality,
 * and UpperBound.
 */
enum ConstraintType {LowerBound, Equality, UpperBound, Disequality};


typedef context::CDList<ConstraintCP> CDConstraintList;

typedef std::unordered_map<Node, ConstraintP, NodeHashFunction> NodetoConstraintMap;

typedef size_t ConstraintRuleID;
static const ConstraintRuleID ConstraintRuleIdSentinel = std::numeric_limits<ConstraintRuleID>::max();

typedef size_t AntecedentId;
static const AntecedentId AntecedentIdSentinel = std::numeric_limits<AntecedentId>::max();


typedef size_t AssertionOrder;
static const AssertionOrder AssertionOrderSentinel = std::numeric_limits<AssertionOrder>::max();


/**
 * A ValueCollection binds together convex constraints that have the same
 * DeltaRational value.
 */
class ValueCollection {
private:

  ConstraintP d_lowerBound;
  ConstraintP d_upperBound;
  ConstraintP d_equality;
  ConstraintP d_disequality;

public:
  ValueCollection();

  static ValueCollection mkFromConstraint(ConstraintP c);

  bool hasLowerBound() const;
  bool hasUpperBound() const;
  bool hasEquality() const;
  bool hasDisequality() const;

  bool hasConstraintOfType(ConstraintType t) const;

  ConstraintP getLowerBound() const;
  ConstraintP getUpperBound() const;
  ConstraintP getEquality() const;
  ConstraintP getDisequality() const;

  ConstraintP getConstraintOfType(ConstraintType t) const;

  /** Returns true if any of the constraints are non-null. */
  bool empty() const;

  /**
   * Remove the constraint of the type t from the collection.
   * Returns true if the ValueCollection is now empty.
   * If true is returned, d_value is now NULL.
   */
  void remove(ConstraintType t);

  /**
   * Adds a constraint to the set.
   * The collection must not have a constraint of that type already.
   */
  void add(ConstraintP c);

  void push_into(std::vector<ConstraintP>& vec) const;

  ConstraintP nonNull() const;

  ArithVar getVariable() const;
  const DeltaRational& getValue() const;
};

/**
 * A Map of ValueCollections sorted by the associated DeltaRational values.
 *
 * Discussion:
 * While it is more natural to consider this a set, this cannot be a set as in
 * sets the type of both iterator and const_iterator in sets are
 * "constant iterators".  We require iterators that dereference to
 * ValueCollection&.
 *
 * See:
 * http://gcc.gnu.org/onlinedocs/libstdc++/ext/lwg-defects.html#103
 */
typedef std::map<DeltaRational, ValueCollection> SortedConstraintMap;
typedef SortedConstraintMap::iterator SortedConstraintMapIterator;
typedef SortedConstraintMap::const_iterator SortedConstraintMapConstIterator;

/** A Pair associating a variables and a Sorted ConstraintSet. */
struct PerVariableDatabase{
  ArithVar d_var;
  SortedConstraintMap d_constraints;

  // x ? c_1, x ? c_2, x ? c_3, ...
  // where ? is a non-empty subset of {lb, ub, eq}
  // c_1 < c_2 < c_3 < ...

  PerVariableDatabase(ArithVar v) : d_var(v), d_constraints() {}

  bool empty() const {
    return d_constraints.empty();
  }

  static bool IsEmpty(const PerVariableDatabase& p){
    return p.empty();
  }
};

/**
 * If proofs are on, there is a vector of rationals for farkas coefficients.
 * This is the owner of the memory for the vector, and calls delete upon
 * cleanup.
 *
 */
struct ConstraintRule {
  ConstraintP d_constraint;
  ArithProofType d_proofType;
  AntecedentId d_antecedentEnd;

  /**
   * In this comment, we abbreviate ConstraintDatabase::d_antecedents
   * and d_farkasCoefficients as ans and fc.
   *
   * This list is always empty if proofs are not enabled.
   *
   * If proofs are enabled, the proof of constraint c at p in ans[p] of length n
   * is (NullConstraint, ans[p-(n-1)], ... , ans[p-1], ans[p])
   *
   * Farkas' proofs show a contradiction with the negation of c, c_not =
   * c->getNegation().
   *
   * We treat the position for NullConstraint (p-n) as the position for the
   * farkas coefficient for so we pretend c_not is ans[p-n]. So this correlation
   * for the constraints we are going to use: (c_not, ans[p-n+(1)], ... ,
   * ans[p-n+(n-1)], ans[p-n+(n)]) With the coefficients at positions: (fc[0],
   * fc[1)], ... fc[n])
   *
   * The index of the constraints in the proof are {i | i <= 0 <= n] } (with
   * c_not being p-n). Partition the indices into L, U, and E, the lower bounds,
   * the upper bounds and equalities.
   *
   * We standardize the proofs to be upper bound oriented following the
   * convention: A x <= b with the proof witness of the form (lambda) Ax <=
   * (lambda) b and lambda >= 0.
   *
   * To accomplish this cleanly, the fc coefficients must be negative for lower
   * bounds. The signs of equalities can be either positive or negative.
   *
   * Thus the proof corresponds to (with multiplication over inequalities):
   *    \sum_{u in U} fc[u] ans[p-n+u] + \sum_{e in E} fc[e] ans[p-n+e]
   *  + \sum_{l in L} fc[l] ans[p-n+l]
   * |= 0 < 0
   * where fc[u] > 0, fc[l] < 0, and fc[e] != 0 (i.e. it can be either +/-).
   *
   * There is no requirement that the proof is minimal.
   * We do however use all of the constraints by requiring non-zero
   * coefficients.
   */
  RationalVectorCP d_farkasCoefficients;
  ConstraintRule()
    : d_constraint(NullConstraint)
    , d_proofType(NoAP)
    , d_antecedentEnd(AntecedentIdSentinel)
  {
    d_farkasCoefficients = RationalVectorCPSentinel;
  }

  ConstraintRule(ConstraintP con, ArithProofType pt)
    : d_constraint(con)
    , d_proofType(pt)
    , d_antecedentEnd(AntecedentIdSentinel)
  {
    d_farkasCoefficients = RationalVectorCPSentinel;
  }
  ConstraintRule(ConstraintP con, ArithProofType pt, AntecedentId antecedentEnd)
    : d_constraint(con)
    , d_proofType(pt)
    , d_antecedentEnd(antecedentEnd)
  {
    d_farkasCoefficients = RationalVectorCPSentinel;
  }

  ConstraintRule(ConstraintP con, ArithProofType pt, AntecedentId antecedentEnd, RationalVectorCP coeffs)
    : d_constraint(con)
    , d_proofType(pt)
    , d_antecedentEnd(antecedentEnd)
  {
    Assert(ARITH_PROOF_ON() || coeffs == RationalVectorCPSentinel);
    d_farkasCoefficients = coeffs;
  }

  void print(std::ostream& out) const;
  void debugPrint() const;
}; /* class ConstraintRule */

class Constraint {

  friend class ConstraintDatabase;

 public:
  /**
   * This begins construction of a minimal constraint.
   *
   * This should only be called by ConstraintDatabase.
   *
   * Because of circular dependencies a Constraint is not fully valid until
   * initialize has been called on it.
   */
  Constraint(ArithVar x,  ConstraintType t, const DeltaRational& v);

  /**
   * Destructor for a constraint.
   * This should only be called if safeToGarbageCollect() is true.
   */
  ~Constraint();

  static ConstraintType constraintTypeOfComparison(const Comparison& cmp);

  inline ConstraintType getType() const {
    return d_type;
  }

  inline ArithVar getVariable() const {
    return d_variable;
  }

  const DeltaRational& getValue() const {
    return d_value;
  }

  inline ConstraintP getNegation() const {
    return d_negation;
  }

  bool isEquality() const{
    return d_type == Equality;
  }
  bool isDisequality() const{
    return d_type == Disequality;
  }
  bool isLowerBound() const{
    return d_type == LowerBound;
  }
  bool isUpperBound() const{
    return d_type == UpperBound;
  }
  bool isStrictUpperBound() const{
    Assert(isUpperBound());
    return getValue().infinitesimalSgn() < 0;
  }

  bool isStrictLowerBound() const{
    Assert(isLowerBound());
    return getValue().infinitesimalSgn() > 0;
  }

  bool isSplit() const {
    return d_split;
  }

  /**
   * Splits the node in the user context.
   * Returns a lemma that is assumed to be true for the rest of the user context.
   * Constraint must be an equality or disequality.
   */
  Node split();

  bool canBePropagated() const {
    return d_canBePropagated;
  }
  void setCanBePropagated();

  /**
   * Light wrapper for calling setCanBePropagated(),
   * on this and this->d_negation.
   */
  void setPreregistered(){
    setCanBePropagated();
    d_negation->setCanBePropagated();
  }

  bool assertedToTheTheory() const {
    Assert((d_assertionOrder < AssertionOrderSentinel) != d_witness.isNull());
    return d_assertionOrder < AssertionOrderSentinel;
  }
  TNode getWitness() const {
    Assert(assertedToTheTheory());
    return d_witness;
  }

  bool assertedBefore(AssertionOrder time) const {
    return d_assertionOrder < time;
  }

  /**
   * Sets the witness literal for a node being on the assertion stack.
   *
   * If the negation of the node is true, inConflict must be true.
   * If the negation of the node is false, inConflict must be false.
   * Hence, negationHasProof() == inConflict.
   *
   * This replaces:
   *   void setAssertedToTheTheory(TNode witness);
   *   void setAssertedToTheTheoryWithNegationTrue(TNode witness);
   */
  void setAssertedToTheTheory(TNode witness, bool inConflict);

  bool hasLiteral() const {
    return !d_literal.isNull();
  }

  void setLiteral(Node n);

  Node getLiteral() const {
    Assert(hasLiteral());
    return d_literal;
  }

  /**
   * Set the node as having a proof and being an assumption.
   * The node must be assertedToTheTheory().
   *
   * Precondition: negationHasProof() == inConflict.
   *
   * Replaces:
   *  selfExplaining().
   *  selfExplainingWithNegationTrue().
   */
  void setAssumption(bool inConflict);

  /** Returns true if the node is an assumption.*/
  bool isAssumption() const;

  /** Set the constraint to have an EqualityEngine proof. */
  void setEqualityEngineProof();
  bool hasEqualityEngineProof() const;

  /** Returns true if the node has a Farkas' proof. */
  bool hasFarkasProof() const;

  /**
   * @brief Returns whether this constraint is provable using a Farkas
   * proof applied to (possibly tightened) input assertions.
   *
   * An example of a constraint that has a simple Farkas proof:
   *    x <= 0 proven from x + y <= 0 and x - y <= 0.
   *
   * An example of another constraint that has a simple Farkas proof:
   *    x <= 0 proven from x + y <= 0 and x - y <= 0.5 for integers x, y
   *       (integer bound-tightening is applied first!).
   *
   * An example of a constraint that might be proven **without** a simple
   * Farkas proof:
   *    x < 0 proven from not(x == 0) and not(x > 0).
   *
   * This could be proven internally by the arithmetic theory using
   * `TrichotomyAP` as the proof type.
   *
   */
  bool hasSimpleFarkasProof() const;
  /**
   * Returns whether this constraint is an assumption or a tightened
   * assumption.
   */
  bool isPossiblyTightenedAssumption() const;

  /** Returns true if the node has a int bound tightening proof. */
  bool hasIntTightenProof() const;

  /** Returns true if the node has a int hole proof. */
  bool hasIntHoleProof() const;

  /** Returns true if the node has a trichotomy proof. */
  bool hasTrichotomyProof() const;

  void printProofTree(std::ostream & out, size_t depth = 0) const;

  /**
   * A sets the constraint to be an internal assumption.
   *
   * This does not need to have a witness or an associated literal.
   * This is always itself in the explanation fringe for both conflicts
   * and propagation.
   * This cannot be converted back into a Node conflict or explanation.
   *
   * This cannot have a proof or be asserted to the theory!
   *
   */
  void setInternalAssumption(bool inConflict);
  bool isInternalAssumption() const;

  /**
   * Returns a explanation of the constraint that is appropriate for conflicts.
   *
   * This is not appropriate for propagation!
   *
   * This is the minimum fringe of the implication tree s.t.
   * every constraint is assertedToTheTheory() or hasEqualityEngineProof().
   */
  Node externalExplainByAssertions() const {
    return externalExplain(AssertionOrderSentinel);
  }

  /**
   * Writes an explanation of a constraint into the node builder.
   * Pushes back an explanation that is acceptable to send to the sat solver.
   * nb is assumed to be an AND.
   *
   * This is the minimum fringe of the implication tree s.t.
   * every constraint is assertedToTheTheory() or hasEqualityEngineProof().
   *
   * This is not appropriate for propagation!
   * Use explainForPropagation() instead.
   */
  void externalExplainByAssertions(NodeBuilder<>& nb) const{
    externalExplain(nb, AssertionOrderSentinel);
  }

  /* Equivalent to calling externalExplainByAssertions on all constraints in b */
  static Node externalExplainByAssertions(const ConstraintCPVec& b);
  static Node externalExplainByAssertions(ConstraintCP a, ConstraintCP b);
  static Node externalExplainByAssertions(ConstraintCP a, ConstraintCP b, ConstraintCP c);

  /**
   * This is the minimum fringe of the implication tree s.t. every constraint is
   * - assertedToTheTheory(),
   * - isInternalDecision() or
   * - hasEqualityEngineProof().
   */
  static void assertionFringe(ConstraintCPVec& v);
  static void assertionFringe(ConstraintCPVec& out, const ConstraintCPVec& in);

  /** The fringe of a farkas' proof. */
  bool onFringe() const {
    return assertedToTheTheory() || isInternalAssumption() || hasEqualityEngineProof();
  }

  /**
   * Returns an explanation of a propagation by the ConstraintDatabase.
   * The constraint must have a proof.
   * The constraint cannot be an assumption.
   *
   * This is the minimum fringe of the implication tree (excluding the constraint itself)
   * s.t. every constraint is assertedToTheTheory() or hasEqualityEngineProof().
   */
  Node externalExplainForPropagation() const {
    Assert(hasProof());
    Assert(!isAssumption());
    Assert(!isInternalAssumption());
    return externalExplain(d_assertionOrder);
  }

  /**
   * Explain the constraint and its negation in terms of assertions.
   * The constraint must be in conflict.
   */
  Node externalExplainConflict() const;


  /** The constraint is known to be true. */
  inline bool hasProof() const {
    return d_crid != ConstraintRuleIdSentinel;
  }

  /** The negation of the constraint is known to hold. */
  inline bool negationHasProof() const {
    return d_negation->hasProof();
  }

  /** Neither the contraint has a proof nor the negation has a proof.*/
  bool truthIsUnknown() const {
    return !hasProof() && !negationHasProof();
  }

  /** This is a synonym for hasProof(). */
  inline bool isTrue() const {
    return hasProof();
  }

  /** Both the constraint and its negation are true. */
  inline bool inConflict() const {
    return hasProof() && negationHasProof();
  }

  /**
   * Returns the constraint that corresponds to taking
   *    x r ceiling(getValue()) where r is the node's getType().
   * Esstentially this is an up branch.
   */
  ConstraintP getCeiling();

  /**
   * Returns the constraint that corresponds to taking
   *    x r floor(getValue()) where r is the node's getType().
   * Esstentially this is a down branch.
   */
  ConstraintP getFloor();

  static ConstraintP makeNegation(ArithVar v, ConstraintType t, const DeltaRational& r);

  const ValueCollection& getValueCollection() const;


  ConstraintP getStrictlyWeakerUpperBound(bool hasLiteral, bool mustBeAsserted) const;
  ConstraintP getStrictlyWeakerLowerBound(bool hasLiteral, bool mustBeAsserted) const;

  /**
   * Marks a the constraint c as being entailed by a.
   * The Farkas proof 1*(a) + -1 (c) |= 0<0
   *
   * After calling impliedByUnate(), the caller should either raise a conflict
   * or try call tryToPropagate().
   */
  void impliedByUnate(ConstraintCP a, bool inConflict);

  /**
   * Marks a the constraint c as being entailed by a.
   * The reason has to do with integer bound tightening.
   *
   * After calling impliedByIntTighten(), the caller should either raise a conflict
   * or try call tryToPropagate().
   */
  void impliedByIntTighten(ConstraintCP a, bool inConflict);

  /**
   * Marks a the constraint c as being entailed by a.
   * The reason has to do with integer reasoning.
   *
   * After calling impliedByIntHole(), the caller should either raise a conflict
   * or try call tryToPropagate().
   */
  void impliedByIntHole(ConstraintCP a, bool inConflict);

  /**
   * Marks a the constraint c as being entailed by a.
   * The reason has to do with integer reasoning.
   *
   * After calling impliedByIntHole(), the caller should either raise a conflict
   * or try call tryToPropagate().
   */
  void impliedByIntHole(const ConstraintCPVec& b, bool inConflict);

  /**
   * This is a lemma of the form:
   *   x < d or x = d or x > d
   * The current constraint c is one of the above constraints and {a,b}
   * are the negation of the other two constraints.
   *
   * Preconditions:
   * - negationHasProof() == inConflict.
   *
   * After calling impliedByTrichotomy(), the caller should either raise a conflict
   * or try call tryToPropagate().
   */
  void impliedByTrichotomy(ConstraintCP a, ConstraintCP b, bool inConflict);

  /**
   * Marks the node as having a Farkas proof.
   *
   * Preconditions:
   * - coeffs == NULL if proofs are off.
   * - See the comments for ConstraintRule for the form of coeffs when
   *   proofs are on.
   * - negationHasProof() == inConflict.
   *
   * After calling impliedByFarkas(), the caller should either raise a conflict
   * or try call tryToPropagate().
   */
  void impliedByFarkas(const ConstraintCPVec& b, RationalVectorCP coeffs, bool inConflict);

  /**
   * Generates an implication node, B => getLiteral(),
   * where B is the result of externalExplainByAssertions(b).
   * Does not guarantee b is the explanation of the constraint.
   */
  Node externalImplication(const ConstraintCPVec& b) const;

  /**
   * Returns true if the variable is assigned the value dr,
   * the constraint would be satisfied.
   */
  bool satisfiedBy(const DeltaRational& dr) const;

  /**
   * The node must have a proof already and be eligible for propagation!
   * You probably want to call tryToPropagate() instead.
   *
   * Preconditions:
   * - hasProof()
   * - canBePropagated()
   * - !assertedToTheTheory()
   */
  void propagate();

  /**
   * If the constraint
   *   canBePropagated() and
   *   !assertedToTheTheory(),
   * the constraint is added to the database's propagation queue.
   *
   * Precondition:
   * - hasProof()
   */
  void tryToPropagate();

  /**
   * Returns a reference to the containing database.
   * Precondition: the constraint must be initialized.
   */
  const ConstraintDatabase& getDatabase() const;

  /** Returns the constraint rule at the position. */
  const ConstraintRule& getConstraintRule() const;

 private:
  /**  Returns true if the constraint has been initialized. */
  bool initialized() const;

  /**
   * This initializes the fields that cannot be set in the constructor due to
   * circular dependencies.
   */
  void initialize(ConstraintDatabase* db,
                  SortedConstraintMapIterator v,
                  ConstraintP negation);

  class ConstraintRuleCleanup
  {
   public:
    inline void operator()(ConstraintRule* crp)
    {
      Assert(crp != NULL);
      ConstraintP constraint = crp->d_constraint;
      Assert(constraint->d_crid != ConstraintRuleIdSentinel);
      constraint->d_crid = ConstraintRuleIdSentinel;
      ARITH_PROOF({
        if (crp->d_farkasCoefficients != RationalVectorCPSentinel)
        {
          delete crp->d_farkasCoefficients;
        }
      });
    }
  };

  class CanBePropagatedCleanup
  {
   public:
    inline void operator()(ConstraintP* p)
    {
      ConstraintP constraint = *p;
      Assert(constraint->d_canBePropagated);
      constraint->d_canBePropagated = false;
    }
  };

  class AssertionOrderCleanup
  {
   public:
    inline void operator()(ConstraintP* p)
    {
      ConstraintP constraint = *p;
      Assert(constraint->assertedToTheTheory());
      constraint->d_assertionOrder = AssertionOrderSentinel;
      constraint->d_witness = TNode::null();
      Assert(!constraint->assertedToTheTheory());
    }
  };

  class SplitCleanup
  {
   public:
    inline void operator()(ConstraintP* p)
    {
      ConstraintP constraint = *p;
      Assert(constraint->d_split);
      constraint->d_split = false;
    }
  };

  /**
   * Returns true if the node is safe to garbage collect.
   * Both it and its negation must have no context dependent data set.
   */
  bool safeToGarbageCollect() const;

  /**
   * Returns true if the constraint has no context dependent data set.
   */
  bool contextDependentDataIsSet() const;

  /**
   * Returns true if the node correctly corresponds to the constraint that is
   * being set.
   */
  bool sanityChecking(Node n) const;

  /** Returns a reference to the map for d_variable. */
  SortedConstraintMap& constraintSet() const;

  /** Returns coefficients for the proofs for farkas cancellation. */
  static std::pair<int, int> unateFarkasSigns(ConstraintCP a, ConstraintCP b);

  Node externalExplain(AssertionOrder order) const;

  /**
   * Returns an explanation of that was assertedBefore(order).
   * The constraint must have a proof.
   * The constraint cannot be selfExplaining().
   *
   * This is the minimum fringe of the implication tree
   * s.t. every constraint is assertedBefore(order) or hasEqualityEngineProof().
   */
  void externalExplain(NodeBuilder<>& nb, AssertionOrder order) const;

  static Node externalExplain(const ConstraintCPVec& b, AssertionOrder order);

  inline ArithProofType getProofType() const {
    return getConstraintRule().d_proofType;
  }

  inline AntecedentId getEndAntecedent() const {
    return getConstraintRule().d_antecedentEnd;
  }

  inline RationalVectorCP getFarkasCoefficients() const
  {
    return ARITH_NULLPROOF(getConstraintRule().d_farkasCoefficients);
  }

  void debugPrint() const;

  /**
   * The proof of the node is empty.
   * The proof must be a special proof. Either
   *   isSelfExplaining() or
   *    hasEqualityEngineProof()
   */
  bool antecentListIsEmpty() const;

  bool antecedentListLengthIsOne() const;

  /** Return true if every element in b has a proof. */
  static bool allHaveProof(const ConstraintCPVec& b);

  /** Precondition: hasFarkasProof()
   * Computes the combination implied by the farkas coefficients. Sees if it is
   * a contradiction.
   */

  bool wellFormedFarkasProof() const;

  /** The ArithVar associated with the constraint. */
  const ArithVar d_variable;

  /** The type of the Constraint. */
  const ConstraintType d_type;

  /** The DeltaRational value with the constraint. */
  const DeltaRational d_value;

  /** A pointer to the associated database for the Constraint. */
  ConstraintDatabase* d_database;

  /**
   * The node to be communicated with the TheoryEngine.
   *
   * This is not context dependent, but may be set once.
   *
   * This must be set if the constraint canBePropagated().
   * This must be set if the constraint assertedToTheTheory().
   * Otherwise, this may be null().
   */
  Node d_literal;

  /** Pointer to the negation of the Constraint. */
  ConstraintP d_negation;

  /**
   * This is true if the associated node can be propagated.
   *
   * This should be enabled if the node has been preregistered.
   *
   * Sat Context Dependent.
   * This is initially false.
   */
  bool d_canBePropagated;

  /**
   * This is the order the constraint was asserted to the theory.
   * If this has been set, the node can be used in conflicts.
   * If this is c.d_assertedOrder < d.d_assertedOrder, then c can be used in the
   * explanation of d.
   *
   * This should be set after the literal is dequeued by Theory::get().
   *
   * Sat Context Dependent.
   * This is initially AssertionOrderSentinel.
   */
  AssertionOrder d_assertionOrder;

  /**
   * This is guaranteed to be on the fact queue.
   * For example if x + y = x + 1 is on the fact queue, then use this
   */
  TNode d_witness;

  /**
   * The position of the constraint in the constraint rule id.
   *
   * Sat Context Dependent.
   * This is initially
   */
  ConstraintRuleID d_crid;

  /**
   * True if the equality has been split.
   * Only meaningful if ConstraintType == Equality.
   *
   * User Context Dependent.
   * This is initially false.
   */
  bool d_split;

  /**
   * Position in sorted constraint set for the variable.
   * Unset if d_type is Disequality.
   */
  SortedConstraintMapIterator d_variablePosition;

}; /* class ConstraintValue */

std::ostream& operator<<(std::ostream& o, const Constraint& c);
std::ostream& operator<<(std::ostream& o, const ConstraintP c);
std::ostream& operator<<(std::ostream& o, const ConstraintCP c);
std::ostream& operator<<(std::ostream& o, const ConstraintType t);
std::ostream& operator<<(std::ostream& o, const ValueCollection& c);
std::ostream& operator<<(std::ostream& o, const ConstraintCPVec& v);
std::ostream& operator<<(std::ostream& o, const ArithProofType);


class ConstraintDatabase {
private:
  /**
   * The map from ArithVars to their unique databases.
   * When the vector changes size, we cannot allow the maps to move so this
   * is a vector of pointers.
   */
  std::vector<PerVariableDatabase*> d_varDatabases;

  SortedConstraintMap& getVariableSCM(ArithVar v) const;

  /** Maps literals to constraints.*/
  NodetoConstraintMap d_nodetoConstraintMap;

  /**
   * A queue of propagated constraints.
   * ConstraintCP are pointers.
   * The elements of the queue do not require destruction.
   */
  context::CDQueue<ConstraintCP> d_toPropagate;

  /**
   * Proofs are lists of valid constraints terminated by the first null
   * sentinel value in the proof list.
   * We abbreviate d_antecedents as ans in the comment.
   *
   * The proof at p in ans[p] of length n is
   *  (NullConstraint, ans[p-(n-1)], ... , ans[p-1], ans[p])
   *
   * The proof at p corresponds to the conjunction:
   *  (and x_i)
   *
   * So the proof of a Constraint c corresponds to the horn clause:
   *  (implies (and x_i) c)
   * where (and x_i) is the proof at c.d_crid d_antecedentEnd.
   *
   * Constraints are pointers so this list is designed not to require any destruction.
   */
  CDConstraintList d_antecedents;

  typedef context::CDList<ConstraintRule, Constraint::ConstraintRuleCleanup> ConstraintRuleList;
  typedef context::CDList<ConstraintP, Constraint::CanBePropagatedCleanup> CBPList;
  typedef context::CDList<ConstraintP, Constraint::AssertionOrderCleanup> AOList;
  typedef context::CDList<ConstraintP, Constraint::SplitCleanup> SplitList;



  /**
   * The watch lists are collected together as they need to be garbage collected
   * carefully.
   */
  struct Watches{

    /**
     * Contains the exact list of constraints that have a proof.
     * Upon pop, this unsets d_crid to NoAP.
     *
     * The index in this list is the proper ordering of the proofs.
     */
    ConstraintRuleList d_constraintProofs;

    /**
     * Contains the exact list of constraints that can be used for propagation.
     */
    CBPList d_canBePropagatedWatches;

    /**
     * Contains the exact list of constraints that have been asserted to the theory.
     */
    AOList d_assertionOrderWatches;


    /**
     * Contains the exact list of atoms that have been preregistered.
     * This is a pointer as it must be destroyed before the elements of
     * d_varDatabases.
     */
    SplitList d_splitWatches;
    Watches(context::Context* satContext, context::Context* userContext);
  };
  Watches* d_watches;

  void pushSplitWatch(ConstraintP c);
  void pushCanBePropagatedWatch(ConstraintP c);
  void pushAssertionOrderWatch(ConstraintP c, TNode witness);

  /** Assumes that antecedents have already been pushed. */
  void pushConstraintRule(const ConstraintRule& crp);

  /** Returns true if all of the entries of the vector are empty. */
  static bool emptyDatabase(const std::vector<PerVariableDatabase>& vec);

  /** Map from nodes to arithvars. */
  const ArithVariables& d_avariables;

  const ArithVariables& getArithVariables() const{
    return d_avariables;
  }

  ArithCongruenceManager& d_congruenceManager;

  const context::Context * const d_satContext;

  RaiseConflict d_raiseConflict;


  const Rational d_one;
  const Rational d_negOne;

  friend class Constraint;

public:

  ConstraintDatabase( context::Context* satContext,
                      context::Context* userContext,
                      const ArithVariables& variables,
                      ArithCongruenceManager& dm,
                      RaiseConflict conflictCallBack);

  ~ConstraintDatabase();

  /** Adds a literal to the database. */
  ConstraintP addLiteral(TNode lit);

  /**
   * If hasLiteral() is true, returns the constraint.
   * Otherwise, returns NullConstraint.
   */
  ConstraintP lookup(TNode literal) const;

  /**
   * Returns true if the literal has been added to the database.
   * This is a hash table lookup.
   * It does not look in the database for an equivalent corresponding constraint.
   */
  bool hasLiteral(TNode literal) const;

  bool hasMorePropagations() const{
    return !d_toPropagate.empty();
  }

  ConstraintCP nextPropagation(){
    Assert(hasMorePropagations());

    ConstraintCP p = d_toPropagate.front();
    d_toPropagate.pop();

    return p;
  }

  void addVariable(ArithVar v);
  bool variableDatabaseIsSetup(ArithVar v) const;
  void removeVariable(ArithVar v);

  Node eeExplain(ConstraintCP c) const;
  void eeExplain(ConstraintCP c, NodeBuilder<>& nb) const;

  /**
   * Returns a constraint with the variable v, the constraint type t, and a value
   * dominated by r (explained below) if such a constraint exists in the database.
   * If no such constraint exists, NullConstraint is returned.
   *
   * t must be either UpperBound or LowerBound.
   * The returned value v is dominated:
   *  If t is UpperBound, r <= v
   *  If t is LowerBound, r >= v
   *
   * variableDatabaseIsSetup(v) must be true.
   */
  ConstraintP getBestImpliedBound(ArithVar v, ConstraintType t, const DeltaRational& r) const;

  /** Returns the constraint, if it exists */
  ConstraintP lookupConstraint(ArithVar v, ConstraintType t, const DeltaRational& r) const;

  /**
   * Returns a constraint with the variable v, the constraint type t and the value r.
   * If there is such a constraint in the database already, it is returned.
   * If there is no such constraint, this constraint is added to the database.
   *
   */
  ConstraintP getConstraint(ArithVar v, ConstraintType t, const DeltaRational& r);

  /**
   * Returns a constraint of the given type for the value and variable
   * for the given ValueCollection, vc.
   * This is made if there is no such constraint.
   */
  ConstraintP ensureConstraint(ValueCollection& vc, ConstraintType t);


  void deleteConstraintAndNegation(ConstraintP c);

  /**
   * Outputs a minimal set of unate implications onto the vector for the variable.
   * This outputs lemmas of the general forms
   *     (= p c) implies (<= p d) for c < d, or
   *     (= p c) implies (not (= p d)) for c != d.
   */
  void outputUnateEqualityLemmas(std::vector<Node>& lemmas) const;
  void outputUnateEqualityLemmas(std::vector<Node>& lemmas, ArithVar v) const;

  /**
   * Outputs a minimal set of unate implications onto the vector for the variable.
   *
   * If ineqs is true, this outputs lemmas of the general form
   *     (<= p c) implies (<= p d) for c < d.
   */
  void outputUnateInequalityLemmas(std::vector<Node>& lemmas) const;
  void outputUnateInequalityLemmas(std::vector<Node>& lemmas, ArithVar v) const;


  void unatePropLowerBound(ConstraintP curr, ConstraintP prev);
  void unatePropUpperBound(ConstraintP curr, ConstraintP prev);
  void unatePropEquality(ConstraintP curr, ConstraintP prevLB, ConstraintP prevUB);

  /** AntecendentID must be in range. */
  ConstraintCP getAntecedent(AntecedentId p) const;

private:
  /** returns true if cons is now in conflict. */
  bool handleUnateProp(ConstraintP ant, ConstraintP cons);

  DenseSet d_reclaimable;

  class Statistics {
  public:
    IntStat d_unatePropagateCalls;
    IntStat d_unatePropagateImplications;

    Statistics();
    ~Statistics();
  } d_statistics;

}; /* ConstraintDatabase */


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ARITH__CONSTRAINT_H */

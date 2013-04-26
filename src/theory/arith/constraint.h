/*********************                                                        */
/*! \file constraint.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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
 **  - A Constrain that is the negation of the Constraint.
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
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__CONSTRAINT_H
#define __CVC4__THEORY__ARITH__CONSTRAINT_H

#include "expr/node.h"

#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdqueue.h"

#include "theory/arith/arithvar.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/congruence_manager.h"
#include "theory/arith/constraint_forward.h"
#include "theory/arith/callbacks.h"

#include <vector>
#include <list>
#include <set>
#include <ext/hash_map>

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * The types of constraints.
 * The convex constraints are the constraints are LowerBound, Equality,
 * and UpperBound.
 */
enum ConstraintType {LowerBound, Equality, UpperBound, Disequality};


typedef context::CDList<Constraint> CDConstraintList;

typedef __gnu_cxx::hash_map<Node, Constraint, NodeHashFunction> NodetoConstraintMap;

typedef size_t ProofId;
static ProofId ProofIdSentinel = std::numeric_limits<ProofId>::max();

typedef size_t AssertionOrder;
static AssertionOrder AssertionOrderSentinel = std::numeric_limits<AssertionOrder>::max();

/**
 * A ValueCollection binds together convex constraints that have the same
 * DeltaRational value.
 */
class ValueCollection {
private:

  Constraint d_lowerBound;
  Constraint d_upperBound;
  Constraint d_equality;
  Constraint d_disequality;

public:
  ValueCollection()
    : d_lowerBound(NullConstraint),
      d_upperBound(NullConstraint),
      d_equality(NullConstraint),
      d_disequality(NullConstraint)
  {}

  static ValueCollection mkFromConstraint(Constraint c);

  bool hasLowerBound() const{
    return d_lowerBound != NullConstraint;
  }
  bool hasUpperBound() const{
    return d_upperBound != NullConstraint;
  }
  bool hasEquality() const{
    return d_equality != NullConstraint;
  }
  bool hasDisequality() const {
    return d_disequality != NullConstraint;
  }

  bool hasConstraintOfType(ConstraintType t) const;

  Constraint getLowerBound() const {
    Assert(hasLowerBound());
    return d_lowerBound;
  }
  Constraint getUpperBound() const {
    Assert(hasUpperBound());
    return d_upperBound;
  }
  Constraint getEquality() const {
    Assert(hasEquality());
    return d_equality;
  }
  Constraint getDisequality() const {
    Assert(hasDisequality());
    return d_disequality;
  }

  Constraint getConstraintOfType(ConstraintType t) const;

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
  void add(Constraint c);

  void push_into(std::vector<Constraint>& vec) const;

  Constraint nonNull() const;

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

class ConstraintValue {
private:
  /** The ArithVar associated with the constraint. */
  const ArithVar d_variable;

  /** The type of the Constraint. */
  const ConstraintType d_type;

  /** The DeltaRational value with the constraint. */
  const DeltaRational d_value;

  /** A pointer to the associated database for the Constraint. */
  ConstraintDatabase * d_database;

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
  Constraint d_negation;

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
  AssertionOrder _d_assertionOrder;
  /**
   * This is guaranteed to be on the fact queue.
   * For example if x + y = x + 1 is on the fact queue, then use this 
   */
  TNode d_witness;

  /**
   * This points at the proof for the constraint in the current context.
   *
   * Sat Context Dependent.
   * This is initially ProofIdSentinel.
   */
  ProofId d_proof;

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

  friend class ConstraintDatabase;

  /**
   * This begins construction of a minimal constraint.
   *
   * This should only be called by ConstraintDatabase.
   *
   * Because of circular dependencies a Constraint is not fully valid until
   * initialize has been called on it.
   */
  ConstraintValue(ArithVar x,  ConstraintType t, const DeltaRational& v);

  /**
   * Destructor for a constraint.
   * This should only be called if safeToGarbageCollect() is true.
   */
  ~ConstraintValue();

  bool initialized() const;

  /**
   * This initializes the fields that cannot be set in the constructor due to
   * circular dependencies.
   */
  void initialize(ConstraintDatabase* db, SortedConstraintMapIterator v, Constraint negation);

  class ProofCleanup {
  public:
    inline void operator()(Constraint* p){
      Constraint constraint = *p;
      Assert(constraint->d_proof != ProofIdSentinel);
      constraint->d_proof = ProofIdSentinel;
    }
  };

  class CanBePropagatedCleanup {
  public:
    inline void operator()(Constraint* p){
      Constraint constraint = *p;
      Assert(constraint->d_canBePropagated);
      constraint->d_canBePropagated = false;
    }
  };

  class AssertionOrderCleanup {
  public:
    inline void operator()(Constraint* p){
      Constraint constraint = *p;
      Assert(constraint->assertedToTheTheory());
      constraint->_d_assertionOrder = AssertionOrderSentinel;
      constraint->d_witness = TNode::null();
      Assert(!constraint->assertedToTheTheory());
    }
  };

  class SplitCleanup {
  public:
    inline void operator()(Constraint* p){
      Constraint constraint = *p;
      Assert(constraint->d_split);
      constraint->d_split = false;
    }
  };

  /** Returns true if the node is safe to garbage collect. */
  bool safeToGarbageCollect() const;

  /**
   * Returns true if the node correctly corresponds to the constraint that is
   * being set.
   */
  bool sanityChecking(Node n) const;

  /** Returns a reference to the map for d_variable. */
  SortedConstraintMap& constraintSet() const;

public:

  ConstraintType getType() const {
    return d_type;
  }

  ArithVar getVariable() const {
    return d_variable;
  }

  const DeltaRational& getValue() const {
    return d_value;
  }

  Constraint getNegation() const {
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
   * Returns a lemma that is assumed to be true fro the rest of the user context.
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
    Assert((_d_assertionOrder < AssertionOrderSentinel) != d_witness.isNull());
    return _d_assertionOrder < AssertionOrderSentinel;
  }
  TNode getWitness() const {
    Assert(assertedToTheTheory());
    return d_witness;
  }

  bool assertedBefore(AssertionOrder time) const {
    return _d_assertionOrder < time;
  }


  void setAssertedToTheTheory(TNode witness);


  bool hasLiteral() const {
    return !d_literal.isNull();
  }

  void setLiteral(Node n);

  Node getLiteral() const {
    Assert(hasLiteral());
    return d_literal;
  }

  /**
   * Set the node as selfExplaining().
   * The node must be assertedToTheTheory().
   */
  void selfExplaining();

  /** Returns true if the node is selfExplaining.*/
  bool isSelfExplaining() const;

  /**
   * Set the constraint to be a EqualityEngine proof.
   */
  void setEqualityEngineProof();
  bool hasEqualityEngineProof() const;


  /**
   * There cannot be a literal associated with this constraint.
   * The explanation is the constant true.
   * explainInto() does nothing.
   */
  //void setPseudoConstraint();
  //bool isPseudoConstraint() const;

  /**
   * Returns a explanation of the constraint that is appropriate for conflicts.
   *
   * This is not appropriate for propagation!
   *
   * This is the minimum fringe of the implication tree s.t.
   * every constraint is assertedToTheTheory() or hasEqualityEngineProof().
   */
  Node explainForConflict() const{
    return explainBefore(AssertionOrderSentinel);
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
  void explainForConflict(NodeBuilder<>& nb) const{
    explainBefore(nb, AssertionOrderSentinel);
  }

  /** Utility function built from explainForConflict. */
  static Node explainConflict(Constraint a, Constraint b);
  static Node explainConflict(Constraint a, Constraint b, Constraint c);

  /**
   * Returns an explanation of a propagation by the ConstraintDatabase.
   * The constraint must have a proof.
   * The constraint cannot be selfExplaining().
   *
   * This is the minimum fringe of the implication tree (excluding the constraint itself)
   * s.t. every constraint is assertedToTheTheory() or hasEqualityEngineProof().
   */
  Node explainForPropagation() const {
    Assert(hasProof());
    Assert(!isSelfExplaining());
    return explainBefore(_d_assertionOrder);
  }

private:
  Node explainBefore(AssertionOrder order) const;

  /**
   * Returns an explanation of that was assertedBefore(order).
   * The constraint must have a proof.
   * The constraint cannot be selfExplaining().
   *
   * This is the minimum fringe of the implication tree
   * s.t. every constraint is assertedBefore(order) or hasEqualityEngineProof().
   */
  void explainBefore(NodeBuilder<>& nb, AssertionOrder order) const;

public:
  bool hasProof() const {
    return d_proof != ProofIdSentinel;
  }
  bool negationHasProof() const {
    return d_negation->hasProof();
  }

  bool truthIsUnknown() const {
    return !hasProof() && !negationHasProof();
  }

  bool isTrue() const {
    return hasProof();
  }

  Constraint getCeiling();

  Constraint getFloor();


  static Constraint makeNegation(ArithVar v, ConstraintType t, const DeltaRational& r);

  const ValueCollection& getValueCollection() const;


  Constraint getStrictlyWeakerUpperBound(bool hasLiteral, bool mustBeAsserted) const;
  Constraint getStrictlyWeakerLowerBound(bool hasLiteral, bool mustBeAsserted) const;

  /**
   * Marks the node as having a proof a.
   * Adds the node the database's propagation queue.
   *
   * Preconditions:
   * canBePropagated()
   * !assertedToTheTheory()
   */
  void propagate(Constraint a);
  void propagate(Constraint a, Constraint b);
  void propagate(const std::vector<Constraint>& b);
  /**
   * The only restriction is that this is not known be true.
   * This propagates if there is a node.
   */
  void impliedBy(Constraint a);
  void impliedBy(Constraint a, Constraint b);
  void impliedBy(const std::vector<Constraint>& b);


  /** The node must have a proof already and be eligible for propagation! */
  void propagate();

  bool satisfiedBy(const DeltaRational& dr) const;

private:
  /**
   * Marks the node as having a proof and being selfExplaining.
   * Neither the node nor its negation can have a proof.
   * This is internal!
   */
  void markAsTrue();
  /**
   * Marks the node as having a proof a.
   * This is safe if the node does not have
   */
  void markAsTrue(Constraint a);

  void markAsTrue(Constraint a, Constraint b);
  void markAsTrue(const std::vector<Constraint>& b);

  void debugPrint() const;

  /**
   * The proof of the node is empty.
   * The proof must be a special proof. Either
   *   isSelfExplaining() or
   *    hasEqualityEngineProof()
   */
  bool proofIsEmpty() const;

}; /* class ConstraintValue */

std::ostream& operator<<(std::ostream& o, const ConstraintValue& c);
std::ostream& operator<<(std::ostream& o, const Constraint c);
std::ostream& operator<<(std::ostream& o, const ConstraintType t);
std::ostream& operator<<(std::ostream& o, const ValueCollection& c);



class ConstraintDatabase {
private:
  /**
   * The map from ArithVars to their unique databases.
   * When the vector changes size, we cannot allow the maps to move so this
   * is a vector of pointers.
   */
  std::vector<PerVariableDatabase*> d_varDatabases;

  SortedConstraintMap& getVariableSCM(ArithVar v) const{
    Assert(variableDatabaseIsSetup(v));
    return d_varDatabases[v]->d_constraints;
  }

  /** Maps literals to constraints.*/
  NodetoConstraintMap d_nodetoConstraintMap;

  /**
   * A queue of propagated constraints.
   *
   * As Constraint are pointers, the elements of the queue do not require destruction.
   */
  context::CDQueue<Constraint> d_toPropagate;

  /**
   * Proof Lists.
   * Proofs are lists of valid constraints terminated by the first smaller
   * sentinel value in the proof list.
   * The proof at p in d_proofs[p] of length n is
   *  (NullConstraint, d_proofs[p-(n-1)], ... , d_proofs[p-1], d_proofs[p])
   * The proof at p corresponds to the conjunction:
   *  (and x_i)
   *
   * So the proof of a Constraint c corresponds to the horn clause:
   *  (implies (and x_i) c)
   * where (and x_i) is the proof at c.d_proofs.
   *
   * Constraints are pointers so this list is designed not to require any
   * destruction.
   */
  CDConstraintList d_proofs;

  /**
   * This is a special proof for marking that nodes are their own explanation
   * from the perspective of the theory.
   * These must always be asserted to the theory.
   *
   * This proof is always a member of the list.
   */
  ProofId d_selfExplainingProof;

  /**
   * Marks a node as being proved by the equality engine.
   * The equality engine will be asked for the explanation of such nodes.
   *
   * This is a special proof that is always a member of the list.
   */
  ProofId d_equalityEngineProof;

  /**
   * Marks a node as being true always.
   * This is only okay for purely internal things.
   *
   * This is a special proof that is always a member of the list.
   */
  //ProofId d_pseudoConstraintProof;

  typedef context::CDList<Constraint, ConstraintValue::ProofCleanup> ProofCleanupList;
  typedef context::CDList<Constraint, ConstraintValue::CanBePropagatedCleanup> CBPList;
  typedef context::CDList<Constraint, ConstraintValue::AssertionOrderCleanup> AOList;
  typedef context::CDList<Constraint, ConstraintValue::SplitCleanup> SplitList;

  /**
   * The watch lists are collected together as they need to be garbage collected
   * carefully.
   */
  struct Watches{
    /**
     * Contains the exact list of atoms that have a proof.
     */
    ProofCleanupList d_proofWatches;

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

  void pushSplitWatch(Constraint c){
    Assert(!c->d_split);
    c->d_split = true;
    d_watches->d_splitWatches.push_back(c);
  }

  void pushCanBePropagatedWatch(Constraint c){
    Assert(!c->d_canBePropagated);
    c->d_canBePropagated = true;
    d_watches->d_canBePropagatedWatches.push_back(c);
  }

  void pushAssertionOrderWatch(Constraint c, TNode witness){
    Assert(!c->assertedToTheTheory());
    c->_d_assertionOrder = d_watches->d_assertionOrderWatches.size();
    c->d_witness = witness;
    d_watches->d_assertionOrderWatches.push_back(c);
  }

  void pushProofWatch(Constraint c, ProofId pid){
    Assert(c->d_proof == ProofIdSentinel);
    c->d_proof = pid;
    d_watches->d_proofWatches.push_back(c);
  }

  /** Returns true if all of the entries of the vector are empty. */
  static bool emptyDatabase(const std::vector<PerVariableDatabase>& vec);

  /** Map from nodes to arithvars. */
  const ArithVariables& d_avariables;

  const ArithVariables& getArithVariables() const{
    return d_avariables;
  }

  ArithCongruenceManager& d_congruenceManager;

  const context::Context * const d_satContext;
  const int d_satAllocationLevel;

  RaiseConflict d_raiseConflict;

  friend class ConstraintValue;

public:

  ConstraintDatabase( context::Context* satContext,
                      context::Context* userContext,
                      const ArithVariables& variables,
                      ArithCongruenceManager& dm,
                      RaiseConflict conflictCallBack);

  ~ConstraintDatabase();

  /** Adds a literal to the database. */
  Constraint addLiteral(TNode lit);

  /**
   * If hasLiteral() is true, returns the constraint.
   * Otherwise, returns NullConstraint.
   */
  Constraint lookup(TNode literal) const;

  /**
   * Returns true if the literal has been added to the database.
   * This is a hash table lookup.
   * It does not look in the database for an equivalent corresponding constraint.
   */
  bool hasLiteral(TNode literal) const;

  bool hasMorePropagations() const{
    return !d_toPropagate.empty();
  }

  Constraint nextPropagation(){
    Assert(hasMorePropagations());

    Constraint p = d_toPropagate.front();
    d_toPropagate.pop();

    return p;
  }

  void addVariable(ArithVar v);
  bool variableDatabaseIsSetup(ArithVar v) const;
  void removeVariable(ArithVar v);

  Node eeExplain(ConstConstraint c) const;
  void eeExplain(ConstConstraint c, NodeBuilder<>& nb) const;

  /**
   * Returns a constraint with the variable v, the constraint type t, and a value
   * dominated by r (explained below) if such a constraint exists in the database.
   * If no such constraint exists, NullConstraint is returned.
   *
   * t must be either UpperBound or LowerBound.
   * The returned value v is dominated:
   *  If t is UpperBound, r <= v
   *  If t is LowerBound, r >= v
   */
  Constraint getBestImpliedBound(ArithVar v, ConstraintType t, const DeltaRational& r) const;

  /**
   * Returns a constraint with the variable v, the constraint type t and the value r.
   * If there is such a constraint in the database already, it is returned.
   * If there is no such constraint, this constraint is added to the database.
   *
   */
  Constraint getConstraint(ArithVar v, ConstraintType t, const DeltaRational& r);

  /**
   * Returns a constraint of the given type for the value and variable
   * for the given ValueCollection, vc.
   * This is made if there is no such constraint.
   */
  Constraint ensureConstraint(ValueCollection& vc, ConstraintType t){
    if(vc.hasConstraintOfType(t)){
      return vc.getConstraintOfType(t);
    }else{
      return getConstraint(vc.getVariable(), t, vc.getValue());
    }
  }


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


  void unatePropLowerBound(Constraint curr, Constraint prev);
  void unatePropUpperBound(Constraint curr, Constraint prev);
  void unatePropEquality(Constraint curr, Constraint prevLB, Constraint prevUB);

private:
  void raiseUnateConflict(Constraint ant, Constraint cons);

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

#endif /* __CVC4__THEORY__ARITH__CONSTRAINT_H */

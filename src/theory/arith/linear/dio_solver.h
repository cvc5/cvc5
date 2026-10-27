/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A Diophantine equation solver for the theory of arithmetic.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__DIO_SOLVER_H
#define CVC5__THEORY__ARITH__DIO_SOLVER_H

#include <unordered_map>
#include <utility>
#include <vector>

#include "context/cdlist.h"
#include "context/cdmaybe.h"
#include "context/cdo.h"
#include "context/cdqueue.h"
#include "smt/env_obj.h"
#include "theory/arith/linear/normal_form.h"
#include "util/rational.h"
#include "util/statistics_stats.h"

namespace cvc5::context {
class Context;
}
namespace cvc5::internal {
namespace theory {
namespace arith::linear {

class DioSolver : protected EnvObj
{
 private:
  typedef size_t TrailIndex;
  typedef size_t InputConstraintIndex;
  typedef size_t SubIndex;

  /**
   * Equations are linear forms over variable ids. Proofs are linear forms
   * whose ids are input constraint indices: the proof of an equation is the
   * linear combination of input constraints it was derived from.
   */
  using Form = DioLinearForm<Integer>;
  using ProofForm = DioLinearForm<Rational>;
  using Var = Form::Var;

  /**
   * The variables of the solver: varNodes[v] is the VarList node of variable
   * v, and d_varIds is its inverse. Ids are never reused, so this table is
   * not context-dependent.
   */
  std::vector<Node> d_varNodes;
  std::unordered_map<Node, Var> d_varIds;

  /** Returns the id of the VarList node n, assigning a new one if needed. */
  Var varId(TNode n);

  /**
   * The set of input constraints is stored in a CDList.
   * Each constraint point to an element of the trail.
   */
  struct InputConstraint
  {
    Node d_reason;
    TrailIndex d_trailPos;
    InputConstraint(Node reason, TrailIndex pos)
        : d_reason(reason), d_trailPos(pos)
    {
    }
  };
  context::CDList<InputConstraint> d_inputConstraints;

  /**
   * This is the next input constraint to handle.
   */
  context::CDO<size_t> d_nextInputConstraintToEnqueue;

  /**
   * The main work horse of the algorithm, the trail of constraints.
   * d_trail[i].d_eq is a linear form that implicitly represents an equality
   * against 0. Each constraint has a proof in terms of a linear combination of
   * the input constraints, d_trail[i].d_proof.
   *
   * Each Constraint also caches the term of d_eq with the smallest absolute
   * coefficient, d_trail[i].d_minTerm, and that absolute value, d_minAbs.
   * Ties are broken by VarList order, as Polynomial::selectAbsMinimum() does.
   * For a constant d_eq the term is meaningless and d_minAbs is 0.
   *
   * See Alberto's paper for how linear proofs are maintained for the abstract
   * state machine in rules (7), (8) and (9).
   */
  struct Constraint
  {
    Form d_eq;
    ProofForm d_proof;
    Form::Term d_minTerm;
    Integer d_minAbs;
    Constraint(const Form& eq, const ProofForm& p, const Form::Term& minTerm)
        : d_eq(eq),
          d_proof(p),
          d_minTerm(minTerm),
          d_minAbs(minTerm.second.abs())
    {
    }
  };
  context::CDList<Constraint> d_trail;

  /** Appends (eq, proof) to the trail and returns its index. */
  TrailIndex pushToTrail(const Form& eq, const ProofForm& proof);

  /**
   * Returns the term of eq with the smallest absolute coefficient, breaking
   * ties by VarList order. Returns (0, 0) if eq is constant.
   */
  Form::Term minimalTerm(const Form& eq) const;

  /** Compares variables a and b by the VarList order of their nodes. */
  int varListCmp(Var a, Var b) const;

  /**
   * A substitution is stored as a constraint in the trail together with
   * the variable to be eliminated, and a fresh variable if one was introduced.
   * The variable d_subs[i].d_eliminated is substituted using the implicit
   * equality in d_trail[d_subs[i].d_constraint]
   *  - d_subs[i].d_eliminated is normalized to have coefficient -1 in
   *    d_trail[d_subs[i].d_constraint].
   *  - if d_subs[i].d_hasFresh, then d_subs[i].d_fresh is a variable that is
   *    normalized to have coefficient 1 in d_trail[d_subs[i].d_constraint].
   */
  struct Substitution
  {
    bool d_hasFresh;
    Var d_fresh;
    Var d_eliminated;
    TrailIndex d_constraint;
    Substitution(bool hasFresh, Var f, Var e, TrailIndex c)
        : d_hasFresh(hasFresh), d_fresh(f), d_eliminated(e), d_constraint(c)
    {
    }
  };
  context::CDList<Substitution> d_subs;

  /**
   * This is the queue of constraints to be processed in the current context
   * level. This is to be empty upon entering solver and cleared upon leaving
   * the solver.
   *
   * All elements in currentF:
   * - are fully substituted according to d_subs.
   * - !isConstant().
   * - The gcd of the coefficients is 1.
   */
  std::deque<TrailIndex> d_currentF;
  context::CDList<TrailIndex> d_savedQueue;
  context::CDO<size_t> d_savedQueueIndex;
  context::CDMaybe<TrailIndex> d_conflictIndex;

  /**
   * Drop derived constraints with a coefficient length larger than
   * the maximum input constraints length than 2**MAX_GROWTH_RATE.
   */
  context::CDO<uint32_t> d_maxInputCoefficientLength;
  static constexpr uint32_t MAX_GROWTH_RATE = 3;

  /** Returns true if the element on the trail should be dropped.*/
  bool anyCoefficientExceedsMaximum(TrailIndex j) const;

  /**
   * Is true if decomposeIndex has been used in this context.
   */
  context::CDO<bool> d_usedDecomposeIndex;

  context::CDO<SubIndex> d_lastPureSubstitution;
  context::CDO<SubIndex> d_pureSubstitionIter;

  /**
   * Decomposition lemma queue.
   */
  context::CDQueue<TrailIndex> d_decompositionLemmaQueue;

 public:
  /** Construct a Diophantine equation solver with the given context. */
  DioSolver(Env& env);

  /** Returns true if the substitutions use no new variables. */
  bool hasMorePureSubstitutions() const
  {
    return d_pureSubstitionIter < d_lastPureSubstitution;
  }

  Node nextPureSubstitution();

  /**
   * Adds an equality to the queue of the DioSolver.
   * orig is blamed in a conflict.
   * orig can either be of the form (= p c) or (and ub lb).
   * where ub is either (leq p c) or (not (> p [- c 1])), and
   * where lb is either (geq p c) or (not (< p [+ c 1]))
   *
   * If eq cannot be used, this constraint is dropped.
   */
  void pushInputConstraint(const Comparison& eq, Node reason);

  /**
   * Processes the queue looking for any conflict.
   * If a conflict is found, this returns conflict.
   * Otherwise, it returns null.
   * The conflict is guarenteed to be over literals given in addEquality.
   */
  Node processEquationsForConflict();

  /**
   * Processes the queue looking for an integer unsatisfiable cutting plane.
   * If such a plane is found this returns an entailed plane using no
   * fresh variables.
   */
  SumPair processEquationsForCut();

 private:
  /** Returns true if the TrailIndex refers to a element in the trail. */
  bool inRange(TrailIndex i) const { return i < d_trail.size(); }

  /**
   * Looks for a variable whose coefficients in the queue have gcd 1. Returns
   * true and sets v to the first such variable found, or returns false.
   */
  bool columnGcdIsOne(Var& v) const;

  /**
   * Returns true if the context dependent flag for conflicts
   * has been raised.
   */
  bool inConflict() const { return d_conflictIndex.isSet(); }

  /** Raises a conflict at the index ti. */
  void raiseConflict(TrailIndex ti)
  {
    Assert(!inConflict());
    d_conflictIndex.set(ti);
  }

  /** Returns the conflict index. */
  TrailIndex getConflictIndex() const
  {
    Assert(inConflict());
    return d_conflictIndex.get();
  }

  /** Empties the unprocessed input constraints into the queue. */
  void enqueueInputConstraints();

  /**
   * Returns true if an input equality is in the map.
   * This is expensive and is only for debug assertions.
   */
  bool debugEqualityInInputEquations(Node eq);

  /** Applies the substitution at subIndex to currentF. */
  void subAndReduceCurrentFByIndex(SubIndex d_subIndex);

  /**
   * Takes as input a TrailIndex i and an integer that divides d_trail[i].d_eq,
   * and returns a TrailIndex j s.t. d_trail[j].d_eq = (1/g) d_trail[i].d_eq and
   *   d_trail[j].d_proof = (1/g) d_trail[i].d_proof.
   *
   * g must be non-zero.
   *
   * This corresponds to an application of Alberto's rule (7).
   */
  TrailIndex scaleEqAtIndex(TrailIndex i, const Integer& g);

  /**
   * Takes as input TrailIndex's i and j and Integer's q and r and a TrailIndex
   * k s.t. d_trail[k].d_eq == d_trail[i].d_eq * q + d_trail[j].d_eq * r and
   *   d_trail[k].d_proof == d_trail[i].d_proof * q + d_trail[j].d_proof * r
   *
   * This corresponds to an application of Alberto's rule (8).
   */
  TrailIndex combineEqAtIndexes(TrailIndex i,
                                const Integer& q,
                                TrailIndex j,
                                const Integer& r);

  /**
   * Decomposes the equation at index ti of trail by the variable
   * with the lowest coefficient.
   * This corresponds to an application of Alberto's rule (9).
   *
   * Returns a pair of a SubIndex and a TrailIndex.
   * The SubIndex is the index of a newly introduced substition.
   */
  std::pair<SubIndex, TrailIndex> decomposeIndex(TrailIndex ti);

  /** Solves the index at ti for the variable of its minimal term. */
  std::pair<SubIndex, TrailIndex> solveIndex(TrailIndex ti);

  /**
   * Exhaustively applies all substitutions discovered to an element of the
   * trail. Returns a TrailIndex corresponding to the substitutions being
   * applied.
   */
  TrailIndex applyAllSubstitutionsToIndex(TrailIndex i);

  /**
   * Applies a substitution to an element in the trail.
   */
  TrailIndex applySubstitution(SubIndex s, TrailIndex i);

  /**
   * Reduces the trail node at i by the gcd of the variables.
   * Returns the new trail element.
   *
   * This raises the conflict flag if unsat is detected.
   */
  TrailIndex reduceByGCD(TrailIndex i);

  /**
   * Returns true if i'th element in the trail is trivially true.
   * (0 = 0)
   */
  bool triviallySat(TrailIndex t);

  /**
   * Returns true if i'th element in the trail is trivially unsatisfiable.
   * (1 = 0)
   */
  bool triviallyUnsat(TrailIndex t);

  /** Returns true if the gcd of the i'th element of the trail is 1.*/
  bool gcdIsOne(TrailIndex t);

  bool debugAnySubstitionApplies(TrailIndex t);
  bool debugSubstitutionApplies(SubIndex si, TrailIndex ti);

  /** Returns true if the queue of nodes to process is empty. */
  bool queueEmpty() const;

  bool queueConditions(TrailIndex t);

  void pushToQueueBack(TrailIndex t)
  {
    Assert(queueConditions(t));
    d_currentF.push_back(t);
  }

  void pushToQueueFront(TrailIndex t)
  {
    Assert(queueConditions(t));
    d_currentF.push_front(t);
  }

  /**
   * Moves the minimum Constraint by absolute value of the minimum coefficient
   * to the front of the queue.
   */
  void moveMinimumByAbsToQueueFront();

  void saveQueue();

  TrailIndex impliedGcdOfOne();

  /**
   * Processing the current set of equations.
   *
   * decomposeIndex() rule is only applied if allowDecomposition is true.
   */
  bool processEquations(bool allowDecomposition);

  /**
   * Constructs a proof from any d_trail[i] in terms of input literals.
   */
  Node proveIndex(TrailIndex i);

  /**
   * Returns the SumPair in d_trail[i].d_eq with all of the fresh variables
   * purified out.
   */
  SumPair purifyIndex(TrailIndex i);

 public:
  bool hasMoreDecompositionLemmas() const
  {
    return !d_decompositionLemmaQueue.empty();
  }
  Node nextDecompositionLemma()
  {
    Assert(hasMoreDecompositionLemmas());
    TrailIndex front = d_decompositionLemmaQueue.front();
    d_decompositionLemmaQueue.pop();
    return trailIndexToEquality(front);
  }

 private:
  Node trailIndexToEquality(TrailIndex i) const;
  void addTrailElementAsLemma(TrailIndex i);

 public:
  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics
  {
   public:
    IntStat d_conflictCalls;
    IntStat d_cutCalls;

    IntStat d_cuts;
    IntStat d_conflicts;

    TimerStat d_conflictTimer;
    TimerStat d_cutTimer;

    Statistics(StatisticsRegistry& sr);
  };

  Statistics d_statistics;
}; /* class DioSolver */

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__DIO_SOLVER_H */

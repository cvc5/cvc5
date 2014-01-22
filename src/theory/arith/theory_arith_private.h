/*********************                                                        */
/*! \file theory_arith_private.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Andrew Reynolds, Tianyi Liang, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#pragma once

#include "theory/arith/theory_arith_private_forward.h"

#include "expr/node.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node_builder.h"

#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/cdqueue.h"

#include "theory/valuation.h"
#include "theory/rewriter.h"

#include "util/rational.h"
#include "util/integer.h"
#include "util/boolean_simplification.h"
#include "util/dense_map.h"
#include "util/statistics_registry.h"
#include "util/result.h"

#include "smt/logic_exception.h"



#include "theory/arith/arithvar.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/matrix.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/linear_equality.h"
#include "theory/arith/arith_static_learner.h"
#include "theory/arith/dio_solver.h"
#include "theory/arith/congruence_manager.h"

#include "theory/arith/simplex.h"
#include "theory/arith/dual_simplex.h"
#include "theory/arith/fc_simplex.h"
#include "theory/arith/soi_simplex.h"
#include "theory/arith/attempt_solution_simplex.h"

#include "theory/arith/constraint.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/matrix.h"

#include "theory/arith/arith_rewriter.h"
#include "theory/arith/constraint.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/normal_form.h"
#include "theory/theory_model.h"

#include "theory/arith/options.h"

#include <stdint.h>

#include <vector>
#include <map>
#include <queue>

namespace CVC4 {
namespace theory {
namespace quantifiers {
  class InstStrategySimplex;
}
namespace arith {

/**
 * Implementation of QF_LRA.
 * Based upon:
 * http://research.microsoft.com/en-us/um/people/leonardo/cav06.pdf
 */
class TheoryArithPrivate {
private:
  friend class quantifiers::InstStrategySimplex;

  static const uint32_t RESET_START = 2;

  TheoryArith& d_containing;

  bool d_nlIncomplete;
  // TODO A better would be:
  //context::CDO<bool> d_nlIncomplete;

  BoundInfoMap d_rowTracking;

  /**
   * The constraint database associated with the theory.
   * This must be declared before ArithPartialModel.
   */
  ConstraintDatabase d_constraintDatabase;

  enum Result::Sat d_qflraStatus;
  // check()
  //   !done() -> d_qflraStatus = Unknown
  //   fullEffort(e) -> simplex returns either sat or unsat
  //   !fullEffort(e) -> simplex returns either sat, unsat or unknown
  //                     if unknown, save the assignment
  //                     if unknown, the simplex priority queue cannot be emptied
  int d_unknownsInARow;


  /**
   * This counter is false if nothing has been done since the last cut.
   * This is used to break an infinite loop.
   */
  bool d_hasDoneWorkSinceCut;

  /** Static learner. */
  ArithStaticLearner d_learner;

  /** quantifiers engine */
  QuantifiersEngine * d_quantEngine;
  //std::vector<ArithVar> d_pool;
public:
  void releaseArithVar(ArithVar v);
  void signal(ArithVar v){ d_errorSet.signalVariable(v); }

private:
  /**
   * The map between arith variables to nodes.
   */
  //ArithVarNodeMap d_arithvarNodeMap;

  typedef ArithVariables::var_iterator var_iterator;
  var_iterator var_begin() const { return d_partialModel.var_begin(); }
  var_iterator var_end() const { return d_partialModel.var_end(); }

  NodeSet d_setupNodes;
public:
  bool isSetup(Node n) const {
    return d_setupNodes.find(n) != d_setupNodes.end();
  }
  void markSetup(Node n){
    Assert(!isSetup(n));
    d_setupNodes.insert(n);
  }
private:

  void setupDivLike(const Variable& x);

  void setupVariable(const Variable& x);
  void setupVariableList(const VarList& vl);
  void setupPolynomial(const Polynomial& poly);
public:
  void setupAtom(TNode atom);
private:
  void cautiousSetupPolynomial(const Polynomial& p);

  /**
   * A superset of all of the assertions that currently are not the literal for
   * their constraint do not match constraint literals. Not just the witnesses.
   */
  context::CDInsertHashMap<Node, Constraint, NodeHashFunction> d_assertionsThatDoNotMatchTheirLiterals;


  /** Returns true if x is of type Integer. */
  inline bool isInteger(ArithVar x) const {
    return d_partialModel.isInteger(x);
    //return d_variableTypes[x] >= ATInteger;
  }

  /** This is the set of variables initially introduced as slack variables. */
  //std::vector<bool> d_slackVars;

  /** Returns true if the variable was initially introduced as a slack variable. */
  inline bool isSlackVariable(ArithVar x) const{
    return d_partialModel.isSlack(x);
    //return d_slackVars[x];
  }

  /**
   * On full effort checks (after determining LA(Q) satisfiability), we
   * consider integer vars, but we make sure to do so fairly to avoid
   * nontermination (although this isn't a guarantee).  To do it fairly,
   * we consider variables in round-robin fashion.  This is the
   * round-robin index.
   */
  ArithVar d_nextIntegerCheckVar;

  /**
   * Queue of Integer variables that are known to be equal to a constant.
   */
  context::CDQueue<ArithVar> d_constantIntegerVariables;

  Node callDioSolver();
  Node dioCutting();

  Comparison mkIntegerEqualityFromAssignment(ArithVar v);

  /**
   * List of all of the disequalities asserted in the current context that are not known
   * to be satisfied.
   */
  context::CDQueue<Constraint> d_diseqQueue;

  /**
   * Constraints that have yet to be processed by proagation work list.
   * All of the elements have type of LowerBound, UpperBound, or
   * Equality.
   *
   * This is empty at the beginning of every check call.
   *
   * If head()->getType() == LowerBound or UpperBound,
   * then d_cPL[1] is the previous constraint in d_partialModel for the
   * corresponding bound.
   * If head()->getType() == Equality,
   * then d_cPL[1] is the previous lowerBound in d_partialModel,
   * and d_cPL[2] is the previous upperBound in d_partialModel.
   */
  std::deque<Constraint> d_currentPropagationList;

  context::CDQueue<Constraint> d_learnedBounds;


  /**
   * Manages information about the assignment and upper and lower bounds on
   * variables.
   */
  ArithVariables d_partialModel;

  /** The set of variables in error in the partial model. */
  ErrorSet d_errorSet;

  /**
   * The tableau for all of the constraints seen thus far in the system.
   */
  Tableau d_tableau;

  /**
   * Maintains the relationship between the PartialModel and the Tableau.
   */
  LinearEqualityModule d_linEq;

  /**
   * A Diophantine equation solver.  Accesses the tableau and partial
   * model (each in a read-only fashion).
   */
  DioSolver d_diosolver;

  /** Counts the number of notifyRestart() calls to the theory. */
  uint32_t d_restartsCounter;

  /**
   * Every number of restarts equal to s_TABLEAU_RESET_PERIOD,
   * the density of the tableau, d, is computed.
   * If d >= s_TABLEAU_RESET_DENSITY * d_initialDensity, the tableau
   * is set to d_initialTableau.
   */
  bool d_tableauSizeHasBeenModified;
  double d_tableauResetDensity;
  uint32_t d_tableauResetPeriod;
  static const uint32_t s_TABLEAU_RESET_INCREMENT = 5;


  /** This is only used by simplex at the moment. */
  context::CDList<Node> d_conflicts;
public:
  inline void raiseConflict(Node n){  d_conflicts.push_back(n); }

private:

  /** Returns true iff a conflict has been raised. */
  inline bool inConflict() const {
    return !d_conflicts.empty();
  }

  /**
   * Outputs the contents of d_conflicts onto d_out.
   * Must be inConflict().
   */
  void outputConflicts();

  /**
   * A copy of the tableau.
   * This is equivalent  to the original tableau if d_tableauSizeHasBeenModified
   * is false.
   * The set of basic and non-basic variables may differ from d_tableau.
   */
  Tableau d_smallTableauCopy;

  /**
   * Returns true if all of the basic variables in the simplex queue of
   * basic variables that violate their bounds in the current tableau
   * are basic in d_smallTableauCopy.
   *
   * d_tableauSizeHasBeenModified must be false when calling this.
   * Simplex's priority queue must be in collection mode.
   */
  bool safeToReset() const;

  /** This keeps track of difference equalities. Mostly for sharing. */
  ArithCongruenceManager d_congruenceManager;

  /** This implements the Simplex decision procedure. */
  DualSimplexDecisionProcedure d_dualSimplex;
  FCSimplexDecisionProcedure d_fcSimplex;
  SumOfInfeasibilitiesSPD d_soiSimplex;
  AttemptSolutionSDP d_attemptSolSimplex;

  bool solveRealRelaxation(Theory::Effort effortLevel);

  class ModelException : public Exception {
  public:
    ModelException(TNode n, const char* msg) throw ();
    virtual ~ModelException() throw ();
  };

  /** Internal model value for the node */
  DeltaRational getDeltaValue(TNode n) const throw (DeltaRationalException, ModelException);

  /** Uninterpretted function symbol for use when interpreting
   * division by zero.
   */
  Node d_realDivideBy0Func;
  Node d_intDivideBy0Func;
  Node d_intModulusBy0Func;
  Node getRealDivideBy0Func();
  Node getIntDivideBy0Func();
  Node getIntModulusBy0Func();

  Node definingIteForDivLike(Node divLike);
  Node axiomIteForTotalDivision(Node div_tot);
  Node axiomIteForTotalIntDivision(Node int_div_like);

  // handle linear /, div, mod, and also is_int, to_int
  Node ppRewriteTerms(TNode atom);

public:
  TheoryArithPrivate(TheoryArith& containing, context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo);
  ~TheoryArithPrivate();

  /**
   * Does non-context dependent setup for a node connected to a theory.
   */
  void preRegisterTerm(TNode n);

  void setMasterEqualityEngine(eq::EqualityEngine* eq);
  void setQuantifiersEngine(QuantifiersEngine* qe);

  void check(Theory::Effort e);
  void propagate(Theory::Effort e);
  Node explain(TNode n);


  Rational deltaValueForTotalOrder() const;

  void collectModelInfo( TheoryModel* m, bool fullModel );

  void shutdown(){ }

  void presolve();
  void notifyRestart();
  Theory::PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);
  Node ppRewrite(TNode atom);
  void ppStaticLearn(TNode in, NodeBuilder<>& learned);

  std::string identify() const { return std::string("TheoryArith"); }

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  void addSharedTerm(TNode n);

  Node getModelValue(TNode var);

private:

  /** The constant zero. */
  DeltaRational d_DELTA_ZERO;

  /** propagates an arithvar */
  void propagateArithVar(bool upperbound, ArithVar var );

  /**
   * Using the simpleKind return the ArithVar associated with the assertion.
   */
  ArithVar determineArithVar(const Polynomial& p) const;
  ArithVar determineArithVar(TNode assertion) const;

  /**
   * Splits the disequalities in d_diseq that are violated using lemmas on demand.
   * returns true if any lemmas were issued.
   * returns false if all disequalities are satisfied in the current model.
   */
  bool splitDisequalities();

  /** A Difference variable is known to be 0.*/
  void zeroDifferenceDetected(ArithVar x);


  /**
   * Looks for the next integer variable without an integer assignment in a round robin fashion.
   * Changes the value of d_nextIntegerCheckVar.
   *
   * If this returns false, d_nextIntegerCheckVar does not have an integer assignment.
   * If this returns true, all integer variables have an integer assignment.
   */
  bool hasIntegerModel();

  /**
   * Issues branches for non-slack integer variables with non-integer assignments.
   * Returns a cut for a lemma.
   * If there is an integer model, this returns Node::null().
   */
  Node roundRobinBranch();

public:
  /**
   * This requests a new unique ArithVar value for x.
   * This also does initial (not context dependent) set up for a variable,
   * except for setting up the initial.
   */
  ArithVar requestArithVar(TNode x, bool slack);

public:
  const BoundsInfo& boundsInfo(ArithVar basic) const;


private:
  /** Initial (not context dependent) sets up for a variable.*/
  void setupBasicValue(ArithVar x);

  /** Initial (not context dependent) sets up for a new slack variable.*/
  void setupSlack(TNode left);


  /**
   * Assert*(n, orig) takes an bound n that is implied by orig.
   * and asserts that as a new bound if it is tighter than the current bound
   * and updates the value of a basic variable if needed.
   *
   * orig must be a literal in the SAT solver so that it can be used for
   * conflict analysis.
   *
   * x is the variable getting the new bound,
   * c is the value of the new bound.
   *
   * If this new bound is in conflict with the other bound,
   * a node describing this conflict is returned.
   * If this new bound is not in conflict, Node::null() is returned.
   */
  bool AssertLower(Constraint constraint);
  bool AssertUpper(Constraint constraint);
  bool AssertEquality(Constraint constraint);
  bool AssertDisequality(Constraint constraint);

  /** Tracks the bounds that were updated in the current round. */
  DenseSet d_updatedBounds;

  /** Tracks the basic variables where propagation might be possible. */
  DenseSet d_candidateBasics;
  DenseSet d_candidateRows;

  bool hasAnyUpdates() { return !d_updatedBounds.empty(); }
  void clearUpdates();

  void revertOutOfConflict();

  void propagateCandidatesNew();
  void dumpUpdatedBoundsToRows();
  bool propagateCandidateRow(RowIndex rid);
  bool propagateMightSucceed(ArithVar v, bool ub) const;
  /** Attempt to perform a row propagation where there is at most 1 possible variable.*/
  bool attemptSingleton(RowIndex ridx, bool rowUp);
  /** Attempt to perform a row propagation where every variable is a potential candidate.*/
  bool attemptFull(RowIndex ridx, bool rowUp);
  bool tryToPropagate(RowIndex ridx, bool rowUp, ArithVar v, bool vUp, const DeltaRational& bound);
  bool rowImplicationCanBeApplied(RowIndex ridx, bool rowUp, Constraint bestImplied);


  void propagateCandidates();
  void propagateCandidate(ArithVar basic);
  bool propagateCandidateBound(ArithVar basic, bool upperBound);

  inline bool propagateCandidateLowerBound(ArithVar basic){
    return propagateCandidateBound(basic, false);
  }
  inline bool propagateCandidateUpperBound(ArithVar basic){
    return propagateCandidateBound(basic, true);
  }

  /**
   * Performs a check to see if it is definitely true that setup can be avoided.
   */
  bool canSafelyAvoidEqualitySetup(TNode equality);

  /**
   * Handles the case splitting for check() for a new assertion.
   * Returns a conflict if one was found.
   * Returns Node::null if no conflict was found.
   */
  Constraint constraintFromFactQueue();
  bool assertionCases(Constraint c);

  /**
   * Returns the basic variable with the shorted row containing a non-basic variable.
   * If no such row exists, return ARITHVAR_SENTINEL.
   */
  ArithVar findShortestBasicRow(ArithVar variable);

  /**
   * Debugging only routine!
   * Returns true iff every variable is consistent in the partial model.
   */
  bool entireStateIsConsistent(const std::string& locationHint);
  bool unenqueuedVariablesAreConsistent();

  bool isImpliedUpperBound(ArithVar var, Node exp);
  bool isImpliedLowerBound(ArithVar var, Node exp);

  void internalExplain(TNode n, NodeBuilder<>& explainBuilder);


  void asVectors(const Polynomial& p,
                 std::vector<Rational>& coeffs,
                 std::vector<ArithVar>& variables);

  /** Routine for debugging. Print the assertions the theory is aware of. */
  void debugPrintAssertions(std::ostream& out) const;
  /** Debugging only routine. Prints the model. */
  void debugPrintModel(std::ostream& out) const;

  inline LogicInfo getLogicInfo() const { return d_containing.getLogicInfo(); }
  inline bool done() const { return d_containing.done(); }
  inline TNode get() { return d_containing.get(); }
  inline bool isLeaf(TNode x) const { return d_containing.isLeaf(x); }
  inline TheoryId theoryOf(TNode x) const { return d_containing.theoryOf(x); }
  inline void debugPrintFacts() const { d_containing.debugPrintFacts(); }
  inline context::Context* getSatContext() const { return d_containing.getSatContext(); }
  inline void setIncomplete() {
    (d_containing.d_out)->setIncomplete();
    d_nlIncomplete = true;
  }
  inline void outputLemma(TNode lem) { (d_containing.d_out)->lemma(lem); }
  inline void outputPropagate(TNode lit) { (d_containing.d_out)->propagate(lit); }
  inline void outputRestart() { (d_containing.d_out)->demandRestart(); }

  inline bool isSatLiteral(TNode l) const {
    return (d_containing.d_valuation).isSatLiteral(l);
  }
  inline Node getSatValue(TNode n) const {
    return (d_containing.d_valuation).getSatValue(n);
  }


  /** Counts the number of fullCheck calls to arithmetic. */
  uint32_t d_fullCheckCounter;
  std::vector<ArithVar> cutAllBounded() const;
  Node branchIntegerVariable(ArithVar x) const;
  void branchVector(const std::vector<ArithVar>& lemmas);

  context::CDO<unsigned> d_cutCount;
  context::CDHashSet<ArithVar, std::hash<ArithVar> > d_cutInContext;

  context::CDO<bool> d_likelyIntegerInfeasible;


  context::CDO<bool> d_guessedCoeffSet;
  ArithRatPairVec d_guessedCoeffs;

  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statAssertUpperConflicts, d_statAssertLowerConflicts;

    IntStat d_statUserVariables, d_statSlackVariables;
    IntStat d_statDisequalitySplits;
    IntStat d_statDisequalityConflicts;
    TimerStat d_simplifyTimer;
    TimerStat d_staticLearningTimer;

    TimerStat d_presolveTime;

    TimerStat d_newPropTime;

    IntStat d_externalBranchAndBounds;

    IntStat d_initialTableauSize;
    IntStat d_currSetToSmaller;
    IntStat d_smallerSetToCurr;
    TimerStat d_restartTimer;

    TimerStat d_boundComputationTime;
    IntStat d_boundComputations, d_boundPropagations;

    IntStat d_unknownChecks;
    IntStat d_maxUnknownsInARow;
    AverageStat d_avgUnknownsInARow;

    IntStat d_revertsOnConflicts;
    IntStat d_commitsOnConflicts;
    IntStat d_nontrivialSatChecks;


    HistogramStat<uint32_t> d_satPivots;
    HistogramStat<uint32_t> d_unsatPivots;
    HistogramStat<uint32_t> d_unknownPivots;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;


};/* class TheoryArithPrivate */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

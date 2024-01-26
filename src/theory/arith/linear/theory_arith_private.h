/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#pragma once

#include <map>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "proof/trust_node.h"
#include "theory/arith/linear/arith_static_learner.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/linear/arithvar.h"
#include "theory/arith/linear/attempt_solution_simplex.h"
#include "theory/arith/branch_and_bound.h"
#include "theory/arith/linear/congruence_manager.h"
#include "theory/arith/linear/constraint.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/linear/dio_solver.h"
#include "theory/arith/linear/dual_simplex.h"
#include "theory/arith/linear/error_set.h"
#include "theory/arith/linear/fc_simplex.h"
#include "theory/arith/linear/infer_bounds.h"
#include "theory/arith/linear/linear_equality.h"
#include "theory/arith/linear/matrix.h"
#include "theory/arith/linear/normal_form.h"
#include "theory/arith/linear/partial_model.h"
#include "theory/arith/linear/soi_simplex.h"
#include "theory/arith/theory_arith.h"
#include "theory/valuation.h"
#include "util/dense_map.h"
#include "util/integer.h"
#include "util/rational.h"
#include "util/result.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

class EagerProofGenerator;

namespace theory {

class TheoryModel;

namespace arith::linear {

class BranchCutInfo;
class TreeLog;
class ApproximateStatistics;

class ArithEntailmentCheckParameters;
class ArithEntailmentCheckSideEffects;
namespace inferbounds {
  class InferBoundAlgorithm;
}
class InferBoundsResult;
  
/**
 * Implementation of QF_LRA.
 * Based upon:
 * http://research.microsoft.com/en-us/um/people/leonardo/cav06.pdf
 */
class TheoryArithPrivate : protected EnvObj
{
 private:
  static constexpr uint32_t RESET_START = 2;

  TheoryArith& d_containing;

  /**
   * Whether we encountered non-linear arithmetic at any time during solving.
   */
  bool d_foundNl;

  BoundInfoMap d_rowTracking;
  /** Branch and bound utility */
  BranchAndBound& d_bab;
  // For proofs
  /** Manages the proof nodes of this theory. */
  ProofNodeManager* d_pnm;
  /** Stores proposition(node)/proof pairs. */
  std::unique_ptr<EagerProofGenerator> d_pfGen;

  /**
   * The constraint database associated with the theory.
   * This must be declared before ArithPartialModel.
   */
  ConstraintDatabase d_constraintDatabase;

  enum Result::Status d_qflraStatus;
  // check()
  //   !done() -> d_qflraStatus = Unknown
  //   fullEffort(e) -> simplex returns either sat or unsat
  //   !fullEffort(e) -> simplex returns either sat, unsat or unknown
  //                     if unknown, save the assignment
  //                     if unknown, the simplex priority queue cannot be emptied
  int d_unknownsInARow;

  bool d_replayedLemmas;

  /**
   * This counter is false if nothing has been done since the last cut.
   * This is used to break an infinite loop.
   */
  bool d_hasDoneWorkSinceCut;

  /** Static learner. */
  ArithStaticLearner d_learner;

  //std::vector<ArithVar> d_pool;
public:
  void releaseArithVar(ArithVar v);
  void signal(ArithVar v){ d_errorSet.signalVariable(v); }


private:
  // t does not contain constants
  void entailmentCheckBoundLookup(std::pair<Node, DeltaRational>& tmp, int sgn, TNode tp) const;
  void entailmentCheckRowSum(std::pair<Node, DeltaRational>& tmp, int sgn, TNode tp) const;

  /**
   * Infers either a new upper/lower bound on term in the real relaxation.
   * Either:
   * - term is malformed (see below)
   * - a maximum/minimum is found with the result being a pair
   * -- <dr, exp> where
   * -- term <?> dr is implies by exp
   * -- <?> is <= if inferring an upper bound, >= otherwise
   * -- exp is in terms of the assertions to the theory.
   * - No upper or lower bound is inferrable in the real relaxation.
   * -- Returns <0, Null()>
   * - the maximum number of rounds was exhausted:
   * -- Returns <v, term> where v is the current feasible value of term
   * - Threshold reached:
   * -- If theshold != NULL, and a feasible value is found to exceed threshold
   * -- Simplex stops and returns <threshold, term>
   */
  //std::pair<DeltaRational, Node> inferBound(TNode term, bool lb, int maxRounds = -1, const DeltaRational* threshold = NULL);

private:
 static bool decomposeTerm(Node t, Rational& m, Node& p, Rational& c);
 bool decomposeLiteral(Node lit,
                       Kind& k,
                       int& dir,
                       Rational& lm,
                       Node& lp,
                       Rational& rm,
                       Node& rp,
                       Rational& dm,
                       Node& dp,
                       DeltaRational& sep);
 static void setToMin(int sgn,
                      std::pair<Node, DeltaRational>& min,
                      const std::pair<Node, DeltaRational>& e);

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
  context::CDInsertHashMap<Node, ConstraintP>
      d_assertionsThatDoNotMatchTheirLiterals;

  /** Returns true if x is of type Integer. */
  inline bool isInteger(ArithVar x) const {
    return d_partialModel.isInteger(x);
  }


  /** Returns true if the variable was initially introduced as an auxiliary variable. */
  inline bool isAuxiliaryVariable(ArithVar x) const{
    return d_partialModel.isAuxiliary(x);
  }

  inline bool isIntegerInput(ArithVar x) const
  {
    return d_partialModel.isIntegerInput(x)
           && d_preregisteredNodes.contains(d_partialModel.asNode(x));
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
  /**
   * Produces lemmas of the form (or (>= f 0) (<= f 0)),
   * where f is a plane that the diophantine solver is interested in.
   *
   * More precisely, produces lemmas of the form (or (>= lc -c) (<= lc -c))
   * where lc is a linear combination of variables, c is a constant, and lc + c
   * is the plane.
   */
  TrustNode dioCutting();

  Comparison mkIntegerEqualityFromAssignment(ArithVar v);

  /**
   * List of all of the disequalities asserted in the current context that are not known
   * to be satisfied.
   */
  context::CDQueue<ConstraintP> d_diseqQueue;

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
  std::deque<ConstraintP> d_currentPropagationList;

  context::CDQueue<ConstraintP> d_learnedBounds;

  /**
   * Contains all nodes that have been preregistered
   */
  context::CDHashSet<Node> d_preregisteredNodes;

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
  static constexpr uint32_t s_TABLEAU_RESET_INCREMENT = 5;

  /** This is only used by simplex at the moment. */
  context::CDList<std::pair<ConstraintCP, InferenceId>> d_conflicts;

  /** This is only used by simplex at the moment. */
  context::CDO<Node> d_blackBoxConflict;
  /** For holding the proof of the above conflict node. */
  context::CDO<std::shared_ptr<ProofNode>> d_blackBoxConflictPf;

  bool isProofEnabled() const;

 public:
  /**
   * This adds the constraint a to the queue of conflicts in d_conflicts.
   * Both a and ~a must have a proof.
   */
  void raiseConflict(ConstraintCP a, InferenceId id);

  // inline void raiseConflict(const ConstraintCPVec& cv){
  //   d_conflicts.push_back(cv);
  // }

  // void raiseConflict(ConstraintCP a, ConstraintCP b);
  // void raiseConflict(ConstraintCP a, ConstraintCP b, ConstraintCP c);

  /** This is a conflict that is magically known to hold. */
  void raiseBlackBoxConflict(Node bb, std::shared_ptr<ProofNode> pf = nullptr);
  /**
   * Returns true iff a conflict has been raised. This method is public since
   * it is needed by the ArithState class to know whether we are in conflict.
   */
  bool anyConflict() const;

 private:
  inline bool conflictQueueEmpty() const {
    return d_conflicts.empty();
  }

  /**
   * Outputs the contents of d_conflicts onto d_out.
   * The conditions of anyConflict() must hold.
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
  context::CDO<bool> d_cmEnabled;

  /** This implements the Simplex decision procedure. */
  DualSimplexDecisionProcedure d_dualSimplex;
  FCSimplexDecisionProcedure d_fcSimplex;
  SumOfInfeasibilitiesSPD d_soiSimplex;
  AttemptSolutionSDP d_attemptSolSimplex;

  bool solveRealRelaxation(Theory::Effort effortLevel);

  /* Returns true if this is heuristically a good time to try
   * to solve the integers.
   */
  bool attemptSolveInteger(Theory::Effort effortLevel, bool emmmittedLemmaOrSplit);
  bool replayLemmas(ApproximateSimplex* approx);
  void solveInteger(Theory::Effort effortLevel);
  bool safeToCallApprox() const;
  SimplexDecisionProcedure& selectSimplex(bool pass1);
  SimplexDecisionProcedure* d_pass1SDP;
  SimplexDecisionProcedure* d_otherSDP;
  /* Sets d_qflraStatus */
  void importSolution(const ApproximateSimplex::Solution& solution);
  bool solveRelaxationOrPanic(Theory::Effort effortLevel);
  context::CDO<int> d_lastContextIntegerAttempted;
  bool replayLog(ApproximateSimplex* approx);

  class ModelException : public Exception {
   public:
    ModelException(TNode n, const char* msg);
    ~ModelException() override;
  };

  /**
   * Computes the delta rational value of a term from the current partial
   * model. This returns the delta value assignment to the term if it is in the
   * partial model. Otherwise, this is computed recursively for arithmetic terms
   * from each subterm.
   *
   * This throws a DeltaRationalException if the value cannot be represented as
   * a DeltaRational. This throws a ModelException if there is a term is not in
   * the partial model and is not a theory of arithmetic term.
   *
   * precondition: The linear abstraction of the nodes must be satisfiable.
   */
  DeltaRational getDeltaValue(TNode term) const
      /* throw(DeltaRationalException, ModelException) */;
 public:
  TheoryArithPrivate(TheoryArith& containing, Env& env, BranchAndBound& bab);
  ~TheoryArithPrivate();

  //--------------------------------- initialization
  /** finish initialize */
  void finishInit();
  //--------------------------------- end initialization

  /**
   * Does non-context dependent setup for a node connected to a theory.
   */
  void preRegisterTerm(TNode n);

  void propagate(Theory::Effort e);
  TrustNode explain(TNode n);

  Rational deltaValueForTotalOrder() const;

  bool collectModelInfo(TheoryModel* m);
  /**
   * Collect model values. This is the main method for extracting information
   * about how to construct the model. This method relies on the caller for
   * processing the map, which is done so that other modules (e.g. the
   * non-linear extension) can modify arithModel before it is sent to the model.
   *
   * @param termSet The set of relevant terms
   * @param arithModel Mapping from terms (of int/real type) to their values.
   * The caller should assert equalities to the model for each entry in this
   * map.
   * @param arithModelIllTyped Mapping from terms (of int type) to real values.
   * This is used for catching cases where this solver mistakenly set an
   * integer variable to a real.
   */
  void collectModelValues(const std::set<Node>& termSet,
                          std::map<Node, Node>& arithModel,
                          std::map<Node, Node>& arithModelIllTyped);

  void shutdown(){ }

  void presolve();
  void notifyRestart();
  Theory::PPAssertStatus ppAssert(TrustNode tin,
                                  TrustSubstitutionMap& outSubstitutions);
  void ppStaticLearn(TNode in, NodeBuilder& learned);

  std::string identify() const { return std::string("TheoryArith"); }

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  /** Called when n is notified as being a shared term with TheoryArith. */
  void notifySharedTerm(TNode n);

  Node getCandidateModelValue(TNode var);

  std::pair<bool, Node> entailmentCheck(TNode lit);

  //--------------------------------- standard check
  /** Pre-check, called before the fact queue of the theory is processed. */
  bool preCheck(Theory::Effort level);
  /** Pre-notify fact. */
  void preNotifyFact(TNode atom, bool pol, TNode fact);
  /**
   * Post-check, called after the fact queue of the theory is processed. Returns
   * true if a conflict or lemma was emitted.
   */
  bool postCheck(Theory::Effort level);
  //--------------------------------- end standard check
  /**
   * Found non-linear? This returns true if this solver ever encountered
   * any non-linear terms that were unhandled. Note that this class is not
   * responsible for handling non-linear arithmetic. If the owner of this
   * class does not handle non-linear arithmetic in another way, then
   * setModelUnsound should be called on the output channel of TheoryArith.
   */
  bool foundNonlinear() const;

  /** get the congruence manager, if we are using one */
  ArithCongruenceManager* getCongruenceManager();

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
   * Looks for the next integer variable without an integer assignment in a
   * round-robin fashion. Changes the value of d_nextIntegerCheckVar.
   *
   * This returns true if all integer variables have integer assignments.
   * If this returns false, d_nextIntegerCheckVar does not have an integer
   * assignment.
   */
  bool hasIntegerModel();

  /**
   * Looks for through the variables starting at d_nextIntegerCheckVar
   * for the first integer variable that is between its upper and lower bounds
   * that has a non-integer assignment.
   *
   * If assumeBounds is true, skip the check that the variable is in bounds.
   *
   * If there is no such variable, returns ARITHVAR_SENTINEL;
   */
  ArithVar nextIntegerViolation(bool assumeBounds) const;

  /**
   * Issues branches for non-auxiliary integer variables with non-integer assignments.
   * Returns a cut for a lemma.
   * If there is an integer model, this returns the empty vector.
   */
  std::vector<TrustNode> roundRobinBranch();

  bool proofsEnabled() const { return d_pnm; }

 public:
  /**
   * This requests a new unique ArithVar value for x.
   * This also does initial (not context dependent) set up for a variable,
   * except for setting up the initial.
   *
   * If aux is true, this is an auxiliary variable.
   * If internal is true, x might not be unique up to a constant multiple.
   */
  ArithVar requestArithVar(TNode x, bool aux, bool internal);

public:
  const BoundsInfo& boundsInfo(ArithVar basic) const;


private:
  /** Initial (not context dependent) sets up for a variable.*/
  void setupBasicValue(ArithVar x);

  /** Initial (not context dependent) sets up for a new auxiliary variable.*/
  void setupAuxiliary(TNode left);


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
  bool AssertLower(ConstraintP constraint);
  bool AssertUpper(ConstraintP constraint);
  bool AssertEquality(ConstraintP constraint);
  bool AssertDisequality(ConstraintP constraint);

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
  bool rowImplicationCanBeApplied(RowIndex ridx, bool rowUp, ConstraintP bestImplied);
  //void enqueueConstraints(std::vector<ConstraintCP>& out, Node n) const;
  //ConstraintCPVec resolveOutPropagated(const ConstraintCPVec& v, const std::set<ConstraintCP>& propagated) const;
  void resolveOutPropagated(std::vector<ConstraintCPVec>& confs, const std::set<ConstraintCP>& propagated) const;
  void subsumption(std::vector<ConstraintCPVec>& confs) const;

  Node cutToLiteral(ApproximateSimplex*  approx, const CutInfo& cut) const;
  Node branchToNode(ApproximateSimplex* approx, const NodeLog& cut) const;

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
   *
   * @param assertion The assertion that was just popped from the fact queue
   * of TheoryArith and given to this class via preNotifyFact.
   */
  ConstraintP constraintFromFactQueue(TNode assertion);
  bool assertionCases(ConstraintP c);

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

  void internalExplain(TNode n, NodeBuilder& explainBuilder);

  void asVectors(const Polynomial& p,
                 std::vector<Rational>& coeffs,
                 std::vector<ArithVar>& variables);

  /** Routine for debugging. Print the assertions the theory is aware of. */
  void debugPrintAssertions(std::ostream& out) const;
  /** Debugging only routine. Prints the model. */
  void debugPrintModel(std::ostream& out) const;

  bool done() const { return d_containing.done(); }
  bool isLeaf(TNode x) const { return d_containing.isLeaf(x); }
  TheoryId theoryOf(TNode x) const { return d_containing.theoryOf(x); }
  void debugPrintFacts() const { d_containing.debugPrintFacts(); }
  bool outputTrustedLemma(TrustNode lem, InferenceId id);
  bool outputLemma(TNode lem, InferenceId id);
  void outputTrustedConflict(TrustNode conf, InferenceId id);
  void outputConflict(TNode lit, InferenceId id);
  void outputPropagate(TNode lit);
  void outputRestart();

  inline bool isSatLiteral(TNode l) const {
    return (d_containing.d_valuation).isSatLiteral(l);
  }
  inline Node getSatValue(TNode n) const {
    return (d_containing.d_valuation).getSatValue(n);
  }

  /** Used for replaying approximate simplex */
  context::CDQueue<TrustNode> d_approxCuts;
  /** Also used for replaying approximate simplex. "approximate cuts temporary storage" */
  std::vector<TrustNode> d_acTmp;

  /** Counts the number of fullCheck calls to arithmetic. */
  uint32_t d_fullCheckCounter;
  std::vector<ArithVar> cutAllBounded() const;
  std::vector<TrustNode> branchIntegerVariable(ArithVar x) const;
  void branchVector(const std::vector<ArithVar>& lemmas);

  context::CDO<unsigned> d_cutCount;
  context::CDHashSet<ArithVar, std::hash<ArithVar>> d_cutInContext;

  context::CDO<bool> d_likelyIntegerInfeasible;

  context::CDO<bool> d_guessedCoeffSet;
  ArithRatPairVec d_guessedCoeffs;


  TreeLog* d_treeLog;
  TreeLog& getTreeLog();


  ArithVarVec d_replayVariables;
  std::vector<ConstraintP> d_replayConstraints;
  DenseMap<Rational> d_lhsTmp;

  /* Approximate simpplex solvers are given a copy of their stats */
  ApproximateStatistics* d_approxStats;
  ApproximateStatistics& getApproxStats();
  context::CDO<int32_t> d_attemptSolveIntTurnedOff;
  void turnOffApproxFor(int32_t rounds);
  bool getSolveIntegerResource();

  void tryBranchCut(ApproximateSimplex* approx, int nid, BranchCutInfo& bl);
  std::vector<ConstraintCPVec> replayLogRec(ApproximateSimplex* approx, int nid, ConstraintP bc, int depth);

  std::pair<ConstraintP, ArithVar> replayGetConstraint(const CutInfo& info);
  std::pair<ConstraintP, ArithVar> replayGetConstraint(
      ApproximateSimplex* approx, const NodeLog& nl);
  std::pair<ConstraintP, ArithVar> replayGetConstraint(const DenseMap<Rational>& lhs, Kind k, const Rational& rhs, bool branch);

  void replayAssert(ConstraintP c);

  static ConstraintCP vectorToIntHoleConflict(const ConstraintCPVec& conflict);
  static void intHoleConflictToVector(ConstraintCP conflicting, ConstraintCPVec& conflict);

  // Returns true if the node contains a literal
  // that is an arithmetic literal and is not a sat literal
  // No caching is done so this should likely only
  // be called carefully!
  bool hasFreshArithLiteral(Node n) const;

  int32_t d_dioSolveResources;
  bool getDioCuttingResource();

  uint32_t d_solveIntMaybeHelp, d_solveIntAttempts;

  RationalVector d_farkasBuffer;

  //---------------- during check
  /** Whether there were new facts during preCheck */
  bool d_newFacts;
  /** The previous status, computed during preCheck */
  Result::Status d_previousStatus;
  //---------------- end during check

  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statAssertUpperConflicts, d_statAssertLowerConflicts;

    IntStat d_statUserVariables, d_statAuxiliaryVariables;
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

    IntStat d_replayLogRecCount,
      d_replayLogRecConflictEscalation,
      d_replayLogRecEarlyExit,
      d_replayBranchCloseFailures,
      d_replayLeafCloseFailures,
      d_replayBranchSkips,
      d_mirCutsAttempted,
      d_gmiCutsAttempted,
      d_branchCutsAttempted,
      d_cutsReconstructed,
      d_cutsReconstructionFailed,
      d_cutsProven,
      d_cutsProofFailed,
      d_mipReplayLemmaCalls,
      d_mipExternalCuts,
      d_mipExternalBranch;

    IntStat d_inSolveInteger,
      d_branchesExhausted,
      d_execExhausted,
      d_pivotsExhausted,
      d_panicBranches,
      d_relaxCalls,
      d_relaxLinFeas,
      d_relaxLinFeasFailures,
      d_relaxLinInfeas,
      d_relaxLinInfeasFailures,
      d_relaxLinExhausted,
      d_relaxOthers;

    IntStat d_applyRowsDeleted;
    TimerStat d_replaySimplexTimer;

    TimerStat d_replayLogTimer,
      d_solveIntTimer,
      d_solveRealRelaxTimer;

    IntStat d_solveIntCalls,
      d_solveStandardEffort;

    IntStat d_approxDisabled;
    IntStat d_replayAttemptFailed;

    IntStat d_cutsRejectedDuringReplay;
    IntStat d_cutsRejectedDuringLemmas;

    HistogramStat<uint32_t> d_satPivots;
    HistogramStat<uint32_t> d_unsatPivots;
    HistogramStat<uint32_t> d_unknownPivots;

    IntStat d_solveIntModelsAttempts;
    IntStat d_solveIntModelsSuccessful;
    TimerStat d_mipTimer;
    TimerStat d_lpTimer;

    IntStat d_mipProofsAttempted;
    IntStat d_mipProofsSuccessful;

    IntStat d_numBranchesFailed;

    Statistics(StatisticsRegistry& reg, const std::string& name);
  };


  Statistics d_statistics;
}; /* class TheoryArithPrivate */


}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

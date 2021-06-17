/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Alex Ozdemir, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

#include "theory/arith/theory_arith_private.h"

#include <map>
#include <queue>
#include <vector>

#include "base/output.h"
#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "expr/skolem_manager.h"
#include "options/arith_options.h"
#include "options/base_options.h"
#include "preprocessing/util/ite_utilities.h"
#include "proof/proof_generator.h"
#include "proof/proof_node_manager.h"
#include "proof/proof_rule.h"
#include "smt/logic_exception.h"
#include "smt/smt_statistics_registry.h"
#include "smt_util/boolean_simplification.h"
#include "theory/arith/approx_simplex.h"
#include "theory/arith/arith_ite_utils.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/arith_static_learner.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/congruence_manager.h"
#include "theory/arith/constraint.h"
#include "theory/arith/cut_log.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/dio_solver.h"
#include "theory/arith/linear_equality.h"
#include "theory/arith/matrix.h"
#include "theory/arith/nl/nonlinear_extension.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/simplex.h"
#include "theory/arith/theory_arith.h"
#include "theory/ext_theory.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"
#include "theory/valuation.h"
#include "util/dense_map.h"
#include "util/integer.h"
#include "util/random.h"
#include "util/rational.h"
#include "util/result.h"
#include "util/statistics_stats.h"

using namespace std;
using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {

static Node toSumNode(const ArithVariables& vars, const DenseMap<Rational>& sum);
static bool complexityBelow(const DenseMap<Rational>& row, uint32_t cap);

TheoryArithPrivate::TheoryArithPrivate(TheoryArith& containing,
                                       context::Context* c,
                                       context::UserContext* u,
                                       OutputChannel& out,
                                       Valuation valuation,
                                       const LogicInfo& logicInfo,
                                       ProofNodeManager* pnm)
    : d_containing(containing),
      d_foundNl(false),
      d_rowTracking(),
      d_pnm(pnm),
      d_checker(),
      d_pfGen(new EagerProofGenerator(d_pnm, u)),
      d_constraintDatabase(c,
                           u,
                           d_partialModel,
                           d_congruenceManager,
                           RaiseConflict(*this),
                           d_pfGen.get(),
                           d_pnm),
      d_qflraStatus(Result::SAT_UNKNOWN),
      d_unknownsInARow(0),
      d_hasDoneWorkSinceCut(false),
      d_learner(u),
      d_assertionsThatDoNotMatchTheirLiterals(c),
      d_nextIntegerCheckVar(0),
      d_constantIntegerVariables(c),
      d_diseqQueue(c, false),
      d_currentPropagationList(),
      d_learnedBounds(c),
      d_preregisteredNodes(u),
      d_partialModel(c, DeltaComputeCallback(*this)),
      d_errorSet(
          d_partialModel, TableauSizes(&d_tableau), BoundCountingLookup(*this)),
      d_tableau(),
      d_linEq(d_partialModel,
              d_tableau,
              d_rowTracking,
              BasicVarModelUpdateCallBack(*this)),
      d_diosolver(c),
      d_restartsCounter(0),
      d_tableauSizeHasBeenModified(false),
      d_tableauResetDensity(1.6),
      d_tableauResetPeriod(10),
      d_conflicts(c),
      d_blackBoxConflict(c, Node::null()),
      d_blackBoxConflictPf(c, std::shared_ptr<ProofNode>(nullptr)),
      d_congruenceManager(c,
                          u,
                          d_constraintDatabase,
                          SetupLiteralCallBack(*this),
                          d_partialModel,
                          RaiseEqualityEngineConflict(*this),
                          d_pnm),
      d_cmEnabled(c, true),

      d_dualSimplex(
          d_linEq, d_errorSet, RaiseConflict(*this), TempVarMalloc(*this)),
      d_fcSimplex(
          d_linEq, d_errorSet, RaiseConflict(*this), TempVarMalloc(*this)),
      d_soiSimplex(
          d_linEq, d_errorSet, RaiseConflict(*this), TempVarMalloc(*this)),
      d_attemptSolSimplex(
          d_linEq, d_errorSet, RaiseConflict(*this), TempVarMalloc(*this)),
      d_pass1SDP(NULL),
      d_otherSDP(NULL),
      d_lastContextIntegerAttempted(c, -1),

      d_DELTA_ZERO(0),
      d_approxCuts(c),
      d_fullCheckCounter(0),
      d_cutCount(c, 0),
      d_cutInContext(c),
      d_likelyIntegerInfeasible(c, false),
      d_guessedCoeffSet(c, false),
      d_guessedCoeffs(),
      d_treeLog(NULL),
      d_replayVariables(),
      d_replayConstraints(),
      d_lhsTmp(),
      d_approxStats(NULL),
      d_attemptSolveIntTurnedOff(u, 0),
      d_dioSolveResources(0),
      d_solveIntMaybeHelp(0u),
      d_solveIntAttempts(0u),
      d_newFacts(false),
      d_previousStatus(Result::SAT_UNKNOWN),
      d_statistics("theory::arith::")
{
}

TheoryArithPrivate::~TheoryArithPrivate(){
  if(d_treeLog != NULL){ delete d_treeLog; }
  if(d_approxStats != NULL) { delete d_approxStats; }
}

bool TheoryArithPrivate::needsEqualityEngine(EeSetupInfo& esi)
{
  return d_congruenceManager.needsEqualityEngine(esi);
}
void TheoryArithPrivate::finishInit()
{
  eq::EqualityEngine* ee = d_containing.getEqualityEngine();
  eq::ProofEqEngine* pfee = d_containing.getProofEqEngine();
  Assert(ee != nullptr);
  d_congruenceManager.finishInit(ee, pfee);
}

static bool contains(const ConstraintCPVec& v, ConstraintP con){
  for(unsigned i = 0, N = v.size(); i < N; ++i){
    if(v[i] == con){
      return true;
    }
  }
  return false;
}
static void drop( ConstraintCPVec& v, ConstraintP con){
  size_t readPos, writePos, N;
  for(readPos = 0, writePos = 0, N = v.size(); readPos < N; ++readPos){
    ConstraintCP curr = v[readPos];
    if(curr != con){
      v[writePos] = curr;
      writePos++;
    }
  }
  v.resize(writePos);
}


static void resolve(ConstraintCPVec& buf, ConstraintP c, const ConstraintCPVec& pos, const ConstraintCPVec& neg){
  unsigned posPos CVC5_UNUSED = pos.size();
  for(unsigned i = 0, N = pos.size(); i < N; ++i){
    if(pos[i] == c){
      posPos = i;
    }else{
      buf.push_back(pos[i]);
    }
  }
  Assert(posPos < pos.size());
  ConstraintP negc = c->getNegation();
  unsigned negPos CVC5_UNUSED = neg.size();
  for(unsigned i = 0, N = neg.size(); i < N; ++i){
    if(neg[i] == negc){
      negPos = i;
    }else{
      buf.push_back(neg[i]);
    }
  }
  Assert(negPos < neg.size());

  // Assert(dnconf.getKind() == kind::AND);
  // Assert(upconf.getKind() == kind::AND);
  // Assert(dnpos < dnconf.getNumChildren());
  // Assert(uppos < upconf.getNumChildren());
  // Assert(equalUpToNegation(dnconf[dnpos], upconf[uppos]));

  // NodeBuilder nb(kind::AND);
  // dropPosition(nb, dnconf, dnpos);
  // dropPosition(nb, upconf, uppos);
  // return safeConstructNary(nb);
}

TheoryArithPrivate::ModelException::ModelException(TNode n, const char* msg)
{
  stringstream ss;
  ss << "Cannot construct a model for " << n << " as " << endl << msg;
  setMessage(ss.str());
}
TheoryArithPrivate::ModelException::~ModelException() {}

TheoryArithPrivate::Statistics::Statistics(const std::string& name)
    : d_statAssertUpperConflicts(
        smtStatisticsRegistry().registerInt(name + "AssertUpperConflicts")),
      d_statAssertLowerConflicts(
          smtStatisticsRegistry().registerInt(name + "AssertLowerConflicts")),
      d_statUserVariables(
          smtStatisticsRegistry().registerInt(name + "UserVariables")),
      d_statAuxiliaryVariables(
          smtStatisticsRegistry().registerInt(name + "AuxiliaryVariables")),
      d_statDisequalitySplits(
          smtStatisticsRegistry().registerInt(name + "DisequalitySplits")),
      d_statDisequalityConflicts(
          smtStatisticsRegistry().registerInt(name + "DisequalityConflicts")),
      d_simplifyTimer(
          smtStatisticsRegistry().registerTimer(name + "simplifyTimer")),
      d_staticLearningTimer(
          smtStatisticsRegistry().registerTimer(name + "staticLearningTimer")),
      d_presolveTime(
          smtStatisticsRegistry().registerTimer(name + "presolveTime")),
      d_newPropTime(
          smtStatisticsRegistry().registerTimer(name + "newPropTimer")),
      d_externalBranchAndBounds(smtStatisticsRegistry().registerInt(
          name + "externalBranchAndBounds")),
      d_initialTableauSize(
          smtStatisticsRegistry().registerInt(name + "initialTableauSize")),
      d_currSetToSmaller(
          smtStatisticsRegistry().registerInt(name + "currSetToSmaller")),
      d_smallerSetToCurr(
          smtStatisticsRegistry().registerInt(name + "smallerSetToCurr")),
      d_restartTimer(
          smtStatisticsRegistry().registerTimer(name + "restartTimer")),
      d_boundComputationTime(
          smtStatisticsRegistry().registerTimer(name + "bound::time")),
      d_boundComputations(smtStatisticsRegistry().registerInt(
          name + "bound::boundComputations")),
      d_boundPropagations(smtStatisticsRegistry().registerInt(
          name + "bound::boundPropagations")),
      d_unknownChecks(
          smtStatisticsRegistry().registerInt(name + "status::unknowns")),
      d_maxUnknownsInARow(smtStatisticsRegistry().registerInt(
          name + "status::maxUnknownsInARow")),
      d_avgUnknownsInARow(smtStatisticsRegistry().registerAverage(
          name + "status::avgUnknownsInARow")),
      d_revertsOnConflicts(smtStatisticsRegistry().registerInt(
          name + "status::revertsOnConflicts")),
      d_commitsOnConflicts(smtStatisticsRegistry().registerInt(
          name + "status::commitsOnConflicts")),
      d_nontrivialSatChecks(smtStatisticsRegistry().registerInt(
          name + "status::nontrivialSatChecks")),
      d_replayLogRecCount(
          smtStatisticsRegistry().registerInt(name + "z::approx::replay::rec")),
      d_replayLogRecConflictEscalation(smtStatisticsRegistry().registerInt(
          name + "z::approx::replay::rec::escalation")),
      d_replayLogRecEarlyExit(smtStatisticsRegistry().registerInt(
          name + "z::approx::replay::rec::earlyexit")),
      d_replayBranchCloseFailures(smtStatisticsRegistry().registerInt(
          name + "z::approx::replay::rec::branch::closefailures")),
      d_replayLeafCloseFailures(smtStatisticsRegistry().registerInt(
          name + "z::approx::replay::rec::leaf::closefailures")),
      d_replayBranchSkips(smtStatisticsRegistry().registerInt(
          name + "z::approx::replay::rec::branch::skips")),
      d_mirCutsAttempted(smtStatisticsRegistry().registerInt(
          name + "z::approx::cuts::mir::attempted")),
      d_gmiCutsAttempted(smtStatisticsRegistry().registerInt(
          name + "z::approx::cuts::gmi::attempted")),
      d_branchCutsAttempted(smtStatisticsRegistry().registerInt(
          name + "z::approx::cuts::branch::attempted")),
      d_cutsReconstructed(smtStatisticsRegistry().registerInt(
          name + "z::approx::cuts::reconstructed")),
      d_cutsReconstructionFailed(smtStatisticsRegistry().registerInt(
          name + "z::approx::cuts::reconstructed::failed")),
      d_cutsProven(smtStatisticsRegistry().registerInt(
          name + "z::approx::cuts::proofs")),
      d_cutsProofFailed(smtStatisticsRegistry().registerInt(
          name + "z::approx::cuts::proofs::failed")),
      d_mipReplayLemmaCalls(smtStatisticsRegistry().registerInt(
          name + "z::approx::external::calls")),
      d_mipExternalCuts(smtStatisticsRegistry().registerInt(
          name + "z::approx::external::cuts")),
      d_mipExternalBranch(smtStatisticsRegistry().registerInt(
          name + "z::approx::external::branches")),
      d_inSolveInteger(smtStatisticsRegistry().registerInt(
          name + "z::approx::inSolverInteger")),
      d_branchesExhausted(smtStatisticsRegistry().registerInt(
          name + "z::approx::exhausted::branches")),
      d_execExhausted(smtStatisticsRegistry().registerInt(
          name + "z::approx::exhausted::exec")),
      d_pivotsExhausted(smtStatisticsRegistry().registerInt(
          name + "z::approx::exhausted::pivots")),
      d_panicBranches(
          smtStatisticsRegistry().registerInt(name + "z::arith::paniclemmas")),
      d_relaxCalls(
          smtStatisticsRegistry().registerInt(name + "z::arith::relax::calls")),
      d_relaxLinFeas(smtStatisticsRegistry().registerInt(
          name + "z::arith::relax::feasible::res")),
      d_relaxLinFeasFailures(smtStatisticsRegistry().registerInt(
          name + "z::arith::relax::feasible::failures")),
      d_relaxLinInfeas(smtStatisticsRegistry().registerInt(
          name + "z::arith::relax::infeasible")),
      d_relaxLinInfeasFailures(smtStatisticsRegistry().registerInt(
          name + "z::arith::relax::infeasible::failures")),
      d_relaxLinExhausted(smtStatisticsRegistry().registerInt(
          name + "z::arith::relax::exhausted")),
      d_relaxOthers(
          smtStatisticsRegistry().registerInt(name + "z::arith::relax::other")),
      d_applyRowsDeleted(smtStatisticsRegistry().registerInt(
          name + "z::arith::cuts::applyRowsDeleted")),
      d_replaySimplexTimer(smtStatisticsRegistry().registerTimer(
          name + "z::approx::replay::simplex::timer")),
      d_replayLogTimer(smtStatisticsRegistry().registerTimer(
          name + "z::approx::replay::log::timer")),
      d_solveIntTimer(
          smtStatisticsRegistry().registerTimer(name + "z::solveInt::timer")),
      d_solveRealRelaxTimer(smtStatisticsRegistry().registerTimer(
          name + "z::solveRealRelax::timer")),
      d_solveIntCalls(
          smtStatisticsRegistry().registerInt(name + "z::solveInt::calls")),
      d_solveStandardEffort(smtStatisticsRegistry().registerInt(
          name + "z::solveInt::calls::standardEffort")),
      d_approxDisabled(
          smtStatisticsRegistry().registerInt(name + "z::approxDisabled")),
      d_replayAttemptFailed(
          smtStatisticsRegistry().registerInt(name + "z::replayAttemptFailed")),
      d_cutsRejectedDuringReplay(smtStatisticsRegistry().registerInt(
          name + "z::approx::replay::cuts::rejected")),
      d_cutsRejectedDuringLemmas(smtStatisticsRegistry().registerInt(
          name + "z::approx::external::cuts::rejected")),
      d_satPivots(smtStatisticsRegistry().registerHistogram<uint32_t>(
          name + "pivots::sat")),
      d_unsatPivots(smtStatisticsRegistry().registerHistogram<uint32_t>(
          name + "pivots::unsat")),
      d_unknownPivots(smtStatisticsRegistry().registerHistogram<uint32_t>(
          name + "pivots::unknown")),
      d_solveIntModelsAttempts(smtStatisticsRegistry().registerInt(
          name + "z::solveInt::models::attempts")),
      d_solveIntModelsSuccessful(smtStatisticsRegistry().registerInt(
          name + "zzz::solveInt::models::successful")),
      d_mipTimer(smtStatisticsRegistry().registerTimer(
          name + "z::approx::mip::timer")),
      d_lpTimer(
          smtStatisticsRegistry().registerTimer(name + "z::approx::lp::timer")),
      d_mipProofsAttempted(smtStatisticsRegistry().registerInt(
          name + "z::mip::proofs::attempted")),
      d_mipProofsSuccessful(smtStatisticsRegistry().registerInt(
          name + "z::mip::proofs::successful")),
      d_numBranchesFailed(smtStatisticsRegistry().registerInt(
          name + "z::mip::branch::proof::failed"))
{
}

bool complexityBelow(const DenseMap<Rational>& row, uint32_t cap){
  DenseMap<Rational>::const_iterator riter, rend;
  for(riter=row.begin(), rend=row.end(); riter != rend; ++riter){
    ArithVar v = *riter;
    const Rational& q = row[v];
    if(q.complexity() > cap){
      return false;
    }
  }
  return true;
}

bool TheoryArithPrivate::isProofEnabled() const
{
  return d_pnm != nullptr;
}

void TheoryArithPrivate::raiseConflict(ConstraintCP a, InferenceId id){
  Assert(a->inConflict());
  d_conflicts.push_back(std::make_pair(a, id));
}

void TheoryArithPrivate::raiseBlackBoxConflict(Node bb,
                                               std::shared_ptr<ProofNode> pf)
{
  Debug("arith::bb") << "raiseBlackBoxConflict: " << bb << std::endl;
  if (d_blackBoxConflict.get().isNull())
  {
    if (isProofEnabled())
    {
      Debug("arith::bb") << "  with proof " << pf << std::endl;
      d_blackBoxConflictPf.set(pf);
    }
    d_blackBoxConflict = bb;
  }
}

bool TheoryArithPrivate::anyConflict() const
{
  return !conflictQueueEmpty() || !d_blackBoxConflict.get().isNull();
}

void TheoryArithPrivate::revertOutOfConflict(){
  d_partialModel.revertAssignmentChanges();
  clearUpdates();
  d_currentPropagationList.clear();
}

void TheoryArithPrivate::clearUpdates(){
  d_updatedBounds.purge();
}

// void TheoryArithPrivate::raiseConflict(ConstraintCP a, ConstraintCP b){
//   ConstraintCPVec v;
//   v.push_back(a);
//   v.push_back(b);
//   d_conflicts.push_back(v);
// }

// void TheoryArithPrivate::raiseConflict(ConstraintCP a, ConstraintCP b, ConstraintCP c){
//   ConstraintCPVec v;
//   v.push_back(a);
//   v.push_back(b);
//   v.push_back(c);
//   d_conflicts.push_back(v);
// }

void TheoryArithPrivate::zeroDifferenceDetected(ArithVar x){
  if(d_cmEnabled){
    Assert(d_congruenceManager.isWatchedVariable(x));
    Assert(d_partialModel.upperBoundIsZero(x));
    Assert(d_partialModel.lowerBoundIsZero(x));

    ConstraintP lb = d_partialModel.getLowerBoundConstraint(x);
    ConstraintP ub = d_partialModel.getUpperBoundConstraint(x);

    if(lb->isEquality()){
      d_congruenceManager.watchedVariableIsZero(lb);
    }else if(ub->isEquality()){
      d_congruenceManager.watchedVariableIsZero(ub);
    }else{
      d_congruenceManager.watchedVariableIsZero(lb, ub);
    }
  }
}

bool TheoryArithPrivate::getSolveIntegerResource(){
  if(d_attemptSolveIntTurnedOff > 0){
    d_attemptSolveIntTurnedOff = d_attemptSolveIntTurnedOff - 1;
    return false;
  }else{
    return true;
  }
}

bool TheoryArithPrivate::getDioCuttingResource(){
  if(d_dioSolveResources > 0){
    d_dioSolveResources--;
    if(d_dioSolveResources == 0){
      d_dioSolveResources = -options::rrTurns();
    }
    return true;
  }else{
    d_dioSolveResources++;
    if(d_dioSolveResources >= 0){
      d_dioSolveResources = options::dioSolverTurns();
    }
    return false;
  }
}

/* procedure AssertLower( x_i >= c_i ) */
bool TheoryArithPrivate::AssertLower(ConstraintP constraint){
  Assert(constraint != NullConstraint);
  Assert(constraint->isLowerBound());
  Assert(constraint->isTrue());
  Assert(!constraint->negationHasProof());

  ArithVar x_i = constraint->getVariable();
  const DeltaRational& c_i = constraint->getValue();

  Debug("arith") << "AssertLower(" << x_i << " " << c_i << ")"<< std::endl;

  Assert(!isInteger(x_i) || c_i.isIntegral());

  //TODO Relax to less than?
  if(d_partialModel.lessThanLowerBound(x_i, c_i)){
    return false; //sat
  }

  int cmpToUB = d_partialModel.cmpToUpperBound(x_i, c_i);
  if(cmpToUB > 0){ //  c_i < \lowerbound(x_i)
    ConstraintP ubc = d_partialModel.getUpperBoundConstraint(x_i);
    ConstraintP negation = constraint->getNegation();
    negation->impliedByUnate(ubc, true);

    raiseConflict(constraint, InferenceId::ARITH_CONF_LOWER);

    ++(d_statistics.d_statAssertLowerConflicts);
    return true;
  }else if(cmpToUB == 0){
    if(isInteger(x_i)){
      d_constantIntegerVariables.push_back(x_i);
      Debug("dio::push") << "dio::push " << x_i << endl;
    }
    ConstraintP ub = d_partialModel.getUpperBoundConstraint(x_i);

    if(d_cmEnabled){
      if(!d_congruenceManager.isWatchedVariable(x_i) || c_i.sgn() != 0){
        // if it is not a watched variable report it
        // if it is is a watched variable and c_i == 0,
        // let zeroDifferenceDetected(x_i) catch this
        d_congruenceManager.equalsConstant(constraint, ub);
      }
    }

    const ValueCollection& vc = constraint->getValueCollection();
    if(vc.hasEquality()){
      Assert(vc.hasDisequality());
      ConstraintP eq = vc.getEquality();
      ConstraintP diseq = vc.getDisequality();
      // x <= b, x >= b |= x = b
      // (x > b or x < b or x = b)
      Debug("arith::eq") << "lb == ub, propagate eq" << eq << endl;
      bool triConflict = diseq->isTrue();

      if(!eq->isTrue()){
        eq->impliedByTrichotomy(constraint, ub, triConflict);
        eq->tryToPropagate();
      }
      if(triConflict){
        ++(d_statistics.d_statDisequalityConflicts);
        raiseConflict(eq, InferenceId::ARITH_CONF_TRICHOTOMY);
        return true;
      }
    }
  }else{
    // l <= x <= u and l < u
    Assert(cmpToUB < 0);
    const ValueCollection& vc = constraint->getValueCollection();

    if(vc.hasDisequality()){
      const ConstraintP diseq = vc.getDisequality();
      if(diseq->isTrue()){
        const ConstraintP ub = d_constraintDatabase.ensureConstraint(const_cast<ValueCollection&>(vc), UpperBound);
        ConstraintP negUb = ub->getNegation();

        // l <= x, l != x |= l < x
        // |= not (l >= x)
        bool ubInConflict = ub->hasProof();
        bool learnNegUb = !(negUb->hasProof());
        if(learnNegUb){
          negUb->impliedByTrichotomy(constraint, diseq, ubInConflict);
          negUb->tryToPropagate();
        }
        if(ubInConflict){
          raiseConflict(ub, InferenceId::ARITH_CONF_TRICHOTOMY);
          return true;
        }else if(learnNegUb){
          d_learnedBounds.push_back(negUb);
        }
      }
    }
  }

  d_currentPropagationList.push_back(constraint);
  d_currentPropagationList.push_back(d_partialModel.getLowerBoundConstraint(x_i));

  d_partialModel.setLowerBoundConstraint(constraint);

  if(d_cmEnabled){
    if(d_congruenceManager.isWatchedVariable(x_i)){
      int sgn = c_i.sgn();
      if(sgn > 0){
        d_congruenceManager.watchedVariableCannotBeZero(constraint);
      }else if(sgn == 0 && d_partialModel.upperBoundIsZero(x_i)){
        zeroDifferenceDetected(x_i);
      }
    }
  }

  d_updatedBounds.softAdd(x_i);

  if(Debug.isOn("model")) {
    Debug("model") << "before" << endl;
    d_partialModel.printModel(x_i);
    d_tableau.debugPrintIsBasic(x_i);
  }

  if(!d_tableau.isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) < c_i){
      d_linEq.update(x_i, c_i);
    }
  }else{
    d_errorSet.signalVariable(x_i);
  }

  if(Debug.isOn("model")) {
    Debug("model") << "after" << endl;
    d_partialModel.printModel(x_i);
    d_tableau.debugPrintIsBasic(x_i);
 }

  return false; //sat
}

/* procedure AssertUpper( x_i <= c_i) */
bool TheoryArithPrivate::AssertUpper(ConstraintP constraint){
  Assert(constraint != NullConstraint);
  Assert(constraint->isUpperBound());
  Assert(constraint->isTrue());
  Assert(!constraint->negationHasProof());

  ArithVar x_i = constraint->getVariable();
  const DeltaRational& c_i = constraint->getValue();

  Debug("arith") << "AssertUpper(" << x_i << " " << c_i << ")"<< std::endl;


  //Too strong because of rounding with integers
  //Assert(!constraint->hasLiteral() || original == constraint->getLiteral());
  Assert(!isInteger(x_i) || c_i.isIntegral());

  Debug("arith") << "AssertUpper(" << x_i << " " << c_i << ")"<< std::endl;

  if(d_partialModel.greaterThanUpperBound(x_i, c_i) ){ // \upperbound(x_i) <= c_i
    return false; //sat
  }

  // cmpToLb =  \lowerbound(x_i).cmp(c_i)
  int cmpToLB = d_partialModel.cmpToLowerBound(x_i, c_i);
  if( cmpToLB < 0 ){ //  \upperbound(x_i) < \lowerbound(x_i)
    // l_i <= x_i and c_i < l_i |= c_i < x_i
    // or ... |= not (x_i <= c_i)
    ConstraintP lbc = d_partialModel.getLowerBoundConstraint(x_i);
    ConstraintP negConstraint = constraint->getNegation();
    negConstraint->impliedByUnate(lbc, true);
    raiseConflict(constraint, InferenceId::ARITH_CONF_UPPER);
    ++(d_statistics.d_statAssertUpperConflicts);
    return true;
  }else if(cmpToLB == 0){ // \lowerBound(x_i) == \upperbound(x_i)
    if(isInteger(x_i)){
      d_constantIntegerVariables.push_back(x_i);
      Debug("dio::push") << "dio::push " << x_i << endl;
    }

    const ValueCollection& vc = constraint->getValueCollection();
    ConstraintP lb = d_partialModel.getLowerBoundConstraint(x_i);
    if(d_cmEnabled){
      if(!d_congruenceManager.isWatchedVariable(x_i) || c_i.sgn() != 0){
        // if it is not a watched variable report it
        // if it is is a watched variable and c_i == 0,
        // let zeroDifferenceDetected(x_i) catch this
        d_congruenceManager.equalsConstant(lb, constraint);
      }
    }

    if(vc.hasDisequality()){
      Assert(vc.hasDisequality());
      ConstraintP eq = vc.getEquality();
      ConstraintP diseq = vc.getDisequality();
      // x <= b, x >= b |= x = b
      // (x > b or x < b or x = b)
      Debug("arith::eq") << "lb == ub, propagate eq" << eq << endl;
      bool triConflict = diseq->isTrue();
      if(!eq->isTrue()){
        eq->impliedByTrichotomy(constraint, lb, triConflict);
        eq->tryToPropagate();
      }
      if(triConflict){
        ++(d_statistics.d_statDisequalityConflicts);
        raiseConflict(eq, InferenceId::ARITH_CONF_TRICHOTOMY);
        return true;
      }
    }
  }else if(cmpToLB > 0){
    // l <= x <= u and l < u
    Assert(cmpToLB > 0);
    const ValueCollection& vc = constraint->getValueCollection();

    if(vc.hasDisequality()){
      const ConstraintP diseq = vc.getDisequality();
      if(diseq->isTrue()){
        const ConstraintP lb = d_constraintDatabase.ensureConstraint(const_cast<ValueCollection&>(vc), LowerBound);
        ConstraintP negLb = lb->getNegation();

        // x <= u, u != x |= u < x
        // |= not (u >= x)
        bool lbInConflict = lb->hasProof();
        bool learnNegLb = !(negLb->hasProof());
        if(learnNegLb){
          negLb->impliedByTrichotomy(constraint, diseq, lbInConflict);
          negLb->tryToPropagate();
        }
        if(lbInConflict){
          raiseConflict(lb, InferenceId::ARITH_CONF_TRICHOTOMY);
          return true;
        }else if(learnNegLb){
          d_learnedBounds.push_back(negLb);
        }
      }
    }
  }

  d_currentPropagationList.push_back(constraint);
  d_currentPropagationList.push_back(d_partialModel.getUpperBoundConstraint(x_i));
  //It is fine if this is NullConstraint

  d_partialModel.setUpperBoundConstraint(constraint);

  if(d_cmEnabled){
    if(d_congruenceManager.isWatchedVariable(x_i)){
      int sgn = c_i.sgn();
      if(sgn < 0){
        d_congruenceManager.watchedVariableCannotBeZero(constraint);
      }else if(sgn == 0 && d_partialModel.lowerBoundIsZero(x_i)){
        zeroDifferenceDetected(x_i);
      }
    }
  }

  d_updatedBounds.softAdd(x_i);

  if(Debug.isOn("model")) {
    Debug("model") << "before" << endl;
    d_partialModel.printModel(x_i);
    d_tableau.debugPrintIsBasic(x_i);
  }

  if(!d_tableau.isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) > c_i){
      d_linEq.update(x_i, c_i);
    }
  }else{
    d_errorSet.signalVariable(x_i);
  }

  if(Debug.isOn("model")) {
    Debug("model") << "after" << endl;
    d_partialModel.printModel(x_i);
    d_tableau.debugPrintIsBasic(x_i);
  }

  return false; //sat
}


/* procedure AssertEquality( x_i == c_i ) */
bool TheoryArithPrivate::AssertEquality(ConstraintP constraint){
  Assert(constraint != NullConstraint);
  Assert(constraint->isEquality());
  Assert(constraint->isTrue());
  Assert(!constraint->negationHasProof());

  ArithVar x_i = constraint->getVariable();
  const DeltaRational& c_i = constraint->getValue();

  Debug("arith") << "AssertEquality(" << x_i << " " << c_i << ")"<< std::endl;

  //Should be fine in integers
  Assert(!isInteger(x_i) || c_i.isIntegral());

  int cmpToLB = d_partialModel.cmpToLowerBound(x_i, c_i);
  int cmpToUB = d_partialModel.cmpToUpperBound(x_i, c_i);

  // u_i <= c_i <= l_i
  // This can happen if both c_i <= x_i and x_i <= c_i are in the system.
  if(cmpToUB >= 0 && cmpToLB <= 0){
    return false; //sat
  }

  if(cmpToUB > 0 || cmpToLB < 0){
    ConstraintP cb = (cmpToUB > 0) ?  d_partialModel.getUpperBoundConstraint(x_i) :
      d_partialModel.getLowerBoundConstraint(x_i);
    ConstraintP diseq = constraint->getNegation();
    Assert(!diseq->isTrue());
    diseq->impliedByUnate(cb, true);
    raiseConflict(constraint, InferenceId::ARITH_CONF_EQ);
    return true;
  }

  Assert(cmpToUB <= 0);
  Assert(cmpToLB >= 0);
  Assert(cmpToUB < 0 || cmpToLB > 0);

  if(isInteger(x_i)){
    d_constantIntegerVariables.push_back(x_i);
    Debug("dio::push") << "dio::push " << x_i << endl;
  }

  // Don't bother to check whether x_i != c_i is in d_diseq
  // The a and (not a) should never be on the fact queue
  d_currentPropagationList.push_back(constraint);
  d_currentPropagationList.push_back(d_partialModel.getLowerBoundConstraint(x_i));
  d_currentPropagationList.push_back(d_partialModel.getUpperBoundConstraint(x_i));

  d_partialModel.setUpperBoundConstraint(constraint);
  d_partialModel.setLowerBoundConstraint(constraint);

  if(d_cmEnabled){
    if(d_congruenceManager.isWatchedVariable(x_i)){
      int sgn = c_i.sgn();
      if(sgn == 0){
        zeroDifferenceDetected(x_i);
      }else{
        d_congruenceManager.watchedVariableCannotBeZero(constraint);
        d_congruenceManager.equalsConstant(constraint);
      }
    }else{
      d_congruenceManager.equalsConstant(constraint);
    }
  }

  d_updatedBounds.softAdd(x_i);

  if(Debug.isOn("model")) {
    Debug("model") << "before" << endl;
    d_partialModel.printModel(x_i);
    d_tableau.debugPrintIsBasic(x_i);
  }

  if(!d_tableau.isBasic(x_i)){
    if(!(d_partialModel.getAssignment(x_i) == c_i)){
      d_linEq.update(x_i, c_i);
    }
  }else{
    d_errorSet.signalVariable(x_i);
  }

  if(Debug.isOn("model")) {
    Debug("model") << "after" << endl;
    d_partialModel.printModel(x_i);
    d_tableau.debugPrintIsBasic(x_i);
  }

  return false;
}


/* procedure AssertDisequality( x_i != c_i ) */
bool TheoryArithPrivate::AssertDisequality(ConstraintP constraint){
  Assert(constraint != NullConstraint);
  Assert(constraint->isDisequality());
  Assert(constraint->isTrue());
  Assert(!constraint->negationHasProof());

  ArithVar x_i = constraint->getVariable();
  const DeltaRational& c_i = constraint->getValue();
  Debug("arith") << "AssertDisequality(" << x_i << " " << c_i << ")"<< std::endl;

  //Should be fine in integers
  Assert(!isInteger(x_i) || c_i.isIntegral());

  if(d_cmEnabled){
    if(d_congruenceManager.isWatchedVariable(x_i)){
      int sgn = c_i.sgn();
      if(sgn == 0){
        d_congruenceManager.watchedVariableCannotBeZero(constraint);
      }
    }
  }

  const ValueCollection& vc = constraint->getValueCollection();
  if(vc.hasLowerBound() && vc.hasUpperBound()){
    const ConstraintP lb = vc.getLowerBound();
    const ConstraintP ub = vc.getUpperBound();
    if(lb->isTrue() && ub->isTrue()){
      ConstraintP eq = constraint->getNegation();
      eq->impliedByTrichotomy(lb, ub, true);
      raiseConflict(constraint, InferenceId::ARITH_CONF_TRICHOTOMY);
      //in conflict
      ++(d_statistics.d_statDisequalityConflicts);
      return true;
    }
  }
  if(vc.hasLowerBound() ){
    const ConstraintP lb = vc.getLowerBound();
    if(lb->isTrue()){
      const ConstraintP ub = d_constraintDatabase.ensureConstraint(const_cast<ValueCollection&>(vc), UpperBound);
      Assert(!ub->isTrue());
      Debug("arith::eq") << "propagate UpperBound " << constraint << lb << ub << endl;
      const ConstraintP negUb = ub->getNegation();
      if(!negUb->isTrue()){
        negUb->impliedByTrichotomy(constraint, lb, false);
        negUb->tryToPropagate();
        d_learnedBounds.push_back(negUb);
      }
    }
  }
  if(vc.hasUpperBound()){
    const ConstraintP ub = vc.getUpperBound();
    if(ub->isTrue()){
      const ConstraintP lb = d_constraintDatabase.ensureConstraint(const_cast<ValueCollection&>(vc), LowerBound);
      Assert(!lb->isTrue());

      Debug("arith::eq") << "propagate LowerBound " << constraint << lb << ub << endl;
      const ConstraintP negLb = lb->getNegation();
      if(!negLb->isTrue()){
        negLb->impliedByTrichotomy(constraint, ub, false);
        negLb->tryToPropagate();
        d_learnedBounds.push_back(negLb);
      }
    }
  }

  bool split = constraint->isSplit();

  if(!split && c_i == d_partialModel.getAssignment(x_i)){
    Debug("arith::eq") << "lemma now! " << constraint << endl;
    outputTrustedLemma(constraint->split(), InferenceId::ARITH_SPLIT_DEQ);
    return false;
  }else if(d_partialModel.strictlyLessThanLowerBound(x_i, c_i)){
    Debug("arith::eq") << "can drop as less than lb" << constraint << endl;
  }else if(d_partialModel.strictlyGreaterThanUpperBound(x_i, c_i)){
    Debug("arith::eq") << "can drop as less than ub" << constraint << endl;
  }else if(!split){
    Debug("arith::eq") << "push back" << constraint << endl;
    d_diseqQueue.push(constraint);
    d_partialModel.invalidateDelta();
  }else{
    Debug("arith::eq") << "skipping already split " << constraint << endl;
  }
  return false;
}

void TheoryArithPrivate::notifySharedTerm(TNode n)
{
  Debug("arith::notifySharedTerm") << "notifySharedTerm: " << n << endl;
  if(n.isConst()){
    d_partialModel.invalidateDelta();
  }
  if(!n.isConst() && !isSetup(n)){
    Polynomial poly = Polynomial::parsePolynomial(n);
    Polynomial::iterator it = poly.begin();
    Polynomial::iterator it_end = poly.end();
    for (; it != it_end; ++ it) {
      Monomial m = *it;
      if (!m.isConstant() && !isSetup(m.getVarList().getNode())) {
        setupVariableList(m.getVarList());
      }
    }
  }
}

Node TheoryArithPrivate::getModelValue(TNode term) {
  try{
    const DeltaRational drv = getDeltaValue(term);
    const Rational& delta = d_partialModel.getDelta();
    const Rational qmodel = drv.substituteDelta( delta );
    return mkRationalNode( qmodel );
  } catch (DeltaRationalException& dr) {
    return Node::null();
  } catch (ModelException& me) {
    return Node::null();
  }
}

Theory::PPAssertStatus TheoryArithPrivate::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_simplifyTimer);
  TNode in = tin.getNode();
  Debug("simplify") << "TheoryArithPrivate::solve(" << in << ")" << endl;


  // Solve equalities
  Rational minConstant = 0;
  Node minMonomial;
  Node minVar;
  if (in.getKind() == kind::EQUAL &&
      Theory::theoryOf(in[0].getType()) == THEORY_ARITH) {
    Comparison cmp = Comparison::parseNormalForm(in);

    Polynomial left = cmp.getLeft();

    Monomial m = left.getHead();
    if (m.getVarList().singleton()){
      VarList vl = m.getVarList();
      Node var = vl.getNode();
      if (var.isVar())
      {
        // if vl.isIntegral then m.getConstant().isOne()
        if(!vl.isIntegral() || m.getConstant().isOne()){
          minVar = var;
        }
      }
    }

    // Solve for variable
    if (!minVar.isNull()) {
      Polynomial right = cmp.getRight();
      Node elim = right.getNode();
      // ax + p = c -> (ax + p) -ax - c = -ax
      // x = (p - ax - c) * -1/a
      // Add the substitution if not recursive
      Assert(elim == Rewriter::rewrite(elim));

      if (right.size() > options::ppAssertMaxSubSize())
      {
        Debug("simplify")
            << "TheoryArithPrivate::solve(): did not substitute due to the "
               "right hand side containing too many terms: "
            << minVar << ":" << elim << endl;
        Debug("simplify") << right.size() << endl;
      }
      else if (d_containing.isLegalElimination(minVar, elim))
      {
        // cannot eliminate integers here unless we know the resulting
        // substitution is integral
        Debug("simplify") << "TheoryArithPrivate::solve(): substitution "
                          << minVar << " |-> " << elim << endl;

        outSubstitutions.addSubstitutionSolved(minVar, elim, tin);
        return Theory::PP_ASSERT_STATUS_SOLVED;
      }
      else
      {
        Debug("simplify") << "TheoryArithPrivate::solve(): can't substitute "
                          << minVar << ":" << minVar.getType() << " |-> "
                          << elim << ":" << elim.getType() << endl;
      }
    }
  }

  // If a relation, remember the bound
  switch(in.getKind()) {
  case kind::LEQ:
  case kind::LT:
  case kind::GEQ:
  case kind::GT:
    if (in[0].isVar()) {
      d_learner.addBound(in);
    }
    break;
  default:
    // Do nothing
    break;
  }

  return Theory::PP_ASSERT_STATUS_UNSOLVED;
}

void TheoryArithPrivate::ppStaticLearn(TNode n, NodeBuilder& learned)
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_staticLearningTimer);

  d_learner.staticLearning(n, learned);
}

ArithVar TheoryArithPrivate::findShortestBasicRow(ArithVar variable){
  ArithVar bestBasic = ARITHVAR_SENTINEL;
  uint64_t bestRowLength = std::numeric_limits<uint64_t>::max();

  Tableau::ColIterator basicIter = d_tableau.colIterator(variable);
  for(; !basicIter.atEnd(); ++basicIter){
    const Tableau::Entry& entry = *basicIter;
    Assert(entry.getColVar() == variable);
    RowIndex ridx = entry.getRowIndex();
    ArithVar basic = d_tableau.rowIndexToBasic(ridx);
    uint32_t rowLength = d_tableau.getRowLength(ridx);
    if((rowLength < bestRowLength) ||
       (rowLength == bestRowLength && basic < bestBasic)){
      bestBasic = basic;
      bestRowLength = rowLength;
    }
  }
  Assert(bestBasic == ARITHVAR_SENTINEL
         || bestRowLength < std::numeric_limits<uint32_t>::max());
  return bestBasic;
}

void TheoryArithPrivate::setupVariable(const Variable& x){
  Node n = x.getNode();

  Assert(!isSetup(n));

  ++(d_statistics.d_statUserVariables);
  requestArithVar(n, false,  false);
  //ArithVar varN = requestArithVar(n,false);
  //setupInitialValue(varN);

  markSetup(n);
}

void TheoryArithPrivate::setupVariableList(const VarList& vl){
  Assert(!vl.empty());

  TNode vlNode = vl.getNode();
  Assert(!isSetup(vlNode));
  Assert(!d_partialModel.hasArithVar(vlNode));

  for(VarList::iterator i = vl.begin(), end = vl.end(); i != end; ++i){
    Variable var = *i;

    if(!isSetup(var.getNode())){
      setupVariable(var);
    }
  }

  if(!vl.singleton()){
    // vl is the product of at least 2 variables
    // vl : (* v1 v2 ...)
    if(getLogicInfo().isLinear()){
      throw LogicException("A non-linear fact was asserted to arithmetic in a linear logic.");
    }
    d_foundNl = true;

    ++(d_statistics.d_statUserVariables);
    requestArithVar(vlNode, false, false);
    //ArithVar av = requestArithVar(vlNode, false);
    //setupInitialValue(av);

    markSetup(vlNode);
  }
  else if (vlNode.getKind() == kind::EXPONENTIAL
           || vlNode.getKind() == kind::SINE || vlNode.getKind() == kind::COSINE
           || vlNode.getKind() == kind::TANGENT)
  {
    d_foundNl = true;
  }

  /* Note:
   * Only call markSetup if the VarList is not a singleton.
   * See the comment in setupPolynomail for more.
   */
}

void TheoryArithPrivate::cautiousSetupPolynomial(const Polynomial& p){
  if(p.containsConstant()){
    if(!p.isConstant()){
      Polynomial noConstant = p.getTail();
      if(!isSetup(noConstant.getNode())){
        setupPolynomial(noConstant);
      }
    }
  }else if(!isSetup(p.getNode())){
    setupPolynomial(p);
  }
}


void TheoryArithPrivate::setupPolynomial(const Polynomial& poly) {
  Assert(!poly.containsConstant());
  TNode polyNode = poly.getNode();
  Assert(!isSetup(polyNode));
  Assert(!d_partialModel.hasArithVar(polyNode));

  for(Polynomial::iterator i = poly.begin(), end = poly.end(); i != end; ++i){
    Monomial mono = *i;
    const VarList& vl = mono.getVarList();
    if(!isSetup(vl.getNode())){
      setupVariableList(vl);
    }
  }

  if(polyNode.getKind() == PLUS){
    d_tableauSizeHasBeenModified = true;

    vector<ArithVar> variables;
    vector<Rational> coefficients;
    asVectors(poly, coefficients, variables);

    ArithVar varSlack = requestArithVar(polyNode, true, false);
    d_tableau.addRow(varSlack, coefficients, variables);
    setupBasicValue(varSlack);
    d_linEq.trackRowIndex(d_tableau.basicToRowIndex(varSlack));

    //Add differences to the difference manager
    Polynomial::iterator i = poly.begin(), end = poly.end();
    if(i != end){
      Monomial first = *i;
      ++i;
      if(i != end){
        Monomial second = *i;
        ++i;
        if(i == end){
          if(first.getConstant().isOne() && second.getConstant().getValue() == -1){
            VarList vl0 = first.getVarList();
            VarList vl1 = second.getVarList();
            if(vl0.singleton() && vl1.singleton()){
              d_congruenceManager.addWatchedPair(varSlack, vl0.getNode(), vl1.getNode());
            }
          }
        }
      }
    }

    ++(d_statistics.d_statAuxiliaryVariables);
    markSetup(polyNode);
  }

  /* Note:
   * It is worth documenting that polyNode should only be marked as
   * being setup by this function if it has kind PLUS.
   * Other kinds will be marked as being setup by lower levels of setup
   * specifically setupVariableList.
   */
}

void TheoryArithPrivate::setupAtom(TNode atom) {
  Assert(isRelationOperator(atom.getKind())) << atom;
  Assert(Comparison::isNormalAtom(atom));
  Assert(!isSetup(atom));
  Assert(!d_constraintDatabase.hasLiteral(atom));

  Comparison cmp = Comparison::parseNormalForm(atom);
  Polynomial nvp = cmp.normalizedVariablePart();
  Assert(!nvp.isZero());

  if(!isSetup(nvp.getNode())){
    setupPolynomial(nvp);
  }

  d_constraintDatabase.addLiteral(atom);

  markSetup(atom);
}

void TheoryArithPrivate::preRegisterTerm(TNode n) {
  Debug("arith::preregister") <<"begin arith::preRegisterTerm("<< n <<")"<< endl;

  d_preregisteredNodes.insert(n);

  try {
    if(isRelationOperator(n.getKind())){
      if(!isSetup(n)){
        setupAtom(n);
      }
      ConstraintP c = d_constraintDatabase.lookup(n);
      Assert(c != NullConstraint);

      Debug("arith::preregister") << "setup constraint" << c << endl;
      Assert(!c->canBePropagated());
      c->setPreregistered();
    }
  } catch(LogicException& le) {
    std::stringstream ss;
    ss << le.getMessage() << endl << "The fact in question: " << n << endl;
    throw LogicException(ss.str());
  }

  Debug("arith::preregister") << "end arith::preRegisterTerm("<< n <<")" << endl;
}

void TheoryArithPrivate::releaseArithVar(ArithVar v){
  //Assert(d_partialModel.hasNode(v));

  d_constraintDatabase.removeVariable(v);
  d_partialModel.releaseArithVar(v);
}

ArithVar TheoryArithPrivate::requestArithVar(TNode x, bool aux, bool internal){
  //TODO : The VarList trick is good enough?
  Assert(isLeaf(x) || VarList::isMember(x) || x.getKind() == PLUS || internal);
  if(getLogicInfo().isLinear() && Variable::isDivMember(x)){
    stringstream ss;
    ss << "A non-linear fact (involving div/mod/divisibility) was asserted to "
          "arithmetic in a linear logic: "
       << x << std::endl;
    throw LogicException(ss.str());
  }
  Assert(!d_partialModel.hasArithVar(x));
  Assert(x.getType().isReal());  // real or integer

  ArithVar max = d_partialModel.getNumberOfVariables();
  ArithVar varX = d_partialModel.allocate(x, aux);

  bool reclaim =  max >= d_partialModel.getNumberOfVariables();;

  if(!reclaim){
    d_dualSimplex.increaseMax();

    d_tableau.increaseSize();
    d_tableauSizeHasBeenModified = true;
  }
  d_constraintDatabase.addVariable(varX);

  Debug("arith::arithvar") << "@" << getSatContext()->getLevel()
                           << " " << x << " |-> " << varX
                           << "(relaiming " << reclaim << ")" << endl;

  Assert(!d_partialModel.hasUpperBound(varX));
  Assert(!d_partialModel.hasLowerBound(varX));

  return varX;
}

void TheoryArithPrivate::asVectors(const Polynomial& p, std::vector<Rational>& coeffs, std::vector<ArithVar>& variables) {
  for(Polynomial::iterator i = p.begin(), end = p.end(); i != end; ++i){
    const Monomial& mono = *i;
    const Constant& constant = mono.getConstant();
    const VarList& variable = mono.getVarList();

    Node n = variable.getNode();

    Debug("arith::asVectors") << "should be var: " << n << endl;

    // TODO: This VarList::isMember(n) can be stronger
    Assert(isLeaf(n) || VarList::isMember(n));
    Assert(theoryOf(n) != THEORY_ARITH || d_partialModel.hasArithVar(n));

    Assert(d_partialModel.hasArithVar(n));
    ArithVar av = d_partialModel.asArithVar(n);

    coeffs.push_back(constant.getValue());
    variables.push_back(av);
  }
}

/* Requirements:
 * For basic variables the row must have been added to the tableau.
 */
void TheoryArithPrivate::setupBasicValue(ArithVar x){
  Assert(d_tableau.isBasic(x));
  //If the variable is basic, assertions may have already happened and updates
  //may have occured before setting this variable up.

  //This can go away if the tableau creation is done at preregister
  //time instead of register
  DeltaRational safeAssignment = d_linEq.computeRowValue(x, true);
  DeltaRational assignment = d_linEq.computeRowValue(x, false);
  d_partialModel.setAssignment(x,safeAssignment,assignment);

  Debug("arith") << "setupVariable("<<x<<")"<<std::endl;
}

ArithVar TheoryArithPrivate::determineArithVar(const Polynomial& p) const{
  Assert(!p.containsConstant());
  Assert(p.getHead().constantIsPositive());
  TNode n = p.getNode();
  Debug("determineArithVar") << "determineArithVar(" << n << ")" << endl;
  return d_partialModel.asArithVar(n);
}

ArithVar TheoryArithPrivate::determineArithVar(TNode assertion) const{
  Debug("determineArithVar") << "determineArithVar " << assertion << endl;
  Comparison cmp = Comparison::parseNormalForm(assertion);
  Polynomial variablePart = cmp.normalizedVariablePart();
  return determineArithVar(variablePart);
}


bool TheoryArithPrivate::canSafelyAvoidEqualitySetup(TNode equality){
  Assert(equality.getKind() == EQUAL);
  return d_partialModel.hasArithVar(equality[0]);
}

Comparison TheoryArithPrivate::mkIntegerEqualityFromAssignment(ArithVar v){
  const DeltaRational& beta = d_partialModel.getAssignment(v);

  Assert(beta.isIntegral());
  Polynomial betaAsPolynomial = Polynomial::mkPolynomial( Constant::mkConstant(beta.floor()) );

  TNode var = d_partialModel.asNode(v);
  Polynomial varAsPolynomial = Polynomial::parsePolynomial(var);
  return Comparison::mkComparison(EQUAL, varAsPolynomial, betaAsPolynomial);
}

TrustNode TheoryArithPrivate::dioCutting()
{
  context::Context::ScopedPush speculativePush(getSatContext());
  //DO NOT TOUCH THE OUTPUTSTREAM

  for(var_iterator vi = var_begin(), vend = var_end(); vi != vend; ++vi){
    ArithVar v = *vi;
    if(isInteger(v)){
      if(d_partialModel.cmpAssignmentUpperBound(v) == 0 ||
         d_partialModel.cmpAssignmentLowerBound(v) == 0){
        if(!d_partialModel.boundsAreEqual(v)){
          // If the bounds are equal this is already in the dioSolver
          //Add v = dr as a speculation.
          Comparison eq = mkIntegerEqualityFromAssignment(v);
          Debug("dio::push") << "dio::push " << v << " " <<  eq.getNode() << endl;
          Assert(!eq.isBoolean());
          d_diosolver.pushInputConstraint(eq, eq.getNode());
          // It does not matter what the explanation of eq is.
          // It cannot be used in a conflict
        }
      }
    }
  }

  SumPair plane = d_diosolver.processEquationsForCut();
  if(plane.isZero()){
    return TrustNode::null();
  }else{
    Polynomial p = plane.getPolynomial();
    Polynomial c = Polynomial::mkPolynomial(plane.getConstant() * Constant::mkConstant(-1));
    Integer gcd = p.gcd();
    Assert(p.isIntegral());
    Assert(c.isIntegral());
    Assert(gcd > 1);
    Assert(!gcd.divides(c.asConstant().getNumerator()));
    Comparison leq = Comparison::mkComparison(LEQ, p, c);
    Comparison geq = Comparison::mkComparison(GEQ, p, c);
    Node lemma = NodeManager::currentNM()->mkNode(OR, leq.getNode(), geq.getNode());
    Node rewrittenLemma = Rewriter::rewrite(lemma);
    Debug("arith::dio::ex") << "dioCutting found the plane: " << plane.getNode() << endl;
    Debug("arith::dio::ex") << "resulting in the cut: " << lemma << endl;
    Debug("arith::dio::ex") << "rewritten " << rewrittenLemma << endl;
    Debug("arith::dio") << "dioCutting found the plane: " << plane.getNode() << endl;
    Debug("arith::dio") << "resulting in the cut: " << lemma << endl;
    Debug("arith::dio") << "rewritten " << rewrittenLemma << endl;
    if (proofsEnabled())
    {
      NodeManager* nm = NodeManager::currentNM();
      Node gt = nm->mkNode(kind::GT, p.getNode(), c.getNode());
      Node lt = nm->mkNode(kind::LT, p.getNode(), c.getNode());

      Pf pfNotLeq = d_pnm->mkAssume(leq.getNode().negate());
      Pf pfGt =
          d_pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM, {pfNotLeq}, {gt});
      Pf pfNotGeq = d_pnm->mkAssume(geq.getNode().negate());
      Pf pfLt =
          d_pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM, {pfNotGeq}, {lt});
      Pf pfSum =
          d_pnm->mkNode(PfRule::MACRO_ARITH_SCALE_SUM_UB,
                        {pfGt, pfLt},
                        {nm->mkConst<Rational>(-1), nm->mkConst<Rational>(1)});
      Pf pfBot = d_pnm->mkNode(
          PfRule::MACRO_SR_PRED_TRANSFORM, {pfSum}, {nm->mkConst<bool>(false)});
      std::vector<Node> assumptions = {leq.getNode().negate(),
                                       geq.getNode().negate()};
      Pf pfNotAndNot = d_pnm->mkScope(pfBot, assumptions);
      Pf pfOr = d_pnm->mkNode(PfRule::NOT_AND, {pfNotAndNot}, {});
      Pf pfRewritten = d_pnm->mkNode(
          PfRule::MACRO_SR_PRED_TRANSFORM, {pfOr}, {rewrittenLemma});
      return d_pfGen->mkTrustNode(rewrittenLemma, pfRewritten);
    }
    else
    {
      return TrustNode::mkTrustLemma(rewrittenLemma, nullptr);
    }
  }
}

Node TheoryArithPrivate::callDioSolver(){
  while(!d_constantIntegerVariables.empty()){
    ArithVar v = d_constantIntegerVariables.front();
    d_constantIntegerVariables.pop();

    Debug("arith::dio")  << "callDioSolver " << v << endl;

    Assert(isInteger(v));
    Assert(d_partialModel.boundsAreEqual(v));

    ConstraintP lb = d_partialModel.getLowerBoundConstraint(v);
    ConstraintP ub = d_partialModel.getUpperBoundConstraint(v);

    Node orig = Node::null();
    if(lb->isEquality()){
      orig = Constraint::externalExplainByAssertions({lb});
    }else if(ub->isEquality()){
      orig = Constraint::externalExplainByAssertions({ub});
    }else {
      orig = Constraint::externalExplainByAssertions(ub, lb);
    }

    Assert(d_partialModel.assignmentIsConsistent(v));

    Comparison eq = mkIntegerEqualityFromAssignment(v);

    if(eq.isBoolean()){
      //This can only be a conflict
      Assert(!eq.getNode().getConst<bool>());

      //This should be handled by the normal form earlier in the case of equality
      Assert(orig.getKind() != EQUAL);
      return orig;
    }else{
      Debug("dio::push") << "dio::push " << v << " " << eq.getNode() << " with reason " << orig << endl;
      d_diosolver.pushInputConstraint(eq, orig);
    }
  }

  return d_diosolver.processEquationsForConflict();
}

ConstraintP TheoryArithPrivate::constraintFromFactQueue(TNode assertion)
{
  Kind simpleKind = Comparison::comparisonKind(assertion);
  ConstraintP constraint = d_constraintDatabase.lookup(assertion);
  if(constraint == NullConstraint){
    Assert(simpleKind == EQUAL || simpleKind == DISTINCT);
    bool isDistinct = simpleKind == DISTINCT;
    Node eq = (simpleKind == DISTINCT) ? assertion[0] : assertion;
    Assert(!isSetup(eq));
    Node reEq = Rewriter::rewrite(eq);
    Debug("arith::distinct::const") << "Assertion: " << assertion << std::endl;
    Debug("arith::distinct::const") << "Eq       : " << eq << std::endl;
    Debug("arith::distinct::const") << "reEq     : " << reEq << std::endl;
    if(reEq.getKind() == CONST_BOOLEAN){
      if(reEq.getConst<bool>() == isDistinct){
        // if is (not true), or false
        Assert((reEq.getConst<bool>() && isDistinct)
               || (!reEq.getConst<bool>() && !isDistinct));
        if (proofsEnabled())
        {
          Pf assume = d_pnm->mkAssume(assertion);
          std::vector<Node> assumptions = {assertion};
          Pf pf = d_pnm->mkScope(d_pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM,
                                               {d_pnm->mkAssume(assertion)},
                                               {}),
                                 assumptions);
          raiseBlackBoxConflict(assertion, pf);
        }
        else
        {
          raiseBlackBoxConflict(assertion);
        }
      }
      return NullConstraint;
    }
    Assert(reEq.getKind() != CONST_BOOLEAN);
    if(!isSetup(reEq)){
      setupAtom(reEq);
    }
    Node reAssertion = isDistinct ? reEq.notNode() : reEq;
    constraint = d_constraintDatabase.lookup(reAssertion);

    if(assertion != reAssertion){
      Debug("arith::nf") << "getting non-nf assertion " << assertion << " |-> " <<  reAssertion << endl;
      Assert(constraint != NullConstraint);
      d_assertionsThatDoNotMatchTheirLiterals.insert(assertion, constraint);
    }
  }

  Assert(constraint != NullConstraint);

  if(constraint->assertedToTheTheory()){
    //Do nothing
    return NullConstraint;
  }
  Assert(!constraint->assertedToTheTheory());
  bool inConflict = constraint->negationHasProof();
  constraint->setAssertedToTheTheory(assertion, inConflict);

  if(!constraint->hasProof()){
    Debug("arith::constraint") << "marking as constraint as self explaining " << endl;
    constraint->setAssumption(inConflict);
  } else {
    Debug("arith::constraint")
        << "already has proof: "
        << Constraint::externalExplainByAssertions({constraint});
  }

  if(Debug.isOn("arith::negatedassumption") && inConflict){
    ConstraintP negation = constraint->getNegation();
    if(Debug.isOn("arith::negatedassumption") && negation->isAssumption()){
      debugPrintFacts();
    }
    Debug("arith::eq") << "negation has proof" << endl;
    Debug("arith::eq") << constraint << endl;
    Debug("arith::eq") << negation << endl;
  }

  if(inConflict){
    ConstraintP negation = constraint->getNegation();
    if(Debug.isOn("arith::negatedassumption") && negation->isAssumption()){
      debugPrintFacts();
    }
    Debug("arith::eq") << "negation has proof" << endl;
    Debug("arith::eq") << constraint << endl;
    Debug("arith::eq") << negation << endl;
    raiseConflict(negation, InferenceId::UNKNOWN);
    return NullConstraint;
  }else{
    return constraint;
  }
}

bool TheoryArithPrivate::assertionCases(ConstraintP constraint){
  Assert(constraint->hasProof());
  Assert(!constraint->negationHasProof());

  ArithVar x_i = constraint->getVariable();

  switch(constraint->getType()){
  case UpperBound:
    if(isInteger(x_i) && constraint->isStrictUpperBound()){
      ConstraintP floorConstraint = constraint->getFloor();
      if(!floorConstraint->isTrue()){
        bool inConflict = floorConstraint->negationHasProof();
        if (Debug.isOn("arith::intbound")) {
          Debug("arith::intbound") << "literal, before: " << constraint->getLiteral() << std::endl;
          Debug("arith::intbound") << "constraint, after: " << floorConstraint << std::endl;
        }
        floorConstraint->impliedByIntTighten(constraint, inConflict);
        floorConstraint->tryToPropagate();
        if(inConflict){
          raiseConflict(floorConstraint, InferenceId::ARITH_TIGHTEN_FLOOR);
          return true;
        }
      }
      return AssertUpper(floorConstraint);
    }else{
      return AssertUpper(constraint);
    }
  case LowerBound:
    if(isInteger(x_i) && constraint->isStrictLowerBound()){
      ConstraintP ceilingConstraint = constraint->getCeiling();
      if(!ceilingConstraint->isTrue()){
        bool inConflict = ceilingConstraint->negationHasProof();
        if (Debug.isOn("arith::intbound")) {
          Debug("arith::intbound") << "literal, before: " << constraint->getLiteral() << std::endl;
          Debug("arith::intbound") << "constraint, after: " << ceilingConstraint << std::endl;
        }
        ceilingConstraint->impliedByIntTighten(constraint, inConflict);
        ceilingConstraint->tryToPropagate();
        if(inConflict){
          raiseConflict(ceilingConstraint, InferenceId::ARITH_TIGHTEN_CEIL);
          return true;
        }
      }
      return AssertLower(ceilingConstraint);
    }else{
      return AssertLower(constraint);
    }
  case Equality:
    return AssertEquality(constraint);
  case Disequality:
    return AssertDisequality(constraint);
  default:
    Unreachable();
    return false;
  }
}
/**
 * Looks for through the variables starting at d_nextIntegerCheckVar
 * for the first integer variable that is between its upper and lower bounds
 * that has a non-integer assignment.
 *
 * If assumeBounds is true, skip the check that the variable is in bounds.
 *
 * If there is no such variable, returns ARITHVAR_SENTINEL;
 */
ArithVar TheoryArithPrivate::nextIntegerViolation(bool assumeBounds) const
{
  ArithVar numVars = d_partialModel.getNumberOfVariables();
  ArithVar v = d_nextIntegerCheckVar;
  if (numVars > 0)
  {
    const ArithVar rrEnd = d_nextIntegerCheckVar;
    do
    {
      if (isIntegerInput(v))
      {
        if (!d_partialModel.integralAssignment(v))
        {
          if (assumeBounds || d_partialModel.assignmentIsConsistent(v))
          {
            return v;
          }
        }
      }
      v = (1 + v == numVars) ? 0 : (1 + v);
    } while (v != rrEnd);
  }
  return ARITHVAR_SENTINEL;
}

/**
 * Checks the set of integer variables I to see if each variable
 * in I has an integer assignment.
 */
bool TheoryArithPrivate::hasIntegerModel()
{
  ArithVar next = nextIntegerViolation(true);
  if (next != ARITHVAR_SENTINEL)
  {
    d_nextIntegerCheckVar = next;
    if (Debug.isOn("arith::hasIntegerModel"))
    {
      Debug("arith::hasIntegerModel") << "has int model? " << next << endl;
      d_partialModel.printModel(next, Debug("arith::hasIntegerModel"));
    }
    return false;
  }
  else
  {
    return true;
  }
}

Node flattenAndSort(Node n){
  Kind k = n.getKind();
  switch(k){
  case kind::OR:
  case kind::AND:
  case kind::PLUS:
  case kind::MULT:
    break;
  default:
    return n;
  }

  std::vector<Node> out;
  std::vector<Node> process;
  process.push_back(n);
  while(!process.empty()){
    Node b = process.back();
    process.pop_back();
    if(b.getKind() == k){
      for(Node::iterator i=b.begin(), end=b.end(); i!=end; ++i){
        process.push_back(*i);
      }
    } else {
      out.push_back(b);
    }
  }
  Assert(out.size() >= 2);
  std::sort(out.begin(), out.end());
  return NodeManager::currentNM()->mkNode(k, out);
}



/** Outputs conflicts to the output channel. */
void TheoryArithPrivate::outputConflicts(){
  Debug("arith::conflict") << "outputting conflicts" << std::endl;
  Assert(anyConflict());
  static unsigned int conflicts = 0;

  if(!conflictQueueEmpty()){
    Assert(!d_conflicts.empty());
    for(size_t i = 0, i_end = d_conflicts.size(); i < i_end; ++i){
      const std::pair<ConstraintCP, InferenceId>& conf = d_conflicts[i];
      const ConstraintCP& confConstraint = conf.first;
      bool hasProof = confConstraint->hasProof();
      Assert(confConstraint->inConflict());
      const ConstraintRule& pf = confConstraint->getConstraintRule();
      if (Debug.isOn("arith::conflict"))
      {
        pf.print(std::cout);
        std::cout << std::endl;
      }
      if (Debug.isOn("arith::pf::tree"))
      {
        Debug("arith::pf::tree") << "\n\nTree:\n";
        confConstraint->printProofTree(Debug("arith::pf::tree"));
        confConstraint->getNegation()->printProofTree(Debug("arith::pf::tree"));
      }

      TrustNode trustedConflict = confConstraint->externalExplainConflict();
      Node conflict = trustedConflict.getNode();

      ++conflicts;
      Debug("arith::conflict") << "d_conflicts[" << i << "] " << conflict
                               << " has proof: " << hasProof << endl;
      if(Debug.isOn("arith::normalize::external")){
        conflict = flattenAndSort(conflict);
        Debug("arith::conflict") << "(normalized to) " << conflict << endl;
      }

      if (isProofEnabled())
      {
        outputTrustedConflict(trustedConflict, conf.second);
      }
      else
      {
        outputConflict(conflict, conf.second);
      }
    }
  }
  if(!d_blackBoxConflict.get().isNull()){
    Node bb = d_blackBoxConflict.get();
    ++conflicts;
    Debug("arith::conflict") << "black box conflict" << bb
      //<< "("<<conflicts<<")"
                             << endl;
    if(Debug.isOn("arith::normalize::external")){
      bb = flattenAndSort(bb);
      Debug("arith::conflict") << "(normalized to) " << bb << endl;
    }
    if (isProofEnabled() && d_blackBoxConflictPf.get())
    {
      auto confPf = d_blackBoxConflictPf.get();
      outputTrustedConflict(d_pfGen->mkTrustNode(bb, confPf, true), InferenceId::ARITH_BLACK_BOX);
    }
    else
    {
      outputConflict(bb, InferenceId::ARITH_BLACK_BOX);
    }
  }
}

void TheoryArithPrivate::outputTrustedLemma(TrustNode lemma, InferenceId id)
{
  Debug("arith::channel") << "Arith trusted lemma: " << lemma << std::endl;
  d_containing.d_im.trustedLemma(lemma, id);
}

void TheoryArithPrivate::outputLemma(TNode lem, InferenceId id) {
  Debug("arith::channel") << "Arith lemma: " << lem << std::endl;
  d_containing.d_im.lemma(lem, id);
}

void TheoryArithPrivate::outputTrustedConflict(TrustNode conf, InferenceId id)
{
  Debug("arith::channel") << "Arith trusted conflict: " << conf << std::endl;
  d_containing.d_im.trustedConflict(conf, id);
}

void TheoryArithPrivate::outputConflict(TNode lit, InferenceId id) {
  Debug("arith::channel") << "Arith conflict: " << lit << std::endl;
  d_containing.d_im.conflict(lit, id);
}

void TheoryArithPrivate::outputPropagate(TNode lit) {
  Debug("arith::channel") << "Arith propagation: " << lit << std::endl;
  // call the propagate lit method of the
  d_containing.d_im.propagateLit(lit);
}

void TheoryArithPrivate::outputRestart() {
  Debug("arith::channel") << "Arith restart!" << std::endl;
  (d_containing.d_out)->demandRestart();
}

bool TheoryArithPrivate::attemptSolveInteger(Theory::Effort effortLevel, bool emmmittedLemmaOrSplit){
  int level = getSatContext()->getLevel();
  Debug("approx")
    << "attemptSolveInteger " << d_qflraStatus
    << " " << emmmittedLemmaOrSplit
    << " " << effortLevel
    << " " << d_lastContextIntegerAttempted
    << " " << level
    << " " << hasIntegerModel()
    << endl;

  if(d_qflraStatus == Result::UNSAT){ return false; }
  if(emmmittedLemmaOrSplit){ return false; }
  if(!options::useApprox()){ return false; }
  if(!ApproximateSimplex::enabled()){ return false; }

  if(Theory::fullEffort(effortLevel)){
    if(hasIntegerModel()){
      return false;
    }else{
      return getSolveIntegerResource();
    }
  }

  if(d_lastContextIntegerAttempted <= 0){
    if(hasIntegerModel()){
      d_lastContextIntegerAttempted = getSatContext()->getLevel();
      return false;
    }else{
      return getSolveIntegerResource();
    }
  }


  if(!options::trySolveIntStandardEffort()){ return false; }

  if (d_lastContextIntegerAttempted <= (level >> 2))
  {
    double d = (double)(d_solveIntMaybeHelp + 1)
               / (d_solveIntAttempts + 1 + level * level);
    if (Random::getRandom().pickWithProb(d))
    {
      return getSolveIntegerResource();
    }
  }
  return false;
}

bool TheoryArithPrivate::replayLog(ApproximateSimplex* approx){
  TimerStat::CodeTimer codeTimer(d_statistics.d_replayLogTimer);

  ++d_statistics.d_mipProofsAttempted;

  Assert(d_replayVariables.empty());
  Assert(d_replayConstraints.empty());

  size_t enteringPropN = d_currentPropagationList.size();
  Assert(conflictQueueEmpty());
  TreeLog& tl = getTreeLog();
  //tl.applySelected(); /* set row ids */

  d_replayedLemmas = false;

  /* use the try block for the purpose of pushing the sat context */
  context::Context::ScopedPush speculativePush(getSatContext());
  d_cmEnabled = false;
  std::vector<ConstraintCPVec> res =
      replayLogRec(approx, tl.getRootId(), NullConstraint, 1);

  if(res.empty()){
    ++d_statistics.d_replayAttemptFailed;
  }else{
    unsigned successes = 0;
    for(size_t i =0, N = res.size(); i < N; ++i){
      ConstraintCPVec& vec = res[i];
      Assert(vec.size() >= 2);
      for(size_t j=0, M = vec.size(); j < M; ++j){
        ConstraintCP at_j = vec[j];
        Assert(at_j->isTrue());
        if(!at_j->negationHasProof()){
          successes++;
          vec[j] = vec.back();
          vec.pop_back();
          ConstraintP neg_at_j = at_j->getNegation();

          Debug("approx::replayLog") << "Setting the proof for the replayLog conflict on:" << endl
                                     << "  (" << neg_at_j->isTrue() <<") " << neg_at_j << endl
                                     << "  (" << at_j->isTrue() <<") " << at_j << endl;
          neg_at_j->impliedByIntHole(vec, true);
          raiseConflict(at_j, InferenceId::UNKNOWN);
          break;
        }
      }
    }
    if(successes > 0){
      ++d_statistics.d_mipProofsSuccessful;
    }
  }

  if(d_currentPropagationList.size() > enteringPropN){
    d_currentPropagationList.resize(enteringPropN);
  }

  /* It is not clear what the d_qflraStatus is at this point */
  d_qflraStatus = Result::SAT_UNKNOWN;

  Assert(d_replayVariables.empty());
  Assert(d_replayConstraints.empty());

  return !conflictQueueEmpty();
}

std::pair<ConstraintP, ArithVar> TheoryArithPrivate::replayGetConstraint(const DenseMap<Rational>& lhs, Kind k, const Rational& rhs, bool branch)
{
  ArithVar added = ARITHVAR_SENTINEL;
  Node sum = toSumNode(d_partialModel, lhs);
  if(sum.isNull()){ return make_pair(NullConstraint, added); }

  Debug("approx::constraint") << "replayGetConstraint " << sum
                              << " " << k
                              << " " << rhs
                              << endl;

  Assert(k == kind::LEQ || k == kind::GEQ);

  Node comparison = NodeManager::currentNM()->mkNode(k, sum, mkRationalNode(rhs));
  Node rewritten = Rewriter::rewrite(comparison);
  if(!(Comparison::isNormalAtom(rewritten))){
    return make_pair(NullConstraint, added);
  }

  Comparison cmp = Comparison::parseNormalForm(rewritten);
  if(cmp.isBoolean()){ return make_pair(NullConstraint, added); }

  Polynomial nvp =  cmp.normalizedVariablePart();
  if(nvp.isZero()){ return make_pair(NullConstraint, added); }

  Node norm = nvp.getNode();

  ConstraintType t = Constraint::constraintTypeOfComparison(cmp);
  DeltaRational dr = cmp.normalizedDeltaRational();

  Debug("approx::constraint") << "rewriting " << rewritten << endl
                              << " |-> " << norm << " " << t << " " << dr << endl;

  Assert(!branch || d_partialModel.hasArithVar(norm));
  ArithVar v = ARITHVAR_SENTINEL;
  if(d_partialModel.hasArithVar(norm)){

    v = d_partialModel.asArithVar(norm);
    Debug("approx::constraint") << "replayGetConstraint found "
                                << norm << " |-> " << v << " @ " << getSatContext()->getLevel() << endl;
    Assert(!branch || d_partialModel.isIntegerInput(v));
  }else{
    v = requestArithVar(norm, true, true);
    d_replayVariables.push_back(v);

    added = v;

    Debug("approx::constraint") << "replayGetConstraint adding "
                                << norm << " |-> " << v << " @ " << getSatContext()->getLevel() << endl;

    Polynomial poly = Polynomial::parsePolynomial(norm);
    vector<ArithVar> variables;
    vector<Rational> coefficients;
    asVectors(poly, coefficients, variables);
    d_tableau.addRow(v, coefficients, variables);
    setupBasicValue(v);
    d_linEq.trackRowIndex(d_tableau.basicToRowIndex(v));
  }
  Assert(d_partialModel.hasArithVar(norm));
  Assert(d_partialModel.asArithVar(norm) == v);
  Assert(d_constraintDatabase.variableDatabaseIsSetup(v));

  ConstraintP imp = d_constraintDatabase.getBestImpliedBound(v, t, dr);
  if(imp != NullConstraint){
    if(imp->getValue() == dr){
      Assert(added == ARITHVAR_SENTINEL);
      return make_pair(imp, added);
    }
  }

  ConstraintP newc = d_constraintDatabase.getConstraint(v, t, dr);
  d_replayConstraints.push_back(newc);
  return make_pair(newc, added);
}

std::pair<ConstraintP, ArithVar> TheoryArithPrivate::replayGetConstraint(
    ApproximateSimplex* approx, const NodeLog& nl)
{
  Assert(nl.isBranch());
  Assert(d_lhsTmp.empty());

  ArithVar v = approx->getBranchVar(nl);
  if(v != ARITHVAR_SENTINEL && d_partialModel.isIntegerInput(v)){
    if(d_partialModel.hasNode(v)){
      d_lhsTmp.set(v, Rational(1));
      double dval = nl.branchValue();
      Maybe<Rational> maybe_value = ApproximateSimplex::estimateWithCFE(dval);
      if (!maybe_value)
      {
        return make_pair(NullConstraint, ARITHVAR_SENTINEL);
      }
      Rational fl(maybe_value.value().floor());
      pair<ConstraintP, ArithVar> p;
      p = replayGetConstraint(d_lhsTmp, kind::LEQ, fl, true);
      d_lhsTmp.purge();
      return p;
    }
  }
  return make_pair(NullConstraint, ARITHVAR_SENTINEL);
}

std::pair<ConstraintP, ArithVar> TheoryArithPrivate::replayGetConstraint(const CutInfo& ci) {
  Assert(ci.reconstructed());
  const DenseMap<Rational>& lhs = ci.getReconstruction().lhs;
  const Rational& rhs = ci.getReconstruction().rhs;
  Kind k = ci.getKind();

  return replayGetConstraint(lhs, k, rhs, ci.getKlass() == BranchCutKlass);
}

// Node denseVectorToLiteral(const ArithVariables& vars, const DenseVector& dv, Kind k){
//   NodeManager* nm = NodeManager::currentNM();
//   Node sumLhs = toSumNode(vars, dv.lhs);
//   Node ineq = nm->mkNode(k, sumLhs, mkRationalNode(dv.rhs) );
//   Node lit = Rewriter::rewrite(ineq);
//   return lit;
// }

Node toSumNode(const ArithVariables& vars, const DenseMap<Rational>& sum){
  Debug("arith::toSumNode") << "toSumNode() begin" << endl;
  NodeBuilder nb(kind::PLUS);
  NodeManager* nm = NodeManager::currentNM();
  DenseMap<Rational>::const_iterator iter, end;
  iter = sum.begin(), end = sum.end();
  for(; iter != end; ++iter){
    ArithVar x = *iter;
    if(!vars.hasNode(x)){ return Node::null(); }
    Node xNode = vars.asNode(x);
    const Rational& q = sum[x];
    Node mult = nm->mkNode(kind::MULT, mkRationalNode(q), xNode);
    Debug("arith::toSumNode") << "toSumNode() " << x << " " << mult << endl;
    nb << mult;
  }
  Debug("arith::toSumNode") << "toSumNode() end" << endl;
  return safeConstructNary(nb);
}

ConstraintCP TheoryArithPrivate::vectorToIntHoleConflict(const ConstraintCPVec& conflict){
  Assert(conflict.size() >= 2);
  ConstraintCPVec exp(conflict.begin(), conflict.end()-1);
  ConstraintCP back = conflict.back();
  Assert(back->hasProof());
  ConstraintP negBack = back->getNegation();
  // This can select negBack multiple times so we need to test if negBack has a proof.
  if(negBack->hasProof()){
    // back is in conflict already
  } else {
    negBack->impliedByIntHole(exp, true);
  }

  return back;
}

void TheoryArithPrivate::intHoleConflictToVector(ConstraintCP conflicting, ConstraintCPVec& conflict){
  ConstraintCP negConflicting = conflicting->getNegation();
  Assert(conflicting->hasProof());
  Assert(negConflicting->hasProof());

  conflict.push_back(conflicting);
  conflict.push_back(negConflicting);

  Constraint::assertionFringe(conflict);
}

void TheoryArithPrivate::tryBranchCut(ApproximateSimplex* approx, int nid, BranchCutInfo& bci){
  Assert(conflictQueueEmpty());
  std::vector< ConstraintCPVec > conflicts;

  approx->tryCut(nid, bci);
  Debug("approx::branch") << "tryBranchCut" << bci << endl;
  Assert(bci.reconstructed());
  Assert(!bci.proven());
  pair<ConstraintP, ArithVar> p = replayGetConstraint(bci);
  Assert(p.second == ARITHVAR_SENTINEL);
  ConstraintP bc = p.first;
  Assert(bc != NullConstraint);
  if(bc->hasProof()){
    return;
  }

  ConstraintP bcneg = bc->getNegation();
  {
    context::Context::ScopedPush speculativePush(getSatContext());
    replayAssert(bcneg);
    if(conflictQueueEmpty()){
      TimerStat::CodeTimer codeTimer(d_statistics.d_replaySimplexTimer);

      //test for linear feasibility
      d_partialModel.stopQueueingBoundCounts();
      UpdateTrackingCallback utcb(&d_linEq);
      d_partialModel.processBoundsQueue(utcb);
      d_linEq.startTrackingBoundCounts();

      SimplexDecisionProcedure& simplex = selectSimplex(true);
      simplex.findModel(false);
      // Can change d_qflraStatus

      d_linEq.stopTrackingBoundCounts();
      d_partialModel.startQueueingBoundCounts();
    }
    for(size_t i = 0, N = d_conflicts.size(); i < N; ++i){

      conflicts.push_back(ConstraintCPVec());
      intHoleConflictToVector(d_conflicts[i].first, conflicts.back());
      Constraint::assertionFringe(conflicts.back());

      // ConstraintCP conflicting = d_conflicts[i];
      // ConstraintCP negConflicting = conflicting->getNegation();
      // Assert(conflicting->hasProof());
      // Assert(negConflicting->hasProof());

      // conflicts.push_back(ConstraintCPVec());
      // ConstraintCPVec& back = conflicts.back();
      // back.push_back(conflicting);
      // back.push_back(negConflicting);

      // // remove the floor/ceiling contraint implied by bcneg
      // Constraint::assertionFringe(back);
    }

    if(Debug.isOn("approx::branch")){
      if(d_conflicts.empty()){
        entireStateIsConsistent("branchfailure");
      }
    }
  }

  Debug("approx::branch") << "branch constraint " << bc << endl;
  for(size_t i = 0, N = conflicts.size(); i < N; ++i){
    ConstraintCPVec& conf = conflicts[i];

    // make sure to be working on the assertion fringe!
    if(!contains(conf, bcneg)){
      Debug("approx::branch") << "reraise " << conf  << endl;
      ConstraintCP conflicting = vectorToIntHoleConflict(conf);
      raiseConflict(conflicting, InferenceId::UNKNOWN);
    }else if(!bci.proven()){
      drop(conf, bcneg);
      bci.setExplanation(conf);
      Debug("approx::branch") << "dropped " << bci  << endl;
    }
  }
}

void TheoryArithPrivate::replayAssert(ConstraintP c) {
  if(!c->assertedToTheTheory()){
    bool inConflict = c->negationHasProof();
    if(!c->hasProof()){
      c->setInternalAssumption(inConflict);
      Debug("approx::replayAssert") << "replayAssert " << c << " set internal" << endl;
    }else{
      Debug("approx::replayAssert") << "replayAssert " << c << " has explanation" << endl;
    }
    Debug("approx::replayAssert") << "replayAssertion " << c << endl;
    if(inConflict){
      raiseConflict(c, InferenceId::UNKNOWN);
    }else{
      assertionCases(c);
    }
  }else{
    Debug("approx::replayAssert")
        << "replayAssert " << c << " already asserted" << endl;
  }
}


void TheoryArithPrivate::resolveOutPropagated(std::vector<ConstraintCPVec>& confs, const std::set<ConstraintCP>& propagated) const {
  Debug("arith::resolveOutPropagated")
    << "starting resolveOutPropagated() " << confs.size() << endl;
  for(size_t i =0, N = confs.size(); i < N; ++i){
    ConstraintCPVec& conf = confs[i];
    size_t orig = conf.size();
    Constraint::assertionFringe(conf);
    Debug("arith::resolveOutPropagated")
      << "  conf["<<i<<"] " << orig << " to " << conf.size() << endl;
  }
  Debug("arith::resolveOutPropagated")
    << "ending resolveOutPropagated() " << confs.size() << endl;
}

struct SizeOrd {
  bool operator()(const ConstraintCPVec& a, const ConstraintCPVec& b) const{
    return a.size() < b.size();
  }
};

void TheoryArithPrivate::subsumption(
    std::vector<ConstraintCPVec> &confs) const {
  int checks CVC5_UNUSED = 0;
  int subsumed CVC5_UNUSED = 0;

  for (size_t i = 0, N = confs.size(); i < N; ++i) {
    ConstraintCPVec &conf = confs[i];
    std::sort(conf.begin(), conf.end());
  }

  std::sort(confs.begin(), confs.end(), SizeOrd());
  for (size_t i = 0; i < confs.size(); i++) {
    // i is not subsumed
    for (size_t j = i + 1; j < confs.size();) {
      ConstraintCPVec& a = confs[i];
      ConstraintCPVec& b = confs[j];
      checks++;
      bool subsumes = std::includes(a.begin(), a.end(), b.begin(), b.end());
      if (subsumes) {
        ConstraintCPVec& back = confs.back();
        b.swap(back);
        confs.pop_back();
        subsumed++;
      } else {
        j++;
      }
    }
  }
  Debug("arith::subsumption") << "subsumed " << subsumed << "/" << checks
                              << endl;
}

std::vector<ConstraintCPVec> TheoryArithPrivate::replayLogRec(ApproximateSimplex* approx, int nid, ConstraintP bc, int depth){
  ++(d_statistics.d_replayLogRecCount);
  Debug("approx::replayLogRec") << "replayLogRec()" << std::endl;

  size_t rpvars_size = d_replayVariables.size();
  size_t rpcons_size = d_replayConstraints.size();
  std::vector<ConstraintCPVec> res;

  { /* create a block for the purpose of pushing the sat context */
    context::Context::ScopedPush speculativePush(getSatContext());
    Assert(!anyConflict());
    Assert(conflictQueueEmpty());
    set<ConstraintCP> propagated;

    TreeLog& tl = getTreeLog();

    if(bc != NullConstraint){
      replayAssert(bc);
    }

    const NodeLog& nl = tl.getNode(nid);
    NodeLog::const_iterator iter = nl.begin(), end = nl.end();
    for(; conflictQueueEmpty() && iter != end; ++iter){
      CutInfo* ci = *iter;
      bool reject = false;
      //cout << "  trying " << *ci << endl;
      if(ci->getKlass() == RowsDeletedKlass){
        RowsDeleted* rd = dynamic_cast<RowsDeleted*>(ci);

        tl.applyRowsDeleted(nid, *rd);
        // The previous line modifies nl

        ++d_statistics.d_applyRowsDeleted;
      }else if(ci->getKlass() == BranchCutKlass){
        BranchCutInfo* bci = dynamic_cast<BranchCutInfo*>(ci);
        Assert(bci != NULL);
        tryBranchCut(approx, nid, *bci);

        ++d_statistics.d_branchCutsAttempted;
        if(!(conflictQueueEmpty() || ci->reconstructed())){
          ++d_statistics.d_numBranchesFailed;
        }
      }else{
        approx->tryCut(nid, *ci);
        if(ci->getKlass() == GmiCutKlass){
          ++d_statistics.d_gmiCutsAttempted;
        }else if(ci->getKlass() == MirCutKlass){
          ++d_statistics.d_mirCutsAttempted;
        }

        if(ci->reconstructed() && ci->proven()){
          const DenseMap<Rational>& row = ci->getReconstruction().lhs;
          reject = !complexityBelow(row, options::replayRejectCutSize());
        }
      }
      if(conflictQueueEmpty()){
        if(reject){
          ++d_statistics.d_cutsRejectedDuringReplay;
        }else if(ci->reconstructed()){
          // success
          ++d_statistics.d_cutsReconstructed;

          pair<ConstraintP, ArithVar> p = replayGetConstraint(*ci);
          if(p.second != ARITHVAR_SENTINEL){
            Assert(ci->getRowId() >= 1);
            tl.mapRowId(nl.getNodeId(), ci->getRowId(), p.second);
          }
          ConstraintP con = p.first;
          if(Debug.isOn("approx::replayLogRec")){
            Debug("approx::replayLogRec") << "cut was remade " << con << " " << *ci << endl;
          }

          if(ci->proven()){
            ++d_statistics.d_cutsProven;

            const ConstraintCPVec& exp = ci->getExplanation();
            // success
            if(con->isTrue()){
              Debug("approx::replayLogRec") << "not asserted?" << endl;
            }else if(!con->negationHasProof()){
              con->impliedByIntHole(exp, false);
              replayAssert(con);
              Debug("approx::replayLogRec") << "cut prop" << endl;
            }else {
              con->impliedByIntHole(exp, true);
              Debug("approx::replayLogRec") << "cut into conflict " << con << endl;
              raiseConflict(con, InferenceId::UNKNOWN);
            }
          }else{
            ++d_statistics.d_cutsProofFailed;
            Debug("approx::replayLogRec") << "failed to get proof " << *ci << endl;
          }
        }else if(ci->getKlass() != RowsDeletedKlass){
          ++d_statistics.d_cutsReconstructionFailed;
        }
      }
    }

    /* check if the system is feasible under with the cuts */
    if(conflictQueueEmpty()){
      Assert(options::replayEarlyCloseDepths() >= 1);
      if(!nl.isBranch() || depth % options::replayEarlyCloseDepths() == 0 ){
        TimerStat::CodeTimer codeTimer(d_statistics.d_replaySimplexTimer);
        //test for linear feasibility
        d_partialModel.stopQueueingBoundCounts();
        UpdateTrackingCallback utcb(&d_linEq);
        d_partialModel.processBoundsQueue(utcb);
        d_linEq.startTrackingBoundCounts();

        SimplexDecisionProcedure& simplex = selectSimplex(true);
        simplex.findModel(false);
        // can change d_qflraStatus

        d_linEq.stopTrackingBoundCounts();
        d_partialModel.startQueueingBoundCounts();
      }
    }else{
      ++d_statistics.d_replayLogRecConflictEscalation;
    }

    if(!conflictQueueEmpty()){
      /* if a conflict has been found stop */
      for(size_t i = 0, N = d_conflicts.size(); i < N; ++i){
        res.push_back(ConstraintCPVec());
        intHoleConflictToVector(d_conflicts[i].first, res.back());
      }
      ++d_statistics.d_replayLogRecEarlyExit;
    }else if(nl.isBranch()){
      /* if it is a branch try the branch */
      pair<ConstraintP, ArithVar> p = replayGetConstraint(approx, nl);
      Assert(p.second == ARITHVAR_SENTINEL);
      ConstraintP dnc = p.first;
      if(dnc != NullConstraint){
        ConstraintP upc = dnc->getNegation();

        int dnid = nl.getDownId();
        int upid = nl.getUpId();

        NodeLog& dnlog = tl.getNode(dnid);
        NodeLog& uplog = tl.getNode(upid);
        dnlog.copyParentRowIds();
        uplog.copyParentRowIds();

        std::vector<ConstraintCPVec> dnres;
        std::vector<ConstraintCPVec> upres;
        std::vector<size_t> containsdn;
        std::vector<size_t> containsup;
        if(res.empty()){
          dnres = replayLogRec(approx, dnid, dnc, depth+1);
          for(size_t i = 0, N = dnres.size(); i < N; ++i){
            ConstraintCPVec& conf = dnres[i];
            if(contains(conf, dnc)){
              containsdn.push_back(i);
            }else{
              res.push_back(conf);
            }
          }
        }else{
          Debug("approx::replayLogRec") << "replayLogRec() skipping" << dnlog << std::endl;
          ++d_statistics.d_replayBranchSkips;
        }

        if(res.empty()){
          upres = replayLogRec(approx, upid, upc, depth+1);

          for(size_t i = 0, N = upres.size(); i < N; ++i){
            ConstraintCPVec& conf = upres[i];
            if(contains(conf, upc)){
              containsup.push_back(i);
            }else{
              res.push_back(conf);
            }
          }
        }else{
          Debug("approx::replayLogRec") << "replayLogRec() skipping" << uplog << std::endl;
          ++d_statistics.d_replayBranchSkips;
        }

        if(res.empty()){
          for(size_t i = 0, N = containsdn.size(); i < N; ++i){
            ConstraintCPVec& dnconf = dnres[containsdn[i]];
            for(size_t j = 0, M = containsup.size(); j < M; ++j){
              ConstraintCPVec& upconf = upres[containsup[j]];

              res.push_back(ConstraintCPVec());
              ConstraintCPVec& back = res.back();
              resolve(back, dnc, dnconf, upconf);
            }
          }
          if(res.size() >= 2u){
            subsumption(res);

            if(res.size() > 100u){
              res.resize(100u);
            }
          }
        }else{
          Debug("approx::replayLogRec") << "replayLogRec() skipping resolving" << nl << std::endl;
        }
        Debug("approx::replayLogRec") << "found #"<<res.size()<<" conflicts on branch " << nid << endl;
        if(res.empty()){
          ++d_statistics.d_replayBranchCloseFailures;
        }

      }else{
        Debug("approx::replayLogRec") << "failed to make a branch " << nid << endl;
      }
    }else{
      ++d_statistics.d_replayLeafCloseFailures;
      Debug("approx::replayLogRec") << "failed on node " << nid << endl;
      Assert(res.empty());
    }
    resolveOutPropagated(res, propagated);
    Debug("approx::replayLogRec") << "replayLogRec() ending" << std::endl;


    if(options::replayFailureLemma()){
      // must be done inside the sat context to get things
      // propagated at this level
      if(res.empty() && nid == getTreeLog().getRootId()){
        Assert(!d_replayedLemmas);
        d_replayedLemmas = replayLemmas(approx);
        Assert(d_acTmp.empty());
        while(!d_approxCuts.empty()){
          TrustNode lem = d_approxCuts.front();
          d_approxCuts.pop();
          d_acTmp.push_back(lem);
        }
      }
    }
  } /* pop the sat context */

  /* move into the current context. */
  while(!d_acTmp.empty()){
    TrustNode lem = d_acTmp.back();
    d_acTmp.pop_back();
    d_approxCuts.push_back(lem);
  }
  Assert(d_acTmp.empty());

  /* Garbage collect the constraints from this call */
  while(d_replayConstraints.size() > rpcons_size){
    ConstraintP c = d_replayConstraints.back();
    d_replayConstraints.pop_back();
    d_constraintDatabase.deleteConstraintAndNegation(c);
  }

  /* Garbage collect the ArithVars made by this call */
  if(d_replayVariables.size() > rpvars_size){
    d_partialModel.stopQueueingBoundCounts();
    UpdateTrackingCallback utcb(&d_linEq);
    d_partialModel.processBoundsQueue(utcb);
    d_linEq.startTrackingBoundCounts();
    while(d_replayVariables.size() > rpvars_size){
      ArithVar v = d_replayVariables.back();
      d_replayVariables.pop_back();
      Assert(d_partialModel.canBeReleased(v));
      if(!d_tableau.isBasic(v)){
        /* if it is not basic make it basic. */
        ArithVar b = ARITHVAR_SENTINEL;
        for(Tableau::ColIterator ci = d_tableau.colIterator(v); !ci.atEnd(); ++ci){
          const Tableau::Entry& e = *ci;
          b = d_tableau.rowIndexToBasic(e.getRowIndex());
          break;
        }
        Assert(b != ARITHVAR_SENTINEL);
        DeltaRational cp = d_partialModel.getAssignment(b);
        if(d_partialModel.cmpAssignmentLowerBound(b) < 0){
          cp = d_partialModel.getLowerBound(b);
        }else if(d_partialModel.cmpAssignmentUpperBound(b) > 0){
          cp = d_partialModel.getUpperBound(b);
        }
        d_linEq.pivotAndUpdate(b, v, cp);
      }
      Assert(d_tableau.isBasic(v));
      d_linEq.stopTrackingRowIndex(d_tableau.basicToRowIndex(v));
      d_tableau.removeBasicRow(v);

      releaseArithVar(v);
      Debug("approx::vars") << "releasing " << v << endl;
    }
    d_linEq.stopTrackingBoundCounts();
    d_partialModel.startQueueingBoundCounts();
    d_partialModel.attemptToReclaimReleased();
  }
  return res;
}

TreeLog& TheoryArithPrivate::getTreeLog(){
  if(d_treeLog == NULL){
    d_treeLog = new TreeLog();
  }
  return *d_treeLog;
}

ApproximateStatistics& TheoryArithPrivate::getApproxStats(){
  if(d_approxStats == NULL){
    d_approxStats = new ApproximateStatistics();
  }
  return *d_approxStats;
}

Node TheoryArithPrivate::branchToNode(ApproximateSimplex* approx,
                                      const NodeLog& bn) const
{
  Assert(bn.isBranch());
  ArithVar v = approx->getBranchVar(bn);
  if(v != ARITHVAR_SENTINEL && d_partialModel.isIntegerInput(v)){
    if(d_partialModel.hasNode(v)){
      Node n = d_partialModel.asNode(v);
      double dval = bn.branchValue();
      Maybe<Rational> maybe_value = ApproximateSimplex::estimateWithCFE(dval);
      if (!maybe_value)
      {
        return Node::null();
      }
      Rational fl(maybe_value.value().floor());
      NodeManager* nm = NodeManager::currentNM();
      Node leq = nm->mkNode(kind::LEQ, n, mkRationalNode(fl));
      Node norm = Rewriter::rewrite(leq);
      return norm;
    }
  }
  return Node::null();
}

Node TheoryArithPrivate::cutToLiteral(ApproximateSimplex* approx, const CutInfo& ci) const{
  Assert(ci.reconstructed());

  const DenseMap<Rational>& lhs = ci.getReconstruction().lhs;
  Node sum = toSumNode(d_partialModel, lhs);
  if(!sum.isNull()){
    Kind k = ci.getKind();
    Assert(k == kind::LEQ || k == kind::GEQ);
    Node rhs = mkRationalNode(ci.getReconstruction().rhs);

    NodeManager* nm = NodeManager::currentNM();
    Node ineq = nm->mkNode(k, sum, rhs);
    return Rewriter::rewrite(ineq);
  }
  return Node::null();
}

bool TheoryArithPrivate::replayLemmas(ApproximateSimplex* approx){
    ++(d_statistics.d_mipReplayLemmaCalls);
    bool anythingnew = false;

    TreeLog& tl = getTreeLog();
    NodeLog& root = tl.getRootNode();
    root.applySelected(); /* set row ids */

    vector<const CutInfo*> cuts = approx->getValidCuts(root);
    for(size_t i =0, N =cuts.size(); i < N; ++i){
      const CutInfo* cut = cuts[i];
      Assert(cut->reconstructed());
      Assert(cut->proven());

      const DenseMap<Rational>& row =  cut->getReconstruction().lhs;
      if(!complexityBelow(row, options::lemmaRejectCutSize())){
        ++(d_statistics.d_cutsRejectedDuringLemmas);
        continue;
      }

      Node cutConstraint = cutToLiteral(approx, *cut);
      if(!cutConstraint.isNull()){
        const ConstraintCPVec& exp = cut->getExplanation();
        Node asLemma = Constraint::externalExplainByAssertions(exp);

        Node implied = Rewriter::rewrite(cutConstraint);
        anythingnew = anythingnew || !isSatLiteral(implied);

        Node implication = asLemma.impNode(implied);
        // DO NOT CALL OUTPUT LEMMA!
        // TODO (project #37): justify
        d_approxCuts.push_back(TrustNode::mkTrustLemma(implication, nullptr));
        Debug("approx::lemmas") << "cut["<<i<<"] " << implication << endl;
        ++(d_statistics.d_mipExternalCuts);
      }
    }
    if(root.isBranch()){
      Node lit = branchToNode(approx, root);
      if(!lit.isNull()){
        anythingnew = anythingnew || !isSatLiteral(lit);
        Node branch = lit.orNode(lit.notNode());
        if (proofsEnabled())
        {
          d_pfGen->mkTrustNode(branch, PfRule::SPLIT, {}, {lit});
        }
        else
        {
          d_approxCuts.push_back(TrustNode::mkTrustLemma(branch, nullptr));
        }
        ++(d_statistics.d_mipExternalBranch);
        Debug("approx::lemmas") << "branching "<< root <<" as " << branch << endl;
      }
    }
    return anythingnew;
}

void TheoryArithPrivate::turnOffApproxFor(int32_t rounds){
  d_attemptSolveIntTurnedOff = d_attemptSolveIntTurnedOff + rounds;
  ++(d_statistics.d_approxDisabled);
}

bool TheoryArithPrivate::safeToCallApprox() const{
  unsigned numRows = 0;
  unsigned numCols = 0;
  var_iterator vi = var_begin(), vi_end = var_end();
  // Assign each variable to a row and column variable as it appears in the input
  for(; vi != vi_end && !(numRows > 0 && numCols > 0); ++vi){
    ArithVar v = *vi;

    if(d_partialModel.isAuxiliary(v)){
      ++numRows;
    }else{
      ++numCols;
    }
  }
  return (numRows > 0 && numCols > 0);
}

// solve()
//   res = solveRealRelaxation(effortLevel);
//   switch(res){
//   case LinFeas:
//   case LinInfeas:
//     return replay()
//   case Unknown:
//   case Error
//     if()
void TheoryArithPrivate::solveInteger(Theory::Effort effortLevel){
  if(!safeToCallApprox()) { return; }

  Assert(safeToCallApprox());
  TimerStat::CodeTimer codeTimer0(d_statistics.d_solveIntTimer);

  ++(d_statistics.d_solveIntCalls);
  d_statistics.d_inSolveInteger = 1;

  if(!Theory::fullEffort(effortLevel)){
    d_solveIntAttempts++;
    ++(d_statistics.d_solveStandardEffort);
  }

  // if integers are attempted,
  Assert(options::useApprox());
  Assert(ApproximateSimplex::enabled());

  int level = getSatContext()->getLevel();
  d_lastContextIntegerAttempted = level;


  static const int32_t mipLimit = 200000;

  TreeLog& tl = getTreeLog();
  ApproximateStatistics& stats = getApproxStats();
  ApproximateSimplex* approx =
    ApproximateSimplex::mkApproximateSimplexSolver(d_partialModel, tl, stats);

    approx->setPivotLimit(mipLimit);
    if(!d_guessedCoeffSet){
      d_guessedCoeffs = approx->heuristicOptCoeffs();
      d_guessedCoeffSet = true;
    }
    if(!d_guessedCoeffs.empty()){
      approx->setOptCoeffs(d_guessedCoeffs);
    }
    static const int32_t depthForLikelyInfeasible = 10;
    int maxDepthPass1 = d_likelyIntegerInfeasible ?
      depthForLikelyInfeasible : options::maxApproxDepth();
    approx->setBranchingDepth(maxDepthPass1);
    approx->setBranchOnVariableLimit(100);
    LinResult relaxRes = approx->solveRelaxation();
    if( relaxRes == LinFeasible ){
      MipResult mipRes = MipUnknown;
      {
        TimerStat::CodeTimer codeTimer1(d_statistics.d_mipTimer);
        mipRes = approx->solveMIP(false);
      }

      Debug("arith::solveInteger") << "mipRes " << mipRes << endl;
      switch(mipRes) {
      case MipBingo:
        // attempt the solution
        {
          ++(d_statistics.d_solveIntModelsAttempts);

          d_partialModel.stopQueueingBoundCounts();
          UpdateTrackingCallback utcb(&d_linEq);
          d_partialModel.processBoundsQueue(utcb);
          d_linEq.startTrackingBoundCounts();

          ApproximateSimplex::Solution mipSolution;
          mipSolution = approx->extractMIP();
          importSolution(mipSolution);
          solveRelaxationOrPanic(effortLevel);

          if (d_qflraStatus == Result::SAT)
          {
            if (!anyConflict())
            {
              if (ARITHVAR_SENTINEL == nextIntegerViolation(false))
              {
                ++(d_statistics.d_solveIntModelsSuccessful);
              }
            }
          }

          // shutdown simplex
          d_linEq.stopTrackingBoundCounts();
          d_partialModel.startQueueingBoundCounts();
        }
        break;
      case MipClosed:
        /* All integer branches closed */
        approx->setPivotLimit(2*mipLimit);
        {
          TimerStat::CodeTimer codeTimer2(d_statistics.d_mipTimer);
          mipRes = approx->solveMIP(true);
        }

        if(mipRes == MipClosed){
          d_likelyIntegerInfeasible = true;
          replayLog(approx);
          AlwaysAssert(anyConflict() || d_qflraStatus != Result::SAT);

          if (!anyConflict())
          {
            solveRealRelaxation(effortLevel);
          }
        }
        if(!(anyConflict() || !d_approxCuts.empty())){
          turnOffApproxFor(options::replayNumericFailurePenalty());
        }
        break;
      case BranchesExhausted:
      case ExecExhausted:
      case PivotsExhauasted:
        if(mipRes == BranchesExhausted){
          ++d_statistics.d_branchesExhausted;
        }else if(mipRes == ExecExhausted){
          ++d_statistics.d_execExhausted;
        }else if(mipRes == PivotsExhauasted){
          ++d_statistics.d_pivotsExhausted;
        }

        approx->setPivotLimit(2*mipLimit);
        approx->setBranchingDepth(2);
        {
          TimerStat::CodeTimer codeTimer3(d_statistics.d_mipTimer);
          mipRes = approx->solveMIP(true);
        }
        replayLemmas(approx);
        break;
      case MipUnknown:
        break;
      }
    }
  delete approx;

  if(!Theory::fullEffort(effortLevel)){
    if(anyConflict() || !d_approxCuts.empty()){
      d_solveIntMaybeHelp++;
    }
  }

  d_statistics.d_inSolveInteger = 0;
}

SimplexDecisionProcedure& TheoryArithPrivate::selectSimplex(bool pass1){
  if(pass1){
    if(d_pass1SDP == NULL){
      if(options::useFC()){
        d_pass1SDP = (SimplexDecisionProcedure*)(&d_fcSimplex);
      }else if(options::useSOI()){
        d_pass1SDP = (SimplexDecisionProcedure*)(&d_soiSimplex);
      }else{
        d_pass1SDP = (SimplexDecisionProcedure*)(&d_dualSimplex);
      }
    }
    Assert(d_pass1SDP != NULL);
    return *d_pass1SDP;
  }else{
     if(d_otherSDP == NULL){
      if(options::useFC()){
        d_otherSDP  = (SimplexDecisionProcedure*)(&d_fcSimplex);
      }else if(options::useSOI()){
        d_otherSDP = (SimplexDecisionProcedure*)(&d_soiSimplex);
      }else{
        d_otherSDP = (SimplexDecisionProcedure*)(&d_soiSimplex);
      }
    }
    Assert(d_otherSDP != NULL);
    return *d_otherSDP;
  }
}

void TheoryArithPrivate::importSolution(const ApproximateSimplex::Solution& solution){
  if(Debug.isOn("arith::importSolution")){
    Debug("arith::importSolution") << "importSolution before " << d_qflraStatus << endl;
    d_partialModel.printEntireModel(Debug("arith::importSolution"));
  }

  d_qflraStatus = d_attemptSolSimplex.attempt(solution);

  if(Debug.isOn("arith::importSolution")){
    Debug("arith::importSolution") << "importSolution intermediate " << d_qflraStatus << endl;
    d_partialModel.printEntireModel(Debug("arith::importSolution"));
  }

  if(d_qflraStatus != Result::UNSAT){
    static const int32_t pass2Limit = 20;
    int16_t oldCap = options::arithStandardCheckVarOrderPivots();
    Options::current().arith.arithStandardCheckVarOrderPivots = pass2Limit;
    SimplexDecisionProcedure& simplex = selectSimplex(false);
    d_qflraStatus = simplex.findModel(false);
    Options::current().arith.arithStandardCheckVarOrderPivots = oldCap;
  }

  if(Debug.isOn("arith::importSolution")){
    Debug("arith::importSolution") << "importSolution after " << d_qflraStatus << endl;
    d_partialModel.printEntireModel(Debug("arith::importSolution"));
  }
}

bool TheoryArithPrivate::solveRelaxationOrPanic(Theory::Effort effortLevel)
{
  // if at this point the linear relaxation is still unknown,
  //  attempt to branch an integer variable as a last ditch effort on full check
  if (d_qflraStatus == Result::SAT_UNKNOWN)
  {
    d_qflraStatus = selectSimplex(true).findModel(false);
  }

  if (Theory::fullEffort(effortLevel) && d_qflraStatus == Result::SAT_UNKNOWN)
  {
    ArithVar canBranch = nextIntegerViolation(false);
    if (canBranch != ARITHVAR_SENTINEL)
    {
      ++d_statistics.d_panicBranches;
      TrustNode branch = branchIntegerVariable(canBranch);
      Assert(branch.getNode().getKind() == kind::OR);
      Node rwbranch = Rewriter::rewrite(branch.getNode()[0]);
      if (!isSatLiteral(rwbranch))
      {
        d_approxCuts.push_back(branch);
        return true;
      }
    }
    d_qflraStatus = selectSimplex(false).findModel(true);
  }
  return false;
}

bool TheoryArithPrivate::solveRealRelaxation(Theory::Effort effortLevel){
  TimerStat::CodeTimer codeTimer0(d_statistics.d_solveRealRelaxTimer);
  Assert(d_qflraStatus != Result::SAT);

  d_partialModel.stopQueueingBoundCounts();
  UpdateTrackingCallback utcb(&d_linEq);
  d_partialModel.processBoundsQueue(utcb);
  d_linEq.startTrackingBoundCounts();

  bool noPivotLimit = Theory::fullEffort(effortLevel) ||
    !options::restrictedPivots();

  SimplexDecisionProcedure& simplex = selectSimplex(true);

  bool useApprox = options::useApprox() && ApproximateSimplex::enabled() && getSolveIntegerResource();

  Debug("TheoryArithPrivate::solveRealRelaxation")
    << "solveRealRelaxation() approx"
    << " " <<  options::useApprox()
    << " " << ApproximateSimplex::enabled()
    << " " << useApprox
    << " " << safeToCallApprox()
    << endl;

  bool noPivotLimitPass1 = noPivotLimit && !useApprox;
  d_qflraStatus = simplex.findModel(noPivotLimitPass1);

  Debug("TheoryArithPrivate::solveRealRelaxation")
    << "solveRealRelaxation()" << " pass1 " << d_qflraStatus << endl;

  if(d_qflraStatus == Result::SAT_UNKNOWN && useApprox && safeToCallApprox()){
    // pass2: fancy-final
    static const int32_t relaxationLimit = 10000;
    Assert(ApproximateSimplex::enabled());

    TreeLog& tl = getTreeLog();
    ApproximateStatistics& stats = getApproxStats();
    ApproximateSimplex* approxSolver =
      ApproximateSimplex::mkApproximateSimplexSolver(d_partialModel, tl, stats);

    approxSolver->setPivotLimit(relaxationLimit);

    if(!d_guessedCoeffSet){
      d_guessedCoeffs = approxSolver->heuristicOptCoeffs();
      d_guessedCoeffSet = true;
    }
    if(!d_guessedCoeffs.empty()){
      approxSolver->setOptCoeffs(d_guessedCoeffs);
    }

    ++d_statistics.d_relaxCalls;

    ApproximateSimplex::Solution relaxSolution;
    LinResult relaxRes = LinUnknown;
    {
      TimerStat::CodeTimer codeTimer1(d_statistics.d_lpTimer);
      relaxRes = approxSolver->solveRelaxation();
    }
      Debug("solveRealRelaxation") << "solve relaxation? " << endl;
      switch(relaxRes){
      case LinFeasible:
        Debug("solveRealRelaxation") << "lin feasible? " << endl;
        ++d_statistics.d_relaxLinFeas;
        relaxSolution = approxSolver->extractRelaxation();
        importSolution(relaxSolution);
        if(d_qflraStatus != Result::SAT){
          ++d_statistics.d_relaxLinFeasFailures;
        }
        break;
      case LinInfeasible:
        // todo attempt to recreate approximate conflict
        ++d_statistics.d_relaxLinInfeas;
        Debug("solveRealRelaxation") << "lin infeasible " << endl;
        relaxSolution = approxSolver->extractRelaxation();
        importSolution(relaxSolution);
        if(d_qflraStatus != Result::UNSAT){
          ++d_statistics.d_relaxLinInfeasFailures;
        }
        break;
      case LinExhausted:
        ++d_statistics.d_relaxLinExhausted;
        Debug("solveRealRelaxation") << "exhuasted " << endl;
        break;
      case LinUnknown:
      default:
        ++d_statistics.d_relaxOthers;
        break;
      }
    delete approxSolver;

  }

  bool emmittedConflictOrSplit = solveRelaxationOrPanic(effortLevel);

  // TODO Save zeroes with no conflicts
  d_linEq.stopTrackingBoundCounts();
  d_partialModel.startQueueingBoundCounts();

  return emmittedConflictOrSplit;
}

bool TheoryArithPrivate::hasFreshArithLiteral(Node n) const{
  switch(n.getKind()){
  case kind::LEQ:
  case kind::GEQ:
  case kind::GT:
  case kind::LT:
    return !isSatLiteral(n);
  case kind::EQUAL:
    if(n[0].getType().isReal()){
      return !isSatLiteral(n);
    }else if(n[0].getType().isBoolean()){
      return hasFreshArithLiteral(n[0]) ||
        hasFreshArithLiteral(n[1]);
    }else{
      return false;
    }
  case kind::IMPLIES:
    // try the rhs first
    return hasFreshArithLiteral(n[1]) ||
      hasFreshArithLiteral(n[0]);
  default:
    if(n.getType().isBoolean()){
      for(Node::iterator ni=n.begin(), nend=n.end(); ni!=nend; ++ni){
        Node child = *ni;
        if(hasFreshArithLiteral(child)){
          return true;
        }
      }
    }
    return false;
  }
}

bool TheoryArithPrivate::preCheck(Theory::Effort level)
{
  Assert(d_currentPropagationList.empty());
  if(Debug.isOn("arith::consistency")){
    Assert(unenqueuedVariablesAreConsistent());
  }

  d_newFacts = !done();
  // If d_previousStatus == SAT, then reverts on conflicts are safe
  // Otherwise, they are not and must be committed.
  d_previousStatus = d_qflraStatus;
  if (d_newFacts)
  {
    d_qflraStatus = Result::SAT_UNKNOWN;
    d_hasDoneWorkSinceCut = true;
  }
  return false;
}

void TheoryArithPrivate::preNotifyFact(TNode atom, bool pol, TNode fact)
{
  ConstraintP curr = constraintFromFactQueue(fact);
  if (curr != NullConstraint)
  {
    bool res CVC5_UNUSED = assertionCases(curr);
    Assert(!res || anyConflict());
  }
}

bool TheoryArithPrivate::postCheck(Theory::Effort effortLevel)
{
  if(!anyConflict()){
    while(!d_learnedBounds.empty()){
      // we may attempt some constraints twice.  this is okay!
      ConstraintP curr = d_learnedBounds.front();
      d_learnedBounds.pop();
      Debug("arith::learned") << curr << endl;

      bool res CVC5_UNUSED = assertionCases(curr);
      Assert(!res || anyConflict());

      if(anyConflict()){ break; }
    }
  }

  if(anyConflict()){
    d_qflraStatus = Result::UNSAT;
    if (options::revertArithModels() && d_previousStatus == Result::SAT)
    {
      ++d_statistics.d_revertsOnConflicts;
      Debug("arith::bt") << "clearing here "
                         << " " << d_newFacts << " " << d_previousStatus << " "
                         << d_qflraStatus << endl;
      revertOutOfConflict();
      d_errorSet.clear();
    }else{
      ++d_statistics.d_commitsOnConflicts;
      Debug("arith::bt") << "committing here "
                         << " " << d_newFacts << " " << d_previousStatus << " "
                         << d_qflraStatus << endl;
      d_partialModel.commitAssignmentChanges();
      revertOutOfConflict();
    }
    outputConflicts();
    //cout << "unate conflict 1 " << effortLevel << std::endl;
    return true;
  }


  if(Debug.isOn("arith::print_assertions")) {
    debugPrintAssertions(Debug("arith::print_assertions"));
  }

  bool emmittedConflictOrSplit = false;
  Assert(d_conflicts.empty());

  bool useSimplex = d_qflraStatus != Result::SAT;
  Debug("arith::ems") << "ems: " << emmittedConflictOrSplit
                      << "pre realRelax" << endl;

  if(useSimplex){
    emmittedConflictOrSplit = solveRealRelaxation(effortLevel);
  }
  Debug("arith::ems") << "ems: " << emmittedConflictOrSplit
                      << "post realRelax" << endl;


  Debug("arith::ems") << "ems: " << emmittedConflictOrSplit
                      << "pre solveInteger" << endl;

  if(attemptSolveInteger(effortLevel, emmittedConflictOrSplit)){
    solveInteger(effortLevel);
    if(anyConflict()){
      ++d_statistics.d_commitsOnConflicts;
      Debug("arith::bt") << "committing here "
                         << " " << d_newFacts << " " << d_previousStatus << " "
                         << d_qflraStatus << endl;
      revertOutOfConflict();
      d_errorSet.clear();
      outputConflicts();
      return true;
    }
  }

  Debug("arith::ems") << "ems: " << emmittedConflictOrSplit
                      << "post solveInteger" << endl;

  switch(d_qflraStatus){
  case Result::SAT:
    if (d_newFacts)
    {
      ++d_statistics.d_nontrivialSatChecks;
    }

    Debug("arith::bt") << "committing sap inConflit"
                       << " " << d_newFacts << " " << d_previousStatus << " "
                       << d_qflraStatus << endl;
    d_partialModel.commitAssignmentChanges();
    d_unknownsInARow = 0;
    if(Debug.isOn("arith::consistency")){
      Assert(entireStateIsConsistent("sat comit"));
    }
    if(useSimplex && options::collectPivots()){
      if(options::useFC()){
        d_statistics.d_satPivots << d_fcSimplex.getPivots();
      }else{
        d_statistics.d_satPivots << d_dualSimplex.getPivots();
      }
    }
    break;
  case Result::SAT_UNKNOWN:
    ++d_unknownsInARow;
    ++(d_statistics.d_unknownChecks);
    Assert(!Theory::fullEffort(effortLevel));
    Debug("arith::bt") << "committing unknown"
                       << " " << d_newFacts << " " << d_previousStatus << " "
                       << d_qflraStatus << endl;
    d_partialModel.commitAssignmentChanges();
    d_statistics.d_maxUnknownsInARow.maxAssign(d_unknownsInARow);

    if(useSimplex && options::collectPivots()){
      if(options::useFC()){
        d_statistics.d_unknownPivots << d_fcSimplex.getPivots();
      }else{
        d_statistics.d_unknownPivots << d_dualSimplex.getPivots();
      }
    }
    break;
  case Result::UNSAT:
    d_unknownsInARow = 0;

    ++d_statistics.d_commitsOnConflicts;

    Debug("arith::bt") << "committing on conflict"
                       << " " << d_newFacts << " " << d_previousStatus << " "
                       << d_qflraStatus << endl;
    d_partialModel.commitAssignmentChanges();
    revertOutOfConflict();

    if(Debug.isOn("arith::consistency::comitonconflict")){
      entireStateIsConsistent("commit on conflict");
    }
    outputConflicts();
    emmittedConflictOrSplit = true;
    Debug("arith::conflict") << "simplex conflict" << endl;

    if(useSimplex && options::collectPivots()){
      if(options::useFC()){
        d_statistics.d_unsatPivots << d_fcSimplex.getPivots();
      }else{
        d_statistics.d_unsatPivots << d_dualSimplex.getPivots();
      }
    }
    break;
  default:
    Unimplemented();
  }
  d_statistics.d_avgUnknownsInARow << d_unknownsInARow;

  size_t nPivots =
      options::useFC() ? d_fcSimplex.getPivots() : d_dualSimplex.getPivots();
  for (std::size_t i = 0; i < nPivots; ++i)
  {
    d_containing.d_out->spendResource(
        Resource::ArithPivotStep);
  }

  Debug("arith::ems") << "ems: " << emmittedConflictOrSplit
                      << "pre approx cuts" << endl;
  if(!d_approxCuts.empty()){
    bool anyFresh = false;
    while(!d_approxCuts.empty()){
      TrustNode lem = d_approxCuts.front();
      d_approxCuts.pop();
      Debug("arith::approx::cuts") << "approximate cut:" << lem << endl;
      anyFresh = anyFresh || hasFreshArithLiteral(lem.getNode());
      Debug("arith::lemma") << "approximate cut:" << lem << endl;
      outputTrustedLemma(lem, InferenceId::ARITH_APPROX_CUT);
    }
    if(anyFresh){
      emmittedConflictOrSplit = true;
    }
  }

  Debug("arith::ems") << "ems: " << emmittedConflictOrSplit
                      << "post approx cuts" << endl;

  // This should be fine if sat or unknown
  if (!emmittedConflictOrSplit
      && (options::arithPropagationMode()
              == options::ArithPropagationMode::UNATE_PROP
          || options::arithPropagationMode()
                 == options::ArithPropagationMode::BOTH_PROP))
  {
    TimerStat::CodeTimer codeTimer0(d_statistics.d_newPropTime);
    Assert(d_qflraStatus != Result::UNSAT);

    while(!d_currentPropagationList.empty()  && !anyConflict()){
      ConstraintP curr = d_currentPropagationList.front();
      d_currentPropagationList.pop_front();

      ConstraintType t = curr->getType();
      Assert(t != Disequality)
          << "Disequalities are not allowed in d_currentPropagation";

      switch(t){
      case LowerBound:
        {
          ConstraintP prev = d_currentPropagationList.front();
          d_currentPropagationList.pop_front();
          d_constraintDatabase.unatePropLowerBound(curr, prev);
          break;
        }
      case UpperBound:
        {
          ConstraintP prev = d_currentPropagationList.front();
          d_currentPropagationList.pop_front();
          d_constraintDatabase.unatePropUpperBound(curr, prev);
          break;
        }
      case Equality:
        {
          ConstraintP prevLB = d_currentPropagationList.front();
          d_currentPropagationList.pop_front();
          ConstraintP prevUB = d_currentPropagationList.front();
          d_currentPropagationList.pop_front();
          d_constraintDatabase.unatePropEquality(curr, prevLB, prevUB);
          break;
        }
        default: Unhandled() << curr->getType();
      }
    }

    if(anyConflict()){
      Debug("arith::unate") << "unate conflict" << endl;
      revertOutOfConflict();
      d_qflraStatus = Result::UNSAT;
      outputConflicts();
      emmittedConflictOrSplit = true;
      //cout << "unate conflict " << endl;
      Debug("arith::bt") << "committing on unate conflict"
                         << " " << d_newFacts << " " << d_previousStatus << " "
                         << d_qflraStatus << endl;

      Debug("arith::conflict") << "unate arith conflict" << endl;
    }
  }
  else
  {
    TimerStat::CodeTimer codeTimer1(d_statistics.d_newPropTime);
    d_currentPropagationList.clear();
  }
  Assert(d_currentPropagationList.empty());

  Debug("arith::ems") << "ems: " << emmittedConflictOrSplit
                      << "post unate" << endl;

  if(!emmittedConflictOrSplit && Theory::fullEffort(effortLevel)){
    ++d_fullCheckCounter;
  }
  if(!emmittedConflictOrSplit && Theory::fullEffort(effortLevel)){
    emmittedConflictOrSplit = splitDisequalities();
  }
  Debug("arith::ems") << "ems: " << emmittedConflictOrSplit
                      << "pos splitting" << endl;


  Debug("arith") << "integer? "
       << " conf/split " << emmittedConflictOrSplit
       << " fulleffort " << Theory::fullEffort(effortLevel)
       << " hasintmodel " << hasIntegerModel() << endl;

  if(!emmittedConflictOrSplit && Theory::fullEffort(effortLevel) && !hasIntegerModel()){
    Node possibleConflict = Node::null();
    if(!emmittedConflictOrSplit && options::arithDioSolver()){
      possibleConflict = callDioSolver();
      if(possibleConflict != Node::null()){
        revertOutOfConflict();
        Debug("arith::conflict") << "dio conflict   " << possibleConflict << endl;
        // TODO (project #37): justify (proofs in the DIO solver)
        raiseBlackBoxConflict(possibleConflict);
        outputConflicts();
        emmittedConflictOrSplit = true;
      }
    }

    if(!emmittedConflictOrSplit && d_hasDoneWorkSinceCut && options::arithDioSolver()){
      if(getDioCuttingResource()){
        TrustNode possibleLemma = dioCutting();
        if(!possibleLemma.isNull()){
          emmittedConflictOrSplit = true;
          d_hasDoneWorkSinceCut = false;
          d_cutCount = d_cutCount + 1;
          Debug("arith::lemma") << "dio cut   " << possibleLemma << endl;
          outputTrustedLemma(possibleLemma, InferenceId::ARITH_DIO_CUT);
        }
      }
    }

    if(!emmittedConflictOrSplit) {
      TrustNode possibleLemma = roundRobinBranch();
      if (!possibleLemma.getNode().isNull())
      {
        ++(d_statistics.d_externalBranchAndBounds);
        d_cutCount = d_cutCount + 1;
        emmittedConflictOrSplit = true;
        Debug("arith::lemma") << "rrbranch lemma"
                              << possibleLemma << endl;
        outputTrustedLemma(possibleLemma, InferenceId::ARITH_BB_LEMMA);
      }
    }

    if(options::maxCutsInContext() <= d_cutCount){
      if(d_diosolver.hasMoreDecompositionLemmas()){
        while(d_diosolver.hasMoreDecompositionLemmas()){
          Node decompositionLemma = d_diosolver.nextDecompositionLemma();
          Debug("arith::lemma") << "dio decomposition lemma "
                                << decompositionLemma << endl;
          outputLemma(decompositionLemma, InferenceId::ARITH_DIO_DECOMPOSITION);
        }
      }else{
        Debug("arith::restart") << "arith restart!" << endl;
        outputRestart();
      }
    }
  }//if !emmittedConflictOrSplit && fullEffort(effortLevel) && !hasIntegerModel()

  if(Theory::fullEffort(effortLevel)){
    if(Debug.isOn("arith::consistency::final")){
      entireStateIsConsistent("arith::consistency::final");
    }
  }

  if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }
  if(Debug.isOn("arith::print_model")) {
    debugPrintModel(Debug("arith::print_model"));
  }
  Debug("arith") << "TheoryArithPrivate::check end" << std::endl;
  return emmittedConflictOrSplit;
}

bool TheoryArithPrivate::foundNonlinear() const { return d_foundNl; }

TrustNode TheoryArithPrivate::branchIntegerVariable(ArithVar x) const
{
  const DeltaRational& d = d_partialModel.getAssignment(x);
  Assert(!d.isIntegral());
  const Rational& r = d.getNoninfinitesimalPart();
  const Rational& i = d.getInfinitesimalPart();
  Trace("integers") << "integers: assignment to [[" << d_partialModel.asNode(x) << "]] is " << r << "[" << i << "]" << endl;

  Assert(!(r.getDenominator() == 1 && i.getNumerator() == 0));
  Assert(!d.isIntegral());
  TNode var = d_partialModel.asNode(x);
  Integer floor_d = d.floor();

  TrustNode lem = TrustNode::null();
  NodeManager* nm = NodeManager::currentNM();
  if (options::brabTest())
  {
    Trace("integers") << "branch-round-and-bound enabled" << endl;
    Integer ceil_d = d.ceiling();
    Rational f = r - floor_d;
    // Multiply by -1 to get abs value.
    Rational c = (r - ceil_d) * (-1);
    Integer nearest = (c > f) ? floor_d : ceil_d;

    // Prioritize trying a simple rounding of the real solution first,
    // it that fails, fall back on original branch and bound strategy.
    Node ub = Rewriter::rewrite(
        nm->mkNode(kind::LEQ, var, mkRationalNode(nearest - 1)));
    Node lb = Rewriter::rewrite(
        nm->mkNode(kind::GEQ, var, mkRationalNode(nearest + 1)));
    Node right = nm->mkNode(kind::OR, ub, lb);
    Node rawEq = nm->mkNode(kind::EQUAL, var, mkRationalNode(nearest));
    Node eq = Rewriter::rewrite(rawEq);
    // Also preprocess it before we send it out. This is important since
    // arithmetic may prefer eliminating equalities.
    TrustNode teq;
    if (Theory::theoryOf(eq) == THEORY_ARITH)
    {
      teq = d_containing.ppRewriteEq(eq);
      eq = teq.isNull() ? eq : teq.getNode();
    }
    Node literal = d_containing.getValuation().ensureLiteral(eq);
    Trace("integers") << "eq: " << eq << "\nto: " << literal << endl;
    d_containing.getOutputChannel().requirePhase(literal, true);
    Node l = nm->mkNode(kind::OR, literal, right);
    Trace("integers") << "l: " << l << endl;
    if (proofsEnabled())
    {
      Node less = nm->mkNode(kind::LT, var, mkRationalNode(nearest));
      Node greater = nm->mkNode(kind::GT, var, mkRationalNode(nearest));
      // TODO (project #37): justify. Thread proofs through *ensureLiteral*.
      Debug("integers::pf") << "less: " << less << endl;
      Debug("integers::pf") << "greater: " << greater << endl;
      Debug("integers::pf") << "literal: " << literal << endl;
      Debug("integers::pf") << "eq: " << eq << endl;
      Debug("integers::pf") << "rawEq: " << rawEq << endl;
      Pf pfNotLit = d_pnm->mkAssume(literal.negate());
      // rewrite notLiteral to notRawEq, using teq.
      Pf pfNotRawEq =
          literal == rawEq
              ? pfNotLit
              : d_pnm->mkNode(
                  PfRule::MACRO_SR_PRED_TRANSFORM,
                  {pfNotLit, teq.getGenerator()->getProofFor(teq.getProven())},
                  {rawEq.negate()});
      Pf pfBot =
          d_pnm->mkNode(PfRule::CONTRA,
                        {d_pnm->mkNode(PfRule::ARITH_TRICHOTOMY,
                                       {d_pnm->mkAssume(less.negate()), pfNotRawEq},
                                       {greater}),
                         d_pnm->mkAssume(greater.negate())},
                        {});
      std::vector<Node> assumptions = {
          literal.negate(), less.negate(), greater.negate()};
      // Proof of (not (and (not (= v i)) (not (< v i)) (not (> v i))))
      Pf pfNotAnd = d_pnm->mkScope(pfBot, assumptions);
      Pf pfL = d_pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM,
                             {d_pnm->mkNode(PfRule::NOT_AND, {pfNotAnd}, {})},
                             {l});
      lem = d_pfGen->mkTrustNode(l, pfL);
    }
    else
    {
      lem = TrustNode::mkTrustLemma(l, nullptr);
    }
  }
  else
  {
    Node ub =
        Rewriter::rewrite(nm->mkNode(kind::LEQ, var, mkRationalNode(floor_d)));
    Node lb = ub.notNode();
    if (proofsEnabled())
    {
      lem = d_pfGen->mkTrustNode(
          nm->mkNode(kind::OR, ub, lb), PfRule::SPLIT, {}, {ub});
    }
    else
    {
      lem = TrustNode::mkTrustLemma(nm->mkNode(kind::OR, ub, lb), nullptr);
    }
  }

  Trace("integers") << "integers: branch & bound: " << lem << endl;
  if (Debug.isOn("integers"))
  {
    Node l = lem.getNode();
    if (isSatLiteral(l[0]))
    {
      Debug("integers") << "    " << l[0] << " == " << getSatValue(l[0])
                        << endl;
    }
    else
    {
      Debug("integers") << "    " << l[0] << " is not assigned a SAT literal"
                        << endl;
    }
    if (isSatLiteral(l[1]))
    {
      Debug("integers") << "    " << l[1] << " == " << getSatValue(l[1])
                        << endl;
    }
    else
    {
      Debug("integers") << "    " << l[1] << " is not assigned a SAT literal"
                        << endl;
    }
  }
  return lem;
}

std::vector<ArithVar> TheoryArithPrivate::cutAllBounded() const{
  vector<ArithVar> lemmas;
  ArithVar max = d_partialModel.getNumberOfVariables();

  if(options::doCutAllBounded() && max > 0){
    for(ArithVar iter = 0; iter != max; ++iter){
    //Do not include slack variables
      const DeltaRational& d = d_partialModel.getAssignment(iter);
      if(isIntegerInput(iter) &&
         !d_cutInContext.contains(iter) &&
         d_partialModel.hasUpperBound(iter) &&
         d_partialModel.hasLowerBound(iter) &&
         !d.isIntegral()){
        lemmas.push_back(iter);
      }
    }
  }
  return lemmas;
}

/** Returns true if the roundRobinBranching() issues a lemma. */
TrustNode TheoryArithPrivate::roundRobinBranch()
{
  if(hasIntegerModel()){
    return TrustNode::null();
  }else{
    ArithVar v = d_nextIntegerCheckVar;

    Assert(isInteger(v));
    Assert(!isAuxiliaryVariable(v));
    return branchIntegerVariable(v);
  }
}

bool TheoryArithPrivate::splitDisequalities(){
  bool splitSomething = false;

  vector<ConstraintP> save;

  while(!d_diseqQueue.empty()){
    ConstraintP front = d_diseqQueue.front();
    d_diseqQueue.pop();

    if(front->isSplit()){
      Debug("arith::eq") << "split already" << endl;
    }else{
      Debug("arith::eq") << "not split already" << endl;

      ArithVar lhsVar = front->getVariable();

      const DeltaRational& lhsValue = d_partialModel.getAssignment(lhsVar);
      const DeltaRational& rhsValue = front->getValue();
      if(lhsValue == rhsValue){
        Debug("arith::lemma") << "Splitting on " << front << endl;
        Debug("arith::lemma") << "LHS value = " << lhsValue << endl;
        Debug("arith::lemma") << "RHS value = " << rhsValue << endl;
        TrustNode lemma = front->split();
        ++(d_statistics.d_statDisequalitySplits);

        Debug("arith::lemma")
            << "Now " << Rewriter::rewrite(lemma.getNode()) << endl;
        outputTrustedLemma(lemma, InferenceId::ARITH_SPLIT_DEQ);
        //cout << "Now " << Rewriter::rewrite(lemma) << endl;
        splitSomething = true;
      }else if(d_partialModel.strictlyLessThanLowerBound(lhsVar, rhsValue)){
        Debug("arith::eq") << "can drop as less than lb" << front << endl;
      }else if(d_partialModel.strictlyGreaterThanUpperBound(lhsVar, rhsValue)){
        Debug("arith::eq") << "can drop as greater than ub" << front << endl;
      }else{
        Debug("arith::eq") << "save" << front << ": " <<lhsValue << " != " << rhsValue << endl;
        save.push_back(front);
      }
    }
  }
  vector<ConstraintP>::const_iterator i=save.begin(), i_end = save.end();
  for(; i != i_end; ++i){
    d_diseqQueue.push(*i);
  }
  return splitSomething;
}

/**
 * Should be guarded by at least Debug.isOn("arith::print_assertions").
 * Prints to Debug("arith::print_assertions")
 */
void TheoryArithPrivate::debugPrintAssertions(std::ostream& out) const {
  out << "Assertions:" << endl;
  for (var_iterator vi = var_begin(), vend = var_end(); vi != vend; ++vi){
    ArithVar i = *vi;
    if (d_partialModel.hasLowerBound(i)) {
      ConstraintP lConstr = d_partialModel.getLowerBoundConstraint(i);
      out << lConstr << endl;
    }

    if (d_partialModel.hasUpperBound(i)) {
      ConstraintP uConstr = d_partialModel.getUpperBoundConstraint(i);
      out << uConstr << endl;
    }
  }
  context::CDQueue<ConstraintP>::const_iterator it = d_diseqQueue.begin();
  context::CDQueue<ConstraintP>::const_iterator it_end = d_diseqQueue.end();
  for(; it != it_end; ++ it) {
    out << *it << endl;
  }
}

void TheoryArithPrivate::debugPrintModel(std::ostream& out) const{
  out << "Model:" << endl;
  for (var_iterator vi = var_begin(), vend = var_end(); vi != vend; ++vi){
    ArithVar i = *vi;
    if(d_partialModel.hasNode(i)){
      out << d_partialModel.asNode(i) << " : " <<
        d_partialModel.getAssignment(i);
      if(d_tableau.isBasic(i)){
        out << " (basic)";
      }
      out << endl;
    }
  }
}

TrustNode TheoryArithPrivate::explain(TNode n)
{
  Debug("arith::explain") << "explain @" << getSatContext()->getLevel() << ": " << n << endl;

  ConstraintP c = d_constraintDatabase.lookup(n);
  TrustNode exp;
  if(c != NullConstraint){
    Assert(!c->isAssumption());
    exp = c->externalExplainForPropagation(n);
    Debug("arith::explain") << "constraint explanation" << n << ":" << exp << endl;
  }else if(d_assertionsThatDoNotMatchTheirLiterals.find(n) != d_assertionsThatDoNotMatchTheirLiterals.end()){
    c = d_assertionsThatDoNotMatchTheirLiterals[n];
    if(!c->isAssumption()){
      exp = c->externalExplainForPropagation(n);
      Debug("arith::explain") << "assertions explanation" << n << ":" << exp << endl;
    }else{
      Debug("arith::explain") << "this is a strange mismatch" << n << endl;
      Assert(d_congruenceManager.canExplain(n));
      exp = d_congruenceManager.explain(n);
    }
  }else{
    Assert(d_congruenceManager.canExplain(n));
    Debug("arith::explain") << "dm explanation" << n << endl;
    exp = d_congruenceManager.explain(n);
  }
  return exp;
}

void TheoryArithPrivate::propagate(Theory::Effort e) {
  // This uses model values for safety. Disable for now.
  if (d_qflraStatus == Result::SAT
      && (options::arithPropagationMode()
              == options::ArithPropagationMode::BOUND_INFERENCE_PROP
          || options::arithPropagationMode()
                 == options::ArithPropagationMode::BOTH_PROP)
      && hasAnyUpdates())
  {
    if(options::newProp()){
      propagateCandidatesNew();
    }else{
      propagateCandidates();
    }
  }
  else
  {
    clearUpdates();
  }

  while(d_constraintDatabase.hasMorePropagations()){
    ConstraintCP c = d_constraintDatabase.nextPropagation();
    Debug("arith::prop") << "next prop" << getSatContext()->getLevel() << ": " << c << endl;

    if(c->negationHasProof()){
      Debug("arith::prop") << "negation has proof " << c->getNegation() << endl;
      Debug("arith::prop") << c->getNegation()->externalExplainByAssertions()
                           << endl;
    }
    Assert(!c->negationHasProof())
        << "A constraint has been propagated on the constraint propagation "
           "queue, but the negation has been set to true.  Contact Tim now!";

    if(!c->assertedToTheTheory()){
      Node literal = c->getLiteral();
      Debug("arith::prop") << "propagating @" << getSatContext()->getLevel() << " " << literal << endl;

      outputPropagate(literal);
    }else{
      Debug("arith::prop") << "already asserted to the theory " <<  c->getLiteral() << endl;
    }
  }

  while(d_congruenceManager.hasMorePropagations()){
    TNode toProp = d_congruenceManager.getNextPropagation();

    //Currently if the flag is set this came from an equality detected by the
    //equality engine in the the difference manager.
    Node normalized = Rewriter::rewrite(toProp);

    ConstraintP constraint = d_constraintDatabase.lookup(normalized);
    if(constraint == NullConstraint){
      Debug("arith::prop") << "propagating on non-constraint? "  << toProp << endl;

      outputPropagate(toProp);
    }else if(constraint->negationHasProof()){
      // The congruence manager can prove: antecedents => toProp,
      // ergo. antecedents ^ ~toProp is a conflict.
      TrustNode exp = d_congruenceManager.explain(toProp);
      Node notNormalized = normalized.negate();
      std::vector<Node> ants(exp.getNode().begin(), exp.getNode().end());
      ants.push_back(notNormalized);
      Node lp = safeConstructNary(kind::AND, ants);
      Debug("arith::prop") << "propagate conflict" <<  lp << endl;
      if (proofsEnabled())
      {
        // Assume all of antecedents and ~toProp (rewritten)
        std::vector<Pf> pfAntList;
        for (size_t i = 0; i < ants.size(); ++i)
        {
          pfAntList.push_back(d_pnm->mkAssume(ants[i]));
        }
        Pf pfAnt = pfAntList.size() > 1
                       ? d_pnm->mkNode(PfRule::AND_INTRO, pfAntList, {})
                       : pfAntList[0];
        // Use modus ponens to get toProp (un rewritten)
        Pf pfConc = d_pnm->mkNode(
            PfRule::MODUS_PONENS,
            {pfAnt, exp.getGenerator()->getProofFor(exp.getProven())},
            {});
        // prove toProp (rewritten)
        Pf pfConcRewritten = d_pnm->mkNode(
            PfRule::MACRO_SR_PRED_TRANSFORM, {pfConc}, {normalized});
        Pf pfNotNormalized = d_pnm->mkAssume(notNormalized);
        // prove bottom from toProp and ~toProp
        Pf pfBot;
        if (normalized.getKind() == kind::NOT)
        {
          pfBot = d_pnm->mkNode(
              PfRule::CONTRA, {pfNotNormalized, pfConcRewritten}, {});
        }
        else
        {
          pfBot = d_pnm->mkNode(
              PfRule::CONTRA, {pfConcRewritten, pfNotNormalized}, {});
        }
        // close scope
        Pf pfNotAnd = d_pnm->mkScope(pfBot, ants);
        raiseBlackBoxConflict(lp, pfNotAnd);
      }
      else
      {
        raiseBlackBoxConflict(lp);
      }
      outputConflicts();
      return;
    }else{
      Debug("arith::prop") << "propagating still?" <<  toProp << endl;
      outputPropagate(toProp);
    }
  }
}

DeltaRational TheoryArithPrivate::getDeltaValue(TNode term) const
{
  AlwaysAssert(d_qflraStatus != Result::SAT_UNKNOWN);
  Debug("arith::value") << term << std::endl;

  if (d_partialModel.hasArithVar(term)) {
    ArithVar var = d_partialModel.asArithVar(term);
    return d_partialModel.getAssignment(var);
  }

  switch (Kind kind = term.getKind()) {
    case kind::CONST_RATIONAL:
      return term.getConst<Rational>();

    case kind::PLUS: {  // 2+ args
      DeltaRational value(0);
      for (TNode::iterator i = term.begin(), iend = term.end(); i != iend;
           ++i) {
        value = value + getDeltaValue(*i);
      }
      return value;
    }

    case kind::NONLINEAR_MULT:
    case kind::MULT: {  // 2+ args
      Assert(!isSetup(term));
      DeltaRational value(1);
      for (TNode::iterator i = term.begin(), iend = term.end(); i != iend;
           ++i) {
        value = value * getDeltaValue(*i);
      }
      return value;
    }
    case kind::MINUS: {  // 2 args
      return getDeltaValue(term[0]) - getDeltaValue(term[1]);
    }
    case kind::UMINUS: {  // 1 arg
      return (-getDeltaValue(term[0]));
    }

    case kind::DIVISION: {  // 2 args
      Assert(!isSetup(term));
      return getDeltaValue(term[0]) / getDeltaValue(term[1]);
    }
    case kind::DIVISION_TOTAL:
    case kind::INTS_DIVISION_TOTAL:
    case kind::INTS_MODULUS_TOTAL: {  // 2 args
      Assert(!isSetup(term));
      DeltaRational denominator = getDeltaValue(term[1]);
      if (denominator.isZero()) {
        return DeltaRational(0, 0);
      }
      DeltaRational numerator = getDeltaValue(term[0]);
      if (kind == kind::DIVISION_TOTAL) {
        return numerator / denominator;
      } else if (kind == kind::INTS_DIVISION_TOTAL) {
        return Rational(numerator.euclidianDivideQuotient(denominator));
      } else {
        Assert(kind == kind::INTS_MODULUS_TOTAL);
        return Rational(numerator.euclidianDivideRemainder(denominator));
      }
    }

    default:
      throw ModelException(term, "No model assignment.");
  }
}

Rational TheoryArithPrivate::deltaValueForTotalOrder() const{
  Rational min(2);
  std::set<DeltaRational> relevantDeltaValues;
  context::CDQueue<ConstraintP>::const_iterator qiter = d_diseqQueue.begin();
  context::CDQueue<ConstraintP>::const_iterator qiter_end = d_diseqQueue.end();

  for(; qiter != qiter_end; ++qiter){
    ConstraintP curr = *qiter;

    const DeltaRational& rhsValue = curr->getValue();
    relevantDeltaValues.insert(rhsValue);
  }

  Theory::shared_terms_iterator shared_iter = d_containing.shared_terms_begin();
  Theory::shared_terms_iterator shared_end = d_containing.shared_terms_end();
  for(; shared_iter != shared_end; ++shared_iter){
    Node sharedCurr = *shared_iter;

    // ModelException is fatal as this point. Don't catch!
    // DeltaRationalException is fatal as this point. Don't catch!
    DeltaRational val = getDeltaValue(sharedCurr);
    relevantDeltaValues.insert(val);
  }

  for(var_iterator vi = var_begin(), vend = var_end(); vi != vend; ++vi){
    ArithVar v = *vi;
    const DeltaRational& value = d_partialModel.getAssignment(v);
    relevantDeltaValues.insert(value);
    if( d_partialModel.hasLowerBound(v)){
      const DeltaRational& lb = d_partialModel.getLowerBound(v);
      relevantDeltaValues.insert(lb);
    }
    if( d_partialModel.hasUpperBound(v)){
      const DeltaRational& ub = d_partialModel.getUpperBound(v);
      relevantDeltaValues.insert(ub);
    }
  }

  if(relevantDeltaValues.size() >= 2){
    std::set<DeltaRational>::const_iterator iter = relevantDeltaValues.begin();
    std::set<DeltaRational>::const_iterator iter_end = relevantDeltaValues.end();
    DeltaRational prev = *iter;
    ++iter;
    for(; iter != iter_end; ++iter){
      const DeltaRational& curr = *iter;

      Assert(prev < curr);

      DeltaRational::seperatingDelta(min, prev, curr);
      prev = curr;
    }
  }

  Assert(min.sgn() > 0);
  Rational belowMin = min/Rational(2);
  return belowMin;
}

void TheoryArithPrivate::collectModelValues(const std::set<Node>& termSet,
                                            std::map<Node, Node>& arithModel)
{
  AlwaysAssert(d_qflraStatus == Result::SAT);

  if(Debug.isOn("arith::collectModelInfo")){
    debugPrintFacts();
  }

  Debug("arith::collectModelInfo") << "collectModelInfo() begin " << endl;

  // Delta lasts at least the duration of the function call
  const Rational& delta = d_partialModel.getDelta();
  std::unordered_set<TNode> shared = d_containing.currentlySharedTerms();

  // TODO:
  // This is not very good for user push/pop....
  // Revisit when implementing push/pop
  for(var_iterator vi = var_begin(), vend = var_end(); vi != vend; ++vi){
    ArithVar v = *vi;

    if(!isAuxiliaryVariable(v)){
      Node term = d_partialModel.asNode(v);

      if((theoryOf(term) == THEORY_ARITH || shared.find(term) != shared.end())
         && termSet.find(term) != termSet.end()){

        const DeltaRational& mod = d_partialModel.getAssignment(v);
        Rational qmodel = mod.substituteDelta(delta);

        Node qNode = mkRationalNode(qmodel);
        Debug("arith::collectModelInfo") << "m->assertEquality(" << term << ", " << qmodel << ", true)" << endl;
        // Add to the map
        arithModel[term] = qNode;
      }else{
        Debug("arith::collectModelInfo") << "Skipping m->assertEquality(" << term << ", true)" << endl;

      }
    }
  }

  // Iterate over equivalence classes in LinearEqualityModule
  // const eq::EqualityEngine& ee = d_congruenceManager.getEqualityEngine();
  // m->assertEqualityEngine(&ee);

  Debug("arith::collectModelInfo") << "collectModelInfo() end " << endl;
}

bool TheoryArithPrivate::safeToReset() const {
  Assert(!d_tableauSizeHasBeenModified);
  Assert(d_errorSet.noSignals());

  ErrorSet::error_iterator error_iter = d_errorSet.errorBegin();
  ErrorSet::error_iterator error_end = d_errorSet.errorEnd();
  for(; error_iter != error_end; ++error_iter){
    ArithVar basic = *error_iter;
    if(!d_smallTableauCopy.isBasic(basic)){
      return false;
    }
  }

  return true;
}

void TheoryArithPrivate::notifyRestart(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_restartTimer);

  if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }

  ++d_restartsCounter;
  d_solveIntMaybeHelp = 0;
  d_solveIntAttempts = 0;
}

bool TheoryArithPrivate::entireStateIsConsistent(const string& s){
  bool result = true;
  for(var_iterator vi = var_begin(), vend = var_end(); vi != vend; ++vi){
    ArithVar var = *vi;
    //ArithVar var = d_partialModel.asArithVar(*i);
    if(!d_partialModel.assignmentIsConsistent(var)){
      d_partialModel.printModel(var);
      Warning() << s << ":" << "Assignment is not consistent for " << var << d_partialModel.asNode(var);
      if(d_tableau.isBasic(var)){
        Warning() << " (basic)";
      }
      Warning() << endl;
      result = false;
    }else if(d_partialModel.isInteger(var) && !d_partialModel.integralAssignment(var)){
      d_partialModel.printModel(var);
      Warning() << s << ":" << "Assignment is not integer for integer variable " << var << d_partialModel.asNode(var);
      if(d_tableau.isBasic(var)){
        Warning() << " (basic)";
      }
      Warning() << endl;
      result = false;
    }
  }
  return result;
}

bool TheoryArithPrivate::unenqueuedVariablesAreConsistent(){
  bool result = true;
  for(var_iterator vi = var_begin(), vend = var_end(); vi != vend; ++vi){
    ArithVar var = *vi;
    if(!d_partialModel.assignmentIsConsistent(var)){
      if(!d_errorSet.inError(var)){

        d_partialModel.printModel(var);
        Warning() << "Unenqueued var is not consistent for " << var <<  d_partialModel.asNode(var);
        if(d_tableau.isBasic(var)){
          Warning() << " (basic)";
        }
        Warning() << endl;
        result = false;
      } else if(Debug.isOn("arith::consistency::initial")){
        d_partialModel.printModel(var);
        Warning() << "Initial var is not consistent for " << var <<  d_partialModel.asNode(var);
        if(d_tableau.isBasic(var)){
          Warning() << " (basic)";
        }
        Warning() << endl;
      }
     }
  }
  return result;
}

void TheoryArithPrivate::presolve(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_presolveTime);

  d_statistics.d_initialTableauSize = d_tableau.size();

  if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }

  static thread_local unsigned callCount = 0;
  if(Debug.isOn("arith::presolve")) {
    Debug("arith::presolve") << "TheoryArithPrivate::presolve #" << callCount << endl;
    callCount = callCount + 1;
  }

  vector<TrustNode> lemmas;
  if(!options::incrementalSolving()) {
    switch(options::arithUnateLemmaMode()){
      case options::ArithUnateLemmaMode::NO: break;
      case options::ArithUnateLemmaMode::INEQUALITY:
        d_constraintDatabase.outputUnateInequalityLemmas(lemmas);
        break;
      case options::ArithUnateLemmaMode::EQUALITY:
        d_constraintDatabase.outputUnateEqualityLemmas(lemmas);
        break;
      case options::ArithUnateLemmaMode::ALL:
        d_constraintDatabase.outputUnateInequalityLemmas(lemmas);
        d_constraintDatabase.outputUnateEqualityLemmas(lemmas);
        break;
      default: Unhandled() << options::arithUnateLemmaMode();
    }
  }

  vector<TrustNode>::const_iterator i = lemmas.begin(), i_end = lemmas.end();
  for(; i != i_end; ++i){
    TrustNode lem = *i;
    Debug("arith::oldprop") << " lemma lemma duck " <<lem << endl;
    outputTrustedLemma(lem, InferenceId::ARITH_UNATE);
  }
}

EqualityStatus TheoryArithPrivate::getEqualityStatus(TNode a, TNode b) {
  if(d_qflraStatus == Result::SAT_UNKNOWN){
    return EQUALITY_UNKNOWN;
  }else{
    try {
      if (getDeltaValue(a) == getDeltaValue(b)) {
        return EQUALITY_TRUE_IN_MODEL;
      } else {
        return EQUALITY_FALSE_IN_MODEL;
      }
    } catch (DeltaRationalException& dr) {
      return EQUALITY_UNKNOWN;
    } catch (ModelException& me) {
      return EQUALITY_UNKNOWN;
    }
  }
}

bool TheoryArithPrivate::propagateCandidateBound(ArithVar basic, bool upperBound){
  ++d_statistics.d_boundComputations;

  RowIndex ridx = d_tableau.basicToRowIndex(basic);
  DeltaRational bound = d_linEq.computeRowBound(ridx, upperBound, basic);

  if((upperBound && d_partialModel.strictlyLessThanUpperBound(basic, bound)) ||
     (!upperBound && d_partialModel.strictlyGreaterThanLowerBound(basic, bound))){

    // TODO: "Policy point"
    //We are only going to recreate the functionality for now.
    //In the future this can be improved to generate a temporary constraint
    //if none exists.
    //Experiment with doing this every time or only when the new constraint
    //implies an unknown fact.

    ConstraintType t = upperBound ? UpperBound : LowerBound;
    ConstraintP bestImplied = d_constraintDatabase.getBestImpliedBound(basic, t, bound);

    // Node bestImplied = upperBound ?
    //   d_apm.getBestImpliedUpperBound(basic, bound):
    //   d_apm.getBestImpliedLowerBound(basic, bound);

    if(bestImplied != NullConstraint){
      //This should be stronger
      Assert(!upperBound || bound <= bestImplied->getValue());
      Assert(
          !upperBound
          || d_partialModel.lessThanUpperBound(basic, bestImplied->getValue()));

      Assert(upperBound || bound >= bestImplied->getValue());
      Assert(upperBound
             || d_partialModel.greaterThanLowerBound(basic,
                                                     bestImplied->getValue()));
      //slightly changed

      // ConstraintP c = d_constraintDatabase.lookup(bestImplied);
      // Assert(c != NullConstraint);

      bool assertedToTheTheory = bestImplied->assertedToTheTheory();
      bool canBePropagated = bestImplied->canBePropagated();
      bool hasProof = bestImplied->hasProof();

      Debug("arith::prop") << "arith::prop" << basic
                           << " " << assertedToTheTheory
                           << " " << canBePropagated
                           << " " << hasProof
                           << endl;

      if(bestImplied->negationHasProof()){
        Warning() << "the negation of " <<  bestImplied << " : " << endl
                  << "has proof " << bestImplied->getNegation() << endl
                  << bestImplied->getNegation()->externalExplainByAssertions()
                  << endl;
      }

      if(!assertedToTheTheory && canBePropagated && !hasProof ){
        d_linEq.propagateBasicFromRow(bestImplied);
        // I think this can be skipped if canBePropagated is true
        //d_learnedBounds.push(bestImplied);
        if(Debug.isOn("arith::prop")){
          Debug("arith::prop") << "success " << bestImplied << endl;
          d_partialModel.printModel(basic, Debug("arith::prop"));
        }
        return true;
      }
      if(Debug.isOn("arith::prop")){
        Debug("arith::prop") << "failed " << basic
                             << " " << bound
                             << " " << assertedToTheTheory
                             << " " << canBePropagated
                             << " " << hasProof << endl;
        d_partialModel.printModel(basic, Debug("arith::prop"));
      }
    }
  }else if(Debug.isOn("arith::prop")){
    Debug("arith::prop") << "false " << bound << " ";
    d_partialModel.printModel(basic, Debug("arith::prop"));
  }
  return false;
}

void TheoryArithPrivate::propagateCandidate(ArithVar basic){
  bool success = false;
  RowIndex ridx = d_tableau.basicToRowIndex(basic);

  bool tryLowerBound =
    d_partialModel.strictlyAboveLowerBound(basic) &&
    d_linEq.rowLacksBound(ridx, false, basic) == NULL;

  bool tryUpperBound =
    d_partialModel.strictlyBelowUpperBound(basic) &&
    d_linEq.rowLacksBound(ridx, true, basic) == NULL;

  if(tryLowerBound){
    success |= propagateCandidateLowerBound(basic);
  }
  if(tryUpperBound){
    success |= propagateCandidateUpperBound(basic);
  }
  if(success){
    ++d_statistics.d_boundPropagations;
  }
}

void TheoryArithPrivate::propagateCandidates(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_boundComputationTime);

  Debug("arith::prop") << "propagateCandidates begin" << endl;

  Assert(d_candidateBasics.empty());

  if(d_updatedBounds.empty()){ return; }

  DenseSet::const_iterator i = d_updatedBounds.begin();
  DenseSet::const_iterator end = d_updatedBounds.end();
  for(; i != end; ++i){
    ArithVar var = *i;
    if(d_tableau.isBasic(var) &&
       d_tableau.basicRowLength(var) <= options::arithPropagateMaxLength()){
      d_candidateBasics.softAdd(var);
    }else{
      Tableau::ColIterator basicIter = d_tableau.colIterator(var);
      for(; !basicIter.atEnd(); ++basicIter){
        const Tableau::Entry& entry = *basicIter;
        RowIndex ridx = entry.getRowIndex();
        ArithVar rowVar = d_tableau.rowIndexToBasic(ridx);
        Assert(entry.getColVar() == var);
        Assert(d_tableau.isBasic(rowVar));
        if(d_tableau.getRowLength(ridx) <= options::arithPropagateMaxLength()){
          d_candidateBasics.softAdd(rowVar);
        }
      }
    }
  }
  d_updatedBounds.purge();

  while(!d_candidateBasics.empty()){
    ArithVar candidate = d_candidateBasics.back();
    d_candidateBasics.pop_back();
    Assert(d_tableau.isBasic(candidate));
    propagateCandidate(candidate);
  }
  Debug("arith::prop") << "propagateCandidates end" << endl << endl << endl;
}

void TheoryArithPrivate::propagateCandidatesNew(){
  /* Four criteria must be met for progagation on a variable to happen using a row:
   * 0: A new bound has to have been added to the row.
   * 1: The hasBoundsCount for the row must be "full" or be full minus one variable
   *    (This is O(1) to check, but requires book keeping.)
   * 2: The current assignment must be strictly smaller/greater than the current bound.
   *    assign(x) < upper(x)
   *    (This is O(1) to compute.)
   * 3: There is a bound that is strictly smaller/greater than the current assignment.
   *    assign(x) < c for some x <= c literal
   *    (This is O(log n) to compute.)
   * 4: The implied bound on x is strictly smaller/greater than the current bound.
   *    (This is O(n) to compute.)
   */

  TimerStat::CodeTimer codeTimer(d_statistics.d_boundComputationTime);
  Debug("arith::prop") << "propagateCandidatesNew begin" << endl;

  Assert(d_qflraStatus == Result::SAT);
  if(d_updatedBounds.empty()){ return; }
  dumpUpdatedBoundsToRows();
  Assert(d_updatedBounds.empty());

  if(!d_candidateRows.empty()){
    UpdateTrackingCallback utcb(&d_linEq);
    d_partialModel.processBoundsQueue(utcb);
  }

  while(!d_candidateRows.empty()){
    RowIndex candidate = d_candidateRows.back();
    d_candidateRows.pop_back();
    propagateCandidateRow(candidate);
  }
  Debug("arith::prop") << "propagateCandidatesNew end" << endl << endl << endl;
}

bool TheoryArithPrivate::propagateMightSucceed(ArithVar v, bool ub) const{
  int cmp = ub ? d_partialModel.cmpAssignmentUpperBound(v)
    : d_partialModel.cmpAssignmentLowerBound(v);
  bool hasSlack = ub ? cmp < 0 : cmp > 0;
  if(hasSlack){
    ConstraintType t = ub ? UpperBound : LowerBound;
    const DeltaRational& a = d_partialModel.getAssignment(v);

    if(isInteger(v) && !a.isIntegral()){
      return true;
    }

    ConstraintP strongestPossible = d_constraintDatabase.getBestImpliedBound(v, t, a);
    if(strongestPossible == NullConstraint){
      return false;
    }else{
      bool assertedToTheTheory = strongestPossible->assertedToTheTheory();
      bool canBePropagated = strongestPossible->canBePropagated();
      bool hasProof = strongestPossible->hasProof();

      return !assertedToTheTheory && canBePropagated && !hasProof;
    }
  }else{
    return false;
  }
}

bool TheoryArithPrivate::attemptSingleton(RowIndex ridx, bool rowUp){
  Debug("arith::prop") << "  attemptSingleton" << ridx;

  const Tableau::Entry* ep;
  ep = d_linEq.rowLacksBound(ridx, rowUp, ARITHVAR_SENTINEL);
  Assert(ep != NULL);

  ArithVar v = ep->getColVar();
  const Rational& coeff = ep->getCoefficient();

  // 0 = c * v + \sum rest
  // Suppose rowUp
  // - c * v = \sum rest \leq D
  // if c > 0, v \geq -D/c so !vUp
  // if c < 0, v \leq -D/c so  vUp
  // Suppose not rowUp
  // - c * v = \sum rest \geq D
  // if c > 0, v \leq -D/c so  vUp
  // if c < 0, v \geq -D/c so !vUp
  bool vUp = (rowUp == ( coeff.sgn() < 0));

  Debug("arith::prop") << "  " << rowUp << " " << v << " " << coeff << " " << vUp << endl;
  Debug("arith::prop") << "  " << propagateMightSucceed(v, vUp) << endl;

  if(propagateMightSucceed(v, vUp)){
    DeltaRational dr = d_linEq.computeRowBound(ridx, rowUp, v);
    DeltaRational bound = dr / (- coeff);
    return tryToPropagate(ridx, rowUp, v, vUp, bound);
  }
  return false;
}

bool TheoryArithPrivate::attemptFull(RowIndex ridx, bool rowUp){
  Debug("arith::prop") << "  attemptFull" << ridx << endl;

  vector<const Tableau::Entry*> candidates;

  for(Tableau::RowIterator i = d_tableau.ridRowIterator(ridx); !i.atEnd(); ++i){
    const Tableau::Entry& e =*i;
    const Rational& c = e.getCoefficient();
    ArithVar v = e.getColVar();
    bool vUp = (rowUp == (c.sgn() < 0));
    if(propagateMightSucceed(v, vUp)){
      candidates.push_back(&e);
    }
  }
  if(candidates.empty()){ return false; }

  const DeltaRational slack =
    d_linEq.computeRowBound(ridx, rowUp, ARITHVAR_SENTINEL);
  bool any = false;
  vector<const Tableau::Entry*>::const_iterator i, iend;
  for(i = candidates.begin(), iend = candidates.end(); i != iend; ++i){
    const Tableau::Entry* ep = *i;
    const Rational& c = ep->getCoefficient();
    ArithVar v = ep->getColVar();

    // See the comment for attemptSingleton()
    bool activeUp = (rowUp == (c.sgn() > 0));
    bool vUb = (rowUp == (c.sgn() < 0));

    const DeltaRational& activeBound = activeUp ?
      d_partialModel.getUpperBound(v):
      d_partialModel.getLowerBound(v);

    DeltaRational contribution = activeBound * c;
    DeltaRational impliedBound = (slack - contribution)/(-c);

    bool success = tryToPropagate(ridx, rowUp, v, vUb, impliedBound);
    any |= success;
  }
  return any;
}

bool TheoryArithPrivate::tryToPropagate(RowIndex ridx, bool rowUp, ArithVar v, bool vUb, const DeltaRational& bound){

  bool weaker = vUb ? d_partialModel.strictlyLessThanUpperBound(v, bound):
    d_partialModel.strictlyGreaterThanLowerBound(v, bound);
  if(weaker){
    ConstraintType t = vUb ? UpperBound : LowerBound;

    ConstraintP implied = d_constraintDatabase.getBestImpliedBound(v, t, bound);
    if(implied != NullConstraint){
      return rowImplicationCanBeApplied(ridx, rowUp, implied);
    }
  }
  return false;
}

Node flattenImplication(Node imp){
  NodeBuilder nb(kind::OR);
  std::unordered_set<Node> included;
  Node left = imp[0];
  Node right = imp[1];

  if(left.getKind() == kind::AND){
    for(Node::iterator i = left.begin(), iend = left.end(); i != iend; ++i) {
      if (!included.count((*i).negate()))
      {
        nb << (*i).negate();
        included.insert((*i).negate());
      }
    }
  }else{
    if (!included.count(left.negate()))
    {
      nb << left.negate();
      included.insert(left.negate());
    }
  }

  if(right.getKind() == kind::OR){
    for(Node::iterator i = right.begin(), iend = right.end(); i != iend; ++i) {
      if (!included.count(*i))
      {
        nb << *i;
        included.insert(*i);
      }
    }
  }else{
    if (!included.count(right))
    {
      nb << right;
      included.insert(right);
    }
  }

  return nb;
}

bool TheoryArithPrivate::rowImplicationCanBeApplied(RowIndex ridx, bool rowUp, ConstraintP implied){
  Assert(implied != NullConstraint);
  ArithVar v = implied->getVariable();

  bool assertedToTheTheory = implied->assertedToTheTheory();
  bool canBePropagated = implied->canBePropagated();
  bool hasProof = implied->hasProof();

  Debug("arith::prop") << "arith::prop" << v
                       << " " << assertedToTheTheory
                       << " " << canBePropagated
                       << " " << hasProof
                       << endl;


  if( !assertedToTheTheory && canBePropagated && !hasProof ){
    ConstraintCPVec explain;
    ARITH_PROOF(d_farkasBuffer.clear());
    RationalVectorP coeffs = ARITH_NULLPROOF(&d_farkasBuffer);

    // After invoking `propegateRow`:
    //   * coeffs[0] is for implied
    //   * coeffs[i+1] is for explain[i]
    d_linEq.propagateRow(explain, ridx, rowUp, implied, coeffs);
    if(d_tableau.getRowLength(ridx) <= options::arithPropAsLemmaLength()){
      if (Debug.isOn("arith::prop::pf")) {
        for (const auto & constraint : explain) {
          Assert(constraint->hasProof());
          constraint->printProofTree(Debug("arith::prop::pf"));
        }
      }
      Node implication = implied->externalImplication(explain);
      Node clause = flattenImplication(implication);
      std::shared_ptr<ProofNode> clausePf{nullptr};

      if (isProofEnabled())
      {
        // We can prove this lemma from Farkas...
        std::vector<std::shared_ptr<ProofNode>> conflictPfs;
        // Assume the negated getLiteral version of the implied constaint
        // then rewrite it into proof normal form.
        conflictPfs.push_back(
            d_pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM,
                          {d_pnm->mkAssume(implied->getLiteral().negate())},
                          {implied->getNegation()->getProofLiteral()}));
        // Add the explaination proofs.
        for (const auto constraint : explain)
        {
          NodeBuilder nb;
          conflictPfs.push_back(constraint->externalExplainByAssertions(nb));
        }
        // Collect the farkas coefficients, as nodes.
        std::vector<Node> farkasCoefficients;
        farkasCoefficients.reserve(coeffs->size());
        auto nm = NodeManager::currentNM();
        std::transform(
            coeffs->begin(),
            coeffs->end(),
            std::back_inserter(farkasCoefficients),
            [nm](const Rational& r) { return nm->mkConst<Rational>(r); });

        // Prove bottom.
        auto sumPf = d_pnm->mkNode(
            PfRule::MACRO_ARITH_SCALE_SUM_UB, conflictPfs, farkasCoefficients);
        auto botPf = d_pnm->mkNode(
            PfRule::MACRO_SR_PRED_TRANSFORM, {sumPf}, {nm->mkConst(false)});

        // Prove the conflict
        std::vector<Node> assumptions;
        assumptions.reserve(clause.getNumChildren());
        std::transform(clause.begin(),
                       clause.end(),
                       std::back_inserter(assumptions),
                       [](TNode r) { return r.negate(); });
        auto notAndNotPf = d_pnm->mkScope(botPf, assumptions);

        // Convert it to a clause
        auto orNotNotPf = d_pnm->mkNode(PfRule::NOT_AND, {notAndNotPf}, {});
        clausePf = d_pnm->mkNode(
            PfRule::MACRO_SR_PRED_TRANSFORM, {orNotNotPf}, {clause});

        // Output it
        TrustNode trustedClause = d_pfGen->mkTrustNode(clause, clausePf);
        outputTrustedLemma(trustedClause, InferenceId::ARITH_ROW_IMPL);
      }
      else
      {
        outputLemma(clause, InferenceId::ARITH_ROW_IMPL);
      }
    }else{
      Assert(!implied->negationHasProof());
      implied->impliedByFarkas(explain, coeffs, false);
      implied->tryToPropagate();
    }
    return true;
  }

  if(Debug.isOn("arith::prop")){
    Debug("arith::prop")
      << "failed " << v << " " << assertedToTheTheory << " "
      << canBePropagated << " " << hasProof << " " << implied << endl;
    d_partialModel.printModel(v, Debug("arith::prop"));
  }
  return false;
}

bool TheoryArithPrivate::propagateCandidateRow(RowIndex ridx){
  BoundCounts hasCount = d_linEq.hasBoundCount(ridx);
  uint32_t rowLength = d_tableau.getRowLength(ridx);

  bool success = false;
  static int instance = 0;
  ++instance;

  Debug("arith::prop")
    << "propagateCandidateRow " << instance << " attempt " << rowLength << " " <<  hasCount << endl;

  if (rowLength >= options::arithPropagateMaxLength()
      && Random::getRandom().pickWithProb(
             1.0 - double(options::arithPropagateMaxLength()) / rowLength))
  {
    return false;
  }

  if(hasCount.lowerBoundCount() == rowLength){
    success |= attemptFull(ridx, false);
  }else if(hasCount.lowerBoundCount() + 1 == rowLength){
    success |= attemptSingleton(ridx, false);
  }

  if(hasCount.upperBoundCount() == rowLength){
    success |= attemptFull(ridx, true);
  }else if(hasCount.upperBoundCount() + 1 == rowLength){
    success |= attemptSingleton(ridx, true);
  }
  return success;
}

void TheoryArithPrivate::dumpUpdatedBoundsToRows(){
  Assert(d_candidateRows.empty());
  DenseSet::const_iterator i = d_updatedBounds.begin();
  DenseSet::const_iterator end = d_updatedBounds.end();
  for(; i != end; ++i){
    ArithVar var = *i;
    if(d_tableau.isBasic(var)){
      RowIndex ridx = d_tableau.basicToRowIndex(var);
      d_candidateRows.softAdd(ridx);
    }else{
      Tableau::ColIterator basicIter = d_tableau.colIterator(var);
      for(; !basicIter.atEnd(); ++basicIter){
        const Tableau::Entry& entry = *basicIter;
        RowIndex ridx = entry.getRowIndex();
        d_candidateRows.softAdd(ridx);
      }
    }
  }
  d_updatedBounds.purge();
}

const BoundsInfo& TheoryArithPrivate::boundsInfo(ArithVar basic) const{
  RowIndex ridx = d_tableau.basicToRowIndex(basic);
  return d_rowTracking[ridx];
}

std::pair<bool, Node> TheoryArithPrivate::entailmentCheck(TNode lit, const ArithEntailmentCheckParameters& params, ArithEntailmentCheckSideEffects& out){
  using namespace inferbounds;

  // l k r
  // diff : (l - r) k 0
  Debug("arith::entailCheck") << "TheoryArithPrivate::entailmentCheck(" << lit << ")"<< endl;
  Kind k;
  int primDir;
  Rational lm, rm, dm;
  Node lp, rp, dp;
  DeltaRational sep;
  bool successful = decomposeLiteral(lit, k, primDir, lm, lp, rm, rp, dm, dp, sep);
  if(!successful) { return make_pair(false, Node::null()); }

  if(dp.getKind() == CONST_RATIONAL){
    Node eval = Rewriter::rewrite(lit);
    Assert(eval.getKind() == kind::CONST_BOOLEAN);
    // if true, true is an acceptable explaination
    // if false, the node is uninterpreted and eval can be forgotten
    return make_pair(eval.getConst<bool>(), eval);
  }
  Assert(dm != Rational(0));
  Assert(primDir == 1 || primDir == -1);

  int negPrim = -primDir;

  int secDir = (k == EQUAL || k == DISTINCT) ? negPrim: 0;
  int negSecDir = (k == EQUAL || k == DISTINCT) ? primDir: 0;

  // primDir*[lm*( lp )] k primDir*[ [rm*( rp )] + sep ]
  // primDir*[lm*( lp ) - rm*( rp ) ] k primDir*sep
  // primDir*[dm * dp] k primDir*sep

  std::pair<Node, DeltaRational> bestPrimLeft, bestNegPrimRight, bestPrimDiff, tmp;
  std::pair<Node, DeltaRational> bestSecLeft, bestNegSecRight, bestSecDiff;
  bestPrimLeft.first = Node::null(); bestNegPrimRight.first = Node::null(); bestPrimDiff.first = Node::null();
  bestSecLeft.first = Node::null(); bestNegSecRight.first = Node::null(); bestSecDiff.first = Node::null();



  ArithEntailmentCheckParameters::const_iterator alg, alg_end;
  for( alg = params.begin(), alg_end = params.end(); alg != alg_end; ++alg ){
    const inferbounds::InferBoundAlgorithm& ibalg = *alg;

    Debug("arith::entailCheck") << "entailmentCheck trying " << (inferbounds::Algorithms) ibalg.getAlgorithm() << endl;
    switch(ibalg.getAlgorithm()){
    case inferbounds::None:
      break;
    case inferbounds::Lookup:
    case inferbounds::RowSum:
      {
        typedef void (TheoryArithPrivate::*EntailmentCheckFunc)(std::pair<Node, DeltaRational>&, int, TNode) const;

        EntailmentCheckFunc ecfunc =
          (ibalg.getAlgorithm() == inferbounds::Lookup)
          ? (&TheoryArithPrivate::entailmentCheckBoundLookup)
          : (&TheoryArithPrivate::entailmentCheckRowSum);

        (*this.*ecfunc)(tmp, primDir * lm.sgn(), lp);
        setToMin(primDir * lm.sgn(), bestPrimLeft, tmp);

        (*this.*ecfunc)(tmp, negPrim * rm.sgn(), rp);
        setToMin(negPrim * rm.sgn(), bestNegPrimRight, tmp);

        (*this.*ecfunc)(tmp, secDir * lm.sgn(), lp);
        setToMin(secDir * lm.sgn(), bestSecLeft, tmp);

        (*this.*ecfunc)(tmp, negSecDir * rm.sgn(), rp);
        setToMin(negSecDir * rm.sgn(), bestNegSecRight, tmp);

        (*this.*ecfunc)(tmp, primDir * dm.sgn(), dp);
        setToMin(primDir * dm.sgn(), bestPrimDiff, tmp);

        (*this.*ecfunc)(tmp, secDir * dm.sgn(), dp);
        setToMin(secDir * dm.sgn(), bestSecDiff, tmp);
      }
      break;
    default:
      Unhandled();
    }

    // turn bounds on prim * left and -prim * right into bounds on prim * diff
    if(!bestPrimLeft.first.isNull() && !bestNegPrimRight.first.isNull()){
      //  primDir*lm* lp <= primDir*lm*L
      // -primDir*rm* rp <= -primDir*rm*R
      // primDir*lm* lp -primDir*rm* rp <=  primDir*lm*L - primDir*rm*R
      // primDir [lm* lp -rm* rp] <= primDir[lm*L - *rm*R]
      // primDir [dm * dp] <= primDir[lm*L - *rm*R]
      // primDir [dm * dp] <= primDir * dm * ([lm*L - *rm*R]/dm)
      tmp.second = ((bestPrimLeft.second * lm) - (bestNegPrimRight.second * rm)) / dm;
      tmp.first = (bestPrimLeft.first).andNode(bestNegPrimRight.first);
      setToMin(primDir, bestPrimDiff, tmp);
    }

    // turn bounds on sec * left and sec * right into bounds on sec * diff
    if(secDir != 0 && !bestSecLeft.first.isNull() && !bestNegSecRight.first.isNull()){
      //  secDir*lm* lp <= secDir*lm*L
      // -secDir*rm* rp <= -secDir*rm*R
      // secDir*lm* lp -secDir*rm* rp <=  secDir*lm*L - secDir*rm*R
      // secDir [lm* lp -rm* rp] <= secDir[lm*L - *rm*R]
      // secDir [dm * dp] <= secDir[lm*L - *rm*R]
      // secDir [dm * dp] <= secDir * dm * ([lm*L - *rm*R]/dm)
      tmp.second = ((bestSecLeft.second * lm) - (bestNegSecRight.second * rm)) / dm;
      tmp.first = (bestSecLeft.first).andNode(bestNegSecRight.first);
      setToMin(secDir, bestSecDiff, tmp);
    }

    switch(k){
    case LEQ:
      if(!bestPrimDiff.first.isNull()){
        DeltaRational d = (bestPrimDiff.second * dm);
        if((primDir > 0 && d <= sep) || (primDir < 0 && d >= sep) ){
          Debug("arith::entailCheck") << "entailmentCheck found "
                                      << primDir << "*" << dm << "*(" << dp<<")"
                                      << " <= " << primDir << "*" << dm << "*" << bestPrimDiff.second
                                      << " <= " << primDir << "*" << sep << endl
                                      << " by " << bestPrimDiff.first << endl;
          Assert(bestPrimDiff.second * (Rational(primDir) * dm)
                 <= (sep * Rational(primDir)));
          return make_pair(true, bestPrimDiff.first);
        }
      }
      break;
    case EQUAL:
      if(!bestPrimDiff.first.isNull() && !bestSecDiff.first.isNull()){
        // Is primDir [dm * dp] == primDir * sep entailed?
        // Iff [dm * dp] == sep entailed?
        // Iff dp == sep / dm entailed?
        // Iff dp <= sep / dm and dp >= sep / dm entailed?

        // primDir [dm * dp] <= primDir * dm * U
        // secDir [dm * dp] <= secDir * dm * L

        // Suppose primDir * dm > 0
        // then secDir * dm < 0
        //   dp >= (secDir * L) / secDir * dm
        //   dp >= (primDir * L) / primDir * dm
        //
        //   dp <= U / dm
        //   dp >= L / dm
        //   dp == sep / dm entailed iff U == L == sep
        // Suppose primDir * dm < 0
        // then secDir * dm > 0
        //   dp >= U / dm
        //   dp <= L / dm
        //   dp == sep / dm entailed iff U == L == sep
        if(bestPrimDiff.second == bestSecDiff.second){
          if(bestPrimDiff.second == sep){
            return make_pair(true, (bestPrimDiff.first).andNode(bestSecDiff.first));
          }
        }
      }
      // intentionally fall through to DISTINCT case!
      // entailments of negations are eager exit cases for EQUAL
      CVC5_FALLTHROUGH;
    case DISTINCT:
      if(!bestPrimDiff.first.isNull()){
        // primDir [dm * dp] <= primDir * dm * U < primDir * sep
        if((primDir > 0 && (bestPrimDiff.second * dm  < sep)) ||
           (primDir < 0 && (bestPrimDiff.second * dm  > sep))){
          // entailment of negation
          if(k == DISTINCT){
            return make_pair(true, bestPrimDiff.first);
          }else{
            Assert(k == EQUAL);
            return make_pair(false, Node::null());
          }
        }
      }
      if(!bestSecDiff.first.isNull()){
        // If primDir [dm * dp] > primDir * sep, then this is not entailed.
        // If primDir [dm * dp] >= primDir * dm * L > primDir * sep
        // -primDir * dm * L < -primDir * sep
        // secDir * dm * L < secDir * sep
        if((secDir > 0 && (bestSecDiff.second * dm < sep)) ||
           (secDir < 0 && (bestSecDiff.second * dm > sep))){
          if(k == DISTINCT){
            return make_pair(true, bestSecDiff.first);
          }else{
            Assert(k == EQUAL);
            return make_pair(false, Node::null());
          }
        }
      }

      break;
    default:
      Unreachable();
      break;
    }
  }
  return make_pair(false, Node::null());
}

bool TheoryArithPrivate::decomposeTerm(Node term, Rational& m, Node& p, Rational& c){
  Node t = Rewriter::rewrite(term);
  if(!Polynomial::isMember(t)){
    return false;
  }

  // TODO Speed up
  preprocessing::util::ContainsTermITEVisitor ctv;
  if(ctv.containsTermITE(t)){
    return false;
  }

  Polynomial poly = Polynomial::parsePolynomial(t);
  if(poly.isConstant()){
    c = poly.getHead().getConstant().getValue();
    p = mkRationalNode(Rational(0));
    m = Rational(1);
    return true;
  }else if(poly.containsConstant()){
    c = poly.getHead().getConstant().getValue();
    poly = poly.getTail();
  }else{
    c = Rational(0);
  }
  Assert(!poly.isConstant());
  Assert(!poly.containsConstant());

  const bool intVars = poly.allIntegralVariables();

  if(intVars){
    m = Rational(1);
    if(!poly.isIntegral()){
      Integer denom = poly.denominatorLCM();
      m /= denom;
      poly = poly * denom;
    }
    Integer g = poly.gcd();
    m *= g;
    poly = poly * Rational(1,g);
    Assert(poly.isIntegral());
    Assert(poly.leadingCoefficientIsPositive());
  }else{
    Assert(!intVars);
    m = poly.getHead().getConstant().getValue();
    poly = poly * m.inverse();
    Assert(poly.leadingCoefficientIsAbsOne());
  }
  p = poly.getNode();
  return true;
}

void TheoryArithPrivate::setToMin(int sgn, std::pair<Node, DeltaRational>& min, const std::pair<Node, DeltaRational>& e){
  if(sgn != 0){
    if(min.first.isNull() && !e.first.isNull()){
      min = e;
    }else if(!min.first.isNull() && !e.first.isNull()){
      if(sgn > 0 && min.second > e.second){
        min = e;
      }else if(sgn < 0 &&  min.second < e.second){
        min = e;
      }
    }
  }
}

// std::pair<bool, Node> TheoryArithPrivate::entailmentUpperCheck(const Rational& lm, Node lp, const Rational& rm, Node rp, const DeltaRational& sep, const ArithEntailmentCheckParameters& params, ArithEntailmentCheckSideEffects& out){

//   Rational negRM = -rm;
//   Node diff = NodeManager::currentNM()->mkNode(MULT, mkRationalConstan(lm), lp) + (negRM * rp);

//   Rational diffm;
//   Node diffp;
//   decompose(diff, diffm, diffNode);


//   std::pair<Node, DeltaRational> bestUbLeft, bestLbRight, bestUbDiff, tmp;
//   bestUbLeft = bestLbRight = bestUbDiff = make_pair(Node::Null(), DeltaRational());

//   return make_pair(false, Node::null());
// }

/**
 * Decomposes a literal into the form:
 *   dir*[lm*( lp )] k dir*[ [rm*( rp )] + sep ]
 *   dir*[dm* dp]  k dir *sep
 *   dir is either 1 or -1
 */
bool TheoryArithPrivate::decomposeLiteral(Node lit, Kind& k, int& dir, Rational& lm,  Node& lp, Rational& rm, Node& rp, Rational& dm, Node& dp, DeltaRational& sep){
  bool negated = (lit.getKind() == kind::NOT);
  TNode atom = negated ? lit[0] : lit;

  TNode left = atom[0];
  TNode right = atom[1];

  // left : lm*( lp ) + lc
  // right: rm*( rp ) + rc
  Rational lc, rc;
  bool success = decomposeTerm(left, lm, lp, lc);
  if(!success){ return false; }
  success = decomposeTerm(right, rm, rp, rc);
  if(!success){ return false; }

  Node diff = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::MINUS, left, right));
  Rational dc;
  success = decomposeTerm(diff, dm, dp, dc);
  Assert(success);

  // reduce the kind of the to not include literals
  // GT, NOT LEQ
  // GEQ, NOT LT
  // LT, NOT GEQ
  // LEQ, NOT LT
  Kind atomKind = atom.getKind();
  Kind normKind = negated ? negateKind(atomKind) : atomKind;

  if(normKind == GEQ || normKind == GT){
    dir = -1;
    normKind = (normKind == GEQ) ? LEQ : LT;
  }else{
    dir = 1;
  }

  Debug("arith::decomp") << "arith::decomp "
                         << lit << "(" << normKind << "*" << dir << ")"<< endl
                         << "  left:" << lc << " + " << lm << "*(" <<  lp << ") : " <<left << endl
                         << "  right:" << rc << " + " << rm << "*(" <<  rp << ") : " << right << endl
                         << "  diff: " << dc << " + " << dm << "*("<< dp <<"): " << diff << endl
                         << "  sep: " << sep << endl;


  // k in LT, LEQ, EQUAL, DISEQUAL
  // [dir*lm*( lp ) + dir*lc] k [dir*rm*( rp ) + dir*rc]
  Rational change = rc - lc;
  Assert(change == (-dc));
  // [dir*lm*( lp )] k [dir*rm*( rp ) + dir*(rc - lc)]
  if(normKind == LT){
    sep = DeltaRational(change, Rational(-1));
    k = LEQ;
  }else{
    sep = DeltaRational(change);
    k = normKind;
  }
  // k in LEQ, EQUAL, DISEQUAL
  // dir*lm*( lp ) k [dir*rm*( rp )] + dir*(sep + d * delta)
  return true;
}

/**
 *  Precondition:
 *   tp is a polynomial not containing an ite.
 *   either tp is constant or contains no constants.
 *  Post:
 *    if tmp.first is not null, then
 *      sgn * tp <= sgn * tmp.second
 */
void TheoryArithPrivate::entailmentCheckBoundLookup(std::pair<Node, DeltaRational>& tmp, int sgn, TNode tp) const {
  tmp.first = Node::null();
  if(sgn == 0){ return; }

  Assert(Polynomial::isMember(tp));
  if(tp.getKind() == CONST_RATIONAL){
    tmp.first = mkBoolNode(true);
    tmp.second = DeltaRational(tp.getConst<Rational>());
  }else if(d_partialModel.hasArithVar(tp)){
    Assert(tp.getKind() != CONST_RATIONAL);
    ArithVar v = d_partialModel.asArithVar(tp);
    Assert(v != ARITHVAR_SENTINEL);
    ConstraintP c = (sgn > 0)
      ? d_partialModel.getUpperBoundConstraint(v)
      : d_partialModel.getLowerBoundConstraint(v);
    if(c != NullConstraint){
      tmp.first = Constraint::externalExplainByAssertions({c});
      tmp.second = c->getValue();
    }
  }
}

void TheoryArithPrivate::entailmentCheckRowSum(std::pair<Node, DeltaRational>& tmp, int sgn, TNode tp) const {
  tmp.first = Node::null();
  if(sgn == 0){ return; }
  if(tp.getKind() != PLUS){ return; }
  Assert(Polynomial::isMember(tp));

  tmp.second = DeltaRational(0);
  NodeBuilder nb(kind::AND);

  Polynomial p = Polynomial::parsePolynomial(tp);
  for(Polynomial::iterator i = p.begin(), iend = p.end(); i != iend; ++i) {
    Monomial m = *i;
    Node x = m.getVarList().getNode();
    if(d_partialModel.hasArithVar(x)){
      ArithVar v = d_partialModel.asArithVar(x);
      const Rational& coeff = m.getConstant().getValue();
      int dir = sgn * coeff.sgn();
      ConstraintP c = (dir > 0)
        ? d_partialModel.getUpperBoundConstraint(v)
        : d_partialModel.getLowerBoundConstraint(v);
      if(c != NullConstraint){
        tmp.second += c->getValue() * coeff;
        c->externalExplainByAssertions(nb);
      }else{
        //failed
        return;
      }
    }else{
      // failed
      return;
    }
  }
  // success
  tmp.first = nb;
}

ArithProofRuleChecker* TheoryArithPrivate::getProofChecker()
{
  return &d_checker;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5

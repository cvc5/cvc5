/*********************                                                        */
/*! \file theory_arith.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): kshitij, ajreynol, mdeters, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/theory_arith_private.h"

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
#include "theory/arith/simplex.h"
#include "theory/arith/arith_static_learner.h"
#include "theory/arith/dio_solver.h"
#include "theory/arith/congruence_manager.h"

#include "theory/arith/approx_simplex.h"
#include "theory/arith/constraint.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/matrix.h"

#include "theory/arith/arith_rewriter.h"
#include "theory/arith/constraint.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/normal_form.h"
#include "theory/model.h"

#include "theory/arith/options.h"

#include <stdint.h>

#include <vector>
#include <map>
#include <queue>

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

TheoryArithPrivate::TheoryArithPrivate(TheoryArith& containing, context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe) :
  d_containing(containing),
  d_nlIncomplete( false),
  d_boundTracking(),
  d_constraintDatabase(c, u, d_partialModel, d_congruenceManager, RaiseConflict(*this)),
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
  d_partialModel(c, DeltaComputeCallback(*this)),
  d_errorSet(d_partialModel, TableauSizes(&d_tableau), BoundCountingLookup(&d_boundTracking)),
  d_tableau(),
  d_linEq(d_partialModel, d_tableau, d_boundTracking, BasicVarModelUpdateCallBack(*this)),
  d_diosolver(c),
  d_restartsCounter(0),
  d_tableauSizeHasBeenModified(false),
  d_tableauResetDensity(1.6),
  d_tableauResetPeriod(10),
  d_conflicts(c),
  d_congruenceManager(c, d_constraintDatabase, SetupLiteralCallBack(*this), d_partialModel, RaiseConflict(*this)),
  d_dualSimplex(d_linEq, d_errorSet, RaiseConflict(*this), TempVarMalloc(*this)),
  d_pureUpdate(d_linEq, d_errorSet, RaiseConflict(*this), TempVarMalloc(*this)),
  d_fcSimplex(d_linEq, d_errorSet, RaiseConflict(*this), TempVarMalloc(*this)),
  d_soiSimplex(d_linEq, d_errorSet, RaiseConflict(*this), TempVarMalloc(*this)),
  d_DELTA_ZERO(0),
  d_fullCheckCounter(0),
  d_cutCount(c, 0),
  d_cutInContext(c),
  d_statistics()
{
}

TheoryArithPrivate::~TheoryArithPrivate(){ }


void TheoryArithPrivate::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_congruenceManager.setMasterEqualityEngine(eq);
}

Node TheoryArithPrivate::getRealDivideBy0Func(){
  Assert(!getLogicInfo().isLinear());
  Assert(getLogicInfo().areRealsUsed());

  if(d_realDivideBy0Func.isNull()){
    TypeNode realType = NodeManager::currentNM()->realType();
    d_realDivideBy0Func = skolemFunction("/by0_$$", realType, realType);
  }
  return d_realDivideBy0Func;
}

Node TheoryArithPrivate::getIntDivideBy0Func(){
  Assert(!getLogicInfo().isLinear());
  Assert(getLogicInfo().areIntegersUsed());

  if(d_intDivideBy0Func.isNull()){
    TypeNode intType = NodeManager::currentNM()->integerType();
    d_intDivideBy0Func = skolemFunction("divby0_$$", intType, intType);
  }
  return d_intDivideBy0Func;
}

Node TheoryArithPrivate::getIntModulusBy0Func(){
  Assert(!getLogicInfo().isLinear());
  Assert(getLogicInfo().areIntegersUsed());

  if(d_intModulusBy0Func.isNull()){
    TypeNode intType = NodeManager::currentNM()->integerType();
    d_intModulusBy0Func = skolemFunction("modby0_$$", intType, intType);
  }
  return d_intModulusBy0Func;
}

TheoryArithPrivate::ModelException::ModelException(TNode n, const char* msg) throw (){
  stringstream ss;
  ss << "Cannot construct a model for " << n << " as " << endl << msg;
  setMessage(ss.str());
}
TheoryArithPrivate::ModelException::~ModelException() throw (){ }


TheoryArithPrivate::Statistics::Statistics():
  d_statAssertUpperConflicts("theory::arith::AssertUpperConflicts", 0),
  d_statAssertLowerConflicts("theory::arith::AssertLowerConflicts", 0),
  d_statUserVariables("theory::arith::UserVariables", 0),
  d_statSlackVariables("theory::arith::SlackVariables", 0),
  d_statDisequalitySplits("theory::arith::DisequalitySplits", 0),
  d_statDisequalityConflicts("theory::arith::DisequalityConflicts", 0),
  d_simplifyTimer("theory::arith::simplifyTimer"),
  d_staticLearningTimer("theory::arith::staticLearningTimer"),
  d_presolveTime("theory::arith::presolveTime"),
  d_newPropTime("theory::arith::newPropTimer"),
  d_externalBranchAndBounds("theory::arith::externalBranchAndBounds",0),
  d_initialTableauSize("theory::arith::initialTableauSize", 0),
  d_currSetToSmaller("theory::arith::currSetToSmaller", 0),
  d_smallerSetToCurr("theory::arith::smallerSetToCurr", 0),
  d_restartTimer("theory::arith::restartTimer"),
  d_boundComputationTime("theory::arith::bound::time"),
  d_boundComputations("theory::arith::bound::boundComputations",0),
  d_boundPropagations("theory::arith::bound::boundPropagations",0),
  d_unknownChecks("theory::arith::status::unknowns", 0),
  d_maxUnknownsInARow("theory::arith::status::maxUnknownsInARow", 0),
  d_avgUnknownsInARow("theory::arith::status::avgUnknownsInARow"),
  d_revertsOnConflicts("theory::arith::status::revertsOnConflicts",0),
  d_commitsOnConflicts("theory::arith::status::commitsOnConflicts",0),
  d_nontrivialSatChecks("theory::arith::status::nontrivialSatChecks",0),
  d_satPivots("pivots::sat"),
  d_unsatPivots("pivots::unsat"),
  d_unknownPivots("pivots::unkown")
{
  StatisticsRegistry::registerStat(&d_statAssertUpperConflicts);
  StatisticsRegistry::registerStat(&d_statAssertLowerConflicts);

  StatisticsRegistry::registerStat(&d_statUserVariables);
  StatisticsRegistry::registerStat(&d_statSlackVariables);
  StatisticsRegistry::registerStat(&d_statDisequalitySplits);
  StatisticsRegistry::registerStat(&d_statDisequalityConflicts);
  StatisticsRegistry::registerStat(&d_simplifyTimer);
  StatisticsRegistry::registerStat(&d_staticLearningTimer);

  StatisticsRegistry::registerStat(&d_presolveTime);
  StatisticsRegistry::registerStat(&d_newPropTime);

  StatisticsRegistry::registerStat(&d_externalBranchAndBounds);

  StatisticsRegistry::registerStat(&d_initialTableauSize);
  StatisticsRegistry::registerStat(&d_currSetToSmaller);
  StatisticsRegistry::registerStat(&d_smallerSetToCurr);
  StatisticsRegistry::registerStat(&d_restartTimer);

  StatisticsRegistry::registerStat(&d_boundComputationTime);
  StatisticsRegistry::registerStat(&d_boundComputations);
  StatisticsRegistry::registerStat(&d_boundPropagations);

  StatisticsRegistry::registerStat(&d_unknownChecks);
  StatisticsRegistry::registerStat(&d_maxUnknownsInARow);
  StatisticsRegistry::registerStat(&d_avgUnknownsInARow);
  StatisticsRegistry::registerStat(&d_revertsOnConflicts);
  StatisticsRegistry::registerStat(&d_commitsOnConflicts);
  StatisticsRegistry::registerStat(&d_nontrivialSatChecks);


  StatisticsRegistry::registerStat(&d_satPivots);
  StatisticsRegistry::registerStat(&d_unsatPivots);
  StatisticsRegistry::registerStat(&d_unknownPivots);
}

TheoryArithPrivate::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statAssertUpperConflicts);
  StatisticsRegistry::unregisterStat(&d_statAssertLowerConflicts);

  StatisticsRegistry::unregisterStat(&d_statUserVariables);
  StatisticsRegistry::unregisterStat(&d_statSlackVariables);
  StatisticsRegistry::unregisterStat(&d_statDisequalitySplits);
  StatisticsRegistry::unregisterStat(&d_statDisequalityConflicts);
  StatisticsRegistry::unregisterStat(&d_simplifyTimer);
  StatisticsRegistry::unregisterStat(&d_staticLearningTimer);

  StatisticsRegistry::unregisterStat(&d_presolveTime);
  StatisticsRegistry::unregisterStat(&d_newPropTime);

  StatisticsRegistry::unregisterStat(&d_externalBranchAndBounds);

  StatisticsRegistry::unregisterStat(&d_initialTableauSize);
  StatisticsRegistry::unregisterStat(&d_currSetToSmaller);
  StatisticsRegistry::unregisterStat(&d_smallerSetToCurr);
  StatisticsRegistry::unregisterStat(&d_restartTimer);

  StatisticsRegistry::unregisterStat(&d_boundComputationTime);
  StatisticsRegistry::unregisterStat(&d_boundComputations);
  StatisticsRegistry::unregisterStat(&d_boundPropagations);

  StatisticsRegistry::unregisterStat(&d_unknownChecks);
  StatisticsRegistry::unregisterStat(&d_maxUnknownsInARow);
  StatisticsRegistry::unregisterStat(&d_avgUnknownsInARow);
  StatisticsRegistry::unregisterStat(&d_revertsOnConflicts);
  StatisticsRegistry::unregisterStat(&d_commitsOnConflicts);
  StatisticsRegistry::unregisterStat(&d_nontrivialSatChecks);

  StatisticsRegistry::unregisterStat(&d_satPivots);
  StatisticsRegistry::unregisterStat(&d_unsatPivots);
  StatisticsRegistry::unregisterStat(&d_unknownPivots);
}

void TheoryArithPrivate::revertOutOfConflict(){
  d_partialModel.revertAssignmentChanges();
  clearUpdates();
  d_currentPropagationList.clear();
}

void TheoryArithPrivate::clearUpdates(){
  d_updatedBounds.purge();
}

void TheoryArithPrivate::zeroDifferenceDetected(ArithVar x){
  Assert(d_congruenceManager.isWatchedVariable(x));
  Assert(d_partialModel.upperBoundIsZero(x));
  Assert(d_partialModel.lowerBoundIsZero(x));

  Constraint lb = d_partialModel.getLowerBoundConstraint(x);
  Constraint ub = d_partialModel.getUpperBoundConstraint(x);

  if(lb->isEquality()){
    d_congruenceManager.watchedVariableIsZero(lb);
  }else if(ub->isEquality()){
    d_congruenceManager.watchedVariableIsZero(ub);
  }else{
    d_congruenceManager.watchedVariableIsZero(lb, ub);
  }
}

/* procedure AssertLower( x_i >= c_i ) */
bool TheoryArithPrivate::AssertLower(Constraint constraint){
  Assert(constraint != NullConstraint);
  Assert(constraint->isLowerBound());

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
    Constraint ubc = d_partialModel.getUpperBoundConstraint(x_i);
    Node conflict = ConstraintValue::explainConflict(ubc, constraint);
    Debug("arith") << "AssertLower conflict " << conflict << endl;
    ++(d_statistics.d_statAssertLowerConflicts);
    raiseConflict(conflict);
    return true;
  }else if(cmpToUB == 0){
    if(isInteger(x_i)){
      d_constantIntegerVariables.push_back(x_i);
      Debug("dio::push") << x_i << endl;
    }
    Constraint ub = d_partialModel.getUpperBoundConstraint(x_i);

    if(!d_congruenceManager.isWatchedVariable(x_i) || c_i.sgn() != 0){
      // if it is not a watched variable report it
      // if it is is a watched variable and c_i == 0,
      // let zeroDifferenceDetected(x_i) catch this
      d_congruenceManager.equalsConstant(constraint, ub);
    }

    const ValueCollection& vc = constraint->getValueCollection();
    if(vc.hasDisequality()){
      Assert(vc.hasEquality());
      const Constraint eq = vc.getEquality();
      const Constraint diseq = vc.getDisequality();
      if(diseq->isTrue()){
        //const Constraint ub = vc.getUpperBound();
        Node conflict = ConstraintValue::explainConflict(diseq, ub, constraint);

        ++(d_statistics.d_statDisequalityConflicts);
        Debug("eq") << " assert lower conflict " << conflict << endl;
        raiseConflict(conflict);
        return true;
      }else if(!eq->isTrue()){
        Debug("eq") << "lb == ub, propagate eq" << eq << endl;
        eq->impliedBy(constraint, d_partialModel.getUpperBoundConstraint(x_i));
        // do not need to add to d_learnedBounds
      }
    }
  }else{
    Assert(cmpToUB < 0);
    const ValueCollection& vc = constraint->getValueCollection();

    if(vc.hasDisequality()){
      const Constraint diseq = vc.getDisequality();
      if(diseq->isTrue()){
        const Constraint ub = d_constraintDatabase.ensureConstraint(const_cast<ValueCollection&>(vc), UpperBound);

        if(ub->hasProof()){
          Node conflict = ConstraintValue::explainConflict(diseq, ub, constraint);
          Debug("eq") << " assert upper conflict " << conflict << endl;
          raiseConflict(conflict);
          return true;
        }else if(!ub->negationHasProof()){
          Constraint negUb = ub->getNegation();
          negUb->impliedBy(constraint, diseq);
          d_learnedBounds.push_back(negUb);
        }
      }
    }
  }

  d_currentPropagationList.push_back(constraint);
  d_currentPropagationList.push_back(d_partialModel.getLowerBoundConstraint(x_i));

  d_partialModel.setLowerBoundConstraint(constraint);

  if(d_congruenceManager.isWatchedVariable(x_i)){
    int sgn = c_i.sgn();
    if(sgn > 0){
      d_congruenceManager.watchedVariableCannotBeZero(constraint);
    }else if(sgn == 0 && d_partialModel.upperBoundIsZero(x_i)){
      zeroDifferenceDetected(x_i);
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
bool TheoryArithPrivate::AssertUpper(Constraint constraint){
  ArithVar x_i = constraint->getVariable();
  const DeltaRational& c_i = constraint->getValue();

  Debug("arith") << "AssertUpper(" << x_i << " " << c_i << ")"<< std::endl;
  AssertArgument(constraint != NullConstraint,
                 "AssertUpper() called on a NullConstraint.");
  Assert(constraint->isUpperBound());

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
    Constraint lbc = d_partialModel.getLowerBoundConstraint(x_i);
    Node conflict =  ConstraintValue::explainConflict(lbc, constraint);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
    ++(d_statistics.d_statAssertUpperConflicts);
    raiseConflict(conflict);
    return true;
  }else if(cmpToLB == 0){ // \lowerBound(x_i) == \upperbound(x_i)
    if(isInteger(x_i)){
      d_constantIntegerVariables.push_back(x_i);
      Debug("dio::push") << x_i << endl;
    }
    Constraint lb = d_partialModel.getLowerBoundConstraint(x_i);
    if(!d_congruenceManager.isWatchedVariable(x_i) || c_i.sgn() != 0){
      // if it is not a watched variable report it
      // if it is is a watched variable and c_i == 0,
      // let zeroDifferenceDetected(x_i) catch this
      d_congruenceManager.equalsConstant(lb, constraint);
    }

    const ValueCollection& vc = constraint->getValueCollection();
    if(vc.hasDisequality()){
      Assert(vc.hasEquality());
      const Constraint diseq = vc.getDisequality();
      const Constraint eq = vc.getEquality();
      if(diseq->isTrue()){
        Node conflict = ConstraintValue::explainConflict(diseq, lb, constraint);
        Debug("eq") << " assert upper conflict " << conflict << endl;
        raiseConflict(conflict);
        return true;
      }else if(!eq->isTrue()){
        Debug("eq") << "lb == ub, propagate eq" << eq << endl;
        eq->impliedBy(constraint, d_partialModel.getLowerBoundConstraint(x_i));
        //do not bother to add to d_learnedBounds
      }
    }
  }else if(cmpToLB > 0){
    const ValueCollection& vc = constraint->getValueCollection();
    if(vc.hasDisequality()){
      const Constraint diseq = vc.getDisequality();
      if(diseq->isTrue()){
        const Constraint lb =
          d_constraintDatabase.ensureConstraint(const_cast<ValueCollection&>(vc), LowerBound);
        if(lb->hasProof()){
          Node conflict = ConstraintValue::explainConflict(diseq, lb, constraint);
          Debug("eq") << " assert upper conflict " << conflict << endl;
          raiseConflict(conflict);
          return true;
        }else if(!lb->negationHasProof()){
          Constraint negLb = lb->getNegation();
          negLb->impliedBy(constraint, diseq);
          //if(!negLb->canBePropagated()){
          d_learnedBounds.push_back(negLb);
          //}//otherwise let this be propagated/asserted later
        }
      }
    }
  }

  d_currentPropagationList.push_back(constraint);
  d_currentPropagationList.push_back(d_partialModel.getUpperBoundConstraint(x_i));
  //It is fine if this is NullConstraint

  d_partialModel.setUpperBoundConstraint(constraint);

  if(d_congruenceManager.isWatchedVariable(x_i)){
    int sgn = c_i.sgn();
     if(sgn < 0){
       d_congruenceManager.watchedVariableCannotBeZero(constraint);
     }else if(sgn == 0 && d_partialModel.lowerBoundIsZero(x_i)){
       zeroDifferenceDetected(x_i);
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
bool TheoryArithPrivate::AssertEquality(Constraint constraint){
  AssertArgument(constraint != NullConstraint,
                 "AssertUpper() called on a NullConstraint.");

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

  if(cmpToUB > 0){
    Constraint ubc = d_partialModel.getUpperBoundConstraint(x_i);
    Node conflict = ConstraintValue::explainConflict(ubc, constraint);
    Debug("arith") << "AssertEquality conflicts with upper bound " << conflict << endl;
    raiseConflict(conflict);
    return true;
  }

  if(cmpToLB < 0){
    Constraint lbc = d_partialModel.getLowerBoundConstraint(x_i);
    Node conflict = ConstraintValue::explainConflict(lbc, constraint);
    Debug("arith") << "AssertEquality conflicts with lower bound" << conflict << endl;
    raiseConflict(conflict);
    return true;
  }

  Assert(cmpToUB <= 0);
  Assert(cmpToLB >= 0);
  Assert(cmpToUB < 0 || cmpToLB > 0);


  if(isInteger(x_i)){
    d_constantIntegerVariables.push_back(x_i);
    Debug("dio::push") << x_i << endl;
  }

  // Don't bother to check whether x_i != c_i is in d_diseq
  // The a and (not a) should never be on the fact queue
  d_currentPropagationList.push_back(constraint);
  d_currentPropagationList.push_back(d_partialModel.getLowerBoundConstraint(x_i));
  d_currentPropagationList.push_back(d_partialModel.getUpperBoundConstraint(x_i));

  d_partialModel.setUpperBoundConstraint(constraint);
  d_partialModel.setLowerBoundConstraint(constraint);

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
bool TheoryArithPrivate::AssertDisequality(Constraint constraint){

  AssertArgument(constraint != NullConstraint,
                 "AssertUpper() called on a NullConstraint.");
  ArithVar x_i = constraint->getVariable();
  const DeltaRational& c_i = constraint->getValue();

  Debug("arith") << "AssertDisequality(" << x_i << " " << c_i << ")"<< std::endl;

  //Should be fine in integers
  Assert(!isInteger(x_i) || c_i.isIntegral());

  if(d_congruenceManager.isWatchedVariable(x_i)){
    int sgn = c_i.sgn();
    if(sgn == 0){
      d_congruenceManager.watchedVariableCannotBeZero(constraint);
    }
  }

  const ValueCollection& vc = constraint->getValueCollection();
  if(vc.hasLowerBound() && vc.hasUpperBound()){
    const Constraint lb = vc.getLowerBound();
    const Constraint ub = vc.getUpperBound();
    if(lb->isTrue() && ub->isTrue()){
      //in conflict
      Debug("eq") << "explaining" << endl;
      ++(d_statistics.d_statDisequalityConflicts);
      Node conflict = ConstraintValue::explainConflict(constraint, lb, ub);
      raiseConflict(conflict);
      return true;
    }
  }
  if(vc.hasLowerBound() ){
    const Constraint lb = vc.getLowerBound();
    if(lb->isTrue()){
      const Constraint ub = d_constraintDatabase.ensureConstraint(const_cast<ValueCollection&>(vc), UpperBound);
      Debug("eq") << "propagate UpperBound " << constraint << lb << ub << endl;
      const Constraint negUb = ub->getNegation();
      if(!negUb->isTrue()){
        negUb->impliedBy(constraint, lb);
        d_learnedBounds.push_back(negUb);
      }
    }
  }
  if(vc.hasUpperBound()){
    const Constraint ub = vc.getUpperBound();
    if(ub->isTrue()){
      const Constraint lb = d_constraintDatabase.ensureConstraint(const_cast<ValueCollection&>(vc), LowerBound);

      Debug("eq") << "propagate LowerBound " << constraint << lb << ub << endl;
      const Constraint negLb = lb->getNegation();
      if(!negLb->isTrue()){
        negLb->impliedBy(constraint, ub);
        d_learnedBounds.push_back(negLb);
      }
    }
  }

  bool split = constraint->isSplit();

  if(!split && c_i == d_partialModel.getAssignment(x_i)){
    Debug("eq") << "lemma now! " << constraint << endl;
    outputLemma(constraint->split());
    return false;
  }else if(d_partialModel.strictlyLessThanLowerBound(x_i, c_i)){
    Debug("eq") << "can drop as less than lb" << constraint << endl;
  }else if(d_partialModel.strictlyGreaterThanUpperBound(x_i, c_i)){
    Debug("eq") << "can drop as less than ub" << constraint << endl;
  }else if(!split){
    Debug("eq") << "push back" << constraint << endl;
    d_diseqQueue.push(constraint);
    d_partialModel.invalidateDelta();
  }else{
    Debug("eq") << "skipping already split " << constraint << endl;
  }
  return false;
}

void TheoryArithPrivate::addSharedTerm(TNode n){
  Debug("arith::addSharedTerm") << "addSharedTerm: " << n << endl;
  if(n.isConst()){
    d_partialModel.invalidateDelta();
  }

  d_congruenceManager.addSharedTerm(n);
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

Node TheoryArithPrivate::ppRewrite(TNode atom) {
  Debug("arith::preprocess") << "arith::preprocess() : " << atom << endl;


  if (atom.getKind() == kind::EQUAL  && options::arithRewriteEq()) {
    Node leq = NodeBuilder<2>(kind::LEQ) << atom[0] << atom[1];
    Node geq = NodeBuilder<2>(kind::GEQ) << atom[0] << atom[1];
    Node rewritten = Rewriter::rewrite(leq.andNode(geq));
    Debug("arith::preprocess") << "arith::preprocess() : returning "
                               << rewritten << endl;
    return rewritten;
  } else {
    return atom;
  }
}

Theory::PPAssertStatus TheoryArithPrivate::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_simplifyTimer);
  Debug("simplify") << "TheoryArithPrivate::solve(" << in << ")" << endl;


  // Solve equalities
  Rational minConstant = 0;
  Node minMonomial;
  Node minVar;
  if (in.getKind() == kind::EQUAL) {
    Comparison cmp = Comparison::parseNormalForm(in);

    Polynomial left = cmp.getLeft();
    Polynomial right = cmp.getRight();

    Monomial m = left.getHead();
    if (m.getVarList().singleton()){
      VarList vl = m.getVarList();
      Node var = vl.getNode();
      if (var.getKind() == kind::VARIABLE){
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


      static const unsigned MAX_SUB_SIZE = 2;
      if(right.size() > MAX_SUB_SIZE){
        Debug("simplify") << "TheoryArithPrivate::solve(): did not substitute due to the right hand side containing too many terms: " << minVar << ":" << elim << endl;
        Debug("simplify") << right.size() << endl;
        // cout << "TheoryArithPrivate::solve(): did not substitute due to the right hand side containing too many terms: " << minVar << ":" << elim << endl;
        // cout << right.size() << endl;
      }else if(elim.hasSubterm(minVar)){
        Debug("simplify") << "TheoryArithPrivate::solve(): can't substitute due to recursive pattern with sharing: " << minVar << ":" << elim << endl;
        // cout << "TheoryArithPrivate::solve(): can't substitute due to recursive pattern with sharing: " << minVar << ":" << elim << endl;

      }else if (!minVar.getType().isInteger() || right.isIntegral()) {
        Assert(!elim.hasSubterm(minVar));
        // cannot eliminate integers here unless we know the resulting
        // substitution is integral
        Debug("simplify") << "TheoryArithPrivate::solve(): substitution " << minVar << " |-> " << elim << endl;
        //cout << "TheoryArithPrivate::solve(): substitution " << minVar << " |-> " << elim << endl;

        outSubstitutions.addSubstitution(minVar, elim);
        return Theory::PP_ASSERT_STATUS_SOLVED;
      } else {
        Debug("simplify") << "TheoryArithPrivate::solve(): can't substitute b/c it's integer: " << minVar << ":" << minVar.getType() << " |-> " << elim << ":" << elim.getType() << endl;
        //cout << "TheoryArithPrivate::solve(): can't substitute b/c it's integer: " << minVar << ":" << minVar.getType() << " |-> " << elim << ":" << elim.getType() << endl;

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

void TheoryArithPrivate::ppStaticLearn(TNode n, NodeBuilder<>& learned) {
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
  Assert(bestBasic == ARITHVAR_SENTINEL || bestRowLength < std::numeric_limits<uint32_t>::max());
  return bestBasic;
}

void TheoryArithPrivate::setupVariable(const Variable& x){
  Node n = x.getNode();

  Assert(!isSetup(n));

  ++(d_statistics.d_statUserVariables);
  requestArithVar(n,false);
  //ArithVar varN = requestArithVar(n,false);
  //setupInitialValue(varN);

  markSetup(n);


  if(x.isDivLike()){
    setupDivLike(x);
  }

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
      throw LogicException("Non-linear term was asserted to arithmetic in a linear logic.");
    }

    setIncomplete();
    d_nlIncomplete = true;

    ++(d_statistics.d_statUserVariables);
    requestArithVar(vlNode, false);
    //ArithVar av = requestArithVar(vlNode, false);
    //setupInitialValue(av);

    markSetup(vlNode);
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

void TheoryArithPrivate::setupDivLike(const Variable& v){
  Assert(v.isDivLike());

  if(getLogicInfo().isLinear()){
    throw LogicException("Non-linear term was asserted to arithmetic in a linear logic.");
  }

  Node vnode = v.getNode();
  Assert(isSetup(vnode)); // Otherwise there is some invariant breaking recursion
  Polynomial m = Polynomial::parsePolynomial(vnode[0]);
  Polynomial n = Polynomial::parsePolynomial(vnode[1]);

  cautiousSetupPolynomial(m);
  cautiousSetupPolynomial(n);

  Node lem;
  switch(vnode.getKind()){
  case DIVISION:
  case INTS_DIVISION:
  case INTS_MODULUS:
    lem = definingIteForDivLike(vnode);
    break;
  case DIVISION_TOTAL:
    lem = axiomIteForTotalDivision(vnode);
    break;
  case INTS_DIVISION_TOTAL:
  case INTS_MODULUS_TOTAL:
    lem = axiomIteForTotalIntDivision(vnode);
    break;
  default:
    /* intentionally blank */
    break;
  }

  if(!lem.isNull()){
    Debug("arith::div") << lem << endl;
    outputLemma(lem);
  }
}

Node TheoryArithPrivate::definingIteForDivLike(Node divLike){
  Kind k = divLike.getKind();
  Assert(k == DIVISION || k == INTS_DIVISION || k == INTS_MODULUS);
  // (for all ((n Real) (d Real))
  //  (=
  //   (DIVISION n d)
  //   (ite (= d 0)
  //    (APPLY [div_0_skolem_function] n)
  //    (DIVISION_TOTAL x y))))

  Polynomial n = Polynomial::parsePolynomial(divLike[0]);
  Polynomial d = Polynomial::parsePolynomial(divLike[1]);

  NodeManager* currNM = NodeManager::currentNM();
  Node dEq0 = currNM->mkNode(EQUAL, d.getNode(), mkRationalNode(0));

  Kind kTotal = (k == DIVISION) ? DIVISION_TOTAL :
    (k == INTS_DIVISION) ? INTS_DIVISION_TOTAL : INTS_MODULUS_TOTAL;

  Node by0Func = (k == DIVISION) ?  getRealDivideBy0Func():
    (k == INTS_DIVISION) ? getIntDivideBy0Func() : getIntModulusBy0Func();


  Debug("arith::div") << divLike << endl;
  Debug("arith::div") << by0Func << endl;

  Node divTotal = currNM->mkNode(kTotal, n.getNode(), d.getNode());
  Node divZero = currNM->mkNode(APPLY_UF, by0Func, n.getNode());

  Node defining = divLike.eqNode(dEq0.iteNode( divZero, divTotal));

  return defining;
}

Node TheoryArithPrivate::axiomIteForTotalDivision(Node div_tot){
  Assert(div_tot.getKind() == DIVISION_TOTAL);

  // Inverse of multiplication axiom:
  //   (for all ((n Real) (d Real))
  //    (ite (= d 0)
  //     (= (DIVISION_TOTAL n d) 0)
  //     (= (* d (DIVISION_TOTAL n d)) n)))


  Polynomial n = Polynomial::parsePolynomial(div_tot[0]);
  Polynomial d = Polynomial::parsePolynomial(div_tot[1]);
  Polynomial div_tot_p = Polynomial::parsePolynomial(div_tot);

  Comparison invEq = Comparison::mkComparison(EQUAL, n, d * div_tot_p);
  Comparison zeroEq = Comparison::mkComparison(EQUAL, div_tot_p, Polynomial::mkZero());
  Node dEq0 = (d.getNode()).eqNode(mkRationalNode(0));
  Node ite = dEq0.iteNode(zeroEq.getNode(), invEq.getNode());

  return ite;
}

Node TheoryArithPrivate::axiomIteForTotalIntDivision(Node int_div_like){
  Kind k = int_div_like.getKind();
  Assert(k == INTS_DIVISION_TOTAL || k == INTS_MODULUS_TOTAL);

  // (for all ((m Int) (n Int))
  //   (=> (distinct n 0)
  //       (let ((q (div m n)) (r (mod m n)))
  //         (and (= m (+ (* n q) r))
  //              (<= 0 r (- (abs n) 1))))))

  // Updated for div 0 functions
  // (for all ((m Int) (n Int))
  //   (let ((q (div m n)) (r (mod m n)))
  //     (ite (= n 0)
  //          (and (= q (div_0_func m)) (= r (mod_0_func m)))
  //          (and (= m (+ (* n q) r))
  //               (<= 0 r (- (abs n) 1)))))))

  Polynomial n = Polynomial::parsePolynomial(int_div_like[0]);
  Polynomial d = Polynomial::parsePolynomial(int_div_like[1]);

  NodeManager* currNM = NodeManager::currentNM();
  Node zero = mkRationalNode(0);

  Node q = (k == INTS_DIVISION_TOTAL) ? int_div_like : currNM->mkNode(INTS_DIVISION_TOTAL, n.getNode(), d.getNode());
  Node r = (k == INTS_MODULUS_TOTAL) ? int_div_like : currNM->mkNode(INTS_MODULUS_TOTAL, n.getNode(), d.getNode());

  Node dEq0 = (d.getNode()).eqNode(zero);
  Node qEq0 = q.eqNode(zero);
  Node rEq0 = r.eqNode(zero);

  Polynomial rp = Polynomial::parsePolynomial(r);
  Polynomial qp = Polynomial::parsePolynomial(q);

  Node abs_d = (n.isConstant()) ?
    d.getHead().getConstant().abs().getNode() : mkIntSkolem("abs_$$");

  Node eq = Comparison::mkComparison(EQUAL, n, d * qp + rp).getNode();
  Node leq0 = currNM->mkNode(LEQ, zero, r);
  Node leq1 = currNM->mkNode(LT, r, abs_d);

  Node andE = currNM->mkNode(AND, eq, leq0, leq1);
  Node defDivMode = dEq0.iteNode(qEq0.andNode(rEq0), andE);
  Node lem = abs_d.getMetaKind () == metakind::VARIABLE ?
    defDivMode.andNode(d.makeAbsCondition(Variable(abs_d))) : defDivMode;

  return lem;
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

    ArithVar varSlack = requestArithVar(polyNode, true);
    d_tableau.addRow(varSlack, coefficients, variables);
    setupBasicValue(varSlack);
    d_linEq.trackVariable(varSlack);

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

    ++(d_statistics.d_statSlackVariables);
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
  Assert(isRelationOperator(atom.getKind()));
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

  if(isRelationOperator(n.getKind())){
    if(!isSetup(n)){
      setupAtom(n);
    }
    Constraint c = d_constraintDatabase.lookup(n);
    Assert(c != NullConstraint);

    Debug("arith::preregister") << "setup constraint" << c << endl;
    Assert(!c->canBePropagated());
    c->setPreregistered();
  }

  Debug("arith::preregister") << "end arith::preRegisterTerm("<< n <<")" << endl;
}

void TheoryArithPrivate::releaseArithVar(ArithVar v){
  Assert(d_partialModel.hasNode(v));

  d_constraintDatabase.removeVariable(v);
  d_partialModel.releaseArithVar(v);
  d_linEq.maybeRemoveTracking(v);
}

ArithVar TheoryArithPrivate::requestArithVar(TNode x, bool slack){
  //TODO : The VarList trick is good enough?
  Assert(isLeaf(x) || VarList::isMember(x) || x.getKind() == PLUS);
  if(getLogicInfo().isLinear() && Variable::isDivMember(x)){
    throw LogicException("Non-linear term was asserted to arithmetic in a linear logic.");
  }
  Assert(!d_partialModel.hasArithVar(x));
  Assert(x.getType().isReal()); // real or integer

  // ArithVar varX = d_variables.size();
  // d_variables.push_back(Node(x));

  ArithVar max = d_partialModel.getNumberOfVariables();
  ArithVar varX = d_partialModel.allocate(x, slack);

  bool reclaim =  max >= d_partialModel.getNumberOfVariables();;

  if(reclaim){
    // varX = d_pool.back();
    // d_pool.pop_back();

    // d_partialModel.setAssignment(varX, d_DELTA_ZERO, d_DELTA_ZERO);
  }else{
    // varX = d_numberOfVariables;
    // ++d_numberOfVariables;

    // d_slackVars.push_back(true);
    // d_variableTypes.push_back(ATReal);

    d_dualSimplex.increaseMax();

    d_tableau.increaseSize();
    d_tableauSizeHasBeenModified = true;

    //d_partialModel.initialize(varX, d_DELTA_ZERO);
  }

  // ArithType type;
  // if(slack){
  //   //The type computation is not quite accurate for Rationals that are integral.
  //   //We'll use the isIntegral check from the polynomial package instead.
  //   Polynomial p = Polynomial::parsePolynomial(x);
  //   type = p.isIntegral() ? ATInteger : ATReal;
  // }else{
  //   type = nodeToArithType(x);
  // }
  // d_variableTypes[varX] = type;
  // d_slackVars[varX] = slack;

  d_constraintDatabase.addVariable(varX);

  //d_partialModel.setArithVar(x,varX);

  // Debug("integers") << "isInteger[[" << x << "]]: " << x.getType().isInteger() << endl;

  // if(slack){
  //   //The type computation is not quite accurate for Rationals that are integral.
  //   //We'll use the isIntegral check from the polynomial package instead.
  //   Polynomial p = Polynomial::parsePolynomial(x);
  //   d_variableTypes.push_back(p.isIntegral() ? ATInteger : ATReal);
  // }else{
  //   d_variableTypes.push_back(nodeToArithType(x));
  // }

  // d_slackVars.push_back(slack);

  // d_simplex.increaseMax();

  // d_tableau.increaseSize();
  // d_tableauSizeHasBeenModified = true;

  // d_constraintDatabase.addVariable(varX);

  Debug("arith::arithvar") << x << " |-> " << varX << endl;

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

    Debug("rewriter") << "should be var: " << n << endl;

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
  Polynomial betaAsPolynomial( Constant::mkConstant(beta.floor()) );

  TNode var = d_partialModel.asNode(v);
  Polynomial varAsPolynomial = Polynomial::parsePolynomial(var);
  return Comparison::mkComparison(EQUAL, varAsPolynomial, betaAsPolynomial);
}

Node TheoryArithPrivate::dioCutting(){
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
          Debug("dio::push") <<v << " " <<  eq.getNode() << endl;
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
    return Node::null();
  }else{
    Polynomial p = plane.getPolynomial();
    Polynomial c(plane.getConstant() * Constant::mkConstant(-1));
    Integer gcd = p.gcd();
    Assert(p.isIntegral());
    Assert(c.isIntegral());
    Assert(gcd > 1);
    Assert(!gcd.divides(c.asConstant().getNumerator()));
    Comparison leq = Comparison::mkComparison(LEQ, p, c);
    Comparison geq = Comparison::mkComparison(GEQ, p, c);
    Node lemma = NodeManager::currentNM()->mkNode(OR, leq.getNode(), geq.getNode());
    Node rewrittenLemma = Rewriter::rewrite(lemma);
    Debug("arith::dio") << "dioCutting found the plane: " << plane.getNode() << endl;
    Debug("arith::dio") << "resulting in the cut: " << lemma << endl;
    Debug("arith::dio") << "rewritten " << rewrittenLemma << endl;
    return rewrittenLemma;
  }
}

Node TheoryArithPrivate::callDioSolver(){
  while(!d_constantIntegerVariables.empty()){
    ArithVar v = d_constantIntegerVariables.front();
    d_constantIntegerVariables.pop();

    Debug("arith::dio")  << v << endl;

    Assert(isInteger(v));
    Assert(d_partialModel.boundsAreEqual(v));


    Constraint lb = d_partialModel.getLowerBoundConstraint(v);
    Constraint ub = d_partialModel.getUpperBoundConstraint(v);

    Node orig = Node::null();
    if(lb->isEquality()){
      orig = lb->explainForConflict();
    }else if(ub->isEquality()){
      orig = ub->explainForConflict();
    }else {
      orig = ConstraintValue::explainConflict(ub, lb);
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
      Debug("dio::push") << v << " " << eq.getNode() << " with reason " << orig << endl;
      d_diosolver.pushInputConstraint(eq, orig);
    }
  }

  return d_diosolver.processEquationsForConflict();
}

Constraint TheoryArithPrivate::constraintFromFactQueue(){
  Assert(!done());
  TNode assertion = get();

  Kind simpleKind = Comparison::comparisonKind(assertion);
  Constraint constraint = d_constraintDatabase.lookup(assertion);
  if(constraint == NullConstraint){
    Assert(simpleKind == EQUAL || simpleKind == DISTINCT );
    bool isDistinct = simpleKind == DISTINCT;
    Node eq = (simpleKind == DISTINCT) ? assertion[0] : assertion;
    Assert(!isSetup(eq));
    Node reEq = Rewriter::rewrite(eq);
    if(reEq.getKind() == CONST_BOOLEAN){
      if(reEq.getConst<bool>() == isDistinct){
        // if is (not true), or false
        Assert((reEq.getConst<bool>() && isDistinct) ||
               (!reEq.getConst<bool>() && !isDistinct));
        raiseConflict(assertion);
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

  // Kind simpleKind = Comparison::comparisonKind(assertion);
  // Assert(simpleKind != UNDEFINED_KIND);
  // Assert(constraint != NullConstraint ||
  //        simpleKind == EQUAL ||
  //        simpleKind == DISTINCT );
  // if(simpleKind == EQUAL || simpleKind == DISTINCT){
  //   Node eq = (simpleKind == DISTINCT) ? assertion[0] : assertion;

  //   if(!isSetup(eq)){
  //     //The previous code was equivalent to:
  //     setupAtom(eq);
  //     constraint = d_constraintDatabase.lookup(assertion);
  //   }
  // }
  Assert(constraint != NullConstraint);

  if(constraint->negationHasProof()){
    Constraint negation = constraint->getNegation();
    if(negation->isSelfExplaining()){
      if(Debug.isOn("whytheoryenginewhy")){
        debugPrintFacts();
      }
    }
    Debug("arith::eq") << constraint << endl;
    Debug("arith::eq") << negation << endl;

    NodeBuilder<> nb(kind::AND);
    nb << assertion;
    negation->explainForConflict(nb);
    Node conflict = nb;
    Debug("arith::eq") << "conflict" << conflict << endl;
    raiseConflict(conflict);
    return NullConstraint;
  }
  Assert(!constraint->negationHasProof());

  if(constraint->assertedToTheTheory()){
    //Do nothing
    return NullConstraint;
  }else{
    Debug("arith::constraint") << "arith constraint " << constraint << std::endl;
    constraint->setAssertedToTheTheory(assertion);

    if(!constraint->hasProof()){
      Debug("arith::constraint") << "marking as constraint as self explaining " << endl;
      constraint->selfExplaining();
    }else{
      Debug("arith::constraint") << "already has proof: " << constraint->explainForConflict() << endl;
    }

    return constraint;
  }
}

bool TheoryArithPrivate::assertionCases(Constraint constraint){
  Assert(constraint->hasProof());
  Assert(!constraint->negationHasProof());

  ArithVar x_i = constraint->getVariable();

  switch(constraint->getType()){
  case UpperBound:
    if(isInteger(x_i) && constraint->isStrictUpperBound()){
      Constraint floorConstraint = constraint->getFloor();
      if(!floorConstraint->isTrue()){
        if(floorConstraint->negationHasProof()){
          Node conf = ConstraintValue::explainConflict(constraint, floorConstraint->getNegation());
          raiseConflict(conf);
          return true;
        }else{
          floorConstraint->impliedBy(constraint);
          // Do not need to add to d_learnedBounds
        }
      }
      return AssertUpper(floorConstraint);
    }else{
      return AssertUpper(constraint);
    }
  case LowerBound:
    if(isInteger(x_i) && constraint->isStrictLowerBound()){
      Constraint ceilingConstraint = constraint->getCeiling();
      if(!ceilingConstraint->isTrue()){
        if(ceilingConstraint->negationHasProof()){
          Node conf = ConstraintValue::explainConflict(constraint, ceilingConstraint->getNegation());
          raiseConflict(conf);
          return true;
        }
        ceilingConstraint->impliedBy(constraint);
        // Do not need to add to learnedBounds
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
 * Looks for the next integer variable without an integer assignment in a round robin fashion.
 * Changes the value of d_nextIntegerCheckVar.
 *
 * If this returns false, d_nextIntegerCheckVar does not have an integer assignment.
 * If this returns true, all integer variables have an integer assignment.
 */
bool TheoryArithPrivate::hasIntegerModel(){
  //if(d_variables.size() > 0){
  ArithVar numVars = d_partialModel.getNumberOfVariables();
  if(numVars > 0){
    const ArithVar rrEnd = d_nextIntegerCheckVar;
    do {
      //Do not include slack variables
      if(isInteger(d_nextIntegerCheckVar) && !isSlackVariable(d_nextIntegerCheckVar)) { // integer
        const DeltaRational& d = d_partialModel.getAssignment(d_nextIntegerCheckVar);
        if(!d.isIntegral()){
          return false;
        }
      }
    } while((d_nextIntegerCheckVar = (1 + d_nextIntegerCheckVar == numVars ? 0 : 1 + d_nextIntegerCheckVar)) != rrEnd);
  }
  return true;
}

/** Outputs conflicts to the output channel. */
void TheoryArithPrivate::outputConflicts(){
  Assert(!d_conflicts.empty());
  for(size_t i = 0, i_end = d_conflicts.size(); i < i_end; ++i){
    Node conflict = d_conflicts[i];
    Debug("arith::conflict") << "d_conflicts[" << i << "] " << conflict << endl;
    (d_containing.d_out)->conflict(conflict);
  }
}

void TheoryArithPrivate::branchVector(const std::vector<ArithVar>& lemmas){
  //output the lemmas
  for(vector<ArithVar>::const_iterator i = lemmas.begin(); i != lemmas.end(); ++i){
    ArithVar v = *i;
    Assert(!d_cutInContext.contains(v));
    d_cutInContext.insert(v);
    d_cutCount = d_cutCount + 1;
    Node lem = branchIntegerVariable(v);
    outputLemma(lem);
    ++(d_statistics.d_externalBranchAndBounds);
  }
}

bool TheoryArithPrivate::solveRealRelaxation(Theory::Effort effortLevel){
  Assert(d_qflraStatus != Result::SAT);

  d_partialModel.stopQueueingAtBoundQueue();
  UpdateTrackingCallback utcb(&d_linEq);
  d_partialModel.processAtBoundQueue(utcb);
  d_linEq.startTrackingBoundCounts();

  bool noPivotLimit = Theory::fullEffort(effortLevel) ||
    !options::restrictedPivots();

  bool emmittedConflictOrSplit = false;

  SimplexDecisionProcedure& simplex =
    options::useFC() ? (SimplexDecisionProcedure&)d_fcSimplex :
    (options::useSOI() ? (SimplexDecisionProcedure&)d_soiSimplex :
     (SimplexDecisionProcedure&)d_dualSimplex);

  bool useFancyFinal = options::fancyFinal() && ApproximateSimplex::enabled();

  if(!useFancyFinal){
    d_qflraStatus = simplex.findModel(noPivotLimit);
  }else{
    // Fancy final tries the following strategy
    // At final check, try the preferred simplex solver with a pivot cap
    // If that failed, swap the the other simplex solver
    // If that failed, check if there are integer variables to cut
    // If that failed, do a simplex without a pivot limit

    int16_t oldCap = options::arithStandardCheckVarOrderPivots();

    static const int32_t pass2Limit = 10;
    static const int32_t relaxationLimit = 10000;
    static const int32_t mipLimit = 200000;

    d_qflraStatus = simplex.findModel(false);
    if(d_qflraStatus == Result::SAT_UNKNOWN ||
       (d_qflraStatus == Result::SAT && !hasIntegerModel())){

      ApproximateSimplex* approxSolver = ApproximateSimplex::mkApproximateSimplexSolver(d_partialModel);
      approxSolver->setPivotLimit(relaxationLimit);

      ApproximateSimplex::ApproxResult relaxRes, mipRes;
      ApproximateSimplex::Solution relaxSolution, mipSolution;
      relaxRes = approxSolver->solveRelaxation();
      switch(relaxRes){
      case ApproximateSimplex::ApproxSat:
        {
          relaxSolution = approxSolver->extractRelaxation();
          approxSolver->setPivotLimit(mipLimit);
          mipRes = approxSolver->solveMIP();
          d_errorSet.reduceToSignals();
          if(mipRes == ApproximateSimplex::ApproxSat){
            mipSolution = approxSolver->extractMIP();
            ApproximateSimplex::applySolution(d_linEq, mipSolution);
          }else{
            ApproximateSimplex::applySolution(d_linEq, relaxSolution);
            // if(d_qflraStatus != UNSAT){
            //   d_likelyIntegerUnsat = true;
            // }
          }
          options::arithStandardCheckVarOrderPivots.set(pass2Limit);
          d_qflraStatus = simplex.findModel(false);
        }
        break;
      case ApproximateSimplex::ApproxUnsat:
        {
          ApproximateSimplex::Solution sol = approxSolver->extractRelaxation();
          d_errorSet.reduceToSignals();
          ApproximateSimplex::applySolution(d_linEq, sol);
          options::arithStandardCheckVarOrderPivots.set(100);

          d_qflraStatus = simplex.findModel(false);
        }
        break;
      default:
        break;
      }
      delete approxSolver;
    }

    if(d_qflraStatus == Result::SAT_UNKNOWN){
      vector<ArithVar> toCut = cutAllBounded();
      if(toCut.size() > 0){
        branchVector(toCut);
        emmittedConflictOrSplit = true;
      }else{
        d_qflraStatus = simplex.findModel(noPivotLimit);
      }
    }
    options::arithStandardCheckVarOrderPivots.set(oldCap);
  }

  // TODO Save zeroes with no conflicts
  d_linEq.stopTrackingBoundCounts();
  d_partialModel.startQueueingAtBoundQueue();

  return emmittedConflictOrSplit;
}

void TheoryArithPrivate::check(Theory::Effort effortLevel){
  Assert(d_currentPropagationList.empty());
  Debug("effortlevel") << "TheoryArithPrivate::check " << effortLevel << std::endl;
  Debug("arith") << "TheoryArithPrivate::check begun " << effortLevel << std::endl;

  if(Debug.isOn("arith::consistency")){
    Assert(unenqueuedVariablesAreConsistent());
  }

  bool newFacts = !done();
  //If previous == SAT, then reverts on conflicts are safe
  //Otherwise, they are not and must be committed.
  Result::Sat previous = d_qflraStatus;
  if(newFacts){
    d_qflraStatus = Result::SAT_UNKNOWN;
    d_hasDoneWorkSinceCut = true;
  }

  while(!done()){
    Constraint curr = constraintFromFactQueue();
    if(curr != NullConstraint){
      bool res CVC4_UNUSED = assertionCases(curr);
      Assert(!res || inConflict());
    }
    if(inConflict()){ break; }
  }
  if(!inConflict()){
    while(!d_learnedBounds.empty()){
      // we may attempt some constraints twice.  this is okay!
      Constraint curr = d_learnedBounds.front();
      d_learnedBounds.pop();
      Debug("arith::learned") << curr << endl;

      bool res CVC4_UNUSED = assertionCases(curr);
      Assert(!res || inConflict());

      if(inConflict()){ break; }
    }
  }

  if(inConflict()){
    d_qflraStatus = Result::UNSAT;
    if(options::revertArithModels() && previous == Result::SAT){
      ++d_statistics.d_revertsOnConflicts;
      Debug("arith::bt") << "clearing here " << " " << newFacts << " " << previous << " " << d_qflraStatus  << endl;
      revertOutOfConflict();
      d_errorSet.clear();
    }else{
      ++d_statistics.d_commitsOnConflicts;
      Debug("arith::bt") << "committing here " << " " << newFacts << " " << previous << " " << d_qflraStatus  << endl;
      d_partialModel.commitAssignmentChanges();
      revertOutOfConflict();
    }
    outputConflicts();
    return;
  }


  if(Debug.isOn("arith::print_assertions")) {
    debugPrintAssertions();
  }

  bool emmittedConflictOrSplit = false;
  Assert(d_conflicts.empty());

  bool useSimplex = d_qflraStatus != Result::SAT;
  if(useSimplex){
    emmittedConflictOrSplit = solveRealRelaxation(effortLevel);
  }

  switch(d_qflraStatus){
  case Result::SAT:
    if(newFacts){
      ++d_statistics.d_nontrivialSatChecks;
    }

    Debug("arith::bt") << "committing sap inConflit"  << " " << newFacts << " " << previous << " " << d_qflraStatus  << endl;
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
    Debug("arith::bt") << "committing unknown"  << " " << newFacts << " " << previous << " " << d_qflraStatus  << endl;
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
    if(false && previous == Result::SAT){
      ++d_statistics.d_revertsOnConflicts;
      Debug("arith::bt") << "clearing on conflict" << " " << newFacts << " " << previous << " " << d_qflraStatus  << endl;
      revertOutOfConflict();
      d_errorSet.clear();
    }else{
      ++d_statistics.d_commitsOnConflicts;

      Debug("arith::bt") << "committing on conflict" << " " << newFacts << " " << previous << " " << d_qflraStatus  << endl;
      d_partialModel.commitAssignmentChanges();
      revertOutOfConflict();

      if(Debug.isOn("arith::consistency::comitonconflict")){
        entireStateIsConsistent("commit on conflict");
      }
    }
    outputConflicts();
    emmittedConflictOrSplit = true;

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
  d_statistics.d_avgUnknownsInARow.addEntry(d_unknownsInARow);

  // This should be fine if sat or unknown
  if(!emmittedConflictOrSplit &&
     (options::arithPropagationMode() == UNATE_PROP ||
      options::arithPropagationMode() == BOTH_PROP)){
    TimerStat::CodeTimer codeTimer(d_statistics.d_newPropTime);
    Assert(d_qflraStatus != Result::UNSAT);

    while(!d_currentPropagationList.empty()  && !inConflict()){
      Constraint curr = d_currentPropagationList.front();
      d_currentPropagationList.pop_front();

      ConstraintType t = curr->getType();
      Assert(t != Disequality, "Disequalities are not allowed in d_currentPropagation");


      switch(t){
      case LowerBound:
        {
          Constraint prev = d_currentPropagationList.front();
          d_currentPropagationList.pop_front();
          d_constraintDatabase.unatePropLowerBound(curr, prev);
          break;
        }
      case UpperBound:
        {
          Constraint prev = d_currentPropagationList.front();
          d_currentPropagationList.pop_front();
          d_constraintDatabase.unatePropUpperBound(curr, prev);
          break;
        }
      case Equality:
        {
          Constraint prevLB = d_currentPropagationList.front();
          d_currentPropagationList.pop_front();
          Constraint prevUB = d_currentPropagationList.front();
          d_currentPropagationList.pop_front();
          d_constraintDatabase.unatePropEquality(curr, prevLB, prevUB);
          break;
        }
      default:
        Unhandled(curr->getType());
      }
    }

    if(inConflict()){
      Debug("arith::unate") << "unate conflict" << endl;
      revertOutOfConflict();
      d_qflraStatus = Result::UNSAT;
      outputConflicts();
      emmittedConflictOrSplit = true;
      Debug("arith::bt") << "committing on unate conflict" << " " << newFacts << " " << previous << " " << d_qflraStatus  << endl;

    }
  }else{
    TimerStat::CodeTimer codeTimer(d_statistics.d_newPropTime);
    d_currentPropagationList.clear();
  }
  Assert( d_currentPropagationList.empty());

  if(!emmittedConflictOrSplit && Theory::fullEffort(effortLevel)){
    ++d_fullCheckCounter;
  }
  if(!emmittedConflictOrSplit && Theory::fullEffort(effortLevel)){
    emmittedConflictOrSplit = splitDisequalities();
  }
  emmittedConflictOrSplit = false;

  if(!emmittedConflictOrSplit && Theory::fullEffort(effortLevel) && !hasIntegerModel()){
    Node possibleConflict = Node::null();
    if(!emmittedConflictOrSplit && options::arithDioSolver()){
      possibleConflict = callDioSolver();
      if(possibleConflict != Node::null()){
        revertOutOfConflict();
        Debug("arith::conflict") << "dio conflict   " << possibleConflict << endl;
        //cout << "dio conflict   " << possibleConflict << endl;
        raiseConflict(possibleConflict);
        outputConflicts();
        emmittedConflictOrSplit = true;
      }
    }

    if(!emmittedConflictOrSplit && d_hasDoneWorkSinceCut && options::arithDioSolver()){
      Node possibleLemma = dioCutting();
      if(!possibleLemma.isNull()){
        Debug("arith") << "dio cut   " << possibleLemma << endl;
        //cout << "dio cut   " << possibleLemma << endl;
        emmittedConflictOrSplit = true;
        d_hasDoneWorkSinceCut = false;
        d_cutCount = d_cutCount + 1;
        outputLemma(possibleLemma);
      }
    }

    if(!emmittedConflictOrSplit) {
      Node possibleLemma = roundRobinBranch();
      if(!possibleLemma.isNull()){
        ++(d_statistics.d_externalBranchAndBounds);
        d_cutCount = d_cutCount + 1;
        emmittedConflictOrSplit = true;
        outputLemma(possibleLemma);
      }
    }

    if(options::maxCutsInContext() <= d_cutCount){
      if(d_diosolver.hasMoreDecompositionLemmas()){
        while(d_diosolver.hasMoreDecompositionLemmas()){
          Node decompositionLemma = d_diosolver.nextDecompositionLemma();
          Debug("arith") << "dio decomposition lemma   " << decompositionLemma << endl;
          outputLemma(decompositionLemma);
        }
      }else{
        outputRestart();
      }
    }
  }//if !emmittedConflictOrSplit && fullEffort(effortLevel) && !hasIntegerModel()
  if(Theory::fullEffort(effortLevel) && d_nlIncomplete){
    // TODO this is total paranoia
    setIncomplete();
  }

  if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }
  if(Debug.isOn("arith::print_model")) { debugPrintModel(); }
  Debug("arith") << "TheoryArithPrivate::check end" << std::endl;
}

Node TheoryArithPrivate::branchIntegerVariable(ArithVar x) const {
  const DeltaRational& d = d_partialModel.getAssignment(x);
  Assert(!d.isIntegral());
  const Rational& r = d.getNoninfinitesimalPart();
  const Rational& i = d.getInfinitesimalPart();
  Trace("integers") << "integers: assignment to [[" << d_partialModel.asNode(x) << "]] is " << r << "[" << i << "]" << endl;

  Assert(! (r.getDenominator() == 1 && i.getNumerator() == 0));
  Assert(!d.isIntegral());
  TNode var = d_partialModel.asNode(x);
  Integer floor_d = d.floor();

  //Node eq = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::EQUAL, var, mkRationalNode(floor_d+1)));
  //Node diseq = eq.notNode();

  Node ub = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::LEQ, var, mkRationalNode(floor_d)));
  Node lb = ub.notNode();


  //Node lem = NodeManager::currentNM()->mkNode(kind::OR, eq, diseq);
  Node lem = NodeManager::currentNM()->mkNode(kind::OR, ub, lb);
  Trace("integers") << "integers: branch & bound: " << lem << endl;
  if(isSatLiteral(lem[0])) {
    Debug("integers") << "    " << lem[0] << " == " << getSatValue(lem[0]) << endl;
  } else {
    Debug("integers") << "    " << lem[0] << " is not assigned a SAT literal" << endl;
  }
  if(isSatLiteral(lem[1])) {
    Debug("integers") << "    " << lem[1] << " == " << getSatValue(lem[1]) << endl;
    } else {
    Debug("integers") << "    " << lem[1] << " is not assigned a SAT literal" << endl;
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
      if(isInteger(iter) && !isSlackVariable(iter) &&
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
Node TheoryArithPrivate::roundRobinBranch(){
  if(hasIntegerModel()){
    return Node::null();
  }else{
    ArithVar v = d_nextIntegerCheckVar;

    Assert(isInteger(v));
    Assert(!isSlackVariable(v));
    return branchIntegerVariable(v);
  }
}

bool TheoryArithPrivate::splitDisequalities(){
  bool splitSomething = false;

  vector<Constraint> save;

  while(!d_diseqQueue.empty()){
    Constraint front = d_diseqQueue.front();
    d_diseqQueue.pop();

    if(front->isSplit()){
      Debug("eq") << "split already" << endl;
    }else{
      Debug("eq") << "not split already" << endl;

      ArithVar lhsVar = front->getVariable();

      const DeltaRational& lhsValue = d_partialModel.getAssignment(lhsVar);
      const DeltaRational& rhsValue = front->getValue();
      if(lhsValue == rhsValue){
        Debug("arith::lemma") << "Splitting on " << front << endl;
        Debug("arith::lemma") << "LHS value = " << lhsValue << endl;
        Debug("arith::lemma") << "RHS value = " << rhsValue << endl;
        Node lemma = front->split();
        ++(d_statistics.d_statDisequalitySplits);

        Debug("arith::lemma") << "Now " << Rewriter::rewrite(lemma) << endl;
        outputLemma(lemma);
        splitSomething = true;
      }else if(d_partialModel.strictlyLessThanLowerBound(lhsVar, rhsValue)){
        Debug("eq") << "can drop as less than lb" << front << endl;
      }else if(d_partialModel.strictlyGreaterThanUpperBound(lhsVar, rhsValue)){
        Debug("eq") << "can drop as greater than ub" << front << endl;
      }else{
        Debug("eq") << "save" << front << ": " <<lhsValue << " != " << rhsValue << endl;
        save.push_back(front);
      }
    }
  }
  vector<Constraint>::const_iterator i=save.begin(), i_end = save.end();
  for(; i != i_end; ++i){
    d_diseqQueue.push(*i);
  }
  return splitSomething;
}

/**
 * Should be guarded by at least Debug.isOn("arith::print_assertions").
 * Prints to Debug("arith::print_assertions")
 */
void TheoryArithPrivate::debugPrintAssertions() {
  Debug("arith::print_assertions") << "Assertions:" << endl;
  for (var_iterator vi = var_begin(), vend = var_end(); vi != vend; ++vi){
    ArithVar i = *vi;
    if (d_partialModel.hasLowerBound(i)) {
      Constraint lConstr = d_partialModel.getLowerBoundConstraint(i);
      Debug("arith::print_assertions") << lConstr << endl;
    }

    if (d_partialModel.hasUpperBound(i)) {
      Constraint uConstr = d_partialModel.getUpperBoundConstraint(i);
      Debug("arith::print_assertions") << uConstr << endl;
    }
  }
  context::CDQueue<Constraint>::const_iterator it = d_diseqQueue.begin();
  context::CDQueue<Constraint>::const_iterator it_end = d_diseqQueue.end();
  for(; it != it_end; ++ it) {
    Debug("arith::print_assertions") << *it << endl;
  }
}

void TheoryArithPrivate::debugPrintModel(){
  Debug("arith::print_model") << "Model:" << endl;
  for (var_iterator vi = var_begin(), vend = var_end(); vi != vend; ++vi){
    ArithVar i = *vi;
    if(d_partialModel.hasNode(i)){
      Debug("arith::print_model") << d_partialModel.asNode(i) << " : " <<
        d_partialModel.getAssignment(i);
      if(d_tableau.isBasic(i))
        Debug("arith::print_model") << " (basic)";
      Debug("arith::print_model") << endl;
    }
  }
}



Node TheoryArithPrivate::explain(TNode n) {

  Debug("arith::explain") << "explain @" << getSatContext()->getLevel() << ": " << n << endl;

  Constraint c = d_constraintDatabase.lookup(n);
  if(c != NullConstraint){
    Assert(!c->isSelfExplaining());
    Node exp = c->explainForPropagation();
    Debug("arith::explain") << "constraint explanation" << n << ":" << exp << endl;
    return exp;
  }else if(d_assertionsThatDoNotMatchTheirLiterals.find(n) != d_assertionsThatDoNotMatchTheirLiterals.end()){
    c = d_assertionsThatDoNotMatchTheirLiterals[n];
    if(!c->isSelfExplaining()){
      Node exp = c->explainForPropagation();
      Debug("arith::explain") << "assertions explanation" << n << ":" << exp << endl;
      return exp;
    }else{
      Debug("arith::explain") << "this is a strange mismatch" << n << endl;
      Assert(d_congruenceManager.canExplain(n));
      Debug("arith::explain") << "this is a strange mismatch" << n << endl;
      return d_congruenceManager.explain(n);
    }
  }else{
    Assert(d_congruenceManager.canExplain(n));
    Debug("arith::explain") << "dm explanation" << n << endl;
    return d_congruenceManager.explain(n);
  }
}


void TheoryArithPrivate::propagate(Theory::Effort e) {
  // This uses model values for safety. Disable for now.
  if(d_qflraStatus == Result::SAT &&
     (options::arithPropagationMode() == BOUND_INFERENCE_PROP ||
      options::arithPropagationMode() == BOTH_PROP)
     && hasAnyUpdates()){
    propagateCandidates();
  }else{
    clearUpdates();
  }

  while(d_constraintDatabase.hasMorePropagations()){
    Constraint c = d_constraintDatabase.nextPropagation();
    Debug("arith::prop") << "next prop" << getSatContext()->getLevel() << ": " << c << endl;

    if(c->negationHasProof()){
      Debug("arith::prop") << "negation has proof " << c->getNegation() << endl
                           << c->getNegation()->explainForConflict() << endl;
    }
    Assert(!c->negationHasProof(), "A constraint has been propagated on the constraint propagation queue, but the negation has been set to true.  Contact Tim now!");

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

    Constraint constraint = d_constraintDatabase.lookup(normalized);
    if(constraint == NullConstraint){
      Debug("arith::prop") << "propagating on non-constraint? "  << toProp << endl;

      outputPropagate(toProp);
    }else if(constraint->negationHasProof()){
      Node exp = d_congruenceManager.explain(toProp);
      Node notNormalized = normalized.getKind() == NOT ?
        normalized[0] : normalized.notNode();
      Node lp = flattenAnd(exp.andNode(notNormalized));
      Debug("arith::prop") << "propagate conflict" <<  lp << endl;
      raiseConflict(lp);
      outputConflicts();
      return;
    }else{
      Debug("arith::prop") << "propagating still?" <<  toProp << endl;
      outputPropagate(toProp);
    }
  }
}

DeltaRational TheoryArithPrivate::getDeltaValue(TNode n) const throw (DeltaRationalException, ModelException) {
  AlwaysAssert(d_qflraStatus != Result::SAT_UNKNOWN);
  Debug("arith::value") << n << std::endl;

  switch(n.getKind()) {

  case kind::CONST_RATIONAL:
    return n.getConst<Rational>();

  case kind::PLUS: { // 2+ args
    DeltaRational value(0);
    for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
      value = value + getDeltaValue(*i);
    }
    return value;
  }

  case kind::MULT: { // 2+ args
    DeltaRational value(1);
    unsigned variableParts = 0;
    for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
      TNode curr = *i;
      value = value * getDeltaValue(curr);
      if(!curr.isConst()){
        ++variableParts;
      }
    }
    // TODO: This is a bit of a weak check
    if(isSetup(n)){
      ArithVar var = d_partialModel.asArithVar(n);
      const DeltaRational& assign = d_partialModel.getAssignment(var);
      if(assign != value){
        throw ModelException(n, "Model disagrees on non-linear term.");
      }
    }
    return value;
  }
  case kind::MINUS:{ // 2 args
    return getDeltaValue(n[0]) - getDeltaValue(n[1]);
  }

  case kind::UMINUS:{ // 1 arg
    return (- getDeltaValue(n[0]));
  }

  case kind::DIVISION:{ // 2 args
    DeltaRational res = getDeltaValue(n[0]) / getDeltaValue(n[1]);
    if(isSetup(n)){
      ArithVar var = d_partialModel.asArithVar(n);
      if(d_partialModel.getAssignment(var) != res){
        throw ModelException(n, "Model disagrees on non-linear term.");
      }
    }
    return res;
  }
  case kind::DIVISION_TOTAL:
  case kind::INTS_DIVISION_TOTAL:
  case kind::INTS_MODULUS_TOTAL: { // 2 args
    DeltaRational denom = getDeltaValue(n[1]);
    if(denom.isZero()){
      return DeltaRational(0,0);
    }else{
      DeltaRational numer = getDeltaValue(n[0]);
      DeltaRational res;
      if(n.getKind() == kind::DIVISION_TOTAL){
        res = numer / denom;
      }else if(n.getKind() == kind::INTS_DIVISION_TOTAL){
        res = Rational(numer.euclidianDivideQuotient(denom));
      }else{
        Assert(n.getKind() == kind::INTS_MODULUS_TOTAL);
        res = Rational(numer.euclidianDivideRemainder(denom));
      }
      if(isSetup(n)){
        ArithVar var = d_partialModel.asArithVar(n);
        if(d_partialModel.getAssignment(var) != res){
          throw ModelException(n, "Model disagrees on non-linear term.");
        }
      }
      return res;
    }
  }

  default:
    if(isSetup(n)){
      ArithVar var = d_partialModel.asArithVar(n);
      return d_partialModel.getAssignment(var);
    }else{
      throw ModelException(n, "Expected a setup node.");
    }
  }
}

Rational TheoryArithPrivate::deltaValueForTotalOrder() const{
  Rational min(2);
  std::set<DeltaRational> relevantDeltaValues;
  context::CDQueue<Constraint>::const_iterator qiter = d_diseqQueue.begin();
  context::CDQueue<Constraint>::const_iterator qiter_end = d_diseqQueue.end();

  for(; qiter != qiter_end; ++qiter){
    Constraint curr = *qiter;

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

void TheoryArithPrivate::collectModelInfo( TheoryModel* m, bool fullModel ){
  AlwaysAssert(d_qflraStatus ==  Result::SAT);
  //AlwaysAssert(!d_nlIncomplete, "Arithmetic solver cannot currently produce models for input with nonlinear arithmetic constraints");

  if(Debug.isOn("arith::collectModelInfo")){
    debugPrintFacts();
  }

  Debug("arith::collectModelInfo") << "collectModelInfo() begin " << endl;


  // Delta lasts at least the duration of the function call
  const Rational& delta = d_partialModel.getDelta();
  std::hash_set<TNode, TNodeHashFunction> shared = d_containing.currentlySharedTerms();

  // TODO:
  // This is not very good for user push/pop....
  // Revisit when implementing push/pop
  for(var_iterator vi = var_begin(), vend = var_end(); vi != vend; ++vi){
    ArithVar v = *vi;

    if(!isSlackVariable(v)){
      Node term = d_partialModel.asNode(v);

      if(theoryOf(term) == THEORY_ARITH || shared.find(term) != shared.end()){
        const DeltaRational& mod = d_partialModel.getAssignment(v);
        Rational qmodel = mod.substituteDelta(delta);

        Node qNode = mkRationalNode(qmodel);
        Debug("arith::collectModelInfo") << "m->assertEquality(" << term << ", " << qmodel << ", true)" << endl;

        m->assertEquality(term, qNode, true);
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
#warning "removing restart"
  // return;

  // uint32_t currSize = d_tableau.size();
  // uint32_t copySize = d_smallTableauCopy.size();

  // Debug("arith::reset") << "resetting" << d_restartsCounter << endl;
  // Debug("arith::reset") << "curr " << currSize << " copy " << copySize << endl;
  // Debug("arith::reset") << "tableauSizeHasBeenModified " << d_tableauSizeHasBeenModified << endl;

  // if(d_tableauSizeHasBeenModified){
  //   Debug("arith::reset") << "row has been added must copy " << d_restartsCounter << endl;
  //   d_smallTableauCopy = d_tableau;
  //   d_tableauSizeHasBeenModified = false;
  // }else if( d_restartsCounter >= RESET_START){
  //   if(copySize >= currSize * 1.1 ){
  //     Debug("arith::reset") << "size has shrunk " << d_restartsCounter << endl;
  //     ++d_statistics.d_smallerSetToCurr;
  //     d_smallTableauCopy = d_tableau;
  //   }else if(d_tableauResetDensity * copySize <=  currSize){
  //     d_errorSet.popAllSignals();
  //     if(safeToReset()){
  //       Debug("arith::reset") << "resetting " << d_restartsCounter << endl;
  //       ++d_statistics.d_currSetToSmaller;
  //       d_tableau = d_smallTableauCopy;
  //     }else{
  //       Debug("arith::reset") << "not safe to reset at the moment " << d_restartsCounter << endl;
  //     }
  //   }
  // }
  // Assert(unenqueuedVariablesAreConsistent());
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

  d_statistics.d_initialTableauSize.setData(d_tableau.size());

  if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }

  static CVC4_THREADLOCAL(unsigned) callCount = 0;
  if(Debug.isOn("arith::presolve")) {
    Debug("arith::presolve") << "TheoryArithPrivate::presolve #" << callCount << endl;
    callCount = callCount + 1;
  }

  vector<Node> lemmas;
  switch(options::arithUnateLemmaMode()){
  case NO_PRESOLVE_LEMMAS:
    break;
  case INEQUALITY_PRESOLVE_LEMMAS:
    d_constraintDatabase.outputUnateInequalityLemmas(lemmas);
    break;
  case EQUALITY_PRESOLVE_LEMMAS:
    d_constraintDatabase.outputUnateEqualityLemmas(lemmas);
    break;
  case ALL_PRESOLVE_LEMMAS:
    d_constraintDatabase.outputUnateInequalityLemmas(lemmas);
    d_constraintDatabase.outputUnateEqualityLemmas(lemmas);
    break;
  default:
    Unhandled(options::arithUnateLemmaMode());
  }

  vector<Node>::const_iterator i = lemmas.begin(), i_end = lemmas.end();
  for(; i != i_end; ++i){
    Node lem = *i;
    Debug("arith::oldprop") << " lemma lemma duck " <<lem << endl;
    outputLemma(lem);
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

  DeltaRational bound = upperBound ?
    d_linEq.computeUpperBound(basic):
    d_linEq.computeLowerBound(basic);

  if((upperBound && d_partialModel.strictlyLessThanUpperBound(basic, bound)) ||
     (!upperBound && d_partialModel.strictlyGreaterThanLowerBound(basic, bound))){

    // TODO: "Policy point"
    //We are only going to recreate the functionality for now.
    //In the future this can be improved to generate a temporary constraint
    //if none exists.
    //Experiment with doing this everytime or only when the new constraint
    //implies an unknown fact.

    ConstraintType t = upperBound ? UpperBound : LowerBound;
    Constraint bestImplied = d_constraintDatabase.getBestImpliedBound(basic, t, bound);

    // Node bestImplied = upperBound ?
    //   d_apm.getBestImpliedUpperBound(basic, bound):
    //   d_apm.getBestImpliedLowerBound(basic, bound);

    if(bestImplied != NullConstraint){
      //This should be stronger
      Assert(!upperBound || bound <= bestImplied->getValue());
      Assert(!upperBound || d_partialModel.lessThanUpperBound(basic, bestImplied->getValue()));

      Assert( upperBound || bound >= bestImplied->getValue());
      Assert( upperBound || d_partialModel.greaterThanLowerBound(basic, bestImplied->getValue()));
      //slightly changed

      // Constraint c = d_constraintDatabase.lookup(bestImplied);
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
                  << bestImplied->getNegation()->explainForConflict() << endl;
      }

      if(!assertedToTheTheory && canBePropagated && !hasProof ){
        if(upperBound){
          Assert(bestImplied != d_partialModel.getUpperBoundConstraint(basic));
          d_linEq.propagateNonbasicsUpperBound(basic, bestImplied);
        }else{
          Assert(bestImplied != d_partialModel.getLowerBoundConstraint(basic));
          d_linEq.propagateNonbasicsLowerBound(basic, bestImplied);
        }
        // I think this can be skipped if canBePropagated is true
        //d_learnedBounds.push(bestImplied);
        return true;
      }
    }
  }
  return false;
}

void TheoryArithPrivate::propagateCandidate(ArithVar basic){
  bool success = false;
  if(d_partialModel.strictlyAboveLowerBound(basic) && d_linEq.hasLowerBounds(basic)){
    success |= propagateCandidateLowerBound(basic);
  }
  if(d_partialModel.strictlyBelowUpperBound(basic) && d_linEq.hasUpperBounds(basic)){
    success |= propagateCandidateUpperBound(basic);
  }
  if(success){
    ++d_statistics.d_boundPropagations;
  }
}

void TheoryArithPrivate::propagateCandidates(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_boundComputationTime);

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
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

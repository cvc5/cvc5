/*********************                                                        */
/*! \file theory_arith.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters, dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "expr/node.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node_builder.h"

#include "theory/valuation.h"
#include "theory/rewriter.h"

#include "util/rational.h"
#include "util/integer.h"
#include "util/boolean_simplification.h"
#include "util/dense_map.h"


#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/matrix.h"

#include "theory/arith/arith_rewriter.h"
#include "theory/arith/constraint.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/normal_form.h"

#include <stdint.h>

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

const uint32_t RESET_START = 2;


TheoryArith::TheoryArith(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe) :
  Theory(THEORY_ARITH, c, u, out, valuation, logicInfo, qe),
  d_qflraStatus(Result::SAT_UNKNOWN),
  d_unknownsInARow(0),
  d_hasDoneWorkSinceCut(false),
  d_learner(d_pbSubstitutions),
  d_setupLiteralCallback(this),
  d_assertionsThatDoNotMatchTheirLiterals(c),
  d_nextIntegerCheckVar(0),
  d_constantIntegerVariables(c),
  d_diseqQueue(c, false),
  d_currentPropagationList(),
  d_learnedBounds(c),
  d_partialModel(c),
  d_tableau(),
  d_linEq(d_partialModel, d_tableau, d_basicVarModelUpdateCallBack),
  d_diosolver(c),
  d_pbSubstitutions(u),
  d_restartsCounter(0),
  d_tableauSizeHasBeenModified(false),
  d_tableauResetDensity(1.6),
  d_tableauResetPeriod(10),
  d_conflicts(c),
  d_raiseConflict(d_conflicts),
  d_congruenceManager(c, d_constraintDatabase, d_setupLiteralCallback, d_arithvarNodeMap, d_raiseConflict),
  d_simplex(d_linEq, d_raiseConflict),
  d_constraintDatabase(c, u, d_arithvarNodeMap, d_congruenceManager, d_raiseConflict),
  d_basicVarModelUpdateCallBack(d_simplex),
  d_DELTA_ZERO(0),
  d_statistics()
{}

TheoryArith::~TheoryArith(){}

TheoryArith::Statistics::Statistics():
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
  d_nontrivialSatChecks("theory::arith::status::nontrivialSatChecks",0)
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
}

TheoryArith::Statistics::~Statistics(){
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
}

void TheoryArith::revertOutOfConflict(){
  d_partialModel.revertAssignmentChanges();
  clearUpdates();
  d_currentPropagationList.clear();
}

void TheoryArith::clearUpdates(){
  d_updatedBounds.purge();
}

void TheoryArith::zeroDifferenceDetected(ArithVar x){
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
bool TheoryArith::AssertLower(Constraint constraint){
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
    d_raiseConflict(conflict);
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
        d_raiseConflict(conflict);
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
    if(vc.hasDisequality() && vc.hasUpperBound()){
      const Constraint diseq = vc.getDisequality();
      if(diseq->isTrue()){
        const Constraint ub = vc.getUpperBound();
        if(ub->hasProof()){
          Node conflict = ConstraintValue::explainConflict(diseq, ub, constraint);
          Debug("eq") << " assert upper conflict " << conflict << endl;
          d_raiseConflict(conflict);
          return true;
        }else if(!ub->negationHasProof()){
          Constraint negUb = ub->getNegation();
          negUb->impliedBy(constraint, diseq);
          //if(!negUb->canBePropagated()){
          d_learnedBounds.push_back(negUb);
            //}//otherwise let this be propagated/asserted later
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

  if(!d_tableau.isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) < c_i){
      d_linEq.update(x_i, c_i);
    }
  }else{
    d_simplex.updateBasic(x_i);
  }

  if(Debug.isOn("model")) { d_partialModel.printModel(x_i); }

  return false; //sat
}

/* procedure AssertUpper( x_i <= c_i) */
bool TheoryArith::AssertUpper(Constraint constraint){
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
    d_raiseConflict(conflict);
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
        d_raiseConflict(conflict);
        return true;
      }else if(!eq->isTrue()){
        Debug("eq") << "lb == ub, propagate eq" << eq << endl;
        eq->impliedBy(constraint, d_partialModel.getLowerBoundConstraint(x_i));
        //do not bother to add to d_learnedBounds
      }
    }
  }else if(cmpToLB > 0){
    const ValueCollection& vc = constraint->getValueCollection();
    if(vc.hasDisequality() && vc.hasLowerBound()){
      const Constraint diseq = vc.getDisequality();
      if(diseq->isTrue()){
        const Constraint lb = vc.getLowerBound();
        if(lb->hasProof()){
          Node conflict = ConstraintValue::explainConflict(diseq, lb, constraint);
          Debug("eq") << " assert upper conflict " << conflict << endl;
          d_raiseConflict(conflict);
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

  if(!d_tableau.isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) > c_i){
      d_linEq.update(x_i, c_i);
    }
  }else{
    d_simplex.updateBasic(x_i);
  }

  if(Debug.isOn("model")) { d_partialModel.printModel(x_i); }

  return false; //sat
}


/* procedure AssertEquality( x_i == c_i ) */
bool TheoryArith::AssertEquality(Constraint constraint){
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
    d_raiseConflict(conflict);
    return true;
  }

  if(cmpToLB < 0){
    Constraint lbc = d_partialModel.getLowerBoundConstraint(x_i);
    Node conflict = ConstraintValue::explainConflict(lbc, constraint);
    Debug("arith") << "AssertEquality conflicts with lower bound" << conflict << endl;
    d_raiseConflict(conflict);
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

  if(!d_tableau.isBasic(x_i)){
    if(!(d_partialModel.getAssignment(x_i) == c_i)){
      d_linEq.update(x_i, c_i);
    }
  }else{
    d_simplex.updateBasic(x_i);
  }
  return false;
}


/* procedure AssertDisequality( x_i != c_i ) */
bool TheoryArith::AssertDisequality(Constraint constraint){

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

  if(constraint->isSplit()){
    Debug("eq") << "skipping already split " << constraint << endl;
    return false;
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
      d_raiseConflict(conflict);
      return true;

    }else if(lb->isTrue()){
      Debug("eq") << "propagate UpperBound " << constraint << lb << ub << endl;
      const Constraint negUb = ub->getNegation();
      if(!negUb->isTrue()){
        negUb->impliedBy(constraint, lb);
        d_learnedBounds.push_back(negUb);
      }
    }else if(ub->isTrue()){
      Debug("eq") << "propagate LowerBound " << constraint << lb << ub << endl;
      const Constraint negLb = lb->getNegation();
      if(!negLb->isTrue()){
        negLb->impliedBy(constraint, ub);
        //if(!negLb->canBePropagated()){
        d_learnedBounds.push_back(negLb);
        //}
      }
    }
  }


  if(c_i == d_partialModel.getAssignment(x_i)){
    Debug("eq") << "lemma now! " << constraint << endl;
    d_out->lemma(constraint->split());
    return false;
  }else if(d_partialModel.strictlyLessThanLowerBound(x_i, c_i)){
    Debug("eq") << "can drop as less than lb" << constraint << endl;
  }else if(d_partialModel.strictlyGreaterThanUpperBound(x_i, c_i)){
    Debug("eq") << "can drop as less than ub" << constraint << endl;
  }else{
    Debug("eq") << "push back" << constraint << endl;
    d_diseqQueue.push(constraint);
  }
  return false;

}

void TheoryArith::addSharedTerm(TNode n){
  Debug("arith::addSharedTerm") << "addSharedTerm: " << n << endl;
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

Node TheoryArith::ppRewrite(TNode atom) {

  if (!atom.getType().isBoolean()) {
    return atom;
  }

  Debug("arith::preprocess") << "arith::preprocess() : " << atom << endl;

  Node a = d_pbSubstitutions.apply(atom);

  if (a != atom) {
    Debug("pb") << "arith::preprocess() : after pb substitutions: " << a << endl;
    a = Rewriter::rewrite(a);
    Debug("pb") << "arith::preprocess() : after pb substitutions and rewriting: "
                << a << endl;
    Debug("arith::preprocess") << "arith::preprocess() :"
                               << "after pb substitutions and rewriting: "
                               << a << endl;
  }

  if (a.getKind() == kind::EQUAL  && Options::current()->arithRewriteEq) {
    Node leq = NodeBuilder<2>(kind::LEQ) << a[0] << a[1];
    Node geq = NodeBuilder<2>(kind::GEQ) << a[0] << a[1];
    Node rewritten = Rewriter::rewrite(leq.andNode(geq));
    Debug("arith::preprocess") << "arith::preprocess() : returning "
                               << rewritten << endl;
    return rewritten;
  }

  return a;
}

Theory::PPAssertStatus TheoryArith::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_simplifyTimer);
  Debug("simplify") << "TheoryArith::solve(" << in << ")" << endl;

//TODO: Handle this better
// FAIL: preprocess_10.cvc (exit: 1)
// =================================

// running /home/taking/ws/cvc4/branches/arithmetic/infer-bounds/builds/x86_64-unknown-linux-gnu/debug-staticbinary/src/main/cvc4 --lang=cvc4 --segv-nospin preprocess_10.cvc [from working dir /home/taking/ws/cvc4/branches/arithmetic/infer-bounds/builds/x86_64-unknown-linux-gnu/debug-staticbinary/../../../test/regress/regress0/preprocess]
// run_regression: error: differences between expected and actual output on stdout
// --- /tmp/cvc4_expect_stdout.20298.5Ga5123F4L    2012-04-30 12:27:16.136684359 -0400
// +++ /tmp/cvc4_stdout.20298.oZwTuIYuF3   2012-04-30 12:27:16.176685543 -0400
// @@ -1 +1,3 @@
// +TheoryArith::solve(): substitution x |-> IF b THEN 10 ELSE -10 ENDIF
// +minVar is integral 0right 0
//  sat


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


      static const unsigned MAX_SUB_SIZE = 20;
      if(false && right.size() > MAX_SUB_SIZE){
        Debug("simplify") << "TheoryArith::solve(): did not substitute due to the right hand side containing too many terms: " << minVar << ":" << elim << endl;
        Debug("simplify") << right.size() << endl;
      }else if(elim.hasSubterm(minVar)){
        Debug("simplify") << "TheoryArith::solve(): can't substitute due to recursive pattern with sharing: " << minVar << ":" << elim << endl;
      }else if (!minVar.getType().isInteger() || right.isIntegral()) {
        Assert(!elim.hasSubterm(minVar));
        // cannot eliminate integers here unless we know the resulting
        // substitution is integral
        Debug("simplify") << "TheoryArith::solve(): substitution " << minVar << " |-> " << elim << endl;

        outSubstitutions.addSubstitution(minVar, elim);
        return PP_ASSERT_STATUS_SOLVED;
      } else {
        Debug("simplify") << "TheoryArith::solve(): can't substitute b/c it's integer: " << minVar << ":" << minVar.getType() << " |-> " << elim << ":" << elim.getType() << endl;
      }
    }
  }

  // If a relation, remember the bound
  switch(in.getKind()) {
  case kind::LEQ:
  case kind::LT:
  case kind::GEQ:
  case kind::GT:
    if (in[0].getMetaKind() == kind::metakind::VARIABLE) {
      d_learner.addBound(in);
    }
    break;
  default:
    // Do nothing
    break;
  }

  return PP_ASSERT_STATUS_UNSOLVED;
}

void TheoryArith::ppStaticLearn(TNode n, NodeBuilder<>& learned) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_staticLearningTimer);

  d_learner.staticLearning(n, learned);
}



ArithVar TheoryArith::findShortestBasicRow(ArithVar variable){
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

void TheoryArith::setupVariable(const Variable& x){
  Node n = x.getNode();

  Assert(!isSetup(n));

  ++(d_statistics.d_statUserVariables);
  ArithVar varN = requestArithVar(n,false);
  setupInitialValue(varN);

  markSetup(n);
}

void TheoryArith::setupVariableList(const VarList& vl){
  Assert(!vl.empty());

  TNode vlNode = vl.getNode();
  Assert(!isSetup(vlNode));
  Assert(!d_arithvarNodeMap.hasArithVar(vlNode));

  for(VarList::iterator i = vl.begin(), end = vl.end(); i != end; ++i){
    Variable var = *i;

    if(!isSetup(var.getNode())){
      setupVariable(var);
    }
  }

  if(!vl.singleton()){
    // vl is the product of at least 2 variables
    // vl : (* v1 v2 ...)
    d_out->setIncomplete();

    ++(d_statistics.d_statUserVariables);
    ArithVar av = requestArithVar(vlNode, false);
    setupInitialValue(av);

    markSetup(vlNode);
  }

  /* Note:
   * Only call markSetup if the VarList is not a singleton.
   * See the comment in setupPolynomail for more.
   */
}

void TheoryArith::setupPolynomial(const Polynomial& poly) {
  Assert(!poly.containsConstant());
  TNode polyNode = poly.getNode();
  Assert(!isSetup(polyNode));
  Assert(!d_arithvarNodeMap.hasArithVar(polyNode));

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
    setupInitialValue(varSlack);

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

void TheoryArith::setupAtom(TNode atom) {
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

void TheoryArith::preRegisterTerm(TNode n) {
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


ArithVar TheoryArith::requestArithVar(TNode x, bool slack){
  Assert(isLeaf(x) || x.getKind() == PLUS);
  Assert(!d_arithvarNodeMap.hasArithVar(x));
  Assert(x.getType().isReal());// real or integer

  ArithVar varX = d_variables.size();
  d_variables.push_back(Node(x));
  Debug("integers") << "isInteger[[" << x << "]]: " << x.getType().isInteger() << endl;

  if(slack){
    //The type computation is not quite accurate for Rationals that are integral.
    //We'll use the isIntegral check from the polynomial package instead.
    Polynomial p = Polynomial::parsePolynomial(x);
    d_variableTypes.push_back(p.isIntegral() ? ATInteger : ATReal);
  }else{
    d_variableTypes.push_back(nodeToArithType(x));
  }

  d_slackVars.push_back(slack);

  d_simplex.increaseMax();

  d_arithvarNodeMap.setArithVar(x,varX);

  d_tableau.increaseSize();
  d_tableauSizeHasBeenModified = true;

  d_constraintDatabase.addVariable(varX);

  Debug("arith::arithvar") << x << " |-> " << varX << endl;

  return varX;
}

void TheoryArith::asVectors(const Polynomial& p, std::vector<Rational>& coeffs, std::vector<ArithVar>& variables) {
  for(Polynomial::iterator i = p.begin(), end = p.end(); i != end; ++i){
    const Monomial& mono = *i;
    const Constant& constant = mono.getConstant();
    const VarList& variable = mono.getVarList();

    Node n = variable.getNode();

    Debug("rewriter") << "should be var: " << n << endl;

    Assert(isLeaf(n));
    Assert(theoryOf(n) != THEORY_ARITH || d_arithvarNodeMap.hasArithVar(n));

    Assert(d_arithvarNodeMap.hasArithVar(n));
    ArithVar av;
    if (theoryOf(n) != THEORY_ARITH && !d_arithvarNodeMap.hasArithVar(n)) {
      // The only way not to get it through pre-register is if it's a foreign term
      ++(d_statistics.d_statUserVariables);
      av = requestArithVar(n,false);
      setupInitialValue(av);
    } else {
      // Otherwise, we already have it's variable
      av = d_arithvarNodeMap.asArithVar(n);
    }

    coeffs.push_back(constant.getValue());
    variables.push_back(av);
  }
}

/* Requirements:
 * For basic variables the row must have been added to the tableau.
 */
void TheoryArith::setupInitialValue(ArithVar x){

  if(!d_tableau.isBasic(x)){
    d_partialModel.initialize(x, d_DELTA_ZERO);
  }else{
    //If the variable is basic, assertions may have already happened and updates
    //may have occured before setting this variable up.

    //This can go away if the tableau creation is done at preregister
    //time instead of register
    DeltaRational safeAssignment = d_linEq.computeRowValue(x, true);
    DeltaRational assignment = d_linEq.computeRowValue(x, false);
    d_partialModel.initialize(x,safeAssignment);
    d_partialModel.setAssignment(x,assignment);
  }
  Debug("arith") << "setupVariable("<<x<<")"<<std::endl;
}

ArithVar TheoryArith::determineArithVar(const Polynomial& p) const{
  Assert(!p.containsConstant());
  Assert(p.getHead().constantIsPositive());
  TNode n = p.getNode();
  Debug("determineArithVar") << "determineArithVar(" << n << ")" << endl;
  return d_arithvarNodeMap.asArithVar(n);
}

ArithVar TheoryArith::determineArithVar(TNode assertion) const{
  Debug("determineArithVar") << "determineArithVar " << assertion << endl;
  Comparison cmp = Comparison::parseNormalForm(assertion);
  Polynomial variablePart = cmp.normalizedVariablePart();
  return determineArithVar(variablePart);
}


bool TheoryArith::canSafelyAvoidEqualitySetup(TNode equality){
  Assert(equality.getKind() == EQUAL);
  return d_arithvarNodeMap.hasArithVar(equality[0]);
}

Comparison TheoryArith::mkIntegerEqualityFromAssignment(ArithVar v){
  const DeltaRational& beta = d_partialModel.getAssignment(v);

  Assert(beta.isIntegral());
  Polynomial betaAsPolynomial( Constant::mkConstant(beta.floor()) );

  TNode var = d_arithvarNodeMap.asNode(v);
  Polynomial varAsPolynomial = Polynomial::parsePolynomial(var);
  return Comparison::mkComparison(EQUAL, varAsPolynomial, betaAsPolynomial);
}

Node TheoryArith::dioCutting(){
  context::Context::ScopedPush speculativePush(getSatContext());
  //DO NOT TOUCH THE OUTPUTSTREAM

  //TODO: Improve this
  for(ArithVar v = 0, end = d_variables.size(); v != end; ++v){
    if(isInteger(v)){
      const DeltaRational& dr = d_partialModel.getAssignment(v);
      if(d_partialModel.equalsUpperBound(v, dr) || d_partialModel.equalsLowerBound(v, dr)){
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

Node TheoryArith::callDioSolver(){
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
      Debug("dio::push") << v << " " << eq.getNode() << endl;
      d_diosolver.pushInputConstraint(eq, orig);
    }
  }

  return d_diosolver.processEquationsForConflict();
}

Constraint TheoryArith::constraintFromFactQueue(){
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
        d_raiseConflict(assertion);
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
      d_assertionsThatDoNotMatchTheirLiterals[assertion] = constraint;
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
    d_raiseConflict(conflict);
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

bool TheoryArith::assertionCases(Constraint constraint){
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
          d_raiseConflict(conf);
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
          d_raiseConflict(conf);
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
// Node TheoryArith::assertionCases(TNode assertion){
//   Constraint constraint = d_constraintDatabase.lookup(assertion);

//   Kind simpleKind = Comparison::comparisonKind(assertion);
//   Assert(simpleKind != UNDEFINED_KIND);
//   Assert(constraint != NullConstraint ||
//          simpleKind == EQUAL ||
//          simpleKind == DISTINCT );
//   if(simpleKind == EQUAL || simpleKind == DISTINCT){
//     Node eq = (simpleKind == DISTINCT) ? assertion[0] : assertion;

//     if(!isSetup(eq)){
//       //The previous code was equivalent to:
//       setupAtom(eq);
//       constraint = d_constraintDatabase.lookup(assertion);
//     }
//   }
//   Assert(constraint != NullConstraint);

//   if(constraint->negationHasProof()){
//     Constraint negation = constraint->getNegation();
//     if(negation->isSelfExplaining()){
//       if(Debug.isOn("whytheoryenginewhy")){
//         debugPrintFacts();
//       }
// //      Warning() << "arith: Theory engine is sending me both a literal and its negation?"
// //                << "BOOOOOOOOOOOOOOOOOOOOOO!!!!"<< endl;
//     }
//     Debug("arith::eq") << constraint << endl;
//     Debug("arith::eq") << negation << endl;

//     NodeBuilder<> nb(kind::AND);
//     nb << assertion;
//     negation->explainForConflict(nb);
//     Node conflict = nb;
//     Debug("arith::eq") << "conflict" << conflict << endl;
//     return conflict;
//   }
//   Assert(!constraint->negationHasProof());

//   if(constraint->assertedToTheTheory()){
//     //Do nothing
//     return Node::null();
//   }
//   Assert(!constraint->assertedToTheTheory());
//   constraint->setAssertedToTheTheory();

//   ArithVar x_i = constraint->getVariable();
//   //DeltaRational c_i = determineRightConstant(assertion, simpleKind);

//   //Assert(constraint->getVariable() == determineLeftVariable(assertion, simpleKind));
//   //Assert(constraint->getValue() == determineRightConstant(assertion, simpleKind));
//   Assert(!constraint->hasLiteral() || constraint->getLiteral() == assertion);

//   Debug("arith::assertions")  << "arith assertion @" << getSatContext()->getLevel()
//                               <<"(" << assertion
//                               << " \\-> "
//     //<< determineLeftVariable(assertion, simpleKind)
//                               <<" "<< simpleKind <<" "
//     //<< determineRightConstant(assertion, simpleKind)
//                               << ")" << std::endl;


//   Debug("arith::constraint") << "arith constraint " << constraint << std::endl;

//   if(!constraint->hasProof()){
//     Debug("arith::constraint") << "marking as constraint as self explaining " << endl;
//     constraint->selfExplaining();
//   }else{
//     Debug("arith::constraint") << "already has proof: " << constraint->explainForConflict() << endl;
//   }

//   Assert(!isInteger(x_i) ||
//          simpleKind == EQUAL ||
//          simpleKind == DISTINCT ||
//          simpleKind == GEQ ||
//          simpleKind == LT);

//   switch(constraint->getType()){
//   case UpperBound:
//     if(simpleKind == LT && isInteger(x_i)){
//       Constraint floorConstraint = constraint->getFloor();
//       if(!floorConstraint->isTrue()){
//         if(floorConstraint->negationHasProof()){
//           return ConstraintValue::explainConflict(constraint, floorConstraint->getNegation());
//         }else{
//           floorConstraint->impliedBy(constraint);
//         }
//       }
//       //c_i = DeltaRational(c_i.floor());
//       //return AssertUpper(x_i, c_i, assertion, floorConstraint);
//       return AssertUpper(floorConstraint);
//     }else{
//       return AssertUpper(constraint);
//     }
//     //return AssertUpper(x_i, c_i, assertion, constraint);
//   case LowerBound:
//     if(simpleKind == LT && isInteger(x_i)){
//       Constraint ceilingConstraint = constraint->getCeiling();
//       if(!ceilingConstraint->isTrue()){
//         if(ceilingConstraint->negationHasProof()){

//           return ConstraintValue::explainConflict(constraint, ceilingConstraint->getNegation());
//         }
//         ceilingConstraint->impliedBy(constraint);
//       }
//       //c_i = DeltaRational(c_i.ceiling());
//       //return AssertLower(x_i, c_i, assertion, ceilingConstraint);
//       return AssertLower(ceilingConstraint);
//     }else{
//       return AssertLower(constraint);
//     }
//     //return AssertLower(x_i, c_i, assertion, constraint);
//   case Equality:
//     return AssertEquality(constraint);
//     //return AssertEquality(x_i, c_i, assertion, constraint);
//   case Disequality:
//     return AssertDisequality(constraint);
//     //return AssertDisequality(x_i, c_i, assertion, constraint);
//   default:
//     Unreachable();
//     return Node::null();
//   }
// }

/**
 * Looks for the next integer variable without an integer assignment in a round robin fashion.
 * Changes the value of d_nextIntegerCheckVar.
 *
 * If this returns false, d_nextIntegerCheckVar does not have an integer assignment.
 * If this returns true, all integer variables have an integer assignment.
 */
bool TheoryArith::hasIntegerModel(){
  if(d_variables.size() > 0){
    const ArithVar rrEnd = d_nextIntegerCheckVar;
    do {
      //Do not include slack variables
      if(isInteger(d_nextIntegerCheckVar) && !isSlackVariable(d_nextIntegerCheckVar)) { // integer
        const DeltaRational& d = d_partialModel.getAssignment(d_nextIntegerCheckVar);
        if(!d.isIntegral()){
          return false;
        }
      }
    } while((d_nextIntegerCheckVar = (1 + d_nextIntegerCheckVar == d_variables.size() ? 0 : 1 + d_nextIntegerCheckVar)) != rrEnd);
  }
  return true;
}

/** Outputs conflicts to the output channel. */
void TheoryArith::outputConflicts(){
  Assert(!d_conflicts.empty());
  for(size_t i = 0, i_end = d_conflicts.size(); i < i_end; ++i){
    Node conflict = d_conflicts[i];
    Debug("arith::conflict") << "d_conflicts[" << i << "] " << conflict << endl;
    d_out->conflict(conflict);
  }
}

void TheoryArith::check(Effort effortLevel){
  Assert(d_currentPropagationList.empty());
  Debug("effortlevel") << "TheoryArith::check " << effortLevel << std::endl;
  Debug("arith") << "TheoryArith::check begun " << effortLevel << std::endl;

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
      bool res = assertionCases(curr);
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

      bool res = assertionCases(curr);
      Assert(!res || inConflict());

      if(inConflict()){ break; }
    }
  }

  if(inConflict()){
    d_qflraStatus = Result::UNSAT;
    if(previous == Result::SAT){
      ++d_statistics.d_revertsOnConflicts;
      revertOutOfConflict();
      d_simplex.clearQueue();
    }else{
      ++d_statistics.d_commitsOnConflicts;

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

  d_qflraStatus = d_simplex.findModel(fullEffort(effortLevel));
  switch(d_qflraStatus){
  case Result::SAT:
    if(newFacts){
      ++d_statistics.d_nontrivialSatChecks;
    }
    d_partialModel.commitAssignmentChanges();
    d_unknownsInARow = 0;
    if(Debug.isOn("arith::consistency")){
      Assert(entireStateIsConsistent());
    }
    break;
  case Result::SAT_UNKNOWN:
    ++d_unknownsInARow;
    ++(d_statistics.d_unknownChecks);
    Assert(!fullEffort(effortLevel));
    d_partialModel.commitAssignmentChanges();
    d_statistics.d_maxUnknownsInARow.maxAssign(d_unknownsInARow);
    break;
  case Result::UNSAT:
    d_unknownsInARow = 0;
    if(previous == Result::SAT){
      ++d_statistics.d_revertsOnConflicts;
      revertOutOfConflict();
      d_simplex.clearQueue();
    }else{
      ++d_statistics.d_commitsOnConflicts;

      d_partialModel.commitAssignmentChanges();
      revertOutOfConflict();
    }
    outputConflicts();
    emmittedConflictOrSplit = true;
    break;
  default:
    Unimplemented();
  }
  d_statistics.d_avgUnknownsInARow.addEntry(d_unknownsInARow);

  // This should be fine if sat or unknown
  if(!emmittedConflictOrSplit &&
     (Options::current()->arithPropagationMode == Options::UNATE_PROP ||
      Options::current()->arithPropagationMode == Options::BOTH_PROP)){
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
    }
  }else{
    TimerStat::CodeTimer codeTimer(d_statistics.d_newPropTime);
    d_currentPropagationList.clear();
  }
  Assert( d_currentPropagationList.empty());


  if(!emmittedConflictOrSplit && fullEffort(effortLevel)){
    emmittedConflictOrSplit = splitDisequalities();
  }

  if(!emmittedConflictOrSplit && fullEffort(effortLevel) && !hasIntegerModel()){
    Node possibleConflict = Node::null();
    if(!emmittedConflictOrSplit && Options::current()->arithDioSolver){
      possibleConflict = callDioSolver();
      if(possibleConflict != Node::null()){
        revertOutOfConflict();
        Debug("arith::conflict") << "dio conflict   " << possibleConflict << endl;
        d_out->conflict(possibleConflict);
        emmittedConflictOrSplit = true;
      }
    }

    if(!emmittedConflictOrSplit && d_hasDoneWorkSinceCut && Options::current()->arithDioSolver){
      Node possibleLemma = dioCutting();
      if(!possibleLemma.isNull()){
        Debug("arith") << "dio cut   " << possibleLemma << endl;
        emmittedConflictOrSplit = true;
        d_hasDoneWorkSinceCut = false;
        d_out->lemma(possibleLemma);
      }
    }

    if(!emmittedConflictOrSplit) {
      Node possibleLemma = roundRobinBranch();
      if(!possibleLemma.isNull()){
        ++(d_statistics.d_externalBranchAndBounds);
        emmittedConflictOrSplit = true;
        d_out->lemma(possibleLemma);
      }
    }
  }//if !emmittedConflictOrSplit && fullEffort(effortLevel) && !hasIntegerModel()

  if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }
  if(Debug.isOn("arith::print_model")) { debugPrintModel(); }
  Debug("arith") << "TheoryArith::check end" << std::endl;
}

/** Returns true if the roundRobinBranching() issues a lemma. */
Node TheoryArith::roundRobinBranch(){
  if(hasIntegerModel()){
    return Node::null();
  }else{
    ArithVar v = d_nextIntegerCheckVar;

    Assert(isInteger(v));
    Assert(!isSlackVariable(v));

    const DeltaRational& d = d_partialModel.getAssignment(v);
    const Rational& r = d.getNoninfinitesimalPart();
    const Rational& i = d.getInfinitesimalPart();
    Trace("integers") << "integers: assignment to [[" << d_arithvarNodeMap.asNode(v) << "]] is " << r << "[" << i << "]" << endl;

    Assert(! (r.getDenominator() == 1 && i.getNumerator() == 0));
    Assert(!d.isIntegral());

    TNode var = d_arithvarNodeMap.asNode(v);
    Integer floor_d = d.floor();
    Integer ceil_d = d.ceiling();

    Node leq = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::LEQ, var, mkRationalNode(floor_d)));
    Node geq = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::GEQ, var, mkRationalNode(ceil_d)));


    Node lem = NodeManager::currentNM()->mkNode(kind::OR, leq, geq);
    Trace("integers") << "integers: branch & bound: " << lem << endl;
    if(d_valuation.isSatLiteral(lem[0])) {
      Debug("integers") << "    " << lem[0] << " == " << d_valuation.getSatValue(lem[0]) << endl;
    } else {
      Debug("integers") << "    " << lem[0] << " is not assigned a SAT literal" << endl;
    }
    if(d_valuation.isSatLiteral(lem[1])) {
      Debug("integers") << "    " << lem[1] << " == " << d_valuation.getSatValue(lem[1]) << endl;
    } else {
      Debug("integers") << "    " << lem[1] << " is not assigned a SAT literal" << endl;
    }
    return lem;
  }
}

bool TheoryArith::splitDisequalities(){
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
        d_out->lemma(lemma);
        splitSomething = true;
      }else if(d_partialModel.strictlyLessThanLowerBound(lhsVar, rhsValue)){
        Debug("eq") << "can drop as less than lb" << front << endl;
      }else if(d_partialModel.strictlyGreaterThanUpperBound(lhsVar, rhsValue)){
        Debug("eq") << "can drop as greater than ub" << front << endl;
      }else{
        Debug("eq") << "save" << front << endl;
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
void TheoryArith::debugPrintAssertions() {
  Debug("arith::print_assertions") << "Assertions:" << endl;
  for (ArithVar i = 0; i < d_variables.size(); ++ i) {
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

void TheoryArith::debugPrintModel(){
  Debug("arith::print_model") << "Model:" << endl;

  for (ArithVar i = 0; i < d_variables.size(); ++ i) {
    Debug("arith::print_model") << d_variables[i] << " : " <<
      d_partialModel.getAssignment(i);
    if(d_tableau.isBasic(i))
      Debug("arith::print_model") << " (basic)";
    Debug("arith::print_model") << endl;
  }
}



Node TheoryArith::explain(TNode n) {

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


void TheoryArith::propagate(Effort e) {
  // This uses model values for safety. Disable for now.
  if(d_qflraStatus == Result::SAT &&
     (Options::current()->arithPropagationMode == Options::BOUND_INFERENCE_PROP ||
      Options::current()->arithPropagationMode == Options::BOTH_PROP)
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

      d_out->propagate(literal);
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
      d_out->propagate(toProp);
    }else if(constraint->negationHasProof()){
      Node exp = d_congruenceManager.explain(toProp);
      Node notNormalized = normalized.getKind() == NOT ?
        normalized[0] : normalized.notNode();
      Node lp = flattenAnd(exp.andNode(notNormalized));
      Debug("arith::prop") << "propagate conflict" <<  lp << endl;
      d_out->conflict(lp);
      return;
    }else{
      Debug("arith::prop") << "propagating still?" <<  toProp << endl;

      d_out->propagate(toProp);
    }
  }
}

bool TheoryArith::getDeltaAtomValue(TNode n) {
  Assert(d_qflraStatus != Result::SAT_UNKNOWN);

  switch (n.getKind()) {
    case kind::EQUAL: // 2 args
      return getDeltaValue(n[0]) == getDeltaValue(n[1]);
    case kind::LT: // 2 args
      return getDeltaValue(n[0]) < getDeltaValue(n[1]);
    case kind::LEQ: // 2 args
      return getDeltaValue(n[0]) <= getDeltaValue(n[1]);
    case kind::GT: // 2 args
      return getDeltaValue(n[0]) > getDeltaValue(n[1]);
    case kind::GEQ: // 2 args
      return getDeltaValue(n[0]) >= getDeltaValue(n[1]);
    default:
      Unreachable();
  }
}


DeltaRational TheoryArith::getDeltaValue(TNode n) {
  Assert(d_qflraStatus != Result::SAT_UNKNOWN);
  Debug("arith::value") << n << std::endl;

  switch(n.getKind()) {

  case kind::CONST_RATIONAL:
    return n.getConst<Rational>();

  case kind::PLUS: { // 2+ args
    DeltaRational value(0);
    for(TNode::iterator i = n.begin(),
          iend = n.end();
        i != iend;
        ++i) {
      value = value + getDeltaValue(*i);
    }
    return value;
  }

  case kind::MULT: { // 2+ args
    Assert(n.getNumChildren() == 2 && n[0].isConst());
    DeltaRational value(1);
    if (n[0].getKind() == kind::CONST_RATIONAL) {
      return getDeltaValue(n[1]) * n[0].getConst<Rational>();
    }
    Unreachable();
  }

  case kind::MINUS: // 2 args
    // should have been rewritten
    Unreachable();

  case kind::UMINUS: // 1 arg
    // should have been rewritten
    Unreachable();

  case kind::DIVISION: // 2 args
    Assert(n[1].isConst());
    if (n[1].getKind() == kind::CONST_RATIONAL) {
      return getDeltaValue(n[0]) / n[0].getConst<Rational>();
    }
    Unreachable();


  default:
    {
      if(isSetup(n)){
        ArithVar var = d_arithvarNodeMap.asArithVar(n);
        return d_partialModel.getAssignment(var);
      }else{
        Unreachable();
      }
    }
  }
}

Node TheoryArith::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

  Assert(d_qflraStatus == Result::SAT);

  switch(n.getKind()) {
  case kind::VARIABLE: {
    ArithVar var = d_arithvarNodeMap.asArithVar(n);

    DeltaRational drat = d_partialModel.getAssignment(var);
    const Rational& delta = d_partialModel.getDelta();
    Debug("getValue") << n << " " << drat << " " << delta << endl;
    return nodeManager->
      mkConst( drat.getNoninfinitesimalPart() +
               drat.getInfinitesimalPart() * delta );
  }

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( d_valuation.getValue(n[0]) == d_valuation.getValue(n[1]) );

  case kind::PLUS: { // 2+ args
    Rational value(0);
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      value += d_valuation.getValue(*i).getConst<Rational>();
    }
    return nodeManager->mkConst(value);
  }

  case kind::MULT: { // 2+ args
    Rational value(1);
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      value *= d_valuation.getValue(*i).getConst<Rational>();
    }
    return nodeManager->mkConst(value);
  }

  case kind::MINUS: // 2 args
    // should have been rewritten
    Unreachable();

  case kind::UMINUS: // 1 arg
    // should have been rewritten
    Unreachable();

  case kind::DIVISION: // 2 args
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<Rational>() /
                                 d_valuation.getValue(n[1]).getConst<Rational>() );

  case kind::LT: // 2 args
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<Rational>() <
                                 d_valuation.getValue(n[1]).getConst<Rational>() );

  case kind::LEQ: // 2 args
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<Rational>() <=
                                 d_valuation.getValue(n[1]).getConst<Rational>() );

  case kind::GT: // 2 args
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<Rational>() >
                                 d_valuation.getValue(n[1]).getConst<Rational>() );

  case kind::GEQ: // 2 args
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<Rational>() >=
                                 d_valuation.getValue(n[1]).getConst<Rational>() );

  default:
    Unhandled(n.getKind());
  }
}

void TheoryArith::notifyRestart(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_restartTimer);

  if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }

  ++d_restartsCounter;

  uint32_t currSize = d_tableau.size();
  uint32_t copySize = d_smallTableauCopy.size();

  Debug("arith::reset") << "curr " << currSize << " copy " << copySize << endl;
  Debug("arith::reset") << "tableauSizeHasBeenModified " << d_tableauSizeHasBeenModified << endl;

  if(d_tableauSizeHasBeenModified){
    Debug("arith::reset") << "row has been added must copy " << d_restartsCounter << endl;
    d_smallTableauCopy = d_tableau;
    d_tableauSizeHasBeenModified = false;
  }else if( d_restartsCounter >= RESET_START){
    if(copySize >= currSize * 1.1 ){
      ++d_statistics.d_smallerSetToCurr;
      d_smallTableauCopy = d_tableau;
    }else if(d_tableauResetDensity * copySize <=  currSize){
      ++d_statistics.d_currSetToSmaller;
      d_tableau = d_smallTableauCopy;
    }
  }
}

bool TheoryArith::entireStateIsConsistent(){
  typedef std::vector<Node>::const_iterator VarIter;
  bool result = true;
  for(VarIter i = d_variables.begin(), end = d_variables.end(); i != end; ++i){
    ArithVar var = d_arithvarNodeMap.asArithVar(*i);
    if(!d_partialModel.assignmentIsConsistent(var)){
      d_partialModel.printModel(var);
      Warning() << "Assignment is not consistent for " << var << *i;
      if(d_tableau.isBasic(var)){
        Warning() << " (basic)";
      }
      Warning() << endl;
      result = false;
    }
  }
  return result;
}

bool TheoryArith::unenqueuedVariablesAreConsistent(){
  typedef std::vector<Node>::const_iterator VarIter;
  bool result = true;
  for(VarIter i = d_variables.begin(), end = d_variables.end(); i != end; ++i){
    ArithVar var = d_arithvarNodeMap.asArithVar(*i);
    if(!d_partialModel.assignmentIsConsistent(var) &&
       !d_simplex.debugIsInCollectionQueue(var)){

      d_partialModel.printModel(var);
      Warning() << "Unenqueued var is not consistent for " << var << *i;
      if(d_tableau.isBasic(var)){
        Warning() << " (basic)";
      }
      Warning() << endl;
      result = false;
    }
  }
  return result;
}

void TheoryArith::presolve(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_presolveTime);

  d_statistics.d_initialTableauSize.setData(d_tableau.size());

  if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }

  static CVC4_THREADLOCAL(unsigned) callCount = 0;
  if(Debug.isOn("arith::presolve")) {
    Debug("arith::presolve") << "TheoryArith::presolve #" << callCount << endl;
    callCount = callCount + 1;
  }

  vector<Node> lemmas;
  switch(Options::current()->arithUnateLemmaMode){
  case Options::NO_PRESOLVE_LEMMAS:
    break;
  case Options::INEQUALITY_PRESOLVE_LEMMAS:
    d_constraintDatabase.outputUnateInequalityLemmas(lemmas);
    break;
  case Options::EQUALITY_PRESOLVE_LEMMAS:
    d_constraintDatabase.outputUnateEqualityLemmas(lemmas);
    break;
  case Options::ALL_PRESOLVE_LEMMAS:
    d_constraintDatabase.outputUnateInequalityLemmas(lemmas);
    d_constraintDatabase.outputUnateEqualityLemmas(lemmas);
    break;
  default:
    Unhandled(Options::current()->arithUnateLemmaMode);
  }

  vector<Node>::const_iterator i = lemmas.begin(), i_end = lemmas.end();
  for(; i != i_end; ++i){
    Node lem = *i;
    Debug("arith::oldprop") << " lemma lemma duck " <<lem << endl;
    d_out->lemma(lem);
  }

  // if(Options::current()->arithUnateLemmaMode == Options::ALL_UNATE){
  //   vector<Node> lemmas;
  //   d_constraintDatabase.outputAllUnateLemmas(lemmas);
  //   vector<Node>::const_iterator i = lemmas.begin(), i_end = lemmas.end();
  //   for(; i != i_end; ++i){
  //     Node lem = *i;
  //     Debug("arith::oldprop") << " lemma lemma duck " <<lem << endl;
  //     d_out->lemma(lem);
  //   }
  // }

  d_learner.clear();
}

EqualityStatus TheoryArith::getEqualityStatus(TNode a, TNode b) {
  if(d_qflraStatus == Result::SAT_UNKNOWN){
    return EQUALITY_UNKNOWN;
  }else if (getDeltaValue(a) == getDeltaValue(b)) {
    return EQUALITY_TRUE_IN_MODEL;
  } else {
    return EQUALITY_FALSE_IN_MODEL;
  }

}

bool TheoryArith::rowImplication(ArithVar v, bool upperBound, const DeltaRational& r){
  Unimplemented();
  return false;
}

bool TheoryArith::propagateCandidateBound(ArithVar basic, bool upperBound){
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

void TheoryArith::propagateCandidate(ArithVar basic){
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

void TheoryArith::propagateCandidates(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_boundComputationTime);

  Assert(d_candidateBasics.empty());

  if(d_updatedBounds.empty()){ return; }

  DenseSet::const_iterator i = d_updatedBounds.begin();
  DenseSet::const_iterator end = d_updatedBounds.end();
  for(; i != end; ++i){
    ArithVar var = *i;
    if(d_tableau.isBasic(var) &&
       d_tableau.getRowLength(d_tableau.basicToRowIndex(var)) <= Options::current()->arithPropagateMaxLength){
      d_candidateBasics.softAdd(var);
    }else{
      Tableau::ColIterator basicIter = d_tableau.colIterator(var);
      for(; !basicIter.atEnd(); ++basicIter){
        const Tableau::Entry& entry = *basicIter;
        RowIndex ridx = entry.getRowIndex();
        ArithVar rowVar = d_tableau.rowIndexToBasic(ridx);
        Assert(entry.getColVar() == var);
        Assert(d_tableau.isBasic(rowVar));
        if(d_tableau.getRowLength(ridx) <= Options::current()->arithPropagateMaxLength){
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

}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */

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


TheoryArith::TheoryArith(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
  Theory(THEORY_ARITH, c, u, out, valuation, logicInfo),
  d_hasDoneWorkSinceCut(false),
  d_learner(d_pbSubstitutions),
  d_setupLiteralCallback(this),
  d_nextIntegerCheckVar(0),
  d_constantIntegerVariables(c),
  d_diseqQueue(c, false),
  d_partialModel(c),
  d_tableau(),
  d_linEq(d_partialModel, d_tableau, d_basicVarModelUpdateCallBack),
  d_diosolver(c),
  d_pbSubstitutions(u),
  d_restartsCounter(0),
  d_rowHasBeenAdded(false),
  d_tableauResetDensity(1.6),
  d_tableauResetPeriod(10),
  d_conflicts(c),
  d_conflictCallBack(d_conflicts),
  d_congruenceManager(c, d_constraintDatabase, d_setupLiteralCallback, d_arithvarNodeMap),
  d_simplex(d_linEq, d_conflictCallBack),
  d_constraintDatabase(c, u, d_arithvarNodeMap, d_congruenceManager),
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
  d_externalBranchAndBounds("theory::arith::externalBranchAndBounds",0),
  d_initialTableauSize("theory::arith::initialTableauSize", 0),
  d_currSetToSmaller("theory::arith::currSetToSmaller", 0),
  d_smallerSetToCurr("theory::arith::smallerSetToCurr", 0),
  d_restartTimer("theory::arith::restartTimer"),
  d_boundComputationTime("theory::arith::bound::time"),
  d_boundComputations("theory::arith::bound::boundComputations",0),
  d_boundPropagations("theory::arith::bound::boundPropagations",0)
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

  StatisticsRegistry::registerStat(&d_externalBranchAndBounds);

  StatisticsRegistry::registerStat(&d_initialTableauSize);
  StatisticsRegistry::registerStat(&d_currSetToSmaller);
  StatisticsRegistry::registerStat(&d_smallerSetToCurr);
  StatisticsRegistry::registerStat(&d_restartTimer);

  StatisticsRegistry::registerStat(&d_boundComputationTime);
  StatisticsRegistry::registerStat(&d_boundComputations);
  StatisticsRegistry::registerStat(&d_boundPropagations);
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

  StatisticsRegistry::unregisterStat(&d_externalBranchAndBounds);

  StatisticsRegistry::unregisterStat(&d_initialTableauSize);
  StatisticsRegistry::unregisterStat(&d_currSetToSmaller);
  StatisticsRegistry::unregisterStat(&d_smallerSetToCurr);
  StatisticsRegistry::unregisterStat(&d_restartTimer);

  StatisticsRegistry::unregisterStat(&d_boundComputationTime);
  StatisticsRegistry::unregisterStat(&d_boundComputations);
  StatisticsRegistry::unregisterStat(&d_boundPropagations);
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
Node TheoryArith::AssertLower(Constraint constraint){
  Assert(constraint != NullConstraint);
  Assert(constraint->isLowerBound());

  ArithVar x_i = constraint->getVariable();
  const DeltaRational& c_i = constraint->getValue();

  Debug("arith") << "AssertLower(" << x_i << " " << c_i << ")"<< std::endl;

  Assert(!isInteger(x_i) || c_i.isIntegral());

  //TODO Relax to less than?
  if(d_partialModel.lessThanLowerBound(x_i, c_i)){
    return Node::null();
  }

  int cmpToUB = d_partialModel.cmpToUpperBound(x_i, c_i);
  if(cmpToUB > 0){ //  c_i < \lowerbound(x_i)
    Constraint ubc = d_partialModel.getUpperBoundConstraint(x_i);
    Node conflict = ConstraintValue::explainConflict(ubc, constraint);
    Debug("arith") << "AssertLower conflict " << conflict << endl;
    ++(d_statistics.d_statAssertLowerConflicts);
    return conflict;
  }else if(cmpToUB == 0){
    if(isInteger(x_i)){
      d_constantIntegerVariables.push_back(x_i);
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
        return conflict;
      }else if(!eq->isTrue()){
        Debug("eq") << "lb == ub, propagate eq" << eq << endl;
        eq->impliedBy(constraint, d_partialModel.getUpperBoundConstraint(x_i));
      }
    }
  }

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

  return Node::null();
}

/* procedure AssertUpper( x_i <= c_i) */
Node TheoryArith::AssertUpper(Constraint constraint){
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
    return Node::null(); //sat
  }

  // cmpToLb =  \lowerbound(x_i).cmp(c_i)
  int cmpToLB = d_partialModel.cmpToLowerBound(x_i, c_i);
  if( cmpToLB < 0 ){ //  \upperbound(x_i) < \lowerbound(x_i)
    Constraint lbc = d_partialModel.getLowerBoundConstraint(x_i);
    Node conflict =  ConstraintValue::explainConflict(lbc, constraint);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
    ++(d_statistics.d_statAssertUpperConflicts);
    return conflict;
  }else if(cmpToLB == 0){ // \lowerBound(x_i) == \upperbound(x_i)
    if(isInteger(x_i)){
      d_constantIntegerVariables.push_back(x_i);
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
        return conflict;
      }else if(!eq->isTrue()){
        Debug("eq") << "lb == ub, propagate eq" << eq << endl;
        eq->impliedBy(constraint, d_partialModel.getLowerBoundConstraint(x_i));
      }
    }

  }

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

  return Node::null();
}


/* procedure AssertEquality( x_i == c_i ) */
Node TheoryArith::AssertEquality(Constraint constraint){
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
    return Node::null(); //sat
  }

  if(cmpToUB > 0){
    Constraint ubc = d_partialModel.getUpperBoundConstraint(x_i);
    Node conflict = ConstraintValue::explainConflict(ubc, constraint);
    Debug("arith") << "AssertEquality conflicts with upper bound " << conflict << endl;
    return conflict;
  }

  if(cmpToLB < 0){
    Constraint lbc = d_partialModel.getLowerBoundConstraint(x_i);
    Node conflict = ConstraintValue::explainConflict(lbc, constraint);
    Debug("arith") << "AssertEquality conflicts with lower bound" << conflict << endl;
    return conflict;
  }

  Assert(cmpToUB <= 0);
  Assert(cmpToLB >= 0);
  Assert(cmpToUB < 0 || cmpToLB > 0);


  if(isInteger(x_i)){
    d_constantIntegerVariables.push_back(x_i);
  }

  // Don't bother to check whether x_i != c_i is in d_diseq
  // The a and (not a) should never be on the fact queue

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
  return Node::null();
}


/* procedure AssertDisequality( x_i != c_i ) */
Node TheoryArith::AssertDisequality(Constraint constraint){

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
    return Node::null();
  }

  const ValueCollection& vc = constraint->getValueCollection();
  if(vc.hasLowerBound() && vc.hasUpperBound()){
    const Constraint lb = vc.getLowerBound();
    const Constraint ub = vc.getUpperBound();
    if(lb->isTrue() && ub->isTrue()){
      //in conflict
      Debug("eq") << "explaining" << endl;
      ++(d_statistics.d_statDisequalityConflicts);
      return ConstraintValue::explainConflict(constraint, lb, ub);
    }else if(lb->isTrue()){
      Debug("eq") << "propagate UpperBound " << constraint << lb << ub << endl;
      const Constraint negUb = ub->getNegation();
      if(!negUb->isTrue()){
        negUb->impliedBy(constraint, lb);
      }
    }else if(ub->isTrue()){
      Debug("eq") << "propagate LowerBound " << constraint << lb << ub << endl;
      const Constraint negLb = lb->getNegation();
      if(!negLb->isTrue()){
        negLb->impliedBy(constraint, ub);
      }
    }
  }


  if(c_i == d_partialModel.getAssignment(x_i)){
    Debug("eq") << "lemma now! " << constraint << endl;
    d_out->lemma(constraint->split());
    return Node::null();
  }else if(d_partialModel.strictlyLessThanLowerBound(x_i, c_i)){
    Debug("eq") << "can drop as less than lb" << constraint << endl;
  }else if(d_partialModel.strictlyGreaterThanUpperBound(x_i, c_i)){
    Debug("eq") << "can drop as less than ub" << constraint << endl;
  }else{
    Debug("eq") << "push back" << constraint << endl;
    d_diseqQueue.push(constraint);
  }
  return Node::null();

}

void TheoryArith::addSharedTerm(TNode n){
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

      if(elim.hasSubterm(minVar)){
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
    d_rowHasBeenAdded = true;

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
      d_diosolver.pushInputConstraint(eq, orig);
    }
  }

  return d_diosolver.processEquationsForConflict();
}

Node TheoryArith::assertionCases(TNode assertion){
  Constraint constraint = d_constraintDatabase.lookup(assertion);

  Kind simpleKind = Comparison::comparisonKind(assertion);
  Assert(simpleKind != UNDEFINED_KIND);
  Assert(constraint != NullConstraint ||
         simpleKind == EQUAL ||
         simpleKind == DISTINCT );
  if(simpleKind == EQUAL || simpleKind == DISTINCT){
    Node eq = (simpleKind == DISTINCT) ? assertion[0] : assertion;

    if(!isSetup(eq)){
      //The previous code was equivalent to:
      setupAtom(eq);
      constraint = d_constraintDatabase.lookup(assertion);
    }
  }
  Assert(constraint != NullConstraint);

  if(constraint->negationHasProof()){
    Constraint negation = constraint->getNegation();
    if(negation->isSelfExplaining()){
      if(Debug.isOn("whytheoryenginewhy")){
        debugPrintFacts();
      }
//      Warning() << "arith: Theory engine is sending me both a literal and its negation?"
//                << "BOOOOOOOOOOOOOOOOOOOOOO!!!!"<< endl;
    }
    Debug("arith::eq") << constraint << endl;
    Debug("arith::eq") << negation << endl;

    NodeBuilder<> nb(kind::AND);
    nb << assertion;
    negation->explainForConflict(nb);
    Node conflict = nb;
    Debug("arith::eq") << "conflict" << conflict << endl;
    return conflict;
  }
  Assert(!constraint->negationHasProof());

  if(constraint->assertedToTheTheory()){
    //Do nothing
    return Node::null();
  }
  Assert(!constraint->assertedToTheTheory());
  constraint->setAssertedToTheTheory();

  ArithVar x_i = constraint->getVariable();
  //DeltaRational c_i = determineRightConstant(assertion, simpleKind);

  //Assert(constraint->getVariable() == determineLeftVariable(assertion, simpleKind));
  //Assert(constraint->getValue() == determineRightConstant(assertion, simpleKind));
  Assert(!constraint->hasLiteral() || constraint->getLiteral() == assertion);

  Debug("arith::assertions")  << "arith assertion @" << getSatContext()->getLevel()
                              <<"(" << assertion
                              << " \\-> "
    //<< determineLeftVariable(assertion, simpleKind)
                              <<" "<< simpleKind <<" "
    //<< determineRightConstant(assertion, simpleKind)
                              << ")" << std::endl;


  Debug("arith::constraint") << "arith constraint " << constraint << std::endl;

  if(!constraint->hasProof()){
    Debug("arith::constraint") << "marking as constraint as self explaining " << endl;
    constraint->selfExplaining();
  }else{
    Debug("arith::constraint") << "already has proof: " << constraint->explainForConflict() << endl;
  }

  Assert(!isInteger(x_i) ||
         simpleKind == EQUAL ||
         simpleKind == DISTINCT ||
         simpleKind == GEQ ||
         simpleKind == LT);

  switch(constraint->getType()){
  case UpperBound:
    if(simpleKind == LT && isInteger(x_i)){
      Constraint floorConstraint = constraint->getFloor();
      if(!floorConstraint->isTrue()){
        if(floorConstraint->negationHasProof()){
          return ConstraintValue::explainConflict(constraint, floorConstraint->getNegation());
        }else{
          floorConstraint->impliedBy(constraint);
        }
      }
      //c_i = DeltaRational(c_i.floor());
      //return AssertUpper(x_i, c_i, assertion, floorConstraint);
      return AssertUpper(floorConstraint);
    }else{
      return AssertUpper(constraint);
    }
    //return AssertUpper(x_i, c_i, assertion, constraint);
  case LowerBound:
    if(simpleKind == LT && isInteger(x_i)){
      Constraint ceilingConstraint = constraint->getCeiling();
      if(!ceilingConstraint->isTrue()){
        if(ceilingConstraint->negationHasProof()){

          return ConstraintValue::explainConflict(constraint, ceilingConstraint->getNegation());
        }
        ceilingConstraint->impliedBy(constraint);
      }
      //c_i = DeltaRational(c_i.ceiling());
      //return AssertLower(x_i, c_i, assertion, ceilingConstraint);
      return AssertLower(ceilingConstraint);
    }else{
      return AssertLower(constraint);
    }
    //return AssertLower(x_i, c_i, assertion, constraint);
  case Equality:
    return AssertEquality(constraint);
    //return AssertEquality(x_i, c_i, assertion, constraint);
  case Disequality:
    return AssertDisequality(constraint);
    //return AssertDisequality(x_i, c_i, assertion, constraint);
  default:
    Unreachable();
    return Node::null();
  }
}

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


void TheoryArith::check(Effort effortLevel){
  Debug("arith") << "TheoryArith::check begun" << std::endl;

  d_hasDoneWorkSinceCut = d_hasDoneWorkSinceCut || !done();
  while(!done()){

    Node assertion = get();
    Node possibleConflict = assertionCases(assertion);

    if(!possibleConflict.isNull()){
      d_partialModel.revertAssignmentChanges();
      Debug("arith::conflict") << "conflict   " << possibleConflict << endl;
      clearUpdates();
      d_out->conflict(possibleConflict);
      return;
    }
    if(d_congruenceManager.inConflict()){
      Node c = d_congruenceManager.conflict();
      d_partialModel.revertAssignmentChanges();
      Debug("arith::conflict") << "difference manager conflict   " << c << endl;
      clearUpdates();
      d_out->conflict(c);
      return;
    }
  }


  if(Debug.isOn("arith::print_assertions")) {
    debugPrintAssertions();
  }

  bool emmittedConflictOrSplit = false;
  Assert(d_conflicts.empty());
  bool foundConflict = d_simplex.findModel();
  if(foundConflict){
    d_partialModel.revertAssignmentChanges();
    clearUpdates();

    Assert(!d_conflicts.empty());
    for(size_t i = 0, i_end = d_conflicts.size(); i < i_end; ++i){
      Node conflict = d_conflicts[i];
      Debug("arith::conflict") << "d_conflicts[" << i << "] " << conflict << endl;
      d_out->conflict(conflict);      
    }
    emmittedConflictOrSplit = true;
  }else{
    d_partialModel.commitAssignmentChanges();
  }


  if(!emmittedConflictOrSplit && fullEffort(effortLevel)){
    emmittedConflictOrSplit = splitDisequalities();
  }

  Node possibleConflict = Node::null();
  if(!emmittedConflictOrSplit && fullEffort(effortLevel) && !hasIntegerModel()){

    if(!emmittedConflictOrSplit && Options::current()->dioSolver){
      possibleConflict = callDioSolver();
      if(possibleConflict != Node::null()){
        Debug("arith::conflict") << "dio conflict   " << possibleConflict << endl;
        d_out->conflict(possibleConflict);
        emmittedConflictOrSplit = true;
      }
    }

    if(!emmittedConflictOrSplit && d_hasDoneWorkSinceCut && Options::current()->dioSolver){
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

    Node leq = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::LEQ, var, mkIntegerNode(floor_d)));
    Node geq = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::GEQ, var, mkIntegerNode(ceil_d)));


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
  }else{
    Assert(d_congruenceManager.canExplain(n));
    Debug("arith::explain") << "dm explanation" << n << endl;
    return d_congruenceManager.explain(n);
  }
}


void TheoryArith::propagate(Effort e) {
  if(Options::current()->arithPropagation && hasAnyUpdates()){
    propagateCandidates();
  }else{
    clearUpdates();
  }

  while(d_constraintDatabase.hasMorePropagations()){
    Constraint c = d_constraintDatabase.nextPropagation();

    if(c->negationHasProof()){
      Node conflict = ConstraintValue::explainConflict(c, c->getNegation());
      cout << "tears " << conflict << endl;
      Debug("arith::prop") << "propagate conflict" << conflict << endl;
      d_out->conflict(conflict);
      return;
    }else if(!c->assertedToTheTheory()){

      Node literal = c->getLiteral();
      Debug("arith::prop") << "propagating @" << getSatContext()->getLevel() << " " << literal << endl;

      d_out->propagate(literal);
    }else{
      Node literal = c->getLiteral();
      Debug("arith::prop") << "already asserted to the theory " << literal << endl;
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

  Debug("arith::value") << n << std::endl;

  switch(n.getKind()) {

  case kind::CONST_INTEGER:
    return Rational(n.getConst<Integer>());

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
    if (n[0].getKind() == kind::CONST_INTEGER) {
      return getDeltaValue(n[1]) * n[0].getConst<Integer>();
    }
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
    if (n[1].getKind() == kind::CONST_INTEGER) {
      return getDeltaValue(n[0]) / n[0].getConst<Integer>();
    }
    Unreachable();


  default:
  {
    ArithVar var = d_arithvarNodeMap.asArithVar(n);
    return d_partialModel.getAssignment(var);
  }
  }
}

Node TheoryArith::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

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

  static const bool debugResetPolicy = false;

  uint32_t currSize = d_tableau.size();
  uint32_t copySize = d_smallTableauCopy.size();

  if(debugResetPolicy){
    cout << "curr " << currSize << " copy " << copySize << endl;
  }
  if(d_rowHasBeenAdded){
    if(debugResetPolicy){
      cout << "row has been added must copy " << d_restartsCounter << endl;
    }
    d_smallTableauCopy = d_tableau;
    d_rowHasBeenAdded = false;
  }

  if(!d_rowHasBeenAdded && d_restartsCounter >= RESET_START){
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
  for(VarIter i = d_variables.begin(), end = d_variables.end(); i != end; ++i){
    ArithVar var = d_arithvarNodeMap.asArithVar(*i);
    if(!d_partialModel.assignmentIsConsistent(var)){
      d_partialModel.printModel(var);
      cerr << "Assignment is not consistent for " << var << *i << endl;
      return false;
    }
  }
  return true;
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

  if(Options::current()->arithPropagation ){
    vector<Node> lemmas;
    d_constraintDatabase.outputAllUnateLemmas(lemmas);
    vector<Node>::const_iterator i = lemmas.begin(), i_end = lemmas.end();
    for(; i != i_end; ++i){
      Node lem = *i;
      Debug("arith::oldprop") << " lemma lemma duck " <<lem << endl;
      d_out->lemma(lem);
    }
  }

  d_learner.clear();
}

EqualityStatus TheoryArith::getEqualityStatus(TNode a, TNode b) {
  if (getDeltaValue(a) == getDeltaValue(b)) {
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
        //<< " " << assertedValuation
                           << " " << assertedToTheTheory
                           << " " << canBePropagated
                           << " " << hasProof
                           << endl;

      if(!assertedToTheTheory && canBePropagated && !hasProof ){
        if(upperBound){
          Assert(bestImplied != d_partialModel.getUpperBoundConstraint(basic));
          d_linEq.propagateNonbasicsUpperBound(basic, bestImplied);
        }else{
          Assert(bestImplied != d_partialModel.getLowerBoundConstraint(basic));
          d_linEq.propagateNonbasicsLowerBound(basic, bestImplied);
        }
        return true;
      }

      // bool asserted = valuationIsAsserted(bestImplied);
      // bool propagated = d_theRealPropManager.isPropagated(bestImplied);
      // if( !asserted && !propagated){

      //   NodeBuilder<> nb(kind::AND);
      //   if(upperBound){
      //     d_linEq.explainNonbasicsUpperBound(basic, nb);
      //   }else{
      //     d_linEq.explainNonbasicsLowerBound(basic, nb);
      //   }
      //   Node explanation = nb;
      //   d_theRealPropManager.propagate(bestImplied, explanation, false);
      //   return true;
      // }else{
      //   Debug("arith::prop") << basic << " " << asserted << " " << propagated << endl;
      // }
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

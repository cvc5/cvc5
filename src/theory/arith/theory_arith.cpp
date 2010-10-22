/*********************                                                        */
/*! \file theory_arith.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): barrett, dejan, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

#include "theory/theory_engine.h"

#include "util/rational.h"
#include "util/integer.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/tableau.h"
#include "theory/arith/slack.h"
#include "theory/arith/basic.h"
#include "theory/arith/arith_activity.h"

#include "theory/arith/next_arith_rewriter.h"
#include "theory/arith/arith_propagator.h"

#include "theory/arith/theory_arith.h"
#include "theory/arith/normal_form.h"

#include <map>
#include <stdint.h>

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;



TheoryArith::TheoryArith(int id, context::Context* c, OutputChannel& out) :
  Theory(id, c, out),
  d_constants(NodeManager::currentNM()),
  d_partialModel(c),
  d_basicManager(),
  d_activityMonitor(),
  d_diseq(c),
  d_tableau(d_activityMonitor, d_basicManager),
  d_nextRewriter(&d_constants),
  d_propagator(c),
  d_statistics()
{}

TheoryArith::~TheoryArith(){
  for(vector<Node>::iterator i=d_variables.begin(); i!= d_variables.end(); ++i){
    Node var = *i;
    Debug("arithgc") << var << endl;
  }
}

TheoryArith::Statistics::Statistics():
  d_statPivots("theory::arith::pivots",0),
  d_statUpdates("theory::arith::updates",0),
  d_statAssertUpperConflicts("theory::arith::AssertUpperConflicts", 0),
  d_statAssertLowerConflicts("theory::arith::AssertLowerConflicts", 0),
  d_statUpdateConflicts("theory::arith::UpdateConflicts", 0),
  d_statUserVariables("theory::arith::UserVariables", 0),
  d_statSlackVariables("theory::arith::SlackVariables", 0)
{
  StatisticsRegistry::registerStat(&d_statPivots);
  StatisticsRegistry::registerStat(&d_statUpdates);
  StatisticsRegistry::registerStat(&d_statAssertUpperConflicts);
  StatisticsRegistry::registerStat(&d_statAssertLowerConflicts);
  StatisticsRegistry::registerStat(&d_statUpdateConflicts);
  StatisticsRegistry::registerStat(&d_statUserVariables);
  StatisticsRegistry::registerStat(&d_statSlackVariables);
}

TheoryArith::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statPivots);
  StatisticsRegistry::unregisterStat(&d_statUpdates);
  StatisticsRegistry::unregisterStat(&d_statAssertUpperConflicts);
  StatisticsRegistry::unregisterStat(&d_statAssertLowerConflicts);
  StatisticsRegistry::unregisterStat(&d_statUpdateConflicts);
  StatisticsRegistry::unregisterStat(&d_statUserVariables);
  StatisticsRegistry::unregisterStat(&d_statSlackVariables);
}


bool isBasicSum(TNode n){
  if(n.getKind() != kind::PLUS) return false;

  for(TNode::const_iterator i=n.begin(); i!=n.end(); ++i){
    TNode child = *i;
    if(child.getKind() != MULT) return false;
    if(child[0].getKind() != CONST_RATIONAL) return false;
    for(unsigned j=1; j<child.getNumChildren(); ++j){
      TNode var = child[j];
      if(var.getMetaKind() != metakind::VARIABLE) return false;
    }
  }
  return true;
}

bool isNormalAtom(TNode n){

  Comparison parse = Comparison::parseNormalForm(n);

  return parse.isNormalForm();
}


bool TheoryArith::shouldEject(ArithVar var){
  if(d_partialModel.hasEitherBound(var)){
    return false;
  }else if(d_tableau.isEjected(var)) {
    return false;
  }else if(!d_partialModel.hasEverHadABound(var)){
    return true;
  }else if(d_activityMonitor.getActivity(var) >= ActivityMonitor::ACTIVITY_THRESHOLD){
    return true;
  }
  return false;
}

ArithVar TheoryArith::findBasicRow(ArithVar variable){
  for(ArithVarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){
    ArithVar x_j = *basicIter;
    Row* row_j = d_tableau.lookup(x_j);

    if(row_j->has(variable)){
      return x_j;
    }
  }
  return ARITHVAR_SENTINEL;
}

void TheoryArith::ejectInactiveVariables(){
  Debug("decay") << "begin ejectInactiveVariables()" << endl;
  for(ArithVar variable = 0, end = d_variables.size(); variable != end; ++variable){
    //TNode var = *i;
    //ArithVar variable = asArithVar(var);
    if(shouldEject(variable)){
      if(d_basicManager.isBasic(variable)){
        Debug("decay") << "ejecting basic " << variable << endl;;
        d_tableau.ejectBasic(variable);
      }
    }
  }
}

void TheoryArith::reinjectVariable(ArithVar x){
  d_tableau.reinjectBasic(x);


  DeltaRational safeAssignment = computeRowValue(x, true);
  DeltaRational assignment = computeRowValue(x, false);
  d_partialModel.setAssignment(x,safeAssignment,assignment);
}

void TheoryArith::preRegisterTerm(TNode n) {
  Debug("arith_preregister") <<"begin arith::preRegisterTerm("<< n <<")"<< endl;
  Kind k = n.getKind();
  if(k == EQUAL){
    TNode left = n[0];
    TNode right = n[1];

    Node lt = NodeManager::currentNM()->mkNode(LT, left,right);
    Node gt = NodeManager::currentNM()->mkNode(GT, left,right);
    Node eagerSplit = NodeManager::currentNM()->mkNode(OR, n, lt, gt);

    d_splits.push_back(eagerSplit);


    d_out->augmentingLemma(eagerSplit);
  }

  bool isStrictlyVarList = n.getKind() == kind::MULT && VarList::isMember(n);

  if(isStrictlyVarList){
    d_out->setIncomplete();
  }

  if(isTheoryLeaf(n) || isStrictlyVarList){
    ArithVar varN = requestArithVar(n,false);
    setupInitialValue(varN);
  }


  //TODO is an atom
  if(isRelationOperator(k)){
    Assert(isNormalAtom(n));


    d_propagator.addAtom(n);

    TNode left  = n[0];
    TNode right = n[1];
    if(left.getKind() == PLUS){
      //We may need to introduce a slack variable.
      Assert(left.getNumChildren() >= 2);
      if(!left.hasAttribute(Slack())){
        setupSlack(left);
      }
    }
  }
  Debug("arith_preregister") << "end arith::preRegisterTerm("<< n <<")"<< endl;
}



void TheoryArith::checkBasicVariable(ArithVar basic){
  Assert(d_basicManager.isBasic(basic));
  if(!d_partialModel.assignmentIsConsistent(basic)){
    d_possiblyInconsistent.push(basic);
  }
}

bool TheoryArith::isTheoryLeaf(TNode x) const{
  return x.getMetaKind() == kind::metakind::VARIABLE;
}

ArithVar TheoryArith::requestArithVar(TNode x, bool basic){
  Assert(isTheoryLeaf(x));
  Assert(!hasArithVar(x));

  ArithVar varX = d_variables.size();
  d_variables.push_back(Node(x));

  setArithVar(x,varX);

  d_activityMonitor.initActivity(varX);
  d_basicManager.init(varX, basic);
  d_tableau.increaseSize();

  Debug("arith::arithvar") << x << " |-> " << varX << endl;

  return varX;
}

void TheoryArith::asVectors(Polynomial& p, std::vector<Rational>& coeffs, std::vector<ArithVar>& variables) const{
  for(Polynomial::iterator i = p.begin(), end = p.end(); i != end; ++i){
    const Monomial& mono = *i;
    const Constant& constant = mono.getConstant();
    const VarList& variable = mono.getVarList();

    Node n = variable.getNode();

    Assert(isTheoryLeaf(n));
    Assert(hasArithVar(n));

    ArithVar av = asArithVar(n);

    coeffs.push_back(constant.getValue());
    variables.push_back(av);
  }
}

void TheoryArith::setupSlack(TNode left){

  TypeNode real_type = NodeManager::currentNM()->realType();
  Node slack = NodeManager::currentNM()->mkVar(real_type);
  left.setAttribute(Slack(), slack);

  ArithVar varSlack = requestArithVar(slack, true);

  Polynomial polyLeft = Polynomial::parsePolynomial(left);

  vector<ArithVar> variables;
  vector<Rational> coefficients;

  asVectors(polyLeft, coefficients, variables);

  d_tableau.addRow(varSlack, coefficients, variables);

  setupInitialValue(varSlack);
}

/* Requirements:
 * For basic variables the row must have been added to the tableau.
 */
void TheoryArith::setupInitialValue(ArithVar x){

  if(!d_basicManager.isBasic(x)){
    d_partialModel.initialize(x,d_constants.d_ZERO_DELTA);
  }else{
    //If the variable is basic, assertions may have already happened and updates
    //may have occured before setting this variable up.

    //This can go away if the tableau creation is done at preregister
    //time instead of register
    DeltaRational safeAssignment = computeRowValue(x, true);
    DeltaRational assignment = computeRowValue(x, false);
    d_partialModel.initialize(x,safeAssignment);
    d_partialModel.setAssignment(x,assignment);

    checkBasicVariable(x);
    //Strictly speaking checking x is unnessecary as it cannot have an upper or
    //lower bound. This is done to strongly enforce the notion that basic
    //variables should not be changed without begin checked.

  }
  Debug("arithgc") << "setupVariable("<<x<<")"<<std::endl;
};

/**
 * Computes the value of a basic variable using the current assignment.
 */
DeltaRational TheoryArith::computeRowValue(ArithVar x, bool useSafe){
  Assert(d_basicManager.isBasic(x));
  DeltaRational sum = d_constants.d_ZERO_DELTA;

  Row* row = d_tableau.lookup(x);
  for(Row::iterator i = row->begin(); i != row->end();++i){
    ArithVar nonbasic = i->first;
    const Rational& coeff = i->second;

    const DeltaRational& assignment = d_partialModel.getAssignment(nonbasic, useSafe);
    sum = sum + (assignment * coeff);
  }
  return sum;
}


RewriteResponse TheoryArith::preRewrite(TNode n, bool topLevel) {
  return d_nextRewriter.preRewrite(n);
}

void TheoryArith::registerTerm(TNode tn){
  Debug("arith") << "registerTerm(" << tn << ")" << endl;
}

/* procedure AssertUpper( x_i <= c_i) */
bool TheoryArith::AssertUpper(ArithVar x_i, const DeltaRational& c_i, TNode original){

  Debug("arith") << "AssertUpper(" << x_i << " " << c_i << ")"<< std::endl;
  if(d_basicManager.isBasic(x_i) && d_tableau.isEjected(x_i)){
    reinjectVariable(x_i);
  }

  if(d_partialModel.aboveUpperBound(x_i, c_i, false) ){ // \upperbound(x_i) <= c_i
    return false; //sat
  }
  if(d_partialModel.belowLowerBound(x_i, c_i, true)){// \lowerbound(x_i) > c_i
    Node lbc = d_partialModel.getLowerConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, lbc, original);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
    ++(d_statistics.d_statAssertUpperConflicts);
    d_out->conflict(conflict);
    return true;
  }

  d_partialModel.setUpperConstraint(x_i,original);
  d_partialModel.setUpperBound(x_i, c_i);

  d_activityMonitor.resetActivity(x_i);

  if(!d_basicManager.isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) > c_i){
      update(x_i, c_i);
    }
  }else{
    checkBasicVariable(x_i);
  }
  d_partialModel.printModel(x_i);
  return false;
}

/* procedure AssertLower( x_i >= c_i ) */
bool TheoryArith::AssertLower(ArithVar x_i, const DeltaRational& c_i, TNode original){
  Debug("arith") << "AssertLower(" << x_i << " " << c_i << ")"<< std::endl;

  if(d_basicManager.isBasic(x_i) && d_tableau.isEjected(x_i)){
    reinjectVariable(x_i);
  }

  if(d_partialModel.belowLowerBound(x_i, c_i, false)){
    return false; //sat
  }
  if(d_partialModel.aboveUpperBound(x_i, c_i, true)){
    Node ubc = d_partialModel.getUpperConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, ubc, original);
    d_out->conflict(conflict);
    Debug("arith") << "AssertLower conflict " << conflict << endl;
    ++(d_statistics.d_statAssertLowerConflicts);
    return true;
  }

  d_partialModel.setLowerConstraint(x_i,original);
  d_partialModel.setLowerBound(x_i, c_i);
  d_activityMonitor.resetActivity(x_i);

  if(!d_basicManager.isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) < c_i){
      update(x_i, c_i);
    }
  }else{
    checkBasicVariable(x_i);
  }

  return false;
}

/* procedure AssertLower( x_i == c_i ) */
bool TheoryArith::AssertEquality(ArithVar x_i, const DeltaRational& c_i, TNode original){

  Debug("arith") << "AssertEquality(" << x_i << " " << c_i << ")"<< std::endl;

  if(d_basicManager.isBasic(x_i) && d_tableau.isEjected(x_i)){
    reinjectVariable(x_i);
  }

  // u_i <= c_i <= l_i
  // This can happen if both c_i <= x_i and x_i <= c_i are in the system.
  if(d_partialModel.belowLowerBound(x_i, c_i, false) &&
     d_partialModel.aboveUpperBound(x_i, c_i, false)){
    return false; //sat
  }

  if(d_partialModel.aboveUpperBound(x_i, c_i, true)){
    Node ubc = d_partialModel.getUpperConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, ubc, original);
    d_out->conflict(conflict);
    Debug("arith") << "AssertLower conflict " << conflict << endl;
    return true;
  }

  if(d_partialModel.belowLowerBound(x_i, c_i, true)){
    Node lbc = d_partialModel.getLowerConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, lbc, original);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
    d_out->conflict(conflict);
    return true;
  }

  d_partialModel.setLowerConstraint(x_i,original);
  d_partialModel.setLowerBound(x_i, c_i);

  d_partialModel.setUpperConstraint(x_i,original);
  d_partialModel.setUpperBound(x_i, c_i);
  d_activityMonitor.resetActivity(x_i);

  if(!d_basicManager.isBasic(x_i)){
    if(!(d_partialModel.getAssignment(x_i) == c_i)){
      update(x_i, c_i);
    }
  }else{
    checkBasicVariable(x_i);
  }

  return false;
}
void TheoryArith::update(ArithVar x_i, const DeltaRational& v){
  Assert(!d_basicManager.isBasic(x_i));
  DeltaRational assignment_x_i = d_partialModel.getAssignment(x_i);
  ++(d_statistics.d_statUpdates);

  Debug("arith") <<"update " << x_i << ": "
                 << assignment_x_i << "|-> " << v << endl;
  DeltaRational diff = v - assignment_x_i;

  for(ArithVarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){
    ArithVar x_j = *basicIter;
    Row* row_j = d_tableau.lookup(x_j);

    if(row_j->has(x_i)){
      const Rational& a_ji = row_j->lookup(x_i);

      const DeltaRational& assignment = d_partialModel.getAssignment(x_j);
      DeltaRational  nAssignment = assignment+(diff * a_ji);
      d_partialModel.setAssignment(x_j, nAssignment);

      d_activityMonitor.increaseActivity(x_j, 1);

      checkBasicVariable(x_j);
    }
  }

  d_partialModel.setAssignment(x_i, v);

  if(Debug.isOn("paranoid:check_tableau")){
    checkTableau();
  }
}

void TheoryArith::pivotAndUpdate(ArithVar x_i, ArithVar x_j, DeltaRational& v){
  Assert(x_i != x_j);

  Row* row_i = d_tableau.lookup(x_i);
  const Rational& a_ij = row_i->lookup(x_j);


  const DeltaRational& betaX_i = d_partialModel.getAssignment(x_i);

  Rational inv_aij = a_ij.inverse();
  DeltaRational theta = (v - betaX_i)*inv_aij;

  d_partialModel.setAssignment(x_i, v);


  DeltaRational tmp = d_partialModel.getAssignment(x_j) + theta;
  d_partialModel.setAssignment(x_j, tmp);

  for(ArithVarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){
    ArithVar x_k = *basicIter;
    Row* row_k = d_tableau.lookup(x_k);

    if(x_k != x_i && row_k->has(x_j)){
      const Rational& a_kj = row_k->lookup(x_j);
      DeltaRational nextAssignment = d_partialModel.getAssignment(x_k) + (theta * a_kj);
      d_partialModel.setAssignment(x_k, nextAssignment);

      d_activityMonitor.increaseActivity(x_j, 1);

      checkBasicVariable(x_k);
    }
  }

  ++(d_statistics.d_statPivots);
  d_tableau.pivot(x_i, x_j);

  checkBasicVariable(x_j);

  if(Debug.isOn("tableau")){
    d_tableau.printTableau();
  }
}

ArithVar TheoryArith::selectSmallestInconsistentVar(){
  Debug("arith_update") << "selectSmallestInconsistentVar()" << endl;
  Debug("arith_update") << "possiblyInconsistent.size()"
                        << d_possiblyInconsistent.size() << endl;

  while(!d_possiblyInconsistent.empty()){
    ArithVar var = d_possiblyInconsistent.top();
    Debug("arith_update") << "possiblyInconsistent var" << var << endl;
    if(d_basicManager.isBasic(var)){
      if(!d_partialModel.assignmentIsConsistent(var)){
        return var;
      }
    }
    d_possiblyInconsistent.pop();
  }

  if(Debug.isOn("paranoid:variables")){
    for(ArithVarSet::iterator basicIter = d_tableau.begin();
        basicIter != d_tableau.end();
        ++basicIter){

      ArithVar basic = *basicIter;
      Assert(d_partialModel.assignmentIsConsistent(basic));
      if(!d_partialModel.assignmentIsConsistent(basic)){
        return basic;
      }
    }
  }

  return ARITHVAR_SENTINEL;
}

template <bool above>
ArithVar TheoryArith::selectSlack(ArithVar x_i){
   Row* row_i = d_tableau.lookup(x_i);

  for(Row::iterator nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    ArithVar nonbasic = nbi->first;
    const Rational& a_ij = nbi->second;
    int cmp = a_ij.cmp(d_constants.d_ZERO);
    if(above){ // beta(x_i) > u_i
      if( cmp < 0 && d_partialModel.strictlyBelowUpperBound(nonbasic)){
        return nonbasic;
      }else if( cmp > 0 && d_partialModel.strictlyAboveLowerBound(nonbasic)){
        return nonbasic;
      }
    }else{ //beta(x_i) < l_i
      if(cmp > 0 && d_partialModel.strictlyBelowUpperBound(nonbasic)){
        return nonbasic;
      }else if(cmp < 0 && d_partialModel.strictlyAboveLowerBound(nonbasic)){
        return nonbasic;
      }
    }
  }
  return ARITHVAR_SENTINEL;
}


Node TheoryArith::updateInconsistentVars(){ //corresponds to Check() in dM06
  Debug("arith") << "updateInconsistentVars" << endl;

  static int iteratationNum = 0;
  static const int EJECT_FREQUENCY = 10;
  while(true){
    if(Debug.isOn("paranoid:check_tableau")){ checkTableau(); }

    ArithVar x_i = selectSmallestInconsistentVar();
    Debug("arith_update") << "selectSmallestInconsistentVar()=" << x_i << endl;
    if(x_i == ARITHVAR_SENTINEL){
      Debug("arith_update") << "No inconsistent variables" << endl;
      return Node::null(); //sat
    }

    ++iteratationNum;
    if(iteratationNum % EJECT_FREQUENCY == 0)
      ejectInactiveVariables();

    DeltaRational beta_i = d_partialModel.getAssignment(x_i);

    if(d_partialModel.belowLowerBound(x_i, beta_i, true)){
      DeltaRational l_i = d_partialModel.getLowerBound(x_i);
      ArithVar x_j = selectSlackBelow(x_i);
      if(x_j == ARITHVAR_SENTINEL ){
        ++(d_statistics.d_statUpdateConflicts);
        return generateConflictBelow(x_i); //unsat
      }
      pivotAndUpdate(x_i, x_j, l_i);

    }else if(d_partialModel.aboveUpperBound(x_i, beta_i, true)){
      DeltaRational u_i = d_partialModel.getUpperBound(x_i);
      ArithVar x_j = selectSlackAbove(x_i);
      if(x_j == ARITHVAR_SENTINEL ){
        ++(d_statistics.d_statUpdateConflicts);
        return generateConflictAbove(x_i); //unsat
      }
      pivotAndUpdate(x_i, x_j, u_i);
    }
  }
}

Node TheoryArith::generateConflictAbove(ArithVar conflictVar){

  Row* row_i = d_tableau.lookup(conflictVar);

  NodeBuilder<> nb(kind::AND);
  TNode bound = d_partialModel.getUpperConstraint(conflictVar);

  Debug("arith")  << "generateConflictAbove "
                  << "conflictVar " << conflictVar
                  << " " << d_partialModel.getAssignment(conflictVar)
                  << " " << bound << endl;

  nb << bound;

  for(Row::iterator nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    ArithVar nonbasic = nbi->first;
    const Rational& a_ij = nbi->second;

    Assert(a_ij != d_constants.d_ZERO);

    if(a_ij < d_constants.d_ZERO){
      bound =  d_partialModel.getUpperConstraint(nonbasic);
      Debug("arith") << "below 0 " << nonbasic << " "
                     << d_partialModel.getAssignment(nonbasic)
                     << " " << bound << endl;
      nb << bound;
    }else{
      bound =  d_partialModel.getLowerConstraint(nonbasic);
      Debug("arith") << " above 0 " << nonbasic << " "
                     << d_partialModel.getAssignment(nonbasic)
                     << " " << bound << endl;
      nb << bound;
    }
  }
  Node conflict = nb;
  return conflict;
}

Node TheoryArith::generateConflictBelow(ArithVar conflictVar){
  Row* row_i = d_tableau.lookup(conflictVar);

  NodeBuilder<> nb(kind::AND);
  TNode bound = d_partialModel.getLowerConstraint(conflictVar);

  Debug("arith") << "generateConflictBelow "
                 << "conflictVar " << conflictVar
                 << d_partialModel.getAssignment(conflictVar) << " "
                 << " " << bound << endl;
  nb << bound;

  for(Row::iterator nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    ArithVar nonbasic = nbi->first;
    const Rational& a_ij = nbi->second;

    Assert(a_ij != d_constants.d_ZERO);

    if(a_ij < d_constants.d_ZERO){
      TNode bound = d_partialModel.getLowerConstraint(nonbasic);
      Debug("arith") << "Lower "<< nonbasic << " "
                     << d_partialModel.getAssignment(nonbasic) << " "
                     << bound << endl;

      nb << bound;
    }else{
      TNode bound = d_partialModel.getUpperConstraint(nonbasic);
      Debug("arith") << "Upper "<< nonbasic << " "
                     << d_partialModel.getAssignment(nonbasic) << " "
                     << bound << endl;

      nb << bound;
    }
  }
  Node conflict (nb.constructNode());
  return conflict;
}

template <bool selectLeft>
TNode getSide(TNode assertion, Kind simpleKind){
  switch(simpleKind){
  case LT:
  case GT:
  case DISTINCT:
    return selectLeft ? (assertion[0])[0] : (assertion[0])[1];
  case LEQ:
  case GEQ:
  case EQUAL:
    return selectLeft ? assertion[0] : assertion[1];
  default:
    Unreachable();
    return TNode::null();
  }
}

ArithVar TheoryArith::determineLeftVariable(TNode assertion, Kind simpleKind){
  TNode left = getSide<true>(assertion, simpleKind);

  if(isTheoryLeaf(left)){
    return asArithVar(left);
  }else{
    Assert(left.hasAttribute(Slack()));
    TNode slack = left.getAttribute(Slack());
    return asArithVar(slack);
  }
}

DeltaRational determineRightConstant(TNode assertion, Kind simpleKind){
  TNode right = getSide<false>(assertion, simpleKind);

  Assert(right.getKind() == CONST_RATIONAL);
  const Rational& noninf = right.getConst<Rational>();

  Rational inf = Rational(Integer(deltaCoeff(simpleKind)));
  return DeltaRational(noninf, inf);
}

bool TheoryArith::assertionCases(TNode assertion){
  Kind simpKind = simplifiedKind(assertion);
  Assert(simpKind != UNDEFINED_KIND);
  ArithVar x_i = determineLeftVariable(assertion, simpKind);
  DeltaRational c_i = determineRightConstant(assertion, simpKind);

  Debug("arith_assertions") << "arith assertion(" << assertion
                            << " \\-> "
                            <<x_i<<" "<< simpKind <<" "<< c_i << ")" << std::endl;
  switch(simpKind){
  case LEQ:
  case LT:
    return AssertUpper(x_i, c_i, assertion);
  case GT:
  case GEQ:
    return AssertLower(x_i, c_i, assertion);
  case EQUAL:
    return AssertEquality(x_i, c_i, assertion);
  case DISTINCT:
    d_diseq.push_back(assertion);
    return false;
  default:
    Unreachable();
    return false;
  }
}

void TheoryArith::check(Effort level){
  Debug("arith") << "TheoryArith::check begun" << std::endl;

  while(!done()){

    Node assertion = get();

    d_propagator.assertLiteral(assertion);
    bool conflictDuringAnAssert = assertionCases(assertion);

    if(conflictDuringAnAssert){
      d_partialModel.revertAssignmentChanges();
      return;
    }
  }

  //TODO This must be done everytime for the time being
  if(Debug.isOn("paranoid:check_tableau")){ checkTableau(); }

  Node possibleConflict = updateInconsistentVars();
  if(possibleConflict != Node::null()){

    d_partialModel.revertAssignmentChanges();

    if(Debug.isOn("arith::print-conflict"))
      Debug("arith_conflict") << (possibleConflict) << std::endl;

    d_out->conflict(possibleConflict);

    Debug("arith_conflict") <<"Found a conflict "<< possibleConflict << endl;
  }else{
    d_partialModel.commitAssignmentChanges();
  }
  if(Debug.isOn("paranoid:check_tableau")){ checkTableau(); }


  Debug("arith") << "TheoryArith::check end" << std::endl;

  if(Debug.isOn("arith::print_model")) {
    Debug("arith::print_model") << "Model:" << endl;

    for (ArithVar i = 0; i < d_variables.size(); ++ i) {
      Debug("arith::print_model") << d_variables[i] << " : " <<
        d_partialModel.getAssignment(i);
      if(d_basicManager.isBasic(i))
        Debug("arith::print_model") << " (basic)";
      Debug("arith::print_model") << endl;
    }
  }
  if(Debug.isOn("arith::print_assertions")) {
    Debug("arith::print_assertions") << "Assertions:" << endl;
    for (ArithVar i = 0; i < d_variables.size(); ++ i) {
      Node lConstr = d_partialModel.getLowerConstraint(i);
      Debug("arith::print_assertions") << lConstr.toString() << endl;

      Node uConstr = d_partialModel.getUpperConstraint(i);
      Debug("arith::print_assertions") << uConstr.toString() << endl;

    }
  }
}

/**
 * This check is quite expensive.
 * It should be wrapped in a Debug.isOn() guard.
 *   if(Debug.isOn("paranoid:check_tableau")){
 *      checkTableau();
 *   }
 */
void TheoryArith::checkTableau(){

  for(ArithVarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end(); ++basicIter){
    ArithVar basic = *basicIter;
    Row* row_k = d_tableau.lookup(basic);
    DeltaRational sum;
    Debug("paranoid:check_tableau") << "starting row" << basic << endl;
    for(Row::iterator nonbasicIter = row_k->begin();
        nonbasicIter != row_k->end();
        ++nonbasicIter){
      ArithVar nonbasic = nonbasicIter->first;
      const Rational& coeff = nonbasicIter->second;
      DeltaRational beta = d_partialModel.getAssignment(nonbasic);
      Debug("paranoid:check_tableau") << nonbasic << beta << coeff<<endl;
      sum = sum + (beta*coeff);
    }
    DeltaRational shouldBe = d_partialModel.getAssignment(basic);
    Debug("paranoid:check_tableau") << "ending row" << sum
                                    << "," << shouldBe << endl;

    Assert(sum == shouldBe);
  }
}


void TheoryArith::explain(TNode n, Effort e) {
  Node explanation = d_propagator.explain(n);
  Debug("arith") << "arith::explain("<<explanation<<")->"
                 << explanation << endl;
  d_out->explanation(explanation, true);
}

void TheoryArith::propagate(Effort e) {

  if(quickCheckOrMore(e)){
    std::vector<Node> implied = d_propagator.getImpliedLiterals();
    for(std::vector<Node>::iterator i = implied.begin();
        i != implied.end();
        ++i){
      d_out->propagate(*i);
    }
  }
}

Node TheoryArith::getValue(TNode n, TheoryEngine* engine) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {
  case kind::VARIABLE: {
    ArithVar var = asArithVar(n);
    if(d_tableau.isEjected(var)){
      reinjectVariable(var);
    }

    DeltaRational drat = d_partialModel.getAssignment(var);
    const Rational& delta = d_partialModel.getDelta();
    Debug("getValue") << n << " " << drat << " " << delta << endl;
    return nodeManager->
      mkConst( drat.getNoninfinitesimalPart() +
               drat.getInfinitesimalPart() * delta );
  }

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( engine->getValue(n[0]) == engine->getValue(n[1]) );

  case kind::PLUS: { // 2+ args
    Rational value = d_constants.d_ZERO;
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      value += engine->getValue(*i).getConst<Rational>();
    }
    return nodeManager->mkConst(value);
  }

  case kind::MULT: { // 2+ args
    Rational value = d_constants.d_ONE;
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      value *= engine->getValue(*i).getConst<Rational>();
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
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<Rational>() /
                                 engine->getValue(n[1]).getConst<Rational>() );

  case kind::LT: // 2 args
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<Rational>() <
                                 engine->getValue(n[1]).getConst<Rational>() );

  case kind::LEQ: // 2 args
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<Rational>() <=
                                 engine->getValue(n[1]).getConst<Rational>() );

  case kind::GT: // 2 args
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<Rational>() >
                                 engine->getValue(n[1]).getConst<Rational>() );

  case kind::GEQ: // 2 args
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<Rational>() >=
                                 engine->getValue(n[1]).getConst<Rational>() );

  default:
    Unhandled(n.getKind());
  }
}

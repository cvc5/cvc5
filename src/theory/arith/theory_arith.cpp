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
  d_diseq(c),
  d_nextRewriter(&d_constants),
  d_propagator(c),
  d_statistics()
{
  uint64_t ass_id = partial_model::Assignment::getId();
  Debug("arithsetup") << "Assignment: " << ass_id << std::endl;
}
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
  d_statUpdateConflicts("theory::arith::UpdateConflicts", 0)
{
  StatisticsRegistry::registerStat(&d_statPivots);
  StatisticsRegistry::registerStat(&d_statUpdates);
  StatisticsRegistry::registerStat(&d_statAssertUpperConflicts);
  StatisticsRegistry::registerStat(&d_statAssertLowerConflicts);
  StatisticsRegistry::registerStat(&d_statUpdateConflicts);
}

TheoryArith::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statPivots);
  StatisticsRegistry::unregisterStat(&d_statUpdates);
  StatisticsRegistry::unregisterStat(&d_statAssertUpperConflicts);
  StatisticsRegistry::unregisterStat(&d_statAssertLowerConflicts);
  StatisticsRegistry::unregisterStat(&d_statUpdateConflicts);
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


bool TheoryArith::shouldEject(TNode var){
  if(d_partialModel.hasBounds(var)){
    return false;
  }else if(d_tableau.isEjected(var)) {
    return false;
  }else if(!d_partialModel.hasEverHadABound(var)){
    return true;
  }else if(getActivity(var) >= ACTIVITY_THRESHOLD){
    return true;
  }
  return false;
}

TNode TheoryArith::findBasicRow(TNode variable){
  for(Tableau::VarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){
    TNode x_j = *basicIter;
    Row* row_j = d_tableau.lookup(x_j);

    if(row_j->has(variable)){
      return x_j;
    }
  }
  return TNode::null();
}

void TheoryArith::ejectInactiveVariables(){
  Debug("decay") << "begin ejectInactiveVariables()" << endl;
  for(std::vector<Node>::iterator i = d_variables.begin(),
        end = d_variables.end(); i != end; ++i){
    TNode variable = *i;
    if(shouldEject(variable)){
      if(isBasic(variable)){
        Debug("decay") << "ejecting basic " << variable << endl;;
        d_tableau.ejectBasic(variable);
      }
    }
  }
}

void TheoryArith::reinjectVariable(TNode x){
  d_tableau.reinjectBasic(x);


  DeltaRational safeAssignment = computeRowValueUsingSavedAssignment(x);
  DeltaRational assignment = computeRowValueUsingAssignment(x);
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

  if(n.getMetaKind() == metakind::VARIABLE){

    setupVariable(n);
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

void TheoryArith::setupSlack(TNode left){
  TypeNode real_type = NodeManager::currentNM()->realType();
  Node slack = NodeManager::currentNM()->mkVar(real_type);

  left.setAttribute(Slack(), slack);
  makeBasic(slack);

  Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, slack, left);

  d_tableau.addRow(eq);

  setupVariable(slack);
}


void TheoryArith::checkBasicVariable(TNode basic){
  Assert(isBasic(basic));
  if(!d_partialModel.assignmentIsConsistent(basic)){
    d_possiblyInconsistent.push(basic);
  }
}

/* Requirements:
 * For basic variables the row must have been added to the tableau.
 */
void TheoryArith::setupVariable(TNode x){
  Assert(x.getMetaKind() == kind::metakind::VARIABLE);
  d_variables.push_back(Node(x));

  initActivity(x);

  if(!isBasic(x)){
    d_partialModel.initialize(x,d_constants.d_ZERO_DELTA);
  }else{
    //If the variable is basic, assertions may have already happened and updates
    //may have occured before setting this variable up.

    //This can go away if the tableau creation is done at preregister
    //time instead of register
    DeltaRational safeAssignment = computeRowValueUsingSavedAssignment(x);
    DeltaRational assignment = computeRowValueUsingAssignment(x);
    d_partialModel.initialize(x,safeAssignment);
    d_partialModel.setAssignment(x,assignment);

    checkBasicVariable(x);
    //Strictly speaking checking x is unnessecary as it cannot have an upper or
    //lower bound. This is done to strongly enforce the notion that basic
    //variables should not be changed without begin checked.

    //Strictly speaking checking x is unnessecary as it cannot have an upper or
    //lower bound. This is done to strongly enforce the notion that basic
    //variables should not be changed without begin checked.

  }
  Debug("arithgc") << "setupVariable("<<x<<")"<<std::endl;
};

/**
 * Computes the value of a basic variable using the current assignment.
 */
DeltaRational TheoryArith::computeRowValueUsingAssignment(TNode x){
  Assert(isBasic(x));
  DeltaRational sum = d_constants.d_ZERO_DELTA;

  Row* row = d_tableau.lookup(x);
  for(Row::iterator i = row->begin(); i != row->end();++i){
    TNode nonbasic = i->first;
    const Rational& coeff = i->second;
    const DeltaRational& assignment = d_partialModel.getAssignment(nonbasic);
    sum = sum + (assignment * coeff);
  }
  return sum;
}

/**
 * Computes the value of a basic variable using the current assignment.
 */
DeltaRational TheoryArith::computeRowValueUsingSavedAssignment(TNode x){
  Assert(isBasic(x));
  DeltaRational sum = d_constants.d_ZERO_DELTA;

  Row* row = d_tableau.lookup(x);
  for(Row::iterator i = row->begin(); i != row->end();++i){
    TNode nonbasic = i->first;
    const Rational& coeff = i->second;
    const DeltaRational& assignment = d_partialModel.getSafeAssignment(nonbasic);
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
bool TheoryArith::AssertUpper(TNode n, TNode original){
  TNode x_i = n[0];
  Rational dcoeff = Rational(Integer(deltaCoeff(n.getKind())));
  DeltaRational c_i(n[1].getConst<Rational>(), dcoeff);


  Debug("arith") << "AssertUpper(" << x_i << " " << c_i << ")"<< std::endl;
  if(isBasic(x_i) && d_tableau.isEjected(x_i)){
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

  resetActivity(x_i);

  if(!isBasic(x_i)){
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
bool TheoryArith::AssertLower(TNode n, TNode original){
  TNode x_i = n[0];
  Rational dcoeff = Rational(Integer(deltaCoeff(n.getKind())));
  DeltaRational c_i(n[1].getConst<Rational>(),dcoeff);

  Debug("arith") << "AssertLower(" << x_i << " " << c_i << ")"<< std::endl;

  if(isBasic(x_i) && d_tableau.isEjected(x_i)){
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
  resetActivity(x_i);

  if(!isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) < c_i){
      update(x_i, c_i);
    }
  }else{
    checkBasicVariable(x_i);
  }

  return false;
}

/* procedure AssertLower( x_i == c_i ) */
bool TheoryArith::AssertEquality(TNode n, TNode original){
  Assert(n.getKind() == EQUAL);
  TNode x_i = n[0];
  DeltaRational c_i(n[1].getConst<Rational>());

  Debug("arith") << "AssertEquality(" << x_i << " " << c_i << ")"<< std::endl;

  if(isBasic(x_i) && d_tableau.isEjected(x_i)){
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
  resetActivity(x_i);

  if(!isBasic(x_i)){
    if(!(d_partialModel.getAssignment(x_i) == c_i)){
      update(x_i, c_i);
    }
  }else{
    checkBasicVariable(x_i);
  }

  return false;
}
void TheoryArith::update(TNode x_i, DeltaRational& v){
  Assert(!isBasic(x_i));
  DeltaRational assignment_x_i = d_partialModel.getAssignment(x_i);
  ++(d_statistics.d_statUpdates);

  Debug("arith") <<"update " << x_i << ": "
                 << assignment_x_i << "|-> " << v << endl;
  DeltaRational diff = v - assignment_x_i;

  for(Tableau::VarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){
    TNode x_j = *basicIter;
    Row* row_j = d_tableau.lookup(x_j);

    if(row_j->has(x_i)){
      const Rational& a_ji = row_j->lookup(x_i);

      const DeltaRational& assignment = d_partialModel.getAssignment(x_j);
      DeltaRational  nAssignment = assignment+(diff * a_ji);
      d_partialModel.setAssignment(x_j, nAssignment);

      increaseActivity(x_j, 1);

      checkBasicVariable(x_j);
    }
  }

  d_partialModel.setAssignment(x_i, v);

  if(Debug.isOn("paranoid:check_tableau")){
    checkTableau();
  }
}

void TheoryArith::pivotAndUpdate(TNode x_i, TNode x_j, DeltaRational& v){
  Assert(x_i != x_j);

  Row* row_i = d_tableau.lookup(x_i);
  const Rational& a_ij = row_i->lookup(x_j);


  const DeltaRational& betaX_i = d_partialModel.getAssignment(x_i);

  Rational inv_aij = a_ij.inverse();
  DeltaRational theta = (v - betaX_i)*inv_aij;

  d_partialModel.setAssignment(x_i, v);


  DeltaRational tmp = d_partialModel.getAssignment(x_j) + theta;
  d_partialModel.setAssignment(x_j, tmp);

  for(Tableau::VarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){
    TNode x_k = *basicIter;
    Row* row_k = d_tableau.lookup(x_k);

    if(x_k != x_i && row_k->has(x_j)){
      const Rational& a_kj = row_k->lookup(x_j);
      DeltaRational nextAssignment = d_partialModel.getAssignment(x_k) + (theta * a_kj);
      d_partialModel.setAssignment(x_k, nextAssignment);

      increaseActivity(x_j, 1);

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

TNode TheoryArith::selectSmallestInconsistentVar(){
  Debug("arith_update") << "selectSmallestInconsistentVar()" << endl;
  Debug("arith_update") << "possiblyInconsistent.size()"
                        << d_possiblyInconsistent.size() << endl;

  while(!d_possiblyInconsistent.empty()){
    TNode var = d_possiblyInconsistent.top();
    Debug("arith_update") << "possiblyInconsistent var" << var << endl;
    if(isBasic(var)){
      if(!d_partialModel.assignmentIsConsistent(var)){
        return var;
      }
    }
    d_possiblyInconsistent.pop();
  }

  if(Debug.isOn("paranoid:variables")){
    for(Tableau::VarSet::iterator basicIter = d_tableau.begin();
        basicIter != d_tableau.end();
        ++basicIter){

      TNode basic = *basicIter;
      Assert(d_partialModel.assignmentIsConsistent(basic));
      if(!d_partialModel.assignmentIsConsistent(basic)){
        return basic;
      }
    }
  }

  return TNode::null();
}

template <bool above>
TNode TheoryArith::selectSlack(TNode x_i){
   Row* row_i = d_tableau.lookup(x_i);

  for(Row::iterator nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    TNode nonbasic = nbi->first;
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
  return TNode::null();
}


Node TheoryArith::updateInconsistentVars(){ //corresponds to Check() in dM06
  Debug("arith") << "updateInconsistentVars" << endl;

  static int iteratationNum = 0;
  static const int EJECT_FREQUENCY = 10;
  while(true){
    if(Debug.isOn("paranoid:check_tableau")){ checkTableau(); }

    TNode x_i = selectSmallestInconsistentVar();
    Debug("arith_update") << "selectSmallestInconsistentVar()=" << x_i << endl;
    if(x_i == Node::null()){
      Debug("arith_update") << "No inconsistent variables" << endl;
      return Node::null(); //sat
    }

    ++iteratationNum;
    if(iteratationNum % EJECT_FREQUENCY == 0)
      ejectInactiveVariables();

    DeltaRational beta_i = d_partialModel.getAssignment(x_i);

    if(d_partialModel.belowLowerBound(x_i, beta_i, true)){
      DeltaRational l_i = d_partialModel.getLowerBound(x_i);
      TNode x_j = selectSlackBelow(x_i);
      if(x_j == TNode::null() ){
        ++(d_statistics.d_statUpdateConflicts);
        return generateConflictBelow(x_i); //unsat
      }
      pivotAndUpdate(x_i, x_j, l_i);

    }else if(d_partialModel.aboveUpperBound(x_i, beta_i, true)){
      DeltaRational u_i = d_partialModel.getUpperBound(x_i);
      TNode x_j = selectSlackAbove(x_i);
      if(x_j == TNode::null() ){
        ++(d_statistics.d_statUpdateConflicts);
        return generateConflictAbove(x_i); //unsat
      }
      pivotAndUpdate(x_i, x_j, u_i);
    }
  }
}

Node TheoryArith::generateConflictAbove(TNode conflictVar){
  Row* row_i = d_tableau.lookup(conflictVar);

  NodeBuilder<> nb(kind::AND);
  TNode bound = d_partialModel.getUpperConstraint(conflictVar);

  Debug("arith")  << "generateConflictAbove "
                  << "conflictVar " << conflictVar
                  << " " << d_partialModel.getAssignment(conflictVar)
                  << " " << bound << endl;

  nb << bound;

  for(Row::iterator nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    TNode nonbasic = nbi->first;
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

Node TheoryArith::generateConflictBelow(TNode conflictVar){
  Row* row_i = d_tableau.lookup(conflictVar);

  NodeBuilder<> nb(kind::AND);
  TNode bound = d_partialModel.getLowerConstraint(conflictVar);

  Debug("arith") << "generateConflictBelow "
                 << "conflictVar " << conflictVar
                 << d_partialModel.getAssignment(conflictVar) << " "
                 << " " << bound << endl;
  nb << bound;

  for(Row::iterator nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    TNode nonbasic = nbi->first;
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


//TODO get rid of this!
Node TheoryArith::simulatePreprocessing(TNode n){
  if(n.getKind() == NOT){
    Node sub = simulatePreprocessing(n[0]);
    Assert(sub.getKind() != NOT);
    return NodeManager::currentNM()->mkNode(NOT,sub);

  }else{
    Assert(isNormalAtom(n));
    Kind k = n.getKind();

    Assert(isRelationOperator(k));
    if(n[0].getMetaKind() == metakind::VARIABLE){
      return n;
    }else {
      TNode left = n[0];
      TNode right = n[1];
      Assert(left.hasAttribute(Slack()));
      Node slack = left.getAttribute(Slack());
      return NodeManager::currentNM()->mkNode(k,slack,right);
    }
  }
}

bool TheoryArith::assertionCases(TNode original, TNode assertion){
  switch(assertion.getKind()){
  case LEQ:
    return AssertUpper(assertion, original);
  case GEQ:
    return AssertLower(assertion, original);
  case EQUAL:
    return AssertEquality(assertion,original);
  case NOT:
    {
      TNode atom = assertion[0];
      switch(atom.getKind()){
      case LEQ: //(not (LEQ x c)) <=> (GT x c)
        {
          Node pushedin = pushInNegation(assertion);
          return AssertLower(pushedin,original);
        }
      case GEQ: //(not (GEQ x c) <=> (LT x c)
        {
          Node pushedin = pushInNegation(assertion);
          return AssertUpper(pushedin,original);
        }
      case EQUAL:
        d_diseq.push_back(assertion);
        return false;
      default:
        Unreachable();
        return false;
      }
    }
  default:
    Unreachable();
    return false;
  }
}

void TheoryArith::check(Effort level){
  Debug("arith") << "TheoryArith::check begun" << std::endl;

  while(!done()){

    Node original = get();
    Node assertion = simulatePreprocessing(original);
    Debug("arith_assertions") << "arith assertion(" << original
                              << " \\-> " << assertion << ")" << std::endl;

    d_propagator.assertLiteral(original);
    bool conflictDuringAnAssert = assertionCases(original, assertion);


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

    for (unsigned i = 0; i < d_variables.size(); ++ i) {
      Debug("arith::print_model") << d_variables[i] << " : " <<
        d_partialModel.getAssignment(d_variables[i]);
      if(isBasic(d_variables[i]))
        Debug("arith::print_model") << " (basic)";
      Debug("arith::print_model") << endl;
    }
  }
  if(Debug.isOn("arith::print_assertions")) {
    Debug("arith::print_assertions") << "Assertions:" << endl;
    for (unsigned i = 0; i < d_variables.size(); ++ i) {
      Node x = d_variables[i];
      if (x.hasAttribute(partial_model::LowerConstraint())) {
        Node constr = d_partialModel.getLowerConstraint(x);
        Debug("arith::print_assertions") << constr.toString() << endl;
      }
      if (x.hasAttribute(partial_model::UpperConstraint())) {
        Node constr = d_partialModel.getUpperConstraint(x);
        Debug("arith::print_assertions") << constr.toString() << endl;
      }
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

  for(Tableau::VarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end(); ++basicIter){
    TNode basic = *basicIter;
    Row* row_k = d_tableau.lookup(basic);
    DeltaRational sum;
    Debug("paranoid:check_tableau") << "starting row" << basic << endl;
    for(Row::iterator nonbasicIter = row_k->begin();
        nonbasicIter != row_k->end();
        ++nonbasicIter){
      TNode nonbasic = nonbasicIter->first;
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

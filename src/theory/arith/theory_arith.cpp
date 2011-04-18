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

#include "theory/valuation.h"

#include "util/rational.h"
#include "util/integer.h"
#include "util/boolean_simplification.h"


#include "theory/rewriter.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/tableau.h"
#include "theory/arith/arithvar_set.h"

#include "theory/arith/arith_rewriter.h"
#include "theory/arith/unate_propagator.h"

#include "theory/arith/theory_arith.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/arith_prop_manager.h"

#include <stdint.h>

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;

static const uint32_t RESET_START = 2;

struct SlackAttrID;
typedef expr::Attribute<SlackAttrID, bool> Slack;

TheoryArith::TheoryArith(context::Context* c, OutputChannel& out, Valuation valuation) :
  Theory(THEORY_ARITH, c, out, valuation),
  d_partialModel(c),
  d_userVariables(),
  d_diseq(c),
  d_tableau(),
  d_restartsCounter(0),
  d_presolveHasBeenCalled(false),
  d_tableauResetDensity(1.6),
  d_tableauResetPeriod(10),
  d_propagator(c, out),
  d_propManager(c, d_arithvarNodeMap, d_propagator, valuation),
  d_simplex(d_propManager, d_partialModel, d_tableau),
  d_DELTA_ZERO(0),
  d_statistics()
{}

TheoryArith::~TheoryArith(){}

TheoryArith::Statistics::Statistics():
  d_statUserVariables("theory::arith::UserVariables", 0),
  d_statSlackVariables("theory::arith::SlackVariables", 0),
  d_statDisequalitySplits("theory::arith::DisequalitySplits", 0),
  d_statDisequalityConflicts("theory::arith::DisequalityConflicts", 0),
  d_staticLearningTimer("theory::arith::staticLearningTimer"),
  d_permanentlyRemovedVariables("theory::arith::permanentlyRemovedVariables", 0),
  d_presolveTime("theory::arith::presolveTime"),
  d_initialTableauSize("theory::arith::initialTableauSize", 0),
  //d_tableauSizeHistory("theory::arith::tableauSizeHistory"),
  d_currSetToSmaller("theory::arith::currSetToSmaller", 0),
  d_smallerSetToCurr("theory::arith::smallerSetToCurr", 0),
  d_restartTimer("theory::arith::restartTimer")
{
  StatisticsRegistry::registerStat(&d_statUserVariables);
  StatisticsRegistry::registerStat(&d_statSlackVariables);
  StatisticsRegistry::registerStat(&d_statDisequalitySplits);
  StatisticsRegistry::registerStat(&d_statDisequalityConflicts);
  StatisticsRegistry::registerStat(&d_staticLearningTimer);

  StatisticsRegistry::registerStat(&d_permanentlyRemovedVariables);
  StatisticsRegistry::registerStat(&d_presolveTime);


  StatisticsRegistry::registerStat(&d_initialTableauSize);
  //StatisticsRegistry::registerStat(&d_tableauSizeHistory);
  StatisticsRegistry::registerStat(&d_currSetToSmaller);
  StatisticsRegistry::registerStat(&d_smallerSetToCurr);
  StatisticsRegistry::registerStat(&d_restartTimer);
}

TheoryArith::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statUserVariables);
  StatisticsRegistry::unregisterStat(&d_statSlackVariables);
  StatisticsRegistry::unregisterStat(&d_statDisequalitySplits);
  StatisticsRegistry::unregisterStat(&d_statDisequalityConflicts);
  StatisticsRegistry::unregisterStat(&d_staticLearningTimer);

  StatisticsRegistry::unregisterStat(&d_permanentlyRemovedVariables);
  StatisticsRegistry::unregisterStat(&d_presolveTime);


  StatisticsRegistry::unregisterStat(&d_initialTableauSize);
  //StatisticsRegistry::unregisterStat(&d_tableauSizeHistory);
  StatisticsRegistry::unregisterStat(&d_currSetToSmaller);
  StatisticsRegistry::unregisterStat(&d_smallerSetToCurr);
  StatisticsRegistry::unregisterStat(&d_restartTimer);
}

void TheoryArith::staticLearning(TNode n, NodeBuilder<>& learned) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_staticLearningTimer);

  learner.staticLearning(n, learned);
}



ArithVar TheoryArith::findShortestBasicRow(ArithVar variable){
  ArithVar bestBasic = ARITHVAR_SENTINEL;
  uint64_t bestRowLength = std::numeric_limits<uint64_t>::max();

  Tableau::ColIterator basicIter = d_tableau.colIterator(variable);
  for(; !basicIter.atEnd(); ++basicIter){
    const TableauEntry& entry = *basicIter;
    Assert(entry.getColVar() == variable);
    ArithVar basic = entry.getRowVar();
    uint32_t rowLength = d_tableau.getRowLength(basic);
    if((rowLength < bestRowLength) ||
       (rowLength == bestRowLength && basic < bestBasic)){
      bestBasic = basic;
      bestRowLength = rowLength;
    }
  }
  Assert(bestBasic == ARITHVAR_SENTINEL || bestRowLength < std::numeric_limits<uint32_t>::max());
  return bestBasic;
}


void TheoryArith::preRegisterTerm(TNode n) {
  Debug("arith_preregister") <<"begin arith::preRegisterTerm("<< n <<")"<< endl;
  Kind k = n.getKind();

  bool isStrictlyVarList = k == kind::MULT && VarList::isMember(n);

  if(isStrictlyVarList){
    d_out->setIncomplete();
  }

  if(Variable::isMember(n) || isStrictlyVarList){
    ++(d_statistics.d_statUserVariables);
    ArithVar varN = requestArithVar(n,false);
    setupInitialValue(varN);
  }

  if(isRelationOperator(k)){
    Assert(Comparison::isNormalAtom(n));

    //cout << n << endl;

    d_propagator.addAtom(n);

    TNode left  = n[0];
    TNode right = n[1];
    if(left.getKind() == PLUS){
      //We may need to introduce a slack variable.
      Assert(left.getNumChildren() >= 2);
      if(!left.getAttribute(Slack())){
        setupSlack(left);
      }
    }
  }
  Debug("arith_preregister") << "end arith::preRegisterTerm("<< n <<")"<< endl;
}


ArithVar TheoryArith::requestArithVar(TNode x, bool basic){
  Assert(isLeaf(x) || x.getKind() == PLUS);
  Assert(!d_arithvarNodeMap.hasArithVar(x));

  ArithVar varX = d_variables.size();
  d_variables.push_back(Node(x));

  d_simplex.increaseMax();

  d_arithvarNodeMap.setArithVar(x,varX);

  d_userVariables.init(varX, !basic);
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

    Debug("rewriter") << "should be var: " << n << endl;

    Assert(isLeaf(n));
    Assert(d_arithvarNodeMap.hasArithVar(n));

    ArithVar av = d_arithvarNodeMap.asArithVar(n);

    coeffs.push_back(constant.getValue());
    variables.push_back(av);
  }
}

void TheoryArith::setupSlack(TNode left){
  Assert(!left.getAttribute(Slack()));

  ++(d_statistics.d_statSlackVariables);
  left.setAttribute(Slack(), true);

  ArithVar varSlack = requestArithVar(left, true);

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

  if(!d_tableau.isBasic(x)){
    d_partialModel.initialize(x, d_DELTA_ZERO);
  }else{
    //If the variable is basic, assertions may have already happened and updates
    //may have occured before setting this variable up.

    //This can go away if the tableau creation is done at preregister
    //time instead of register
    DeltaRational safeAssignment = d_simplex.computeRowValue(x, true);
    DeltaRational assignment = d_simplex.computeRowValue(x, false);
    d_partialModel.initialize(x,safeAssignment);
    d_partialModel.setAssignment(x,assignment);
  }
  Debug("arithgc") << "setupVariable("<<x<<")"<<std::endl;
};

void TheoryArith::registerTerm(TNode tn){
  Debug("arith") << "registerTerm(" << tn << ")" << endl;
}


ArithVar TheoryArith::determineLeftVariable(TNode assertion, Kind simpleKind){
  TNode left = getSide<true>(assertion, simpleKind);

  if(isLeaf(left)){
    return d_arithvarNodeMap.asArithVar(left);
  }else{
    Assert(left.hasAttribute(Slack()));
    return d_arithvarNodeMap.asArithVar(left);
  }
}


Node TheoryArith::disequalityConflict(TNode eq, TNode lb, TNode ub){
  NodeBuilder<3> conflict(kind::AND);
  conflict << eq << lb << ub;
  ++(d_statistics.d_statDisequalityConflicts);
  return conflict;
}

Node TheoryArith::assertionCases(TNode assertion){
  Kind simpKind = simplifiedKind(assertion);
  Assert(simpKind != UNDEFINED_KIND);
  ArithVar x_i = determineLeftVariable(assertion, simpKind);
  DeltaRational c_i = determineRightConstant(assertion, simpKind);

  Debug("arith_assertions") << "arith assertion(" << assertion
                            << " \\-> "
                            <<x_i<<" "<< simpKind <<" "<< c_i << ")" << std::endl;
  switch(simpKind){
  case LEQ:
    if (d_partialModel.hasLowerBound(x_i) && d_partialModel.getLowerBound(x_i) == c_i) {
      Node diseq = assertion[0].eqNode(assertion[1]).notNode();
      if (d_diseq.find(diseq) != d_diseq.end()) {
        Node lb = d_partialModel.getLowerConstraint(x_i);
        return disequalityConflict(diseq, lb , assertion);
      }
    }
  case LT:
    return  d_simplex.AssertUpper(x_i, c_i, assertion);
  case GEQ:
    if (d_partialModel.hasUpperBound(x_i) && d_partialModel.getUpperBound(x_i) == c_i) {
      Node diseq = assertion[0].eqNode(assertion[1]).notNode();
      if (d_diseq.find(diseq) != d_diseq.end()) {
        Node ub = d_partialModel.getUpperConstraint(x_i);
        return disequalityConflict(diseq, assertion, ub);
      }
    }
  case GT:
    return d_simplex.AssertLower(x_i, c_i, assertion);
  case EQUAL:
    return d_simplex.AssertEquality(x_i, c_i, assertion);
  case DISTINCT:
    {
      d_diseq.insert(assertion);
      // Check if it conflicts with the the bounds
      TNode eq = assertion[0];
      Assert(eq.getKind() == kind::EQUAL);
      TNode lhs = eq[0];
      TNode rhs = eq[1];
      Assert(rhs.getKind() == CONST_RATIONAL);
      ArithVar lhsVar = determineLeftVariable(eq, kind::EQUAL);
      DeltaRational rhsValue = determineRightConstant(eq, kind::EQUAL);
      if (d_partialModel.hasLowerBound(lhsVar) &&
          d_partialModel.hasUpperBound(lhsVar) &&
          d_partialModel.getLowerBound(lhsVar) == rhsValue &&
          d_partialModel.getUpperBound(lhsVar) == rhsValue) {
        Node lb = d_partialModel.getLowerConstraint(lhsVar);
        Node ub = d_partialModel.getUpperConstraint(lhsVar);
        return disequalityConflict(assertion, lb, ub);
      }
    }
    return Node::null();
  default:
    Unreachable();
    return Node::null();
  }
}



void TheoryArith::check(Effort effortLevel){
  Debug("arith") << "TheoryArith::check begun" << std::endl;

  while(!done()){

    Node assertion = get();
    Node possibleConflict = assertionCases(assertion);

    if(!possibleConflict.isNull()){
      d_partialModel.revertAssignmentChanges();
      //Node simpleConflict  = BooleanSimplification::simplifyConflict(possibleConflict);

      Debug("arith::conflict") << "conflict   " << possibleConflict << endl;

      d_simplex.clearUpdates();
      d_out->conflict(possibleConflict);
      return;
    }
  }

  if(Debug.isOn("arith::print_assertions")) {
    debugPrintAssertions();
  }

  Node possibleConflict = d_simplex.updateInconsistentVars();
  if(possibleConflict != Node::null()){
    d_partialModel.revertAssignmentChanges();
    d_simplex.clearUpdates();

    //Node simpleConflict  = BooleanSimplification::simplifyConflict(possibleConflict);

    Debug("arith::conflict") << "conflict   " << possibleConflict << endl;

    d_out->conflict(possibleConflict);
  }else{
    d_partialModel.commitAssignmentChanges();

    if (fullEffort(effortLevel)) {
      splitDisequalities();
    }
  }

  if(Debug.isOn("paranoid:check_tableau")){ d_simplex.debugCheckTableau(); }
  if(Debug.isOn("arith::print_model")) { debugPrintModel(); }
  Debug("arith") << "TheoryArith::check end" << std::endl;
}

void TheoryArith::splitDisequalities(){
  context::CDSet<Node, NodeHashFunction>::iterator it = d_diseq.begin();
  context::CDSet<Node, NodeHashFunction>::iterator it_end = d_diseq.end();
  for(; it != it_end; ++ it) {
    TNode eq = (*it)[0];
    Assert(eq.getKind() == kind::EQUAL);
    TNode lhs = eq[0];
    TNode rhs = eq[1];
    Assert(rhs.getKind() == CONST_RATIONAL);
    ArithVar lhsVar = determineLeftVariable(eq, kind::EQUAL);
    DeltaRational lhsValue = d_partialModel.getAssignment(lhsVar);
    DeltaRational rhsValue = determineRightConstant(eq, kind::EQUAL);
    if (lhsValue == rhsValue) {
      Debug("arith_lemma") << "Splitting on " << eq << endl;
      Debug("arith_lemma") << "LHS value = " << lhsValue << endl;
      Debug("arith_lemma") << "RHS value = " << rhsValue << endl;
      Node ltNode = NodeBuilder<2>(kind::LT) << lhs << rhs;
      Node gtNode = NodeBuilder<2>(kind::GT) << lhs << rhs;
      Node lemma = NodeBuilder<3>(OR) << eq << ltNode << gtNode;

      // // < => !>
      // Node imp1 = NodeBuilder<2>(kind::IMPLIES) << ltNode << gtNode.notNode();
      // // < => !=
      // Node imp2 = NodeBuilder<2>(kind::IMPLIES) << ltNode << eq.notNode();
      // // > => !=
      // Node imp3 = NodeBuilder<2>(kind::IMPLIES) << gtNode << eq.notNode();
      // // All the implication
      // Node impClosure = NodeBuilder<3>(kind::AND) << imp1 << imp2 << imp3;

      ++(d_statistics.d_statDisequalitySplits);
      d_out->lemma(lemma);
    }
  }
}

/**
 * Should be guarded by at least Debug.isOn("arith::print_assertions").
 * Prints to Debug("arith::print_assertions")
 */
void TheoryArith::debugPrintAssertions() {
  Debug("arith::print_assertions") << "Assertions:" << endl;
  for (ArithVar i = 0; i < d_variables.size(); ++ i) {
    if (d_partialModel.hasLowerBound(i)) {
      Node lConstr = d_partialModel.getLowerConstraint(i);
      Debug("arith::print_assertions") << lConstr.toString() << endl;
    }

    if (d_partialModel.hasUpperBound(i)) {
      Node uConstr = d_partialModel.getUpperConstraint(i);
      Debug("arith::print_assertions") << uConstr.toString() << endl;
    }
  }
  context::CDSet<Node, NodeHashFunction>::iterator it = d_diseq.begin();
  context::CDSet<Node, NodeHashFunction>::iterator it_end = d_diseq.end();
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

/*
bool TheoryArith::isImpliedUpperBound(ArithVar var, Node exp){
  Node varAsNode = asNode(var);
  const DeltaRational& ub = d_partialModel.getUpperBound(var);
  Assert(ub.getInfinitesimalPart() <= 0 );
  Kind kind = ub.getInfinitesimalPart() < 0 ? LT : LEQ;
  Node ubAsNode = NodeBuilder<2>(kind) << varAsNode << mkRationalNode(ub.getNoninfinitesimalPart());
  Node bestImplied = d_propagator.getBestImpliedUpperBound(ubAsNode);

  return bestImplied == exp;
}

bool TheoryArith::isImpliedLowerBound(ArithVar var, Node exp){
  Node varAsNode = asNode(var);
  const DeltaRational& lb = d_partialModel.getLowerBound(var);
  Assert(lb.getInfinitesimalPart() >= 0 );
  Kind kind = lb.getInfinitesimalPart() > 0 ? GT : GEQ;
  Node lbAsIneq = NodeBuilder<2>(kind) << varAsNode << mkRationalNode(lb.getNoninfinitesimalPart());
  Node bestImplied = d_propagator.getBestImpliedLowerBound(lbAsIneq);
  return bestImplied == exp;
}
*/

void TheoryArith::explain(TNode n) {
  Debug("explain") << "explain @" << getContext()->getLevel() << ": " << n << endl;
  //Assert(n.hasAttribute(Propagated()));

  //NodeBuilder<> explainBuilder(AND);
  //internalExplain(n,explainBuilder);
  Assert(d_propManager.isPropagated(n));
  Node explanation = d_propManager.explain(n);
  //Node flatExplanation = BooleanSimplification::simplifyConflict(explanation);

  d_out->explanation(explanation, true);
}
/*
void TheoryArith::internalExplain(TNode n, NodeBuilder<>& explainBuilder){
  Assert(n.hasAttribute(Propagated()));
  Node bound = n.getAttribute(Propagated());

  AlwaysAssert(bound.getKind() == kind::AND);

  for(Node::iterator i = bound.begin(), end = bound.end(); i != end; ++i){
    Node lit = *i;
    if(lit.hasAttribute(Propagated())){
      cout << "hoop the sadjklasdj" << endl;
      internalExplain(lit, explainBuilder);
    }else{
      explainBuilder << lit;
    }
  }
}
*/
/*
static const bool EXPORT_LEMMA_INSTEAD_OF_PROPAGATE = false;
void TheoryArith::propagateArithVar(bool upperbound, ArithVar var ){
  Node varAsNode = asNode(var);
  const DeltaRational& b = upperbound ?
    d_partialModel.getUpperBound(var) : d_partialModel.getLowerBound(var);

  Assert((!upperbound) || (b.getInfinitesimalPart() <= 0) );
  Assert(upperbound || (b.getInfinitesimalPart() >= 0) );
  Kind kind;
  if(upperbound){
    kind = b.getInfinitesimalPart() < 0 ? LT : LEQ;
  } else{
    kind = b.getInfinitesimalPart() > 0 ? GT : GEQ;
  }

  Node bAsNode = NodeBuilder<2>(kind) << varAsNode
                                      << mkRationalNode(b.getNoninfinitesimalPart());

  Node bestImplied = upperbound ?
    d_propagator.getBestImpliedUpperBound(bAsNode):
    d_propagator.getBestImpliedLowerBound(bAsNode);

  if(!bestImplied.isNull()){
    Node satValue = d_valuation.getSatValue(bestImplied);
    if(satValue.isNull()){

      Node reason = upperbound ?
        d_partialModel.getUpperConstraint(var) :
        d_partialModel.getLowerConstraint(var);

      //cout << getContext()->getLevel() << " " << bestImplied << " " << reason  << endl;
      if(EXPORT_LEMMA_INSTEAD_OF_PROPAGATE){
        Node lemma = NodeBuilder<2>(IMPLIES) << reason
                                             << bestImplied;

        //Temporary
        Node clause = BooleanSimplification::simplifyHornClause(lemma);
        d_out->lemma(clause);
      }else{
        Assert(!bestImplied.hasAttribute(Propagated()));
        bestImplied.setAttribute(Propagated(), reason);
        d_reasons.push_back(reason);
        d_out->propagate(bestImplied);
      }
    }else{
      Assert(!satValue.isNull());
      Assert(satValue.getKind() == CONST_BOOLEAN);
      Assert(satValue.getConst<bool>());
    }
  }
}
*/

void TheoryArith::propagate(Effort e) {
  if(quickCheckOrMore(e)){
    bool propagated = false;
    if(Options::current()->arithPropagation && d_simplex.hasAnyUpdates()){
      d_simplex.propagateCandidates();
    }else{
      d_simplex.clearUpdates();
    }

    while(d_propManager.hasMorePropagations()){
      TNode toProp = d_propManager.getPropagation();
      Node satValue = d_valuation.getSatValue(toProp);
      AlwaysAssert(satValue.isNull());
      TNode exp = d_propManager.explain(toProp);
      propagated = true;
      d_out->propagate(toProp);
    }

    if(!propagated){
      //Opportunistically export previous conflicts
      while(d_simplex.hasMoreLemmas()){
        Node lemma = d_simplex.popLemma();
        d_out->lemma(lemma);
      }
    }
  }
}

Node TheoryArith::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {
  case kind::VARIABLE: {
    ArithVar var = d_arithvarNodeMap.asArithVar(n);

    if(d_removedRows.find(var) != d_removedRows.end()){
      Node eq = d_removedRows.find(var)->second;
      Assert(n == eq[0]);
      Node rhs = eq[1];
      return getValue(rhs);
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

void TheoryArith::notifyEq(TNode lhs, TNode rhs) {
}

void TheoryArith::notifyRestart(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_restartTimer);

  if(Debug.isOn("paranoid:check_tableau")){ d_simplex.debugCheckTableau(); }

  ++d_restartsCounter;
  /*
  if(d_restartsCounter % d_tableauResetPeriod == 0){
    double currentDensity = d_tableau.densityMeasure();
    d_statistics.d_avgTableauDensityAtRestart.addEntry(currentDensity);
    if(currentDensity >= d_tableauResetDensity * d_initialDensity){

      ++d_statistics.d_tableauResets;
      d_tableauResetPeriod += s_TABLEAU_RESET_INCREMENT;
      d_tableauResetDensity += .2;
      d_tableau = d_initialTableau;
    }
  }
  */
  static const bool debugResetPolicy = false;

  uint32_t currSize = d_tableau.size();
  uint32_t copySize = d_smallTableauCopy.size();

  //d_statistics.d_tableauSizeHistory << currSize;
  if(debugResetPolicy){
    cout << "curr " << currSize << " copy " << copySize << endl;
  }
  if(d_presolveHasBeenCalled && copySize == 0 && currSize > 0){
    if(debugResetPolicy){
      cout << "initial copy " << d_restartsCounter << endl;
    }
    d_smallTableauCopy = d_tableau; // The initial copy
  }

  if(d_presolveHasBeenCalled && d_restartsCounter >= RESET_START){
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

void TheoryArith::permanentlyRemoveVariable(ArithVar v){
  //There are 3 cases
  // 1) v is non-basic and is contained in a row
  // 2) v is basic
  // 3) v is non-basic and is not contained in a row
  //  It appears that this can happen after other variables have been removed!
  //  Tread carefullty with this one.

  bool noRow = false;

  if(!d_tableau.isBasic(v)){
    ArithVar basic = findShortestBasicRow(v);

    if(basic == ARITHVAR_SENTINEL){
      noRow = true;
    }else{
      Assert(basic != ARITHVAR_SENTINEL);
      d_tableau.pivot(basic, v);
    }
  }

  if(d_tableau.isBasic(v)){
    Assert(!noRow);

    //remove the row from the tableau
    Node eq =  d_tableau.rowAsEquality(v, d_arithvarNodeMap.getArithVarToNodeMap());
    d_tableau.removeRow(v);

    if(Debug.isOn("tableau")) d_tableau.printTableau();
    Debug("arith::permanentlyRemoveVariable") << eq << endl;

    Assert(d_tableau.getRowLength(v) == 0);
    Assert(d_tableau.getColLength(v) == 0);
    Assert(d_removedRows.find(v) ==  d_removedRows.end());
    d_removedRows[v] = eq;
  }

  Debug("arith::permanentlyRemoveVariable") << "Permanently removed variable " << v
                                            << ":" << d_arithvarNodeMap.asNode(v) <<endl;
  ++(d_statistics.d_permanentlyRemovedVariables);
}

void TheoryArith::presolve(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_presolveTime);

  typedef std::vector<Node>::const_iterator VarIter;
  for(VarIter i = d_variables.begin(), end = d_variables.end(); i != end; ++i){
    Node variableNode = *i;
    ArithVar var = d_arithvarNodeMap.asArithVar(variableNode);
    if(d_userVariables.isMember(var) && !d_propagator.hasAnyAtoms(variableNode)){
      //The user variable is unconstrained.
      //Remove this variable permanently
      permanentlyRemoveVariable(var);
    }
  }

  d_statistics.d_initialTableauSize.setData(d_tableau.size());

  if(Debug.isOn("paranoid:check_tableau")){ d_simplex.debugCheckTableau(); }

  static int callCount = 0;
  Debug("arith::presolve") << "TheoryArith::presolve #" << (callCount++) << endl;

  learner.clear();

  d_presolveHasBeenCalled = true;
  check(FULL_EFFORT);
}

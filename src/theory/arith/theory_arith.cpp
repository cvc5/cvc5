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
#include "theory/arith/atom_database.h"

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


TheoryArith::TheoryArith(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation) :
  Theory(THEORY_ARITH, c, u, out, valuation),
  d_hasDoneWorkSinceCut(false),
  d_atomsInContext(c),
  d_learner(d_pbSubstitutions),
  d_nextIntegerCheckVar(0),
  d_constantIntegerVariables(c),
  d_CivIterator(c,0),
  d_varsInDioSolver(c),
  d_diseq(c),
  d_partialModel(c, d_differenceManager),
  d_tableau(),
  d_linEq(d_partialModel, d_tableau, d_basicVarModelUpdateCallBack),
  d_diosolver(c),
  d_pbSubstitutions(u),
  d_restartsCounter(0),
  d_rowHasBeenAdded(false),
  d_tableauResetDensity(1.6),
  d_tableauResetPeriod(10),
  d_atomDatabase(c, out),
  d_propManager(c, d_arithvarNodeMap, d_atomDatabase, valuation),
  d_differenceManager(c, d_propManager),
  d_simplex(d_propManager, d_linEq),
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
  d_permanentlyRemovedVariables("theory::arith::permanentlyRemovedVariables", 0),
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

  StatisticsRegistry::registerStat(&d_permanentlyRemovedVariables);
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

  StatisticsRegistry::unregisterStat(&d_permanentlyRemovedVariables);
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

/* procedure AssertLower( x_i >= c_i ) */
Node TheoryArith::AssertLower(ArithVar x_i, DeltaRational& c_i, TNode original){
  Debug("arith") << "AssertLower(" << x_i << " " << c_i << ")"<< std::endl;

  if(isInteger(x_i)){
    c_i = DeltaRational(c_i.ceiling());
  }

  //TODO Relax to less than?
  if(d_partialModel.strictlyLessThanLowerBound(x_i, c_i)){
    return Node::null();
  }

  int cmpToUB = d_partialModel.cmpToUpperBound(x_i, c_i);
  if(cmpToUB > 0){ //  c_i < \lowerbound(x_i)
    Node ubc = d_partialModel.getUpperConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, ubc, original);
    //d_out->conflict(conflict);
    Debug("arith") << "AssertLower conflict " << conflict << endl;
    ++(d_statistics.d_statAssertLowerConflicts);
    return conflict;
  }else if(cmpToUB == 0){
    if(isInteger(x_i)){
      d_constantIntegerVariables.push_back(x_i);
    }
    //check to make sure x_i != c_i has not been asserted
    Node left  = d_arithvarNodeMap.asNode(x_i);

    // if lowerbound and upperbound are equal, then the infinitesimal must be 0
    Assert(c_i.getInfinitesimalPart().isZero());
    Node right = mkRationalNode(c_i.getNoninfinitesimalPart());

    Node diseq = left.eqNode(right).notNode();
    if (d_diseq.find(diseq) != d_diseq.end()) {
      Node ub = d_partialModel.getUpperConstraint(x_i);
      return disequalityConflict(diseq, ub , original);
    }
  }

  d_partialModel.setLowerConstraint(x_i,original);
  d_partialModel.setLowerBound(x_i, c_i);

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
Node TheoryArith::AssertUpper(ArithVar x_i, DeltaRational& c_i, TNode original){
  Debug("arith") << "AssertUpper(" << x_i << " " << c_i << ")"<< std::endl;

  if(isInteger(x_i)){
    c_i = DeltaRational(c_i.floor());
  }

  Debug("arith") << "AssertUpper(" << x_i << " " << c_i << ")"<< std::endl;

  if(d_partialModel.strictlyGreaterThanUpperBound(x_i, c_i) ){ // \upperbound(x_i) <= c_i
    return Node::null(); //sat
  }

  // cmpToLb =  \lowerbound(x_i).cmp(c_i)
  int cmpToLB = d_partialModel.cmpToLowerBound(x_i, c_i);
  if( cmpToLB < 0 ){ //  \upperbound(x_i) < \lowerbound(x_i)
    Node lbc = d_partialModel.getLowerConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, lbc, original);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
    ++(d_statistics.d_statAssertUpperConflicts);
    return conflict;
  }else if(cmpToLB == 0){ // \lowerBound(x_i) == \upperbound(x_i)
    if(isInteger(x_i)){
      d_constantIntegerVariables.push_back(x_i);
    }

    //check to make sure x_i != c_i has not been asserted
    Node left  = d_arithvarNodeMap.asNode(x_i);

    // if lowerbound and upperbound are equal, then the infinitesimal must be 0
    Assert(c_i.getInfinitesimalPart().isZero());
    Node right = mkRationalNode(c_i.getNoninfinitesimalPart());

    Node diseq = left.eqNode(right).notNode();
    if (d_diseq.find(diseq) != d_diseq.end()) {
      Node lb = d_partialModel.getLowerConstraint(x_i);
      return disequalityConflict(diseq, lb , original);
    }
  }

  d_partialModel.setUpperConstraint(x_i,original);
  d_partialModel.setUpperBound(x_i, c_i);

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


/* procedure AssertLower( x_i == c_i ) */
Node TheoryArith::AssertEquality(ArithVar x_i, DeltaRational& c_i, TNode original){

  Debug("arith") << "AssertEquality(" << x_i << " " << c_i << ")"<< std::endl;

  int cmpToLB = d_partialModel.cmpToLowerBound(x_i, c_i);
  int cmpToUB = d_partialModel.cmpToUpperBound(x_i, c_i);

  // u_i <= c_i <= l_i
  // This can happen if both c_i <= x_i and x_i <= c_i are in the system.
  if(cmpToUB >= 0 && cmpToLB <= 0){
    return Node::null(); //sat
  }

  if(cmpToUB > 0){
    Node ubc = d_partialModel.getUpperConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, ubc, original);
    Debug("arith") << "AssertLower conflict " << conflict << endl;
    return conflict;
  }

  if(cmpToLB < 0){
    Node lbc = d_partialModel.getLowerConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, lbc, original);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
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

  d_partialModel.setLowerConstraint(x_i,original);
  d_partialModel.setLowerBound(x_i, c_i);

  d_partialModel.setUpperConstraint(x_i,original);
  d_partialModel.setUpperBound(x_i, c_i);


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


void TheoryArith::addSharedTerm(TNode n){
  d_differenceManager.addSharedTerm(n);
}

Node TheoryArith::ppRewrite(TNode atom) {
  Debug("arith::preprocess") << "arith::preprocess() : " << atom << endl;

  Node a = d_pbSubstitutions.apply(atom);

  if (a != atom) {
    Debug("pb") << "arith::preprocess() : after pb substitutions: " << a << endl;
    a = Rewriter::rewrite(a);
    Debug("pb") << "arith::preprocess() : after pb substitutions and rewriting: "
                << a << endl;
    Debug("arith::preprocess") << "arith::preprocess() :"
                               << "after pb substitutions and rewriting: " << a << endl;
  }

  if (a.getKind() == kind::EQUAL) {
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

  // Solve equalities
  Rational minConstant = 0;
  Node minMonomial;
  Node minVar;
  unsigned nVars = 0;
  if (in.getKind() == kind::EQUAL) {
    Assert(in[1].getKind() == kind::CONST_RATIONAL);
    // Find the variable with the smallest coefficient
    Polynomial p = Polynomial::parsePolynomial(in[0]);
    Polynomial::iterator it = p.begin(), it_end = p.end();
    for (; it != it_end; ++ it) {
      Monomial m = *it;
      // Skip the constant
      if (m.isConstant()) continue;
      // This is a ''variable''
      nVars ++;
      // Skip the non-linear stuff
      if (!m.getVarList().singleton()) continue;
      // Get the minimal one
      Rational constant = m.getConstant().getValue();
      Rational absSconstant = constant > 0 ? constant : -constant;
      if (minVar.isNull() || absSconstant < minConstant) {
        Node var = m.getVarList().getNode();
        if (var.getKind() == kind::VARIABLE) {
          minVar = var;
          minMonomial = m.getNode();
          minConstant = constant;
        }
      }
    }

    // Solve for variable
    if (!minVar.isNull()) {
      // ax + p = c -> (ax + p) -ax - c = -ax
      Node eliminateVar = NodeManager::currentNM()->mkNode(kind::MINUS, in[0], minMonomial);
      if (in[1].getConst<Rational>() != 0) {
        eliminateVar = NodeManager::currentNM()->mkNode(kind::MINUS, eliminateVar, in[1]);
      }
      // x = (p - ax - c) * -1/a
      eliminateVar = NodeManager::currentNM()->mkNode(kind::MULT, eliminateVar, mkRationalNode(- minConstant.inverse()));
      // Add the substitution if not recursive
      Node rewritten = Rewriter::rewrite(eliminateVar);
      if (!rewritten.hasSubterm(minVar)) {
        Node elim = Rewriter::rewrite(eliminateVar);
        if (!minVar.getType().isInteger() || elim.getType().isInteger()) {
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
              d_differenceManager.addDifference(varSlack, vl0.getNode(), vl1.getNode());
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

void TheoryArith::setupAtom(TNode atom, bool addToDatabase) {
  Assert(isRelationOperator(atom.getKind()));
  Assert(Comparison::isNormalAtom(atom));
  Assert(!isSetup(atom));

  Node left = atom[0];
  if(!isSetup(left)){
    Polynomial poly = Polynomial::parsePolynomial(left);
    setupPolynomial(poly);
  }

  if(addToDatabase){
    d_atomDatabase.addAtom(atom);
  }

  markSetup(atom);
}

void TheoryArith::preRegisterTerm(TNode n) {
  Debug("arith::preregister") <<"begin arith::preRegisterTerm("<< n <<")"<< endl;

  if(isRelationOperator(n.getKind())){
    if(!isSetup(n)){
      setupAtom(n, true);
    }
    addToContext(n);
  }

  Debug("arith::preregister") << "end arith::preRegisterTerm(" << n <<")" << endl;
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

ArithVar TheoryArith::determineLeftVariable(TNode assertion, Kind simpleKind){
  TNode left = getSide<true>(assertion, simpleKind);

  return d_arithvarNodeMap.asArithVar(left);
}


Node TheoryArith::disequalityConflict(TNode eq, TNode lb, TNode ub){
  NodeBuilder<3> conflict(kind::AND);
  conflict << eq << lb << ub;
  ++(d_statistics.d_statDisequalityConflicts);
  return conflict;
}

bool TheoryArith::canSafelyAvoidEqualitySetup(TNode equality){
  Assert(equality.getKind() == EQUAL);
  return d_arithvarNodeMap.hasArithVar(equality[0]);
}

Comparison TheoryArith::mkIntegerEqualityFromAssignment(ArithVar v){
  const DeltaRational& beta = d_partialModel.getAssignment(v);

  Assert(beta.isIntegral());
  Constant betaAsConstant = Constant::mkConstant(beta.floor());

  TNode var = d_arithvarNodeMap.asNode(v);
  Polynomial varAsPolynomial = Polynomial::parsePolynomial(var);
  return Comparison::mkComparison(EQUAL, varAsPolynomial, betaAsConstant);
}

Node TheoryArith::dioCutting(){
  context::Context::ScopedPush speculativePush(getContext());
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
    Constant c = plane.getConstant() * Constant::mkConstant(-1);
    Integer gcd = p.gcd();
    Assert(p.isIntegral());
    Assert(c.isIntegral());
    Assert(gcd > 1);
    Assert(!gcd.divides(c.getValue().getNumerator()));
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
  while(d_CivIterator < d_constantIntegerVariables.size()){
    ArithVar v = d_constantIntegerVariables[d_CivIterator];
    d_CivIterator = d_CivIterator + 1;

    Debug("arith::dio")  << v << endl;

    Assert(isInteger(v));
    Assert(d_partialModel.boundsAreEqual(v));

    if(d_varsInDioSolver.find(v) != d_varsInDioSolver.end()){
      continue;
    }else{
      d_varsInDioSolver.insert(v);
    }

    TNode lb = d_partialModel.getLowerConstraint(v);
    TNode ub = d_partialModel.getUpperConstraint(v);

    Node orig = Node::null();
    if(lb == ub){
      Assert(lb.getKind() == EQUAL);
      orig = lb;
    }else if(lb.getKind() == EQUAL){
      orig = lb;
    }else if(ub.getKind() == EQUAL){
      orig = ub;
    }else{
      NodeBuilder<> nb(AND);
      nb << ub << lb;
      orig = nb;
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
  Kind simpleKind = simplifiedKind(assertion);
  Assert(simpleKind != UNDEFINED_KIND);
  if(simpleKind == EQUAL || simpleKind == DISTINCT){
    Node eq = (simpleKind == DISTINCT) ? assertion[0] : assertion;

    if(!isSetup(eq)){
      //The previous code was equivalent to:
      setupAtom(eq, false);
      //We can try:
      //setupAtom(eq, true);
      addToContext(eq);
    }
  }

  ArithVar x_i = determineLeftVariable(assertion, simpleKind);
  DeltaRational c_i = determineRightConstant(assertion, simpleKind);

  // bool tightened = false;

  // //If the variable is an integer tighen the constraint.
  // if(isInteger(x_i)){
  //   if(simpleKind == LT){
  //     tightened = true;
  //     c_i = DeltaRational(c_i.floor());
  //   }else if(simpleKind == GT){
  //     tightened = true;
  //     c_i = DeltaRational(c_i.ceiling());
  //   }
  // }

  Debug("arith::assertions")  << "arith assertion @" << getContext()->getLevel()
                              <<"(" << assertion
                              << " \\-> "
                              << x_i<<" "<< simpleKind <<" "<< c_i << ")" << std::endl;

  switch(simpleKind){
  case LEQ:
  case LT:
    return  AssertUpper(x_i, c_i, assertion);
  case GEQ:
  case GT:
    return AssertLower(x_i, c_i, assertion);
  case EQUAL:
    return AssertEquality(x_i, c_i, assertion);
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
  }

  if(Debug.isOn("arith::print_assertions")) {
    debugPrintAssertions();
  }

  bool emmittedConflictOrSplit = false;
  Node possibleConflict = d_simplex.findModel();
  if(possibleConflict != Node::null()){
    d_partialModel.revertAssignmentChanges();
    clearUpdates();
    Debug("arith::conflict") << "conflict   " << possibleConflict << endl;

    d_out->conflict(possibleConflict);
    emmittedConflictOrSplit = true;
  }else{
    d_partialModel.commitAssignmentChanges();
  }

  if(!emmittedConflictOrSplit && fullEffort(effortLevel)){
    emmittedConflictOrSplit = splitDisequalities();
  }

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

  context::CDHashSet<Node, NodeHashFunction>::iterator it = d_diseq.begin();
  context::CDHashSet<Node, NodeHashFunction>::iterator it_end = d_diseq.end();
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
      Debug("arith::lemma") << "Splitting on " << eq << endl;
      Debug("arith::lemma") << "LHS value = " << lhsValue << endl;
      Debug("arith::lemma") << "RHS value = " << rhsValue << endl;
      Node ltNode = NodeBuilder<2>(kind::LT) << lhs << rhs;
      Node gtNode = NodeBuilder<2>(kind::GT) << lhs << rhs;
      Node lemma = NodeBuilder<3>(OR) << eq << ltNode << gtNode;
      ++(d_statistics.d_statDisequalitySplits);
      d_out->lemma(lemma);
      splitSomething = true;
    }
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
      Node lConstr = d_partialModel.getLowerConstraint(i);
      Debug("arith::print_assertions") << lConstr << endl;
    }

    if (d_partialModel.hasUpperBound(i)) {
      Node uConstr = d_partialModel.getUpperConstraint(i);
      Debug("arith::print_assertions") << uConstr << endl;
    }
  }
  context::CDHashSet<Node, NodeHashFunction>::iterator it = d_diseq.begin();
  context::CDHashSet<Node, NodeHashFunction>::iterator it_end = d_diseq.end();
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
  Debug("arith::explain") << "explain @" << getContext()->getLevel() << ": " << n << endl;
  Assert(d_propManager.isPropagated(n));

  return d_propManager.explain(n);
}

void flattenAnd(Node n, std::vector<TNode>& out){
  Assert(n.getKind() == kind::AND);
  for(Node::iterator i=n.begin(), i_end=n.end(); i != i_end; ++i){
    Node curr = *i;
    if(curr.getKind() == kind::AND){
      flattenAnd(curr, out);
    }else{
      out.push_back(curr);
    }
  }
}

Node flattenAnd(Node n){
  std::vector<TNode> out;
  flattenAnd(n, out);
  return NodeManager::currentNM()->mkNode(kind::AND, out);
}

void TheoryArith::propagate(Effort e) {
  if(quickCheckOrMore(e)){
    bool propagated = false;
    if(Options::current()->arithPropagation && hasAnyUpdates()){
      propagateCandidates();
    }else{
      clearUpdates();
    }

    while(d_propManager.hasMorePropagations()){
      const PropManager::PropUnit next = d_propManager.getNextPropagation();
      bool flag = next.flag;
      TNode toProp = next.consequent;

      TNode atom = (toProp.getKind() == kind::NOT) ? toProp[0] : toProp;

      Debug("arith::propagate") << "propagate  @" << getContext()->getLevel() <<" flag: "<< flag << " " << toProp << endl;

      if(flag) {
        //Currently if the flag is set this came from an equality detected by the
        //equality engine in the the difference manager.
        if(toProp.getKind() == kind::EQUAL){
          Node normalized = Rewriter::rewrite(toProp);
          Node notNormalized = normalized.notNode();

          if(d_diseq.find(notNormalized) == d_diseq.end()){
            d_out->propagate(toProp);
            propagated = true;
          }else{
            Node exp = d_differenceManager.explain(toProp);
            Node lp = flattenAnd(exp.andNode(notNormalized));
            Debug("arith::propagate") << "propagate conflict" <<  lp << endl;
            d_out->conflict(lp);

            propagated = true;
            break;
          }
        }else{
          d_out->propagate(toProp);
          propagated = true;
        }
      }else if(inContextAtom(atom)){
        Node satValue = d_valuation.getSatValue(toProp);
        AlwaysAssert(satValue.isNull());
        propagated = true;
        d_out->propagate(toProp);
      }else{
        //Not clear if this is a good time to do this or not...
        Debug("arith::propagate") << "Atom is not in context" << toProp << endl;
#warning "enable remove atom in database"
        //d_atomDatabase.removeAtom(atom);
      }
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

void TheoryArith::permanentlyRemoveVariable(ArithVar v){
  //There are 3 cases
  // 1) v is non-basic and is contained in a row
  // 2) v is basic
  // 3) v is non-basic and is not contained in a row
  //  It appears that this can happen after other variables have been removed!
  //  Tread carefullty with this one.

  Assert(Options::current()->variableRemovalEnabled);

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

  /* BREADCRUMB : Turn this on for QF_LRA/QF_RDL problems.
   *
   * The big problem for adding things back is that if they are readded they may
   * need to be assigned an initial value at ALL context values.
   * This is unsupported with our current datastructures.
   *
   * A better solution is to KNOW when the permantent removal is safe.
   * This is true for single query QF_LRA/QF_RDL problems.
   * Maybe a mechanism to ask "the sharing manager"
   * if this variable/row can be used in sharing?
   */
  if(Options::current()->variableRemovalEnabled){
    typedef std::vector<Node>::const_iterator VarIter;
    for(VarIter i = d_variables.begin(), end = d_variables.end(); i != end; ++i){
      Node variableNode = *i;
      ArithVar var = d_arithvarNodeMap.asArithVar(variableNode);
      if(!isSlackVariable(var) &&
         !d_atomDatabase.hasAnyAtoms(variableNode) &&
         !variableNode.getType().isInteger()){
	//The user variable is unconstrained.
	//Remove this variable permanently
	permanentlyRemoveVariable(var);
      }
    }
  }

  d_statistics.d_initialTableauSize.setData(d_tableau.size());

  if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }

  static CVC4_THREADLOCAL(unsigned) callCount = 0;
  if(Debug.isOn("arith::presolve")) {
    Debug("arith::presolve") << "TheoryArith::presolve #" << callCount << endl;
    callCount = callCount + 1;
  }

  d_learner.clear();
  check(FULL_EFFORT);
}

EqualityStatus TheoryArith::getEqualityStatus(TNode a, TNode b) {
  if (getValue(a) == getValue(b)) {
    return EQUALITY_TRUE_IN_MODEL;
  } else {
    return EQUALITY_FALSE_IN_MODEL;
  }

}

bool TheoryArith::propagateCandidateBound(ArithVar basic, bool upperBound){
  ++d_statistics.d_boundComputations;

  DeltaRational bound = upperBound ?
    d_linEq.computeUpperBound(basic):
    d_linEq.computeLowerBound(basic);

  if((upperBound && d_partialModel.strictlyLessThanUpperBound(basic, bound)) ||
     (!upperBound && d_partialModel.strictlyGreaterThanLowerBound(basic, bound))){
    Node bestImplied = upperBound ?
      d_propManager.getBestImpliedUpperBound(basic, bound):
      d_propManager.getBestImpliedLowerBound(basic, bound);

    if(!bestImplied.isNull()){
      bool asserted = d_propManager.isAsserted(bestImplied);
      bool propagated = d_propManager.isPropagated(bestImplied);
      if( !asserted && !propagated){

        NodeBuilder<> nb(kind::AND);
        if(upperBound){
          d_linEq.explainNonbasicsUpperBound(basic, nb);
        }else{
          d_linEq.explainNonbasicsLowerBound(basic, nb);
        }
        Node explanation = nb;
        d_propManager.propagate(bestImplied, explanation, false);
        return true;
      }else{
        Debug("arith::prop") << basic << " " << asserted << " " << propagated << endl;
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

  PermissiveBackArithVarSet::const_iterator i = d_updatedBounds.begin();
  PermissiveBackArithVarSet::const_iterator end = d_updatedBounds.end();
  for(; i != end; ++i){
    ArithVar var = *i;
    if(d_tableau.isBasic(var) &&
       d_tableau.getRowLength(var) <= Options::current()->arithPropagateMaxLength){
      d_candidateBasics.softAdd(var);
    }else{
      Tableau::ColIterator basicIter = d_tableau.colIterator(var);
      for(; !basicIter.atEnd(); ++basicIter){
        const TableauEntry& entry = *basicIter;
        ArithVar rowVar = entry.getRowVar();
        Assert(entry.getColVar() == var);
        Assert(d_tableau.isBasic(rowVar));
        if(d_tableau.getRowLength(rowVar) <= Options::current()->arithPropagateMaxLength){
          d_candidateBasics.softAdd(rowVar);
        }
      }
    }
  }
  d_updatedBounds.purge();

  while(!d_candidateBasics.empty()){
    ArithVar candidate = d_candidateBasics.pop_back();
    Assert(d_tableau.isBasic(candidate));
    propagateCandidate(candidate);
  }
}

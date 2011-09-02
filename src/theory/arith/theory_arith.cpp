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

struct SlackAttrID;
typedef expr::Attribute<SlackAttrID, bool> Slack;

TheoryArith::TheoryArith(context::Context* c, OutputChannel& out, Valuation valuation) :
  Theory(THEORY_ARITH, c, out, valuation),
  learner(d_pbSubstitutions),
  d_nextIntegerCheckVar(0),
  d_partialModel(c),
  d_userVariables(),
  d_diseq(c),
  d_tableau(),
  d_diosolver(c, d_tableau, d_partialModel),
  d_restartsCounter(0),
  d_rowHasBeenAdded(false),
  d_tableauResetDensity(1.6),
  d_tableauResetPeriod(10),
  d_atomDatabase(c, out),
  d_propManager(c, d_arithvarNodeMap, d_atomDatabase, valuation),
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
  d_simplifyTimer("theory::arith::simplifyTimer"),
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
  StatisticsRegistry::registerStat(&d_simplifyTimer);
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
  StatisticsRegistry::unregisterStat(&d_simplifyTimer);
  StatisticsRegistry::unregisterStat(&d_staticLearningTimer);

  StatisticsRegistry::unregisterStat(&d_permanentlyRemovedVariables);
  StatisticsRegistry::unregisterStat(&d_presolveTime);


  StatisticsRegistry::unregisterStat(&d_initialTableauSize);
  //StatisticsRegistry::unregisterStat(&d_tableauSizeHistory);
  StatisticsRegistry::unregisterStat(&d_currSetToSmaller);
  StatisticsRegistry::unregisterStat(&d_smallerSetToCurr);
  StatisticsRegistry::unregisterStat(&d_restartTimer);
}

Node TheoryArith::preprocess(TNode atom) {
  Debug("arith::preprocess") << "arith::preprocess() : " << atom << endl;

  Node a = d_pbSubstitutions.apply(atom);

  if (a != atom) {
    Debug("pb") << "arith::preprocess() : after pb substitutions: " << a << endl;
    a = Rewriter::rewrite(a);
    Debug("pb") << "arith::preprocess() : after pb substitutions and rewriting: " << a << endl;
    Debug("arith::preprocess") << "arith::preprocess() : after pb substitutions and rewriting: " << a << endl;
  }

  if (a.getKind() == kind::EQUAL) {
    Node leq = NodeBuilder<2>(kind::LEQ) << a[0] << a[1];
    Node geq = NodeBuilder<2>(kind::GEQ) << a[0] << a[1];
    Node rewritten = Rewriter::rewrite(leq.andNode(geq));
    Debug("arith::preprocess") << "arith::preprocess() : returning " << rewritten << endl;
    return rewritten;
  }

  return a;
}

Theory::SolveStatus TheoryArith::solve(TNode in, SubstitutionMap& outSubstitutions) {
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
          return SOLVE_STATUS_SOLVED;
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
      learner.addBound(in);
    }
    break;
  default:
    // Do nothing
    break;
  }

  return SOLVE_STATUS_UNSOLVED;
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

  /* BREADCRUMB: I am using this bool to compile time enable testing for arbitrary equalities. */
  static bool turnOffEqualityPreRegister = false;
  if(turnOffEqualityPreRegister){
    if(k == LEQ || k == LT || k == GT || k == GEQ){
      TNode left = n[0];
      delayedSetupPolynomial(left);

      d_atomDatabase.addAtom(n);
    }
    return;
  }

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

    d_atomDatabase.addAtom(n);

    TNode left  = n[0];
    TNode right = n[1];
    if(left.getKind() == PLUS){
      //We may need to introduce a slack variable.
      Assert(left.getNumChildren() >= 2);
      if(!left.getAttribute(Slack())){
        setupSlack(left);
      }
    } else {
      if (theoryOf(left) != THEORY_ARITH && !d_arithvarNodeMap.hasArithVar(left)) {
        // The only way not to get it through pre-register is if it's a foreign term
        ++(d_statistics.d_statUserVariables);
        ArithVar av = requestArithVar(left, false);
        setupInitialValue(av);
      } 
    }
  }
  Debug("arith_preregister") << "end arith::preRegisterTerm(" << n <<")" << endl;
}


ArithVar TheoryArith::requestArithVar(TNode x, bool basic){
  Assert(isLeaf(x) || x.getKind() == PLUS);
  Assert(!d_arithvarNodeMap.hasArithVar(x));
  Assert(x.getType().isReal());// real or integer

  ArithVar varX = d_variables.size();
  d_variables.push_back(Node(x));
  Debug("integers") << "isInteger[[" << x << "]]: " << x.getType().isInteger() << endl;
  d_integerVars.push_back(x.getType().isPseudoboolean() ? 2 : (x.getType().isInteger() ? 1 : 0));

  d_simplex.increaseMax();

  d_arithvarNodeMap.setArithVar(x,varX);

  d_userVariables.init(varX, !basic);
  d_tableau.increaseSize();

  Debug("arith::arithvar") << x << " |-> " << varX << endl;

  return varX;
}

void TheoryArith::asVectors(Polynomial& p, std::vector<Rational>& coeffs, std::vector<ArithVar>& variables) {
  for(Polynomial::iterator i = p.begin(), end = p.end(); i != end; ++i){
    const Monomial& mono = *i;
    const Constant& constant = mono.getConstant();
    const VarList& variable = mono.getVarList();

    Node n = variable.getNode();

    Debug("rewriter") << "should be var: " << n << endl;

    Assert(isLeaf(n));
    Assert(theoryOf(n) != THEORY_ARITH || d_arithvarNodeMap.hasArithVar(n));

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

void TheoryArith::setupSlack(TNode left){
  Assert(!left.getAttribute(Slack()));

  ++(d_statistics.d_statSlackVariables);
  left.setAttribute(Slack(), true);

  d_rowHasBeenAdded = true;

  Polynomial polyLeft = Polynomial::parsePolynomial(left);

  vector<ArithVar> variables;
  vector<Rational> coefficients;

  asVectors(polyLeft, coefficients, variables);

  ArithVar varSlack = requestArithVar(left, true);
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

void TheoryArith::delayedSetupMonomial(const Monomial& mono){

  Debug("arith::delay") << "delayedSetupMonomial(" << mono.getNode() << ")" << endl;

  Assert(!mono.isConstant());
  VarList vl = mono.getVarList();
  
  if(!d_arithvarNodeMap.hasArithVar(vl.getNode())){
    for(VarList::iterator i = vl.begin(), end = vl.end(); i != end; ++i){
      Variable var = *i;
      Node n = var.getNode();
      
      ++(d_statistics.d_statUserVariables);
      ArithVar varN = requestArithVar(n,false);
      setupInitialValue(varN);
    }

    if(!vl.singleton()){
      d_out->setIncomplete();

      Node n = vl.getNode();
      ++(d_statistics.d_statUserVariables);
      ArithVar varN = requestArithVar(n,false);
      setupInitialValue(varN);
    }
  }
}

void TheoryArith::delayedSetupPolynomial(TNode polynomial){
  Debug("arith::delay") << "delayedSetupPolynomial(" << polynomial << ")" << endl;

  Assert(Polynomial::isMember(polynomial));
  // if d_nodeMap.hasArithVar() all of the variables and it are setup
  if(!d_arithvarNodeMap.hasArithVar(polynomial)){
    Polynomial poly = Polynomial::parsePolynomial(polynomial);
    Assert(!poly.containsConstant());
    for(Polynomial::iterator i = poly.begin(), end = poly.end(); i != end; ++i){
      Monomial mono = *i;
      delayedSetupMonomial(mono);
    }

    if(polynomial.getKind() == PLUS){
      Assert(!polynomial.getAttribute(Slack()),
	     "Polynomial has slack attribute but not does not have arithvar");
      setupSlack(polynomial);
    }
  }
}

void TheoryArith::delayedSetupEquality(TNode equality){
  Debug("arith::delay") << "delayedSetupEquality(" << equality << ")" << endl;
  
  Assert(equality.getKind() == EQUAL);

  TNode left = equality[0];
  delayedSetupPolynomial(left);
}

bool TheoryArith::canSafelyAvoidEqualitySetup(TNode equality){
  Assert(equality.getKind() == EQUAL);
  return d_arithvarNodeMap.hasArithVar(equality[0]);
}

Node TheoryArith::assertionCases(TNode assertion){
  Kind simpKind = simplifiedKind(assertion);
  Assert(simpKind != UNDEFINED_KIND);
  if(simpKind == EQUAL || simpKind == DISTINCT){
    Node eq = (simpKind == DISTINCT) ? assertion[0] : assertion;
 
    if(!canSafelyAvoidEqualitySetup(eq)){
      delayedSetupEquality(eq);
    }
  }

  ArithVar x_i = determineLeftVariable(assertion, simpKind);
  DeltaRational c_i = determineRightConstant(assertion, simpKind);

  Debug("arith::assertions") << "arith assertion(" << assertion
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
    Debug("arith::conflict") << "conflict   " << possibleConflict << endl;

    d_out->conflict(possibleConflict);
  }else{
    d_partialModel.commitAssignmentChanges();

    if (fullEffort(effortLevel)) {
      splitDisequalities();
    }
  }

  if(fullEffort(effortLevel) && d_integerVars.size() > 0) {
    const ArithVar rrEnd = d_nextIntegerCheckVar;
    do {
      ArithVar v = d_nextIntegerCheckVar;
      short type = d_integerVars[v];
      if(type > 0) { // integer
        const DeltaRational& d = d_partialModel.getAssignment(v);
        const Rational& r = d.getNoninfinitesimalPart();
        const Rational& i = d.getInfinitesimalPart();
        Trace("integers") << "integers: assignment to [[" << d_arithvarNodeMap.asNode(v) << "]] is " << r << "[" << i << "]" << endl;
        if(type == 2) {
          // pseudoboolean
          if(r.getDenominator() == 1 && i.getNumerator() == 0 &&
             (r.getNumerator() == 0 || r.getNumerator() == 1)) {
            // already pseudoboolean; skip
            continue;
          }

          TNode var = d_arithvarNodeMap.asNode(v);
          Node zero = NodeManager::currentNM()->mkConst(Integer(0));
          Node one = NodeManager::currentNM()->mkConst(Integer(1));
          Node eq0 = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::EQUAL, var, zero));
          Node eq1 = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::EQUAL, var, one));
          Node lem = NodeManager::currentNM()->mkNode(kind::OR, eq0, eq1);
          Trace("pb") << "pseudobooleans: branch & bound: " << lem << endl;
          Trace("integers") << "pseudobooleans: branch & bound: " << lem << endl;
          //d_out->lemma(lem);
        }
        if(r.getDenominator() == 1 && i.getNumerator() == 0) {
          // already an integer assignment; skip
          continue;
        }

        // otherwise, try the Diophantine equation solver
        //bool result = d_diosolver.solve();
        //Debug("integers") << "the dio solver returned " << (result ? "true" : "false") << endl;

        // branch and bound
        if(r.getDenominator() == 1) {
          // r is an integer, but the infinitesimal might not be
          if(i.getNumerator() < 0) {
            // lemma: v <= r - 1 || v >= r

            TNode var = d_arithvarNodeMap.asNode(v);
            Node nrMinus1 = NodeManager::currentNM()->mkConst(r - 1);
            Node nr = NodeManager::currentNM()->mkConst(r);
            Node leq = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::LEQ, var, nrMinus1));
            Node geq = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::GEQ, var, nr));

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
            d_out->lemma(lem);

            // split only on one var
            break;
          } else if(i.getNumerator() > 0) {
            // lemma: v <= r || v >= r + 1

            TNode var = d_arithvarNodeMap.asNode(v);
            Node nr = NodeManager::currentNM()->mkConst(r);
            Node nrPlus1 = NodeManager::currentNM()->mkConst(r + 1);
            Node leq = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::LEQ, var, nr));
            Node geq = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::GEQ, var, nrPlus1));

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
            d_out->lemma(lem);

            // split only on one var
            break;
          } else {
            Unreachable();
          }
        } else {
          // lemma: v <= floor(r) || v >= ceil(r)

          TNode var = d_arithvarNodeMap.asNode(v);
          Node floor = NodeManager::currentNM()->mkConst(r.floor());
          Node ceiling = NodeManager::currentNM()->mkConst(r.ceiling());
          Node leq = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::LEQ, var, floor));
          Node geq = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::GEQ, var, ceiling));

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
          d_out->lemma(lem);

          // split only on one var
          break;
        }
      }// if(arithvar is integer-typed)
    } while((d_nextIntegerCheckVar = (1 + d_nextIntegerCheckVar == d_variables.size() ? 0 : 1 + d_nextIntegerCheckVar)) != rrEnd);
  }// if(full effort)

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

void TheoryArith::explain(TNode n) {
  Debug("explain") << "explain @" << getContext()->getLevel() << ": " << n << endl;

  Assert(d_propManager.isPropagated(n));
  Node explanation = d_propManager.explain(n);
  d_out->explanation(explanation, true);
}

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
      if(d_userVariables.isMember(var) &&
         !d_atomDatabase.hasAnyAtoms(variableNode) &&
         !variableNode.getType().isInteger()){
	//The user variable is unconstrained.
	//Remove this variable permanently
	permanentlyRemoveVariable(var);
      }
    }
  }

  d_statistics.d_initialTableauSize.setData(d_tableau.size());

  if(Debug.isOn("paranoid:check_tableau")){ d_simplex.debugCheckTableau(); }

  static int callCount = 0;
  Debug("arith::presolve") << "TheoryArith::presolve #" << (callCount++) << endl;

  learner.clear();
  check(FULL_EFFORT);
}

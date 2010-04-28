#include "expr/node.h"
#include "expr/kind.h"
#include "expr/metakind.h"

#include "util/rational.h"
#include "util/integer.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/tableau.h"
#include "theory/arith/normal.h"
#include "theory/arith/slack.h"

#include "theory/arith/arith_rewriter.h"

#include "theory/arith/theory_arith.h"
#include <map>

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;


bool isBasicSum(TNode n){
  Unimplemented();
  return false;
}

Kind multKind(Kind k){
  switch(k){
  case LT: return GT;
  case LEQ: return GEQ;
  case EQUAL: return EQUAL;
  case GEQ: return LEQ;
  case GT: return LT;
  default:
    Unhandled();
  }
  return NULL_EXPR;
}


void registerAtom(TNode rel){
  addBound(rel);
  //Anything else?
}

Node TheoryArith::rewrite(TNode n){
  return d_rewriter.rewrite(n);
}

void TheoryArith::registerTerm(TNode tn){
  if(tn.isAtomic()){
    Node normalForm = (isNormalized(tn)) ? Node(tn) : rewrite(tn);
    Kind k = normalForm.getKind();

    if(k != kind::CONST_BOOLEAN){
      Assert(isRelationOperator(k));
      TNode left  = normalForm[0];
      TNode right = normalForm[1];
      if(left.getKind() == PLUS){
        //We may need to introduce a slack variable.
        Assert(left.getNumChildren() >= 2);
        Assert(isBasicSum(left));
        Node slack;
        if(!left.getAttribute(Slack(), slack)){
          //TODO
          //slack = NodeManager::currentNM()->mkVar(RealType());
          left.setAttribute(Slack(), slack);
          makeBasic(slack);

          Node slackEqLeft = NodeManager::currentNM()->mkNode(EQUAL,slack,left);
          slackEqLeft.setAttribute(TheoryArithPropagated(), true);
          //TODO this has to be wrong no?
          d_out->lemma(slackEqLeft);

          d_tableau.addRow(slackEqLeft);
        }

        Node rewritten = NodeManager::currentNM()->mkNode(k,slack,right);
        registerAtom(rewritten);
      }else{
        Assert(left.getMetaKind() == metakind::VARIABLE);
        Assert(right.getKind() == CONST_RATIONAL);
        registerAtom(normalForm);
      }
    }
  }
}

/* procedure AssertUpper( x_i <= c_i) */
void TheoryArith::AssertUpper(TNode n){
  TNode x_i = n[0];
  Rational dcoeff = Rational(Integer(deltaCoeff(n.getKind())));
  DeltaRational c_i(n[1].getConst<Rational>(), dcoeff);

  if(aboveUpperBound(x_i, c_i, false) ){
    return; //sat
  }
  if(belowLowerBound(x_i, c_i, true)){
    d_out->conflict(n);
    return;
  }

  setUpperConstraint(n);
  setUpperBound(x_i, c_i);

  if(!isBasic(x_i)){
    if(getAssignment(x_i) > c_i){
      update(x_i, c_i);
    }
  }
}

/* procedure AssertLower( x_i >= c_i ) */
void TheoryArith::AssertLower(TNode n){
  TNode x_i = n[0];
  Rational dcoeff = Rational(Integer(deltaCoeff(n.getKind())));
  DeltaRational c_i(n[1].getConst<Rational>(),dcoeff);

  if(belowLowerBound(x_i, c_i, false)){
    return; //sat
  }
  if(aboveUpperBound(x_i, c_i, true)){
    d_out->conflict(n);
    return;
  }

  setLowerConstraint(n);
  setLowerBound(x_i, c_i);

  if(!isBasic(x_i)){
    if(getAssignment(x_i) > c_i){
      update(x_i, c_i);
    }
  }
}

void TheoryArith::update(TNode x_i, DeltaRational& v){

  DeltaRational assignment_x_i = getAssignment(x_i);
  DeltaRational diff = v - assignment_x_i;

  for(Tableau::VarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){
    TNode x_j = *basicIter;
    Row* row_j = d_tableau.lookup(x_j);

    Rational& a_ji = row_j->lookup(x_i);

    DeltaRational assignment = getAssignment(x_j);
    DeltaRational  nAssignment = assignment+(diff * a_ji);
    setAssignment(x_j, nAssignment);
  }

  setAssignment(x_i, v);
}

void TheoryArith::pivotAndUpdate(TNode x_i, TNode x_j, DeltaRational& v){
  Row* row_i = d_tableau.lookup(x_i);
  Rational& a_ij = row_i->lookup(x_i);


  DeltaRational betaX_i = getAssignment(x_i);

  Rational inv_aij = a_ij.inverse();
  DeltaRational theta = (v - betaX_i)*inv_aij;

  setAssignment(x_i, v);


  DeltaRational tmp = getAssignment(x_j) + theta;
  setAssignment(x_j, tmp);

  for(Tableau::VarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){
    TNode x_k = *basicIter;
    Row* row_k = d_tableau.lookup(x_k);

    if(x_k != x_i){
      DeltaRational a_kj = row_k->lookup(x_j);
      DeltaRational nextAssignment = getAssignment(x_k) + theta;
      setAssignment(x_k, nextAssignment);
    }
  }

  d_tableau.pivot(x_i, x_j);
}

TNode TheoryArith::selectSmallestInconsistentVar(){

  for(Tableau::VarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){

    TNode basic = *basicIter;
    if(!assignmentIsConsistent(basic)){
      return basic;
    }
  }

  return TNode::null();
}

TNode TheoryArith::selectSlackBelow(TNode x_i){ //beta(x_i) < l_i
  Row* row_i = d_tableau.lookup(x_i);

  typedef std::set<TNode>::iterator NonBasicIter;

  for(NonBasicIter nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    TNode nonbasic = *nbi;

    Rational a_ij = row_i->lookup(nonbasic);
    if(a_ij > d_constants.d_ZERO && strictlyBelowUpperBound(nonbasic)){
      return nonbasic;
    }else if(a_ij < d_constants.d_ZERO && strictlyAboveLowerBound(nonbasic)){
      return nonbasic;
    }else{
      Unreachable();
    }
  }
  return TNode::null();
}

TNode TheoryArith::selectSlackAbove(TNode x_i){ // beta(x_i) > u_i
  Row* row_i = d_tableau.lookup(x_i);

  typedef std::set<TNode>::iterator NonBasicIter;

  for(NonBasicIter nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    TNode nonbasic = *nbi;

    Rational a_ij = row_i->lookup(nonbasic);
    if(a_ij < d_constants.d_ZERO && strictlyBelowUpperBound(nonbasic)){
      return nonbasic;
    }else if(a_ij > d_constants.d_ZERO && strictlyAboveLowerBound(nonbasic)){
      return nonbasic;
    }else{
      Unreachable();
    }
  }
  return TNode::null();
}


TNode TheoryArith::updateInconsistentVars(){ //corresponds to Check() in dM06

  while(true){
    TNode x_i = selectSmallestInconsistentVar();
    if(x_i == Node::null()){
      return Node::null(); //sat
    }
    DeltaRational beta_i = getAssignment(x_i);
    DeltaRational l_i = getLowerBound(x_i);
    DeltaRational u_i = getUpperBound(x_i);
    if(belowLowerBound(x_i, beta_i, true)){
      TNode x_j = selectSlackBelow(x_i);
      if(x_j == TNode::null() ){
        return generateConflictBelow(x_i); //unsat
      }
      pivotAndUpdate(x_i, x_j, l_i);
    }else if(aboveUpperBound(x_i, beta_i, true)){
      TNode x_j = selectSlackAbove(x_i);
      if(x_j == TNode::null() ){
        return generateConflictAbove(x_j); //unsat
      }
      pivotAndUpdate(x_i, x_j, u_i);
    }
  }
}

Node TheoryArith::generateConflictAbove(TNode conflictVar){
  Row* row_i = d_tableau.lookup(conflictVar);

  NodeBuilder<> nb(kind::AND);
  nb << getUpperConstraint(conflictVar);

  typedef std::set<TNode>::iterator NonBasicIter;

  for(NonBasicIter nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    TNode nonbasic = *nbi;
    Rational& a_ij = row_i->lookup(nonbasic);

    Assert(a_ij != d_constants.d_ZERO);

    if(a_ij < d_constants.d_ZERO){
      nb << getUpperConstraint(nonbasic);
    }else{
      nb << getLowerConstraint(nonbasic);
    }
  }
  Node conflict = nb;
  return conflict;
}
Node TheoryArith::generateConflictBelow(TNode conflictVar){
  Row* row_i = d_tableau.lookup(conflictVar);

  NodeBuilder<> nb(kind::AND);
  nb << getLowerConstraint(conflictVar);

  typedef std::set<TNode>::iterator NonBasicIter;

  for(NonBasicIter nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    TNode nonbasic = *nbi;
    Rational& a_ij = row_i->lookup(nonbasic);

    Assert(a_ij != d_constants.d_ZERO);

    if(a_ij < d_constants.d_ZERO){
      nb << getLowerConstraint(nonbasic);
    }else{
      nb << getUpperConstraint(nonbasic);
    }
  }
  Node conflict = nb;
  return conflict;
}

void TheoryArith::check(Effort level){
  while(!done()){
    Node assertion = get();

    if(assertion.getKind() == NOT){
      assertion = pushInNegation(assertion);
    }

    switch(assertion.getKind()){
    case LT:
    case LEQ:
      AssertUpper(assertion);
      break;
    case GEQ:
    case GT:
      AssertLower(assertion);
      break;
    case EQUAL:
      AssertUpper(assertion);
      AssertLower(assertion);
      break;
    case NOT:
      Assert(assertion[0].getKind() == EQUAL);
      d_diseq.push_back(assertion);
      break;
    default:
      Unhandled();
    }
  }

  if(fullEffort(level)){
    Node possibleConflict = updateInconsistentVars();
    if(possibleConflict != Node::null()){
      d_out->conflict(possibleConflict);
    }
  }

  if(fullEffort(level)){
    NodeBuilder<> lemmas(AND);
    typedef context::CDList<Node>::const_iterator diseq_iterator;
    for(diseq_iterator i = d_diseq.begin(); i!= d_diseq.end(); ++i){
      Node assertion = *i;
      TNode eq = assertion[0];
      TNode x_i = eq[0];
      TNode c_i = eq[1];
      DeltaRational constant =  c_i.getConst<Rational>();
      if(getAssignment(x_i) == constant){
        Node lt = NodeManager::currentNM()->mkNode(LT,x_i,c_i);
        Node gt = NodeManager::currentNM()->mkNode(GT,x_i,c_i);
        Node disjunct = NodeManager::currentNM()->mkNode(OR, eq, lt, gt);
        lemmas<< disjunct;
      }
    }
    Node caseSplits = lemmas;
    //TODO
    //DemandCaseSplits(caseSplits);
  }
}

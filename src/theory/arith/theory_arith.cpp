#include "expr/node.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node_builder.h"

#include "util/rational.h"
#include "util/integer.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/tableau.h"
#include "theory/arith/normal.h"
#include "theory/arith/slack.h"
#include "theory/arith/basic.h"

#include "theory/arith/arith_rewriter.h"

#include "theory/arith/theory_arith.h"
#include <map>
#include <stdint.h>

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;

TheoryArith::TheoryArith(context::Context* c, OutputChannel& out) :
  Theory(c, out),
  d_constants(NodeManager::currentNM()),
  d_partialModel(c),
  d_diseq(c),
  d_preprocessed(c),
  d_rewriter(&d_constants)
{
  uint64_t ass_id = partial_model::Assignment::getId();
  Debug("arithsetup") << "Assignment: " << ass_id
                      << std::endl;
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
  //addBound(rel);
  //Anything else?
}

Node TheoryArith::rewrite(TNode n){
  Debug("arith") << "rewrite(" << n << ")" << endl;

  Node result = d_rewriter.rewrite(n);
  Debug("arith-rewrite") << "rewrite("
                         << n << " -> " << result
                         << ")" << endl;
  return result;
}

void TheoryArith::registerTerm(TNode tn){
  Debug("arith") << "registerTerm(" << tn << ")" << endl;

  if(tn.getKind() == kind::BUILTIN) return;

  if(tn.getMetaKind() == metakind::VARIABLE){
    d_partialModel.setAssignment(tn,d_constants.d_ZERO_DELTA);
  }

  //TODO is an atom
  if(isRelationOperator(tn.getKind())){
    Node normalForm = (isNormalized(tn)) ? Node(tn) : rewrite(tn);
    normalForm = (normalForm.getKind() == NOT) ? pushInNegation(normalForm):normalForm;
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
          TypeNode real_type = NodeManager::currentNM()->realType();
          slack = NodeManager::currentNM()->mkVar(real_type);
          d_partialModel.setAssignment(slack,d_constants.d_ZERO_DELTA);
          left.setAttribute(Slack(), slack);
          makeBasic(slack);

          Node slackEqLeft = NodeManager::currentNM()->mkNode(EQUAL,slack,left);
          slackEqLeft.setAttribute(TheoryArithPropagated(), true);
          //TODO this has to be wrong no?
          d_out->lemma(slackEqLeft);

          d_tableau.addRow(slackEqLeft);

          Node rewritten = NodeManager::currentNM()->mkNode(k,slack,right);
          registerAtom(rewritten);
        }else{
          Node rewritten = NodeManager::currentNM()->mkNode(k,slack,right);
          registerAtom(rewritten);
        }
      }else{
        Assert(left.getMetaKind() == metakind::VARIABLE);
        Assert(right.getKind() == CONST_RATIONAL);
        registerAtom(normalForm);
      }
    }
  }
}

/* procedure AssertUpper( x_i <= c_i) */
void TheoryArith::AssertUpper(TNode n, TNode original){
  TNode x_i = n[0];
  Rational dcoeff = Rational(Integer(deltaCoeff(n.getKind())));
  DeltaRational c_i(n[1].getConst<Rational>(), dcoeff);


  Debug("arith") << "AssertUpper(" << x_i << " " << c_i << ")"<< std::endl;


  if(d_partialModel.aboveUpperBound(x_i, c_i, false) ){
    return; //sat
  }
  if(d_partialModel.belowLowerBound(x_i, c_i, true)){
    Node conflict =  NodeManager::currentNM()->mkNode(AND, d_partialModel.getLowerConstraint(x_i), original);
    d_out->conflict(conflict);
    return;
  }

  d_partialModel.setUpperConstraint(x_i,original);
  d_partialModel.setUpperBound(x_i, c_i);

  if(!isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) > c_i){
      update(x_i, c_i);
    }
  }
}

/* procedure AssertLower( x_i >= c_i ) */
void TheoryArith::AssertLower(TNode n, TNode orig){
  TNode x_i = n[0];
  Rational dcoeff = Rational(Integer(deltaCoeff(n.getKind())));
  DeltaRational c_i(n[1].getConst<Rational>(),dcoeff);

  Debug("arith") << "AssertLower(" << x_i << " " << c_i << ")"<< std::endl;

  if(d_partialModel.belowLowerBound(x_i, c_i, false)){
    return; //sat
  }
  if(d_partialModel.aboveUpperBound(x_i, c_i, true)){
    Node conflict =  NodeManager::currentNM()->mkNode(AND, d_partialModel.getUpperConstraint(x_i), orig);
    d_out->conflict(conflict);
    return;
  }

  d_partialModel.setLowerConstraint(x_i,orig);
  d_partialModel.setLowerBound(x_i, c_i);

  if(!isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) < c_i){
      update(x_i, c_i);
    }
  }
}

void TheoryArith::update(TNode x_i, DeltaRational& v){

  DeltaRational assignment_x_i = d_partialModel.getAssignment(x_i);

  Debug("arith") <<"update " << x_i << ": "
                 << assignment_x_i << "|-> " << v << endl;
  DeltaRational diff = v - assignment_x_i;

  for(Tableau::VarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){
    TNode x_j = *basicIter;
    Row* row_j = d_tableau.lookup(x_j);

    Rational& a_ji = row_j->lookup(x_i);

    DeltaRational assignment = d_partialModel.getAssignment(x_j);
    DeltaRational  nAssignment = assignment+(diff * a_ji);
    d_partialModel.setAssignment(x_j, nAssignment);
  }

  d_partialModel.setAssignment(x_i, v);
}

void TheoryArith::pivotAndUpdate(TNode x_i, TNode x_j, DeltaRational& v){
  Row* row_i = d_tableau.lookup(x_i);
  Rational& a_ij = row_i->lookup(x_j);


  DeltaRational betaX_i = d_partialModel.getAssignment(x_i);

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

    if(x_k != x_i){
      DeltaRational a_kj = row_k->lookup(x_j);
      DeltaRational nextAssignment = d_partialModel.getAssignment(x_k) + theta;
      d_partialModel.setAssignment(x_k, nextAssignment);
    }
  }

  d_tableau.pivot(x_i, x_j);
}

TNode TheoryArith::selectSmallestInconsistentVar(){

  for(Tableau::VarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){

    TNode basic = *basicIter;
    if(!d_partialModel.assignmentIsConsistent(basic)){
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
    if(a_ij > d_constants.d_ZERO && d_partialModel.strictlyBelowUpperBound(nonbasic)){
      return nonbasic;
    }else if(a_ij < d_constants.d_ZERO && d_partialModel.strictlyAboveLowerBound(nonbasic)){
      return nonbasic;
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
    if(a_ij < d_constants.d_ZERO && d_partialModel.strictlyBelowUpperBound(nonbasic)){
      return nonbasic;
    }else if(a_ij > d_constants.d_ZERO && d_partialModel.strictlyAboveLowerBound(nonbasic)){
      return nonbasic;
    }
  }

  return TNode::null();
}


Node TheoryArith::updateInconsistentVars(){ //corresponds to Check() in dM06
  Debug("arith") << "updateInconsistentVars" << endl;

  d_partialModel.beginRecordingAssignments();
  while(true){
    TNode x_i = selectSmallestInconsistentVar();
    if(x_i == Node::null()){
      d_partialModel.stopRecordingAssignments(false);
      return Node::null(); //sat
    }
    DeltaRational beta_i = d_partialModel.getAssignment(x_i);

    if(d_partialModel.belowLowerBound(x_i, beta_i, true)){
      DeltaRational l_i = d_partialModel.getLowerBound(x_i);
      TNode x_j = selectSlackBelow(x_i);
      if(x_j == TNode::null() ){
        d_partialModel.stopRecordingAssignments(true);
        return generateConflictBelow(x_i); //unsat
      }
      pivotAndUpdate(x_i, x_j, l_i);
    }else if(d_partialModel.aboveUpperBound(x_i, beta_i, true)){
      DeltaRational u_i = d_partialModel.getUpperBound(x_i);
      TNode x_j = selectSlackAbove(x_i);
      if(x_j == TNode::null() ){
        d_partialModel.stopRecordingAssignments(true);
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
                  << " " << bound << endl;

  nb << bound;

  typedef std::set<TNode>::iterator NonBasicIter;

  for(NonBasicIter nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    TNode nonbasic = *nbi;
    Rational& a_ij = row_i->lookup(nonbasic);

    Assert(a_ij != d_constants.d_ZERO);

    if(a_ij < d_constants.d_ZERO){
      bound =  d_partialModel.getUpperConstraint(nonbasic);
      Debug("arith") << "below 0 "<< nonbasic << " " << bound << endl;
      nb << bound;
    }else{
      bound =  d_partialModel.getLowerConstraint(nonbasic);
      Debug("arith") << " above 0 "<< nonbasic << " " << bound << endl;
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
                 << " " << bound << endl;
  nb << bound;

  typedef std::set<TNode>::iterator NonBasicIter;

  for(NonBasicIter nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    TNode nonbasic = *nbi;
    Rational& a_ij = row_i->lookup(nonbasic);

    Assert(a_ij != d_constants.d_ZERO);

    if(a_ij < d_constants.d_ZERO){
      TNode bound = d_partialModel.getLowerConstraint(nonbasic);
      Debug("arith") << "Lower "<< nonbasic << " " << bound << endl;

      nb << bound;
    }else{
      TNode bound = d_partialModel.getUpperConstraint(nonbasic);
      Debug("arith") << "Upper "<< nonbasic << " " << bound << endl;

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
    return NodeManager::currentNM()->mkNode(NOT,sub);
  }else{
    Node rewritten = rewrite(n);
    Kind k = rewritten.getKind();
    if(!isRelationOperator(k)){
      return rewritten;
    }else if(rewritten[0].getMetaKind() == metakind::VARIABLE){
      return rewritten;
    }else {
      TNode left = rewritten[0];
      TNode right = rewritten[1];
      Node slack;
      if(!left.getAttribute(Slack(), slack)){
        Unreachable("Slack must be have been created!");
      }else{
        return NodeManager::currentNM()->mkNode(k,slack,right);
      }
    }
  }
}

void TheoryArith::check(Effort level){
  Debug("arith") << "TheoryArith::check begun" << std::endl;

  while(!done()){
    Node original = get();
    Node assertion = simulatePreprocessing(original);
    Debug("arith") << "arith assertion(" << original
                   << " \\-> " << assertion << ")" << std::endl;

    d_preprocessed.push_back(assertion);

    switch(assertion.getKind()){
    case LEQ:
      AssertUpper(assertion, original);
      break;
    case GEQ:
      AssertLower(assertion, original);
      break;
    case EQUAL:
      AssertUpper(assertion, original);
      AssertLower(assertion, original);
      break;
    case NOT:
      {
        TNode atom = assertion[0];
        switch(atom.getKind()){
        case LEQ: //(not (LEQ x c)) <=> (GT x c)
          {
            Node pushedin = pushInNegation(assertion);
            AssertLower(pushedin,original);
            break;
          }
        case GEQ: //(not (GEQ x c) <=> (LT x c)
          {
            Node pushedin = pushInNegation(assertion);
            AssertUpper(pushedin,original);
            break;
          }
        case EQUAL:
          d_diseq.push_back(assertion);
          break;
        default:
          Unhandled();
        }
        break;
      }
    default:
      Unhandled();
    }
  }

  if(fullEffort(level)){
    Node possibleConflict = updateInconsistentVars();
    if(possibleConflict != Node::null()){
      Debug("arith") << "Found a conflict " << possibleConflict << endl;
      d_out->conflict(possibleConflict);
    }
  }

  if(fullEffort(level)){
    bool enqueuedCaseSplit = false;
    typedef context::CDList<Node>::const_iterator diseq_iterator;
    for(diseq_iterator i = d_diseq.begin(); i!= d_diseq.end(); ++i){
      Node assertion = *i;
      TNode eq = assertion[0];
      TNode x_i = eq[0];
      TNode c_i = eq[1];
      DeltaRational constant =  c_i.getConst<Rational>();
      if(d_partialModel.getAssignment(x_i) == constant){
        enqueuedCaseSplit = true;
        Node lt = NodeManager::currentNM()->mkNode(LT,x_i,c_i);
        Node gt = NodeManager::currentNM()->mkNode(GT,x_i,c_i);
        Node caseSplit = NodeManager::currentNM()->mkNode(OR, eq, lt, gt);
        //d_out->enqueueCaseSplits(caseSplit);
      }
    }
    if(enqueuedCaseSplit){
      //d_out->caseSplit();
    }
  }
}

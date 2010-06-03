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

struct EagerSplittingTag {};
typedef expr::Attribute<EagerSplittingTag, bool> EagerlySplitUpon;


TheoryArith::TheoryArith(context::Context* c, OutputChannel& out) :
  Theory(c, out),
  d_preprocessed(c),
  d_constants(NodeManager::currentNM()),
  d_partialModel(c),
  d_diseq(c),
  d_rewriter(&d_constants)
{
  uint64_t ass_id = partial_model::Assignment::getId();
  Debug("arithsetup") << "Assignment: " << ass_id << std::endl;

  d_partialModel.beginRecordingAssignments();
}
TheoryArith::~TheoryArith(){
  for(vector<Node>::iterator i=d_variables.begin(); i!= d_variables.end(); ++i){
    Node var = *i;
    Debug("arithgc") << var << endl;
  }
}

void TheoryArith::preRegisterTerm(TNode n) {
  Debug("arith_preregister") << "arith: begin TheoryArith::preRegisterTerm("
                             << n << ")" << endl;

  if(n.getKind() == EQUAL){
    if(!n.getAttribute(EagerlySplitUpon())){
      TNode left = n[0];
      TNode right = n[1];

      Node lt = NodeManager::currentNM()->mkNode(LT, left,right);
      Node gt = NodeManager::currentNM()->mkNode(GT, left,right);
      Node eagerSplit = NodeManager::currentNM()->mkNode(OR, n, lt, gt);

      d_splits.push_back(eagerSplit);


      n.setAttribute(EagerlySplitUpon(), true);
      d_out->augmentingLemma(eagerSplit);
    }
  }

  if(n.getMetaKind() == metakind::VARIABLE){

    setupVariable(n);
  }

  Debug("arith_preregister") << "arith: end TheoryArith::preRegisterTerm("
                             << n << ")" << endl;
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



void registerAtom(TNode rel){
  //addBound(rel);
  //Anything else?

}

/* Requirements:
 * Variable must have been set to be basic.
 * For basic variables the row must have been added to the tableau.
 */
void TheoryArith::setupVariable(TNode x){
  Assert(x.getMetaKind() == kind::metakind::VARIABLE);
  d_variables.push_back(Node(x));

  if(!isBasic(x)){
    d_partialModel.initialize(x,d_constants.d_ZERO_DELTA);
  }else{
    //If the variable is basic, assertions may have already happened and updates
    //may have occured before setting this variable up.

    //This can go away if the tableau creation is done at preregister
    //time instead of register

    DeltaRational q = computeRowValueUsingSavedAssignment(x);
    if(!(q == d_constants.d_ZERO_DELTA)){
      Debug("arith_setup") << "setup("<<x<< " " <<q<<")"<<std::endl;
    }
    d_partialModel.initialize(x,q);

    q = computeRowValueUsingAssignment(x);
    if(!(q == d_constants.d_ZERO_DELTA)){
      Debug("arith_setup") << "setup("<<x<< " " <<q<<")"<<std::endl;
    }
    d_partialModel.setAssignment(x,q);
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
  for(std::set<TNode>::iterator i = row->begin(); i != row->end();++i){
    TNode nonbasic = *i;
    Rational& coeff = row->lookup(nonbasic);
    DeltaRational assignment = d_partialModel.getAssignment(nonbasic);
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
  for(std::set<TNode>::iterator i = row->begin(); i != row->end();++i){
    TNode nonbasic = *i;
    Rational& coeff = row->lookup(nonbasic);
    DeltaRational assignment = d_partialModel.getSavedAssignment(nonbasic);
    sum = sum + (assignment * coeff);
  }
  return sum;
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

          left.setAttribute(Slack(), slack);
          makeBasic(slack);



          Node slackEqLeft = NodeManager::currentNM()->mkNode(EQUAL,slack,left);
          slackEqLeft.setAttribute(TheoryArithPropagated(), true);
          //TODO this has to be wrong no? YES (dejan)
          // d_out->lemma(slackEqLeft);

          Debug("slack") << "slack " << slackEqLeft << endl;

          d_tableau.addRow(slackEqLeft);

          setupVariable(slack);

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
bool TheoryArith::AssertUpper(TNode n, TNode original){
  TNode x_i = n[0];
  Rational dcoeff = Rational(Integer(deltaCoeff(n.getKind())));
  DeltaRational c_i(n[1].getConst<Rational>(), dcoeff);


  Debug("arith") << "AssertUpper(" << x_i << " " << c_i << ")"<< std::endl;


  if(d_partialModel.aboveUpperBound(x_i, c_i, false) ){
    return false; //sat
  }
  if(d_partialModel.belowLowerBound(x_i, c_i, true)){
    Node lbc = d_partialModel.getLowerConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, lbc, original);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
    d_out->conflict(conflict);
    return true;
  }

  d_partialModel.setUpperConstraint(x_i,original);
  d_partialModel.setUpperBound(x_i, c_i);

  if(!isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) > c_i){
      update(x_i, c_i);
    }
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

  if(d_partialModel.belowLowerBound(x_i, c_i, false)){
    return false; //sat
  }
  if(d_partialModel.aboveUpperBound(x_i, c_i, true)){
    Node ubc = d_partialModel.getUpperConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, ubc, original);
    d_out->conflict(conflict);
    Debug("arith") << "AssertLower conflict " << conflict << endl;
    return true;
  }

  d_partialModel.setLowerConstraint(x_i,original);
  d_partialModel.setLowerBound(x_i, c_i);

  if(!isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) < c_i){
      update(x_i, c_i);
    }
  }
  //d_partialModel.printModel(x_i);

  return false;
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

    if(row_j->has(x_i)){
      Rational& a_ji = row_j->lookup(x_i);

      DeltaRational assignment = d_partialModel.getAssignment(x_j);
      DeltaRational  nAssignment = assignment+(diff * a_ji);
      d_partialModel.setAssignment(x_j, nAssignment);
    }
  }

  d_partialModel.setAssignment(x_i, v);

  if(debugTagIsOn("paranoid:check_tableau")){
    checkTableau();
  }
}

void TheoryArith::pivotAndUpdate(TNode x_i, TNode x_j, DeltaRational& v){
  Assert(x_i != x_j);

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

    if(x_k != x_i && row_k->has(x_j)){
      Rational a_kj = row_k->lookup(x_j);
      DeltaRational nextAssignment = d_partialModel.getAssignment(x_k) + (theta * a_kj);
      d_partialModel.setAssignment(x_k, nextAssignment);
    }
  }

  d_tableau.pivot(x_i, x_j);

  if(debugTagIsOn("tableau")){
    d_tableau.printTableau();
  }
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


  while(true){
    if(debugTagIsOn("paranoid:check_tableau")){
      checkTableau();
    }

    TNode x_i = selectSmallestInconsistentVar();
    Debug("arith_update") << "selectSmallestInconsistentVar()=" << x_i << endl;
    if(x_i == Node::null()){
      Debug("arith_update") << "No inconsistent variables" << endl;

      if(debugTagIsOn("paranoid:check_tableau")){
        checkTableau();
      }

      d_partialModel.stopRecordingAssignments(false);
      d_partialModel.beginRecordingAssignments();

      if(debugTagIsOn("paranoid:check_tableau")){
        checkTableau();
      }



      return Node::null(); //sat
    }
    DeltaRational beta_i = d_partialModel.getAssignment(x_i);

    if(d_partialModel.belowLowerBound(x_i, beta_i, true)){
      DeltaRational l_i = d_partialModel.getLowerBound(x_i);
      TNode x_j = selectSlackBelow(x_i);
      if(x_j == TNode::null() ){
        Debug("arith_update") << "conflict below" << endl;

        if(debugTagIsOn("paranoid:check_tableau")){
          checkTableau();
        }

        d_partialModel.stopRecordingAssignments(true);
        d_partialModel.beginRecordingAssignments();

        if(debugTagIsOn("paranoid:check_tableau")){
          checkTableau();
        }

        return generateConflictBelow(x_i); //unsat
      }
      pivotAndUpdate(x_i, x_j, l_i);

    }else if(d_partialModel.aboveUpperBound(x_i, beta_i, true)){
      DeltaRational u_i = d_partialModel.getUpperBound(x_i);
      TNode x_j = selectSlackAbove(x_i);
      if(x_j == TNode::null() ){
        Debug("arith_update") << "conflict above" << endl;

        if(debugTagIsOn("paranoid:check_tableau")){
          checkTableau();
        }

        d_partialModel.stopRecordingAssignments(true);
        d_partialModel.beginRecordingAssignments();

        if(debugTagIsOn("paranoid:check_tableau")){
          checkTableau();
        }
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

  typedef std::set<TNode>::iterator NonBasicIter;

  for(NonBasicIter nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    TNode nonbasic = *nbi;
    Rational& a_ij = row_i->lookup(nonbasic);

    Assert(a_ij != d_constants.d_ZERO);

    if(a_ij < d_constants.d_ZERO){
      bound =  d_partialModel.getUpperConstraint(nonbasic);
      Debug("arith") << "below 0 " << nonbasic << " "
                     << d_partialModel.getAssignment(nonbasic) << " " << bound << endl;
      nb << bound;
    }else{
      bound =  d_partialModel.getLowerConstraint(nonbasic);
      Debug("arith") << " above 0 " << nonbasic << " "
                     << d_partialModel.getAssignment(nonbasic) << " " << bound << endl;
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

  typedef std::set<TNode>::iterator NonBasicIter;

  for(NonBasicIter nbi = row_i->begin(); nbi != row_i->end(); ++nbi){
    TNode nonbasic = *nbi;
    Rational& a_ij = row_i->lookup(nonbasic);

    Assert(a_ij != d_constants.d_ZERO);

    if(a_ij < d_constants.d_ZERO){
      TNode bound = d_partialModel.getLowerConstraint(nonbasic);
      Debug("arith") << "Lower "<< nonbasic << " "
                     << d_partialModel.getAssignment(nonbasic) << " "<< bound << endl;

      nb << bound;
    }else{
      TNode bound = d_partialModel.getUpperConstraint(nonbasic);
      Debug("arith") << "Upper "<< nonbasic << " "
                     << d_partialModel.getAssignment(nonbasic) << " "<< bound << endl;

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
    if(sub.getKind() == NOT){
      return sub[0];
    }else{
      return NodeManager::currentNM()->mkNode(NOT,sub);
    }
  }else{
    Node rewritten = rewrite(n);
    Kind k = rewritten.getKind();

    if(rewritten.getKind() == NOT){
      Node sub = simulatePreprocessing(rewritten[0]);
      if(sub.getKind() == NOT){
        return sub[0];
      }else{
        return NodeManager::currentNM()->mkNode(NOT,sub);
      }
    } else if(!isRelationOperator(k)){
      if(rewritten.getKind() == CONST_BOOLEAN){
        Warning() << "How did I get a const boolean here" << endl;
        Warning() << "offending node has id " << n.getId() << endl;
        Warning() << "offending node is "<< n << endl;
        return rewritten;
      }else{
        Unreachable("Unexpected type!");
      }
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

  bool conflictDuringAnAssert = false;

  while(!done()){
    //checkTableau();
    Node original = get();
    Node assertion = simulatePreprocessing(original);
    Debug("arith_assertions") << "arith assertion(" << original
                              << " \\-> " << assertion << ")" << std::endl;

    d_preprocessed.push_back(assertion);

    switch(assertion.getKind()){
    case CONST_BOOLEAN:
      Warning() << "No bools should be reached dagnabbit" << endl;
      break;
    case LEQ:
      conflictDuringAnAssert = AssertUpper(assertion, original);
      break;
    case GEQ:
      conflictDuringAnAssert = AssertLower(assertion, original);
      break;
    case EQUAL:
      conflictDuringAnAssert = AssertUpper(assertion, original);
      conflictDuringAnAssert |= AssertLower(assertion, original);
      break;
    case NOT:
      {
        TNode atom = assertion[0];
        switch(atom.getKind()){
        case LEQ: //(not (LEQ x c)) <=> (GT x c)
          {
            Node pushedin = pushInNegation(assertion);
            conflictDuringAnAssert = AssertLower(pushedin,original);
            break;
          }
        case GEQ: //(not (GEQ x c) <=> (LT x c)
          {
            Node pushedin = pushInNegation(assertion);
            conflictDuringAnAssert = AssertUpper(pushedin,original);
            break;
          }
        case EQUAL:
          d_diseq.push_back(assertion);
          break;
        case CONST_BOOLEAN:
          Warning() << "No bools should be reached dagnabbit" << endl;
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
  if(conflictDuringAnAssert){
    //clear the queue;
    while(!done()) {
      get();
    }
    //return
    return;
  }

  if(fullEffort(level)){
    Node possibleConflict = updateInconsistentVars();
    if(possibleConflict != Node::null()){
      Debug("arith_conflict") << "Found a conflict "
                              << possibleConflict << endl;
      d_out->conflict(possibleConflict);
    }else{
      Debug("arith_conflict") << "No conflict found" << endl;
    }
  }

  if(fullEffort(level)){
    bool enqueuedCaseSplit = false;
    typedef context::CDList<Node>::const_iterator diseq_iterator;
    for(diseq_iterator i = d_diseq.begin(); i!= d_diseq.end(); ++i){

      Node assertion = *i;
      Debug("arith") << "splitting"  << assertion << endl;
      TNode eq = assertion[0];
      TNode x_i = eq[0];
      TNode c_i = eq[1];
      DeltaRational constant =  c_i.getConst<Rational>();
      Debug("arith") << "broken apart" << endl;
      if(d_partialModel.getAssignment(x_i) == constant){
        Debug("arith") << "here" << endl;
        enqueuedCaseSplit = true;
        Node lt = NodeManager::currentNM()->mkNode(LT,x_i,c_i);
        Node gt = NodeManager::currentNM()->mkNode(GT,x_i,c_i);
        Node caseSplit = NodeManager::currentNM()->mkNode(OR, eq, lt, gt);
        //d_out->enqueueCaseSplits(caseSplit);
        Debug("arith") << "finished" << caseSplit << endl;
      }
      Debug("arith") << "end of for loop" << endl;

    }
    Debug("arith") << "finished" << endl;

    if(enqueuedCaseSplit){
      //d_out->caseSplit();
      //Warning() << "Outstanding case split in theory arith" << endl;
    }
  }

  Debug("arith") << "TheoryArith::check end" << std::endl;

}

/**
 * This check is quite expensive.
 * It should be wrapped in a debugTagIsOn guard.
 *   if(debugTagIsOn("paranoid:check_tableau")){
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
    for(std::set<TNode>::iterator nonbasicIter = row_k->begin();
        nonbasicIter != row_k->end();
        ++nonbasicIter){
      TNode nonbasic = *nonbasicIter;
      Rational& coeff = row_k->lookup(nonbasic);
      DeltaRational beta = d_partialModel.getAssignment(nonbasic);
      Debug("paranoid:check_tableau") << nonbasic << beta << coeff<<endl;
      sum = sum + (beta*coeff);
    }
    DeltaRational shouldBe = d_partialModel.getAssignment(basic);
    Debug("paranoid:check_tableau") << "ending row" << sum << "," << shouldBe << endl;

    Assert(sum == shouldBe);
  }
}

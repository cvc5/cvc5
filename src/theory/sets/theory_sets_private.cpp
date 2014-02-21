/*********************                                                        */
/*! \file theory_sets_private.cpp
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2013-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Sets theory implementation.
 **/

#include "theory/sets/theory_sets.h"
#include "theory/sets/theory_sets_private.h"

#include "theory/sets/options.h"
#include "theory/sets/expr_patterns.h" // ONLY included here

#include "util/result.h"

using namespace std;
using namespace CVC4::expr::pattern;

namespace CVC4 {
namespace theory {
namespace sets {

const char* element_of_str = " \u2208 ";

/**************************** TheorySetsPrivate *****************************/
/**************************** TheorySetsPrivate *****************************/
/**************************** TheorySetsPrivate *****************************/

void TheorySetsPrivate::check(Theory::Effort level) {

  CodeTimer checkCodeTimer(d_statistics.d_checkTime);

  while(!d_external.done() && !d_conflict) {
    // Get all the assertions
    Assertion assertion = d_external.get();
    TNode fact = assertion.assertion;

    Debug("sets") << "\n\n[sets] TheorySetsPrivate::check(): processing "
                  << fact << std::endl;

    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];

    // Solve each
    switch(atom.getKind()) {
    case kind::EQUAL:
      Debug("sets") << atom[0] << " should " << (polarity ? "":"NOT ")
                    << "be equal to " << atom[1] << std::endl;
      assertEquality(fact, fact, /* learnt = */ false);
      break;

    case kind::IN:
      Debug("sets") << atom[0] << " should " << (polarity ? "":"NOT ")
                    << "be in " << atom[1] << std::endl;
      assertMemebership(fact, fact, /* learnt = */ false);
      break;

    default:
      Unhandled(fact.getKind());
    }
    finishPropagation();

    Debug("sets") << "[sets]  in conflict = " << d_conflict << std::endl;

    if(d_conflict && !d_equalityEngine.consistent()) return;
    Assert(!d_conflict);
    Assert(d_equalityEngine.consistent());
  }

  Debug("sets") << "[sets]  is complete = " << isComplete() << std::endl;

  if( (Theory::EFFORT_FULL || options::setsEagerLemmas() ) && !isComplete()) {
    d_external.d_out->lemma(getLemma());
  }

  return;
}/* TheorySetsPrivate::check() */


void TheorySetsPrivate::assertEquality(TNode fact, TNode reason, bool learnt)
{
  Debug("sets-assert") << "\n[sets-assert] adding equality: " << fact
                    << ", " << reason
                    << ", " << learnt << std::endl;

  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];

  // fact already holds
  if( holds(atom, polarity) ) {
    Debug("sets-assert") << "[sets-assert]   already present, skipping" << std::endl;
    return;
  }

  // assert fact & check for conflict
  if(learnt) {
    registerReason(reason, /*save=*/ true);
  }
  d_equalityEngine.assertEquality(atom, polarity, reason);

  if(!d_equalityEngine.consistent()) {
    Debug("sets-assert") << "[sets-assert]   running into a conflict" << std::endl;
    d_conflict = true;
    return;
  }

  if(!polarity && atom[0].getType().isSet()) {
    addToPending(atom);
  }

}/* TheorySetsPrivate::assertEquality() */


void TheorySetsPrivate::assertMemebership(TNode fact, TNode reason, bool learnt)
{
  Debug("sets-assert") << "\n[sets-assert] adding membership: " << fact
                       << ", " << reason
                       << ", " << learnt << std::endl;

  bool polarity = fact.getKind() == kind::NOT ? false : true;
  TNode atom = polarity ? fact : fact[0];

  // fact already holds
  if( holds(atom, polarity) ) {
    Debug("sets-assert") << "[sets-assert]   already present, skipping" << std::endl;
    return;
  }

  // assert fact & check for conflict
  if(learnt) {
    registerReason(reason, true);
  }
  d_equalityEngine.assertPredicate(atom, polarity, reason);

  if(!d_equalityEngine.consistent()) {
    Debug("sets-assert") << "[sets-assert]   running into a conflict" << std::endl;
    d_conflict = true;
    return;
  }

  // update term info data structures
  d_termInfoManager->notifyMembership(fact);

  // propagation
  TNode x = d_equalityEngine.getRepresentative(atom[0]);
  eq::EqClassIterator j(d_equalityEngine.getRepresentative(atom[1]),
                        &d_equalityEngine);
  TNode S = (*j);
  Node cur_atom = IN(x, S);

  /**
   * It is sufficient to do emptyset propagation outside the loop as
   * constant term is guaranteed to be class representative.
   */
  if(polarity && S.getKind() == kind::EMPTYSET) {
    Debug("sets-prop") << "[sets-prop]  something in empty set? conflict."
                       << std::endl;
    learnLiteral(cur_atom, false, cur_atom);
    Assert(d_conflict);
    return;
  }

  for(; !j.isFinished(); ++j) {
    TNode S = (*j);
    Node cur_atom = IN(x, S);

    // propagation : children
    Debug("sets-prop") << "[sets-prop] Propagating 'down' for "
                       << x << element_of_str << S << std::endl;
    if(S.getKind() == kind::UNION ||
       S.getKind() == kind::INTERSECTION ||
       S.getKind() == kind::SETMINUS ||
       S.getKind() == kind::SET_SINGLETON) {
      doSettermPropagation(x, S);
      if(d_conflict) return;
    }// propagation: children


    // propagation : parents
    Debug("sets-prop") << "[sets-prop] Propagating 'up' for "
                       << x << element_of_str << S << std::endl;
    const CDTNodeList* parentList = d_termInfoManager->getParents(S);
    for(typeof(parentList->begin()) k = parentList->begin();
        k != parentList->end(); ++k) {
      doSettermPropagation(x, *k);
      if(d_conflict) return;
    }// propagation : parents


  }//j loop

}/* TheorySetsPrivate::assertMemebership() */


void TheorySetsPrivate::doSettermPropagation(TNode x, TNode S)
{
  Debug("sets-prop") << "[sets-prop] doSettermPropagation("
                     << x << ", " << S << std::endl;

  Assert(S.getType().isSet() && S.getType().getSetElementType() == x.getType());

  Node literal, left_literal, right_literal;

  // axiom: literal <=> left_literal AND right_literal
  switch(S.getKind()) {
  case kind::INTERSECTION:
    literal       =       IN(x, S)      ;
    left_literal  =       IN(x, S[0])   ;
    right_literal =       IN(x, S[1])   ;
    break;
  case kind::UNION:
    literal       = NOT(  IN(x, S)     );
    left_literal  = NOT(  IN(x, S[0])  );
    right_literal = NOT(  IN(x, S[1])  );
    break;
  case kind::SETMINUS:
    literal       =       IN(x, S)      ;
    left_literal  =       IN(x, S[0])   ;
    right_literal = NOT(  IN(x, S[1])  );
    break;
  case kind::SET_SINGLETON: {
    Node atom = IN(x, S);
    if(holds(atom, true)) {
      learnLiteral(EQUAL(x, S[0]), true, atom);
    } else if(holds(atom, false)) {
      learnLiteral(EQUAL(x, S[0]), false, NOT(atom));
    }
    return;
  }
  default:
    Unhandled();
  }

  Debug("sets-prop-details")
    << "[sets-prop-details]   " << literal << " IFF " << left_literal
    << " AND " << right_literal << std::endl;

  Debug("sets-prop-details")
    << "[sets-prop-details]   "
    << (holds(literal) ? "yes" : (holds(literal.negate()) ? " no" : " _ "))
    << " IFF "
    << (holds(left_literal) ? "yes" : (holds(left_literal.negate()) ? "no " : " _ "))
    << " AND "
    << (holds(right_literal) ? "yes" : (holds(right_literal.negate()) ? "no " : " _ "))
    << std::endl;

  Assert( present( IN(x, S)    ) ||
          present( IN(x, S[0]) ) ||
          present( IN(x, S[1]) ) );

  if( holds(literal) ) {
    // 1a. literal => left_literal
    Debug("sets-prop") << "[sets-prop]  ... via case 1a. ..." << std::endl;
    learnLiteral(left_literal, literal);
    if(d_conflict) return;

    // 1b. literal => right_literal
    Debug("sets-prop") << "[sets-prop]  ... via case 1b. ..." << std::endl;
    learnLiteral(right_literal, literal);
    if(d_conflict) return;

    // subsumption requirement met, exit
    return;
  }
  else if( holds(literal.negate() ) ) {
    // 4. neg(literal), left_literal => neg(right_literal)
    if( holds(left_literal) ) {
      Debug("sets-prop") << "[sets-prop]  ... via case 4. ..." << std::endl;
      learnLiteral(right_literal.negate(), AND( literal.negate(),
                                                left_literal) );
      if(d_conflict) return;
    }

    // 5. neg(literal), right_literal => neg(left_literal)
    if( holds(right_literal) ) {
      Debug("sets-prop") << "[sets-prop]  ... via case 5. ..." << std::endl;
      learnLiteral(left_literal.negate(), AND( literal.negate(),
                                               right_literal) );
      if(d_conflict) return;
    }
  }
  else {
    // 2,3. neg(left_literal) v neg(right_literal) => neg(literal)
    if(holds(left_literal.negate())) {
      Debug("sets-prop") << "[sets-prop]  ... via case 2. ..." << std::endl;
      learnLiteral(literal.negate(), left_literal.negate());
      if(d_conflict) return;
    }
    else if(holds(right_literal.negate())) {
      Debug("sets-prop") << "[sets-prop]  ... via case 3. ..." << std::endl;
      learnLiteral(literal.negate(), right_literal.negate());
      if(d_conflict) return;
    }

    // 6. the axiom itself:
    else if(holds(left_literal) && holds(right_literal)) {
      Debug("sets-prop") << "[sets-prop]  ... via case 6. ..." << std::endl;
      learnLiteral(literal, AND(left_literal, right_literal) );
      if(d_conflict) return;
    }
  }

  // check fulfilling rule
  Node n;
  switch(S.getKind()) {
  case kind::UNION:
    if( holds(IN(x, S)) &&
        !present( IN(x, S[0]) ) )
      addToPending( IN(x, S[0]) );
    break;
  case kind::SETMINUS: // intentional fallthrough
  case kind::INTERSECTION:
    if( holds(IN(x, S[0])) &&
        !present( IN(x, S[1]) ))
      addToPending( IN(x, S[1]) );
    break;
  default:
    Assert(false, "MembershipEngine::doSettermPropagation");
  }
}


void TheorySetsPrivate::learnLiteral(TNode atom, bool polarity, Node reason) {
  Debug("sets-learn") << "[sets-learn] learnLiteral(" << atom
                      << ", " << polarity << ")" << std::endl;

  if( holds(atom, polarity) ) {
    Debug("sets-learn") << "[sets-learn] \u2514 already known, skipping" << std::endl;
    return;
  }

  if( holds(atom, !polarity) ) {
    Debug("sets-learn") << "[sets-learn] \u2514 conflict found" << std::endl;

    registerReason(reason, /*save=*/ true);

    if(atom.getKind() == kind::EQUAL) {
      d_equalityEngine.assertEquality(atom, polarity, reason);
    } else {
      d_equalityEngine.assertPredicate(atom, polarity, reason);
    }
    Assert(d_conflict);       // should be marked due to equality engine
    return;
  }

  Assert(atom.getKind() == kind::EQUAL || atom.getKind() == kind::IN);

  Node learnt_literal = polarity ? Node(atom) : NOT(atom);
  d_propagationQueue.push_back( make_pair(learnt_literal, reason) );
}

/********************** Helper functions ***************************/
/********************** Helper functions ***************************/
/********************** Helper functions ***************************/

Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;

  for (unsigned i = 0; i < conjunctions.size(); ++i) {
    TNode t = conjunctions[i];

    if (t.getKind() == kind::AND) {
      for(TNode::iterator child_it = t.begin();
          child_it != t.end(); ++child_it) {
        Assert((*child_it).getKind() != kind::AND);
        all.insert(*child_it);
      }
    }
    else {
      all.insert(t);
    }

  }

  Assert(all.size() > 0);

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}/* mkAnd() */


TheorySetsPrivate::Statistics::Statistics() :
  d_checkTime("theory::sets::time") {
  StatisticsRegistry::registerStat(&d_checkTime);
}


TheorySetsPrivate::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_checkTime);
}


bool TheorySetsPrivate::present(TNode atom) {
  return holds(atom) || holds(atom.notNode());
}


bool TheorySetsPrivate::holds(TNode atom, bool polarity) {
  Node polarity_atom = NodeManager::currentNM()->mkConst<bool>(polarity);

  Node atomModEq = NodeManager::currentNM()->mkNode
    (atom.getKind(), d_equalityEngine.getRepresentative(atom[0]),
     d_equalityEngine.getRepresentative(atom[1]) );

  d_equalityEngine.addTerm(atomModEq);

  return d_equalityEngine.areEqual(atomModEq, polarity_atom);
}


void TheorySetsPrivate::registerReason(TNode reason, bool save)
{
  if(save) d_nodeSaver.insert(reason);

  if(reason.getKind() == kind::AND) {
    Assert(reason.getNumChildren() == 2);
    registerReason(reason[0], false);
    registerReason(reason[1], false);
  } else if(reason.getKind() == kind::NOT) {
    registerReason(reason[0], false);
  } else if(reason.getKind() == kind::IN) {
    d_equalityEngine.addTerm(reason);
    Assert(present(reason));
  } else if(reason.getKind() == kind::EQUAL) {
    d_equalityEngine.addTerm(reason);
    Assert(present(reason));
  } else if(reason.getKind() == kind::CONST_BOOLEAN) {
    // That's OK, already in EqEngine
  } else {
    Unhandled();
  }
}

void TheorySetsPrivate::finishPropagation()
{
  while(!d_conflict && !d_settermPropagationQueue.empty()) {
    std::pair<TNode,TNode> np = d_settermPropagationQueue.front();
    d_settermPropagationQueue.pop();
    doSettermPropagation(np.first, np.second);
  }
  while(!d_conflict && !d_propagationQueue.empty()) {
    std::pair<Node,Node> np = d_propagationQueue.front();
    d_propagationQueue.pop();
    TNode atom = np.first.getKind() == kind::NOT ? np.first[0] : np.first;
    if(atom.getKind() == kind::IN) {
      assertMemebership(np.first, np.second, /* learnt = */ true);
    } else {
      assertEquality(np.first, np.second, /* learnt = */ true);
    }
  }
}

void TheorySetsPrivate::addToPending(Node n) {
  if(d_pendingEverInserted.find(n) == d_pendingEverInserted.end()) {
    if(n.getKind() == kind::IN) {
      d_pending.push(n);
    } else {
      Assert(n.getKind() == kind::EQUAL);
      d_pendingDisequal.push(n);
    }
    d_pendingEverInserted.insert(n);
  }
}

bool TheorySetsPrivate::isComplete() {
  while(!d_pending.empty() && present(d_pending.front()))
    d_pending.pop();
  return d_pending.empty() && d_pendingDisequal.empty();
}

Node TheorySetsPrivate::getLemma() {
  Assert(!d_pending.empty() || !d_pendingDisequal.empty());

  Node lemma;

  if(!d_pending.empty()) {
    Node n = d_pending.front();
    d_pending.pop();

    Assert(!present(n));
    Assert(n.getKind() == kind::IN);

    lemma = OR(n, NOT(n));
  } else {
    Node n = d_pendingDisequal.front();
    d_pendingDisequal.pop();

    Assert(n.getKind() == kind::EQUAL && n[0].getType().isSet());
    Node x = NodeManager::currentNM()->mkSkolem("sde_$$", n[0].getType().getSetElementType());
    Node l1 = IN(x, n[0]), l2 = IN(x, n[1]);

    // d_equalityEngine.addTerm(x);
    // d_equalityEngine.addTerm(l1);
    // d_equalityEngine.addTerm(l2);
    // d_terms.insert(x);

    lemma = OR(n, AND(l1, NOT(l2)), AND(NOT(l1), l2));
  }

  Debug("sets-lemma") << "[sets-lemma] " << lemma << std::endl;

  return  lemma;
}


TheorySetsPrivate::TheorySetsPrivate(TheorySets& external,
                                     context::Context* c,
                                     context::UserContext* u):
  d_external(external),
  d_notify(*this),
  d_equalityEngine(d_notify, c, "theory::sets::TheorySetsPrivate"),
  d_conflict(c),
  d_termInfoManager(NULL),
  d_propagationQueue(c),
  d_settermPropagationQueue(c),
  d_nodeSaver(c),
  d_pending(u),
  d_pendingDisequal(u),
  d_pendingEverInserted(u)
{
  d_termInfoManager = new TermInfoManager(*this, c, &d_equalityEngine);

  d_equalityEngine.addFunctionKind(kind::UNION);
  d_equalityEngine.addFunctionKind(kind::INTERSECTION);
  d_equalityEngine.addFunctionKind(kind::SETMINUS);

  d_equalityEngine.addFunctionKind(kind::IN);
  d_equalityEngine.addFunctionKind(kind::SUBSET);
}/* TheorySetsPrivate::TheorySetsPrivate() */

TheorySetsPrivate::~TheorySetsPrivate()
{
  delete d_termInfoManager;
}



void TheorySetsPrivate::propagate(Theory::Effort e)
{
  return;
}

bool TheorySetsPrivate::propagate(TNode literal) {
  Debug("sets-prop") << " propagate(" << literal  << ")" << std::endl;

  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("sets-prop") << "TheoryUF::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }

  // Propagate out
  bool ok = d_external.d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }

  return ok;
}/* TheorySetsPropagate::propagate(TNode) */


void TheorySetsPrivate::conflict(TNode a, TNode b)
{
  if (a.getKind() == kind::CONST_BOOLEAN) {
    d_conflictNode = explain(a.iffNode(b));
  } else {
    d_conflictNode = explain(a.eqNode(b));
  }
  d_external.d_out->conflict(d_conflictNode);
  Debug("sets") << "[sets] conflict: " << a << " iff " << b
                << ", explaination " << d_conflictNode << std::endl;
  d_conflict = true;
}

Node TheorySetsPrivate::explain(TNode literal)
{
  Debug("sets") << "TheorySetsPrivate::explain(" << literal << ")"
                << std::endl;

  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  std::vector<TNode> assumptions;

  if(atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
     d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else if(atom.getKind() == kind::IN) {
    if( !d_equalityEngine.hasTerm(atom)) {
      d_equalityEngine.addTerm(atom);
    }
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
  } else {
    Debug("sets") << "unhandled: " << literal << "; (" << atom << ", "
                  << polarity << "); kind" << atom.getKind() << std::endl;
    Unhandled();
  }

  return mkAnd(assumptions);
}

void TheorySetsPrivate::preRegisterTerm(TNode node)
{
  Debug("sets") << "TheorySetsPrivate::preRegisterTerm(" << node << ")"
                << std::endl;

  switch(node.getKind()) {
  case kind::EQUAL:
    // TODO: what's the point of this
    d_equalityEngine.addTriggerEquality(node);
    break;
  case kind::IN:
    // TODO: what's the point of this
    d_equalityEngine.addTriggerPredicate(node);
    break;
  default:
    d_termInfoManager->addTerm(node);
    d_equalityEngine.addTriggerTerm(node, THEORY_SETS);
    // d_equalityEngine.addTerm(node);
  }
  if(node.getKind() == kind::SET_SINGLETON) {
    Node true_node = NodeManager::currentNM()->mkConst<bool>(true);
    learnLiteral(IN(node[0], node), true, true_node);
    //intentional fallthrough
  }
}



/**************************** eq::NotifyClass *****************************/
/**************************** eq::NotifyClass *****************************/
/**************************** eq::NotifyClass *****************************/


bool TheorySetsPrivate::NotifyClass::eqNotifyTriggerEquality(TNode equality, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerEquality: equality = " << equality << " value = " << value << std::endl;
  if (value) {
    return d_theory.propagate(equality);
  } else {
    // We use only literal triggers so taking not is safe
    return d_theory.propagate(equality.notNode());
  }
}

bool TheorySetsPrivate::NotifyClass::eqNotifyTriggerPredicate(TNode predicate, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerPredicate: predicate = " << predicate << " value = " << value << std::endl;
  if (value) {
    return d_theory.propagate(predicate);
  } else {
    return d_theory.propagate(predicate.notNode());
  }
}

bool TheorySetsPrivate::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerTermEquality: tag = " << tag << " t1 = " << t1 << "  t2 = " << t2 << "  value = " << value << std::endl;
  if(value) {
    d_theory.d_termInfoManager->mergeTerms(t1, t2);
  }
  return true;
}

void TheorySetsPrivate::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyConstantTermMerge " << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.conflict(t1, t2);
}

void TheorySetsPrivate::NotifyClass::eqNotifyNewClass(TNode t)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyNewClass:" << " t = " << t << std::endl;
}

void TheorySetsPrivate::NotifyClass::eqNotifyPreMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyPreMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
}

void TheorySetsPrivate::NotifyClass::eqNotifyPostMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
}

void TheorySetsPrivate::NotifyClass::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyDisequal:" << " t1 = " << t1 << " t2 = " << t2 << " reason = " << reason << std::endl;
}


/**************************** TermInfoManager *****************************/
/**************************** TermInfoManager *****************************/
/**************************** TermInfoManager *****************************/

void TheorySetsPrivate::TermInfoManager::mergeLists
(CDTNodeList* la, const CDTNodeList* lb) const {
  // straight from theory/arrays/array_info.cpp
  std::set<TNode> temp;
  CDTNodeList::const_iterator it;
  for(it = la->begin() ; it != la->end(); it++ ) {
    temp.insert((*it));
  }

  for(it = lb->begin() ; it!= lb->end(); it++ ) {
    if(temp.count(*it) == 0) {
      la->push_back(*it);
    }
  }
}

TheorySetsPrivate::TermInfoManager::TermInfoManager
(TheorySetsPrivate& theory, context::Context* satContext, eq::EqualityEngine* eq):
  d_theory(theory),
  d_context(satContext),
  d_eqEngine(eq),
  d_terms(satContext),
  d_info()
{ }

TheorySetsPrivate::TermInfoManager::~TermInfoManager() {
  for( typeof(d_info.begin()) it = d_info.begin();
       it != d_info.end(); ++it) {
    delete (*it).second;
  }
}

void TheorySetsPrivate::TermInfoManager::notifyMembership(TNode fact) {
  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];

  TNode x = d_eqEngine->getRepresentative(atom[0]);
  TNode S = d_eqEngine->getRepresentative(atom[1]);

  Debug("sets-terminfo") << "[sets-terminfo] Adding membership " << x
                         << " in " << S << " " << polarity << std::endl;

  d_info[S]->addToElementList(x, polarity);
}

const CDTNodeList* TheorySetsPrivate::TermInfoManager::getParents(TNode x) {
  return d_info[x]->parents;
}

void TheorySetsPrivate::TermInfoManager::addTerm(TNode n) {
  unsigned numChild = n.getNumChildren();

  if(!d_terms.contains(n)) {
    d_terms.insert(n);
    d_info[n] = new TheorySetsTermInfo(d_context);
  }

  if(n.getKind() == kind::UNION ||
     n.getKind() == kind::INTERSECTION ||
     n.getKind() == kind::SETMINUS ||
     n.getKind() == kind::SET_SINGLETON) {

    for(unsigned i = 0; i < numChild; ++i) {
      if(d_terms.contains(n[i])) {
        Debug("sets-parent") << "Adding " << n << " to parent list of "
                             << n[i] << std::endl;
        d_info[n[i]]->parents->push_back(n);
      }
    }

  }
}

void TheorySetsPrivate::TermInfoManager::pushToSettermPropagationQueue
(CDTNodeList* l, TNode S, bool polarity)
{
  for(typeof(l->begin()) i = l->begin(); i != l->end(); ++i) {
    Debug("sets-prop") << "[sets-terminfo]  setterm todo: "
                       << IN(*i, d_eqEngine->getRepresentative(S))
                       << std::endl;

    d_eqEngine->addTerm(IN(d_eqEngine->getRepresentative(*i),
                           d_eqEngine->getRepresentative(S)));

    for(eq::EqClassIterator j(d_eqEngine->getRepresentative(S), d_eqEngine);
        !j.isFinished(); ++j) {

      TNode x = (*i);
      TNode S = (*j);
      Node cur_atom = IN(x, S);

      // propagation : empty set
      if(polarity && S.getKind() == kind::EMPTYSET) {
        Debug("sets-prop") << "[sets-prop]  something in empty set? conflict."
                           << std::endl;
        d_theory.learnLiteral(cur_atom, false, cur_atom);
        return;
      }// propagation: empty set

      // propagation : children
      if(S.getKind() == kind::UNION ||
         S.getKind() == kind::INTERSECTION ||
         S.getKind() == kind::SETMINUS ||
         S.getKind() == kind::SET_SINGLETON) {
        d_theory.d_settermPropagationQueue.push_back(std::make_pair(x, S));
      }// propagation: children

      // propagation : parents
      const CDTNodeList* parentList = getParents(S);
      for(typeof(parentList->begin()) k = parentList->begin();
          k != parentList->end(); ++k) {
        d_theory.d_settermPropagationQueue.push_back(std::make_pair(x, *k));
      }// propagation : parents


    }//j loop

  }

}

void TheorySetsPrivate::TermInfoManager::mergeTerms(TNode a, TNode b) {
  // merge b into a

  if(!a.getType().isSet()) return;

  Debug("sets-terminfo") << "[sets-terminfo] Merging (into) a = " << a
                         << ", b = " << b << std::endl;
  Debug("sets-terminfo") << "[sets-terminfo] reps"
                         << ", a: " << d_eqEngine->getRepresentative(a)
                         << ", b: " << d_eqEngine->getRepresentative(b)
                         << std::endl;

  typeof(d_info.begin()) ita = d_info.find(a);
  typeof(d_info.begin()) itb = d_info.find(b);

  Assert(ita != d_info.end());
  Assert(itb != d_info.end());

  pushToSettermPropagationQueue( (*ita).second->elementsInThisSet, b, true );
  pushToSettermPropagationQueue( (*ita).second->elementsNotInThisSet, b, false );
  pushToSettermPropagationQueue( (*itb).second->elementsNotInThisSet, a, false );
  pushToSettermPropagationQueue( (*itb).second->elementsInThisSet, a, true );

  mergeLists((*ita).second->elementsInThisSet,
             (*itb).second->elementsInThisSet);

  mergeLists((*ita).second->elementsNotInThisSet,
             (*itb).second->elementsNotInThisSet);
}


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

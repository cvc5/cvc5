/*********************                                                        */
/*! \file theory_arrays.cpp
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of arrays.
 **
 ** Implementation of the theory of arrays.
 **/


#include "theory/arrays/theory_arrays.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include <map>

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::arrays;


TheoryArrays::TheoryArrays(Context* c, OutputChannel& out, Valuation valuation) :
  Theory(THEORY_ARRAY, c, out, valuation),
  d_ccChannel(this),
  d_cc(c, &d_ccChannel),
  d_unionFind(c),
  d_backtracker(c),
  d_infoMap(c,&d_backtracker),
  d_disequalities(c),
  d_equalities(c),
  d_prop_queue(c),
  d_atoms(),
  d_explanations(c),
  d_conflict(),
  d_numRow("theory::arrays::number of Row lemmas", 0),
  d_numExt("theory::arrays::number of Ext lemmas", 0),
  d_numProp("theory::arrays::number of propagations", 0),
  d_numExplain("theory::arrays::number of explanations", 0),
  d_checkTimer("theory::arrays::checkTime"),
  d_donePreregister(false)
{
  //d_backtracker = new Backtracker<TNode>(c);
  //d_infoMap = ArrayInfo(c, d_backtracker);

  StatisticsRegistry::registerStat(&d_numRow);
  StatisticsRegistry::registerStat(&d_numExt);
  StatisticsRegistry::registerStat(&d_numProp);
  StatisticsRegistry::registerStat(&d_numExplain);
  StatisticsRegistry::registerStat(&d_checkTimer);


}


TheoryArrays::~TheoryArrays() {

  StatisticsRegistry::unregisterStat(&d_numRow);
  StatisticsRegistry::unregisterStat(&d_numExt);
  StatisticsRegistry::unregisterStat(&d_numProp);
  StatisticsRegistry::unregisterStat(&d_numExplain);
  StatisticsRegistry::unregisterStat(&d_checkTimer);

}


void TheoryArrays::addSharedTerm(TNode t) {
  Debug("arrays") << "Arrays::addSharedTerm(): "
                  << t << endl;
}


void TheoryArrays::notifyEq(TNode lhs, TNode rhs) {
}

void TheoryArrays::notifyCongruent(TNode a, TNode b) {
  Debug("arrays") << "Arrays::notifyCongruent(): "
       << a << " = " << b << endl;
  if(!d_conflict.isNull()) {
    return;
  }
  merge(a,b);
}


void TheoryArrays::check(Effort e) {
  TimerStat::CodeTimer codeTimer(d_checkTimer);

  if(!d_donePreregister ) {
    // only start looking for lemmas after preregister on all input terms
    // has been called
   return;
  }

  Debug("arrays") <<"Arrays::start check ";
  while(!done()) {
    Node assertion = get();
    Debug("arrays") << "Arrays::check(): " << assertion << endl;

    switch(assertion.getKind()) {
    case kind::EQUAL:
    case kind::IFF:
      d_cc.addEquality(assertion);
      if(!d_conflict.isNull()) {
        // addEquality can cause a notify congruent which calls merge
        // which can lead to a conflict
        Node conflict = constructConflict(d_conflict);
        d_conflict = Node::null();
        d_out->conflict(conflict, false);
        return;
      }
      merge(assertion[0], assertion[1]);
      break;
    case kind::NOT:
    {
      Assert(assertion[0].getKind() == kind::EQUAL ||
         assertion[0].getKind() == kind::IFF );
      Node a = assertion[0][0];
      Node b = assertion[0][1];
      addDiseq(assertion[0]);

      d_cc.addTerm(a);
      d_cc.addTerm(b);

      if(!d_conflict.isNull()) {
        // we got notified through notifyCongruent which called merge
        // after addTerm since we weren't watching a or b before
        Node conflict = constructConflict(d_conflict);
        d_conflict = Node::null();
        d_out->conflict(conflict, false);
        return;
      }
      else if(find(a) == find(b)) {
        Node conflict = constructConflict(assertion[0]);
        d_out->conflict(conflict, false);
        return;
        }
      Assert(!d_cc.areCongruent(a,b));
      if(a.getType().isArray()) {
        queueExtLemma(a, b);
      }
      break;
    }
    default:
      Unhandled(assertion.getKind());
    }

  }

  if(fullEffort(e)) {
    // generate the lemmas on the worklist
    //while(!d_RowQueue.empty() || ! d_extQueue.empty()) {
    dischargeLemmas();
    Debug("arrays-lem")<<"Arrays::discharged lemmas "<<d_RowQueue.size()<<"\n";
    //}
  }
  Debug("arrays") << "Arrays::check(): done" << endl;
}

Node TheoryArrays::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( d_valuation.getValue(n[0]) == d_valuation.getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}

void TheoryArrays::merge(TNode a, TNode b) {
  Assert(d_conflict.isNull());

  Debug("arrays-merge")<<"Arrays::merge() " << a <<" and " <<b <<endl;

  /*
   * take care of the congruence closure part
   */

  // make "a" the one with shorter diseqList
  CNodeTNodesMap::iterator deq_ia = d_disequalities.find(a);
  CNodeTNodesMap::iterator deq_ib = d_disequalities.find(b);

  if(deq_ia != d_disequalities.end()) {
    if(deq_ib == d_disequalities.end() ||
       (*deq_ia).second->size() > (*deq_ib).second->size()) {
      TNode tmp = a;
      a = b;
      b = tmp;
    }
  }
  a = find(a);
  b = find(b);

  if( a == b) {
    return;
  }


  // b becomes the canon of a
  setCanon(a, b);

  deq_ia = d_disequalities.find(a);
  map<TNode, TNode> alreadyDiseqs;
  if(deq_ia != d_disequalities.end()) {
    /*
     * Collecting the disequalities of b, no need to check for conflicts
     * since the representative of b does not change and we check all the things
     * in a's class when we look at the diseq list of find(a)
     */

    CNodeTNodesMap::iterator deq_ib = d_disequalities.find(b);
    if(deq_ib != d_disequalities.end()) {
      CTNodeListAlloc* deq = (*deq_ib).second;
      for(CTNodeListAlloc::const_iterator j = deq->begin(); j!=deq->end(); j++) {
        TNode deqn = *j;
        TNode s = deqn[0];
        TNode t = deqn[1];
        TNode sp = find(s);
        TNode tp = find(t);
        Assert(sp == b || tp == b);
        if(sp == b) {
          alreadyDiseqs[tp] = deqn;
        } else {
          alreadyDiseqs[sp] = deqn;
        }
      }
    }

    /*
     * Looking for conflicts in the a disequality list. Note
     * that at this point a and b are already merged. Also has
     * the side effect that it adds them to the list of b (which
     * became the canonical representative)
     */

    CTNodeListAlloc* deqa = (*deq_ia).second;
    for(CTNodeListAlloc::const_iterator i = deqa->begin(); i!= deqa->end(); i++) {
      TNode deqn = (*i);
      Assert(deqn.getKind() == kind::EQUAL || deqn.getKind() == kind::IFF);
      TNode s = deqn[0];
      TNode t = deqn[1];
      TNode sp = find(s);
      TNode tp = find(t);

      if(find(s) == find(t)) {
        d_conflict = deqn;
        return;
      }
      Assert( sp == b || tp == b);

      // make sure not to add duplicates

      if(sp == b) {
        if(alreadyDiseqs.find(tp) == alreadyDiseqs.end()) {
          appendToDiseqList(b, deqn);
          alreadyDiseqs[tp] = deqn;
        }
      } else {
        if(alreadyDiseqs.find(sp) == alreadyDiseqs.end()) {
          appendToDiseqList(b, deqn);
          alreadyDiseqs[sp] = deqn;
        }
      }

    }
  }

  // TODO: check for equality propagations
  // a and b are find(a) and find(b) here
  checkPropagations(a,b);

  if(a.getType().isArray()) {
    checkRowLemmas(a,b);
    checkRowLemmas(b,a);
    // note the change in order, merge info adds the list of
    // the 2nd argument to the first
    d_infoMap.mergeInfo(b, a);
  }


}


void TheoryArrays::checkPropagations(TNode a, TNode b) {
  EqLists::const_iterator ita = d_equalities.find(a);
  EqLists::const_iterator itb = d_equalities.find(b);

  if(ita != d_equalities.end()) {
    if(itb!= d_equalities.end()) {
      // because b is the canonical representative
      List<TNode>* eqsa = (*ita).second;
      List<TNode>* eqsb = (*itb).second;

      for(List<TNode>::const_iterator it = eqsa->begin(); it!= eqsa->end(); ++it) {
        Node eq = *it;
        Assert(eq.getKind() == kind::EQUAL || eq.getKind() == kind::IFF);
        if(find(eq[0])== find(eq[1])) {
          d_prop_queue.push_back(eq);
        }
      }
     eqsb->concat(eqsa);
    }
    else {
      List<TNode>* eqsb = new List<TNode>(&d_backtracker);
      List<TNode>* eqsa = (*ita).second;
      d_equalities.insert(b, eqsb);
      eqsb->concat(eqsa);
    }
  } else {
    List<TNode>* eqsb = new List<TNode>(&d_backtracker);
    d_equalities.insert(b, eqsb);
    List<TNode>* eqsa = new List<TNode>(&d_backtracker);
    d_equalities.insert(a, eqsa);
    eqsb->concat(eqsa);
  }
}


bool TheoryArrays::isNonLinear(TNode a) {
  Assert(a.getType().isArray());
  const CTNodeList* inst = d_infoMap.getInStores(find(a));
  if(inst->size()<=1) {
    return false;
  }
  return true;
}

bool TheoryArrays::isAxiom(TNode t1, TNode t2) {
  Debug("arrays-axiom")<<"Arrays::isAxiom start "<<t1<<" = "<<t2<<"\n";
  if(t1.getKind() == kind::SELECT) {
    TNode a = t1[0];
    TNode i = t1[1];

    if(a.getKind() == kind::STORE) {
      TNode b = a[0];
      TNode j = a[1];
      TNode v = a[2];
      if(i == j && v == t2) {
        Debug("arrays-axiom")<<"Arrays::isAxiom true\n";
        return true;
      }
    }
  }
  return false;
}


Node TheoryArrays::constructConflict(TNode diseq) {
  Debug("arrays") << "arrays: begin constructConflict()" << endl;
  Debug("arrays") << "arrays:   using diseq == " << diseq << endl;

  // returns the reason the two terms are equal
  Node explanation = d_cc.explain(diseq[0], diseq[1]);

  NodeBuilder<> nb(kind::AND);

  if(explanation.getKind() == kind::EQUAL ||
     explanation.getKind() == kind::IFF) {
    // if the explanation is only one literal
    if(!isAxiom(explanation[0], explanation[1]) &&
       !isAxiom(explanation[1], explanation[0])) {
      nb<<explanation;
    }
  }
  else {
    Assert(explanation.getKind() == kind::AND);
    for(TNode::iterator i  = TNode(explanation).begin();
        i != TNode(explanation).end(); i++) {
      if(!isAxiom((*i)[0], (*i)[1]) && !isAxiom((*i)[1], (*i)[0])) {
        nb<<*i;
      }
    }
  }

  nb<<diseq.notNode();
  Node conflict = nb;
  Debug("arrays") << "conflict constructed : " << conflict << endl;
  return conflict;
}

/*
void TheoryArrays::addAtom(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL);

  TNode lhs = eq[0];
  TNode rhs = eq[1];

  appendToAtomList(find(lhs), rhs);
  appendToAtomList(find(rhs), lhs);
}

void TheoryArrays::appendToAtomList(TNode a, TNode b) {
  Assert(find(a) == a);

  NodeTNodesMap::const_iterator it = d_atoms.find(a);
  if(it != d_atoms.end()) {
    (*it).second->push_back(b);
  }
  else {
   CTNodeList* list = new (true)CTNodeList(getContext());
   list->push_back(b);
   d_atoms[a] = list;
  }

}
*/

void TheoryArrays::addEq(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  TNode a = eq[0];
  TNode b = eq[1];

  // don't need to say find(a) because due to the structure of the lists it gets
  // automatically added
  appendToEqList(a, eq);
  appendToEqList(b, eq);

}

void TheoryArrays::appendToEqList(TNode n, TNode eq) {
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);

  EqLists::const_iterator it = d_equalities.find(n);
  if(it == d_equalities.end()) {
    List<TNode>* eqs = new List<TNode>(&d_backtracker);
    eqs->append(eq);
    d_equalities.insert(n, eqs);
  } else {
    List<TNode>* eqs = (*it).second;
    eqs->append(eq);
  }
}

void TheoryArrays::addDiseq(TNode diseq) {
  Assert(diseq.getKind() == kind::EQUAL ||
         diseq.getKind() == kind::IFF);
  TNode a = diseq[0];
  TNode b = diseq[1];

  appendToDiseqList(find(a), diseq);
  appendToDiseqList(find(b), diseq);

}

void TheoryArrays::appendToDiseqList(TNode of, TNode eq) {
  Debug("arrays") << "appending " << eq << endl
              << "  to diseq list of " << of << endl;
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);

  CNodeTNodesMap::iterator deq_i = d_disequalities.find(of);
  CTNodeListAlloc* deq;
  if(deq_i == d_disequalities.end()) {
    deq = new(getContext()->getCMM()) CTNodeListAlloc(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_disequalities.insertDataFromContextMemory(of, deq);
  } else {
    deq = (*deq_i).second;
  }

  deq->push_back(eq);
}


/**
 * Iterates through the indices of a and stores of b and checks if any new
 * Row lemmas need to be instantiated.
 */

bool TheoryArrays::isRedundandRowLemma(TNode a, TNode b, TNode i, TNode j) {
  Assert(a.getType().isArray());
  Assert(b.getType().isArray());

  if(d_RowAlreadyAdded.count(make_quad(a, b, i, j)) != 0 ||
     d_RowAlreadyAdded.count(make_quad(b, a, i, j)) != 0 ) {
    return true;
  }

  return false;
}

bool TheoryArrays::isRedundantInContext(TNode a, TNode b, TNode i, TNode j) {
  NodeManager* nm = NodeManager::currentNM();
  Node aj = nm->mkNode(kind::SELECT, a, j);
  Node bj = nm->mkNode(kind::SELECT, b, j);

  if(find(i) == find(j) || find(aj) == find(bj)) {
    //Debug("arrays-lem")<<"isRedundantInContext valid "<<a<<" "<<b<<" "<<i<<" "<<j<<"\n";
    checkRowForIndex(j,b); // why am i doing this?
    checkRowForIndex(i,a);
    return true;
    }
  if(alreadyAddedRow(a,b,i,j)) {
   // Debug("arrays-lem")<<"isRedundantInContext already added "<<a<<" "<<b<<" "<<i<<" "<<j<<"\n";
    return true;
  }
  return false;
}

TNode TheoryArrays::areDisequal(TNode a, TNode b) {
  Debug("arrays-prop")<<"Arrays::areDisequal "<<a<<" "<<b<<"\n";

  a = find(a);
  b = find(b);

  CNodeTNodesMap::const_iterator it = d_disequalities.find(a);
  if(it!= d_disequalities.end()) {
    CTNodeListAlloc::const_iterator i = (*it).second->begin();
    for( ; i!= (*it).second->end(); i++) {
      Debug("arrays-prop")<<"   "<<*i<<"\n";
      TNode s = (*i)[0];
      TNode t = (*i)[1];

      Assert(find(s) == a || find(t) == a);
      TNode sp, tp;
      if(find(t) == a) {
        sp = find(t);
        tp = find(s);
      }
      else {
        sp = find(s);
        tp = find(t);
      }

      if(tp == b) {
        return *i;
      }

    }
  }
  Debug("arrays-prop")<<"    not disequal \n";
  return TNode::null();
}

bool TheoryArrays::propagateFromRow(TNode a, TNode b, TNode i, TNode j) {
  Debug("arrays-prop")<<"Arrays::propagateFromRow "<<a<<" "<<b<<" "<<i<<" "<<j<<"\n";

  NodeManager* nm = NodeManager::currentNM();
  Node aj = nm->mkNode(kind::SELECT, a, j);
  Node bj = nm->mkNode(kind::SELECT, b, j);

  Node eq_aj_bj = nm->mkNode(kind::EQUAL,aj, bj);
  Node eq_ij = nm->mkNode(kind::EQUAL, i, j);

  // first check if the current context implies NOT (i = j)
  // in which case we can propagate a[j] = b[j]
  // FIXME: does i = j need to be a SAT literal or can we propagate anyway?

  // if it does not have an atom we must add the lemma (do we?!)
  if(d_atoms.count(eq_aj_bj) != 0 ||
     d_atoms.count(nm->mkNode(kind::EQUAL, bj, aj))!=0) {
    Node diseq = areDisequal(i, j);
    // check if the current context implies that (NOT i = j)
    if(diseq != TNode::null()) {
      // if it's unassigned
      Debug("arrays-prop")<<"satValue "<<d_valuation.getSatValue(eq_aj_bj).isNull();
      if(d_valuation.getSatValue(eq_aj_bj).isNull()) {
        d_out->propagate(eq_aj_bj);
        ++d_numProp;
        // save explanation
        d_explanations.insert(eq_aj_bj,std::make_pair(eq_ij, diseq));
        return true;
      }

    }
  }

  // now check if the current context implies NOT a[j] = b[j]
  // in which case we propagate i = j

  // we can't propagate if it does not have an atom
  if(d_atoms.count(eq_ij) != 0 || d_atoms.count(nm->mkNode(kind::EQUAL, j, i))!= 0) {

    Node diseq = areDisequal(aj, bj);
    Assert(TNode::null() == Node::null());

    if(diseq != TNode::null()) {
      if(d_valuation.getSatValue(eq_ij) == Node::null()) {
        d_out->propagate(eq_ij);
        ++d_numProp;
        // save explanation
        d_explanations.insert(eq_ij, std::make_pair(eq_aj_bj,diseq));
        return true;
      }
    }
  }

  Debug("arrays-prop")<<"Arrays::propagateFromRow no prop \n";
  return false;
}

void TheoryArrays::explain(TNode n) {


  Debug("arrays")<<"Arrays::explain start for "<<n<<"\n";
  ++d_numExplain;

  Assert(n.getKind()==kind::EQUAL);

  Node explanation = d_cc.explain(n[0], n[1]);

  NodeBuilder<> nb(kind::AND);

  if(explanation.getKind() == kind::EQUAL ||
     explanation.getKind() == kind::IFF) {
    // if the explanation is only one literal
    if(!isAxiom(explanation[0], explanation[1]) &&
       !isAxiom(explanation[1], explanation[0])) {
      nb<<explanation;
    }
  }
  else {
    Assert(explanation.getKind() == kind::AND);
    for(TNode::iterator i  = TNode(explanation).begin();
        i != TNode(explanation).end(); i++) {
      if(!isAxiom((*i)[0], (*i)[1]) && !isAxiom((*i)[1], (*i)[0])) {
        nb<<*i;
      }
    }
  }
  Node reason = nb;

  d_out->explanation(reason);

  /*
  context::CDMap<TNode, std::pair<TNode, TNode>, TNodeHashFunction>::const_iterator
                                                    it = d_explanations.find(n);
  Assert(it!= d_explanations.end());
  TNode diseq = (*it).second.second;
  TNode s = diseq[0];
  TNode t = diseq[1];

  TNode eq = (*it).second.first;
  TNode a = eq[0];
  TNode b = eq[1];

  Assert ((find(a) == find(s) && find(b) == find(t)) ||
          (find(a) == find(t) && find(b) == find(s)));


  if(find(a) == find(t)) {
    TNode temp = t;
    t = s;
    s = temp;
  }

  // construct the explanation

  NodeBuilder<> nb(kind::AND);
  Node explanation1 = d_cc.explain(a, s);
  Node explanation2 = d_cc.explain(b, t);

  if(explanation1.getKind() == kind::AND) {
    for(TNode::iterator i= TNode(explanation1).begin();
        i!=TNode(explanation1).end(); ++i) {
      nb << *i;
    }
  } else {
    Assert(explanation1.getKind() == kind::EQUAL ||
           explanation1.getKind() == kind::IFF);
    nb << explanation1;
  }

  if(explanation2.getKind() == kind::AND) {
    for(TNode::iterator i= TNode(explanation2).begin();
        i!=TNode(explanation2).end(); ++i) {
      nb << *i;
    }
  } else {
    Assert(explanation2.getKind() == kind::EQUAL ||
           explanation2.getKind() == kind::IFF);
    nb << explanation2;
  }

  nb << diseq;
  Node reason = nb;
  d_out->explanation(reason);
  Debug("arrays")<<"explanation "<< reason<<" done \n";
  */
}

void TheoryArrays::checkRowLemmas(TNode a, TNode b) {

  Debug("arrays-crl")<<"Arrays::checkLemmas begin \n"<<a<<"\n";
  if(Debug.isOn("arrays-crl"))
    d_infoMap.getInfo(a)->print();
  Debug("arrays-crl")<<"  ------------  and "<<b<<"\n";
  if(Debug.isOn("arrays-crl"))
    d_infoMap.getInfo(b)->print();

  List<TNode>* i_a = d_infoMap.getIndices(a);
  const CTNodeList* st_b = d_infoMap.getStores(b);
  const CTNodeList* inst_b = d_infoMap.getInStores(b);

  List<TNode>::const_iterator it = i_a->begin();
  CTNodeList::const_iterator its;

  for( ; it != i_a->end(); it++ ) {
    TNode i = *it;
    its = st_b->begin();
    for ( ; its != st_b->end(); its++) {
      TNode store = *its;
      Assert(store.getKind() == kind::STORE);
      TNode j = store[1];
      TNode c = store[0];

      if(  !isRedundandRowLemma(store, c, j, i)){
         //&&!propagateFromRow(store, c, j, i)) {
        queueRowLemma(store, c, j, i);
      }
    }

  }

  it = i_a->begin();

  for( ; it != i_a->end(); it++ ) {
    TNode i = *it;
    its = inst_b->begin();
    for ( ; its !=inst_b->end(); its++) {
      TNode store = *its;
      Assert(store.getKind() == kind::STORE);
      TNode j = store[1];
      TNode c = store[0];

      if (   isNonLinear(c)
          &&!isRedundandRowLemma(store, c, j, i)){
          //&&!propagateFromRow(store, c, j, i)) {
        queueRowLemma(store, c, j, i);
      }

    }
  }

  Debug("arrays-crl")<<"Arrays::checkLemmas done.\n";
}

/**
 * Adds a new Row lemma of the form i = j OR a[j] = b[j] if i and j are not the
 * same and a and b are also not identical.
 *
 */

inline void TheoryArrays::addRowLemma(TNode a, TNode b, TNode i, TNode j) {
 Assert(a.getType().isArray());
 Assert(b.getType().isArray());

 // construct lemma
 NodeManager* nm = NodeManager::currentNM();
 Node aj = nm->mkNode(kind::SELECT, a, j);
 Node bj = nm->mkNode(kind::SELECT, b, j);
 Node eq1 = nm->mkNode(kind::EQUAL, aj, bj);
 Node eq2 = nm->mkNode(kind::EQUAL, i, j);
 Node lem = nm->mkNode(kind::OR, eq2, eq1);



 Debug("arrays-lem")<<"Arrays::addRowLemma adding "<<lem<<"\n";
 d_RowAlreadyAdded.insert(make_quad(a,b,i,j));
 d_out->lemma(lem);
 ++d_numRow;

}


/**
 * Because a is now being read at position i check if new lemmas can be
 * instantiated for all store terms equal to a and all store terms of the form
 * store(a _ _ )
 */
void TheoryArrays::checkRowForIndex(TNode i, TNode a) {
  Debug("arrays-cri")<<"Arrays::checkRowForIndex "<<a<<"\n";
  Debug("arrays-cri")<<"                   index "<<i<<"\n";

  if(Debug.isOn("arrays-cri")) {
    d_infoMap.getInfo(a)->print();
  }
  Assert(a.getType().isArray());

  const CTNodeList* stores = d_infoMap.getStores(a);
  const CTNodeList* instores = d_infoMap.getInStores(a);
  CTNodeList::const_iterator it = stores->begin();

  for(; it!= stores->end(); it++) {
    TNode store = *it;
    Assert(store.getKind()==kind::STORE);
    TNode j = store[1];
    //Debug("arrays-lem")<<"Arrays::checkRowForIndex ("<<store<<", "<<store[0]<<", "<<j<<", "<<i<<")\n";
    if(!isRedundandRowLemma(store, store[0], j, i)) {
      //Debug("arrays-lem")<<"Arrays::checkRowForIndex ("<<store<<", "<<store[0]<<", "<<j<<", "<<i<<")\n";
      queueRowLemma(store, store[0], j, i);
    }
  }

  it = instores->begin();
  for(; it!= instores->end(); it++) {
    TNode instore = *it;
    Assert(instore.getKind()==kind::STORE);
    TNode j = instore[1];
    //Debug("arrays-lem")<<"Arrays::checkRowForIndex ("<<instore<<", "<<instore[0]<<", "<<j<<", "<<i<<")\n";
    if(!isRedundandRowLemma(instore, instore[0], j, i)) {
      //Debug("arrays-lem")<<"Arrays::checkRowForIndex ("<<instore<<", "<<instore[0]<<", "<<j<<", "<<i<<")\n";
      queueRowLemma(instore, instore[0], j, i);
    }
  }

}


void TheoryArrays::checkStore(TNode a) {
  Debug("arrays-cri")<<"Arrays::checkStore "<<a<<"\n";

  if(Debug.isOn("arrays-cri")) {
    d_infoMap.getInfo(a)->print();
  }
  Assert(a.getType().isArray());
  Assert(a.getKind()==kind::STORE);
  TNode b = a[0];
  TNode i = a[1];

  List<TNode>* js = d_infoMap.getIndices(b);
  List<TNode>::const_iterator it = js->begin();

  for(; it!= js->end(); it++) {
    TNode j = *it;

    if(!isRedundandRowLemma(a, b, i, j)) {
      //Debug("arrays-lem")<<"Arrays::checkRowStore ("<<a<<", "<<b<<", "<<i<<", "<<j<<")\n";
      queueRowLemma(a,b,i,j);
    }
  }

}

inline void TheoryArrays::queueExtLemma(TNode a, TNode b) {
  Assert(a.getType().isArray() && b.getType().isArray());

  d_extQueue.insert(make_pair(a,b));
}

void TheoryArrays::queueRowLemma(TNode a, TNode b, TNode i, TNode j) {
  Assert(a.getType().isArray() && b.getType().isArray());
//if(!isRedundantInContext(a,b,i,j)) {
  d_RowQueue.insert(make_quad(a, b, i, j));
}

/**
* Adds a new Ext lemma of the form
*    a = b OR a[k]!=b[k], for a new variable k
*/

inline void TheoryArrays::addExtLemma(TNode a, TNode b) {
 Assert(a.getType().isArray());
 Assert(b.getType().isArray());

 Debug("arrays-cle")<<"Arrays::checkExtLemmas "<<a<<" \n";
 Debug("arrays-cle")<<"                   and "<<b<<" \n";


 if(   d_extAlreadyAdded.count(make_pair(a, b)) == 0
    && d_extAlreadyAdded.count(make_pair(b, a)) == 0) {

   NodeManager* nm = NodeManager::currentNM();
   Node k = nm->mkVar(a.getType()[0]);
   Node eq = nm->mkNode(kind::EQUAL, a, b);
   Node ak = nm->mkNode(kind::SELECT, a, k);
   Node bk = nm->mkNode(kind::SELECT, b, k);
   Node neq = nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, ak, bk));
   Node lem = nm->mkNode(kind::OR, eq, neq);

   Debug("arrays-lem")<<"Arrays::addExtLemma "<<lem<<"\n";
   d_extAlreadyAdded.insert(make_pair(a,b));
   d_out->lemma(lem);
   ++d_numExt;
   return;
 }
 Debug("arrays-cle")<<"Arrays::checkExtLemmas lemma already generated. \n";

}


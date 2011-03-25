/*********************                                                        */
/*! \file theory_uf_morgan.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of uninterpreted functions.
 **
 ** Implementation of the theory of uninterpreted functions.
 **/

#include "theory/uf/morgan/theory_uf_morgan.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include "util/congruence_closure.h"

#include <map>

using namespace std;

using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;
using namespace CVC4::theory::uf::morgan;

TheoryUFMorgan::TheoryUFMorgan(Context* ctxt, OutputChannel& out, Valuation valuation) :
  TheoryUF(ctxt, out, valuation),
  d_assertions(ctxt),
  d_ccChannel(this),
  d_cc(ctxt, &d_ccChannel),
  d_unionFind(ctxt),
  d_disequalities(ctxt),
  d_equalities(ctxt),
  d_conflict(),
  d_trueNode(),
  d_falseNode(),
  d_trueEqFalseNode(),
  d_ccExplanationLength("theory::uf::morgan::cc::averageExplanationLength",
                        d_cc.getExplanationLength()),
  d_ccNewSkolemVars("theory::uf::morgan::cc::newSkolemVariables",
                    d_cc.getNewSkolemVars()) {

  StatisticsRegistry::registerStat(&d_ccExplanationLength);
  StatisticsRegistry::registerStat(&d_ccNewSkolemVars);

  NodeManager* nm = NodeManager::currentNM();
  TypeNode boolType = nm->booleanType();
  d_trueNode = nm->mkVar("TRUE_UF", boolType);
  d_falseNode = nm->mkVar("FALSE_UF", boolType);
  d_trueEqFalseNode = nm->mkNode(kind::IFF, d_trueNode, d_falseNode);
  addDisequality(d_trueEqFalseNode);
  d_cc.addTerm(d_trueNode);
  d_cc.addTerm(d_falseNode);
}

TheoryUFMorgan::~TheoryUFMorgan() {
  d_trueNode = Node::null();
  d_falseNode = Node::null();
  d_trueEqFalseNode = Node::null();

  StatisticsRegistry::unregisterStat(&d_ccExplanationLength);
  StatisticsRegistry::unregisterStat(&d_ccNewSkolemVars);
}

void TheoryUFMorgan::preRegisterTerm(TNode n) {
  Debug("uf") << "uf: preRegisterTerm(" << n << ")" << endl;
  if(n.getKind() == kind::EQUAL || n.getKind() == kind::IFF) {
    registerEqualityForPropagation(n);
  }
}

void TheoryUFMorgan::registerTerm(TNode n) {
  Debug("uf") << "uf: registerTerm(" << n << ")" << endl;
}

Node TheoryUFMorgan::constructConflict(TNode diseq) {
  Debug("uf") << "uf: begin constructConflict()" << endl;
  Debug("uf") << "uf:   using diseq == " << diseq << endl;

  Node explanation = d_cc.explain(diseq[0], diseq[1]);

  NodeBuilder<> nb(kind::AND);
  if(explanation.getKind() == kind::AND) {
    for(TNode::iterator i = TNode(explanation).begin();
        i != TNode(explanation).end();
        ++i) {
      TNode n = *i;
      Assert(n.getKind() == kind::EQUAL ||
             n.getKind() == kind::IFF);
      Assert(n[0] != d_trueNode &&
             n[0] != d_falseNode);
      if(n[1] == d_trueNode) {
        nb << n[0];
      } else if(n[1] == d_falseNode) {
        nb << n[0].notNode();
      } else {
        nb << n;
      }
    }
  } else {
    Assert(explanation.getKind() == kind::EQUAL ||
           explanation.getKind() == kind::IFF);
    Assert(explanation[0] != d_trueNode &&
           explanation[0] != d_falseNode);
    if(explanation[1] == d_trueNode) {
      nb << explanation[0];
    } else if(explanation[1] == d_falseNode) {
      nb << explanation[0].notNode();
    } else {
      nb << explanation;
    }
  }
  if(diseq != d_trueEqFalseNode) {
    nb << diseq.notNode();
  }

  // by construction this should be true
  Assert(nb.getNumChildren() > 1);

  Node conflict = nb;
  Debug("uf") << "conflict constructed : " << conflict << endl;

  Debug("uf") << "uf: ending constructConflict()" << endl;

  return conflict;
}

void TheoryUFMorgan::notifyCongruent(TNode a, TNode b) {
  Debug("uf") << "uf: notified of merge " << a << endl
              << "                  and " << b << endl;
  if(!d_conflict.isNull()) {
    // if already a conflict, we don't care
    return;
  }

  merge(a, b);
}

void TheoryUFMorgan::merge(TNode a, TNode b) {
  Assert(d_conflict.isNull());

  // make "a" the one with shorter diseqList
  EqLists::iterator deq_ia = d_disequalities.find(a);
  EqLists::iterator deq_ib = d_disequalities.find(b);
  if(deq_ia != d_disequalities.end()) {
    if(deq_ib == d_disequalities.end() ||
       (*deq_ia).second->size() > (*deq_ib).second->size()) {
      TNode tmp = a;
      a = b;
      b = tmp;
      Debug("uf") << "    swapping to make a shorter diseqList" << endl;
    }
  }
  a = find(a);
  b = find(b);
  Debug("uf") << "uf: uf reps are " << a << endl
              << "            and " << b << endl;

  if(a == b) {
    return;
  }

  // should have already found such a conflict
  Assert(find(d_trueNode) != find(d_falseNode));

  d_unionFind.setCanon(a, b);

  EqLists::iterator deq_i = d_disequalities.find(a);
  // a set of other trees we are already disequal to, and their
  // (TNode) equalities (for optimizations below)
  map<TNode, TNode> alreadyDiseqs;
  if(deq_i != d_disequalities.end()) {
    EqLists::iterator deq_ib = d_disequalities.find(b);
    if(deq_ib != d_disequalities.end()) {
      EqList* deq = (*deq_ib).second;
      for(EqList::const_iterator j = deq->begin(); j != deq->end(); ++j) {
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

    EqList* deq = (*deq_i).second;
    if(Debug.isOn("uf")) {
      Debug("uf") << "a == " << a << endl;
      Debug("uf") << "size of deq(a) is " << deq->size() << endl;
    }
    for(EqList::const_iterator j = deq->begin(); j != deq->end(); ++j) {
      Debug("uf") << "  deq(a) ==> " << *j << endl;
      TNode deqn = *j;
      Assert(deqn.getKind() == kind::EQUAL ||
             deqn.getKind() == kind::IFF);
      TNode s = deqn[0];
      TNode t = deqn[1];
      if(Debug.isOn("uf")) {
        Debug("uf") << "       s  ==> " << s << endl
                    << "       t  ==> " << t << endl
                    << "  find(s) ==> " << debugFind(s) << endl
                    << "  find(t) ==> " << debugFind(t) << endl;
      }
      TNode sp = find(s);
      TNode tp = find(t);
      if(sp == tp) {
        d_conflict = deqn;
        return;
      }
      Assert(sp == b || tp == b);
      // optimization: don't put redundant diseq's in the list
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
    Debug("uf") << "end diseq-list." << endl;
  }

  // Note that at this point, alreadyDiseqs contains everything we're
  // disequal to, and the attendant disequality

  // FIXME these could be "remembered" and then done in propagation (?)
//  EqLists::iterator eq_i = d_equalities.find(a);
//  if(eq_i != d_equalities.end()) {
//    EqList* eq = (*eq_i).second;
//    if(Debug.isOn("uf")) {
//      Debug("uf") << "a == " << a << endl;
//      Debug("uf") << "size of eq(a) is " << eq->size() << endl;
//    }
//    for(EqList::const_iterator j = eq->begin(); j != eq->end(); ++j) {
//      Debug("uf") << "  eq(a) ==> " << *j << endl;
//      TNode eqn = *j;
//      Assert(eqn.getKind() == kind::EQUAL ||
//             eqn.getKind() == kind::IFF);
//      TNode s = eqn[0];
//      TNode t = eqn[1];
//      if(Debug.isOn("uf")) {
//        Debug("uf") << "       s  ==> " << s << endl
//                    << "       t  ==> " << t << endl
//                    << "  find(s) ==> " << debugFind(s) << endl
//                    << "  find(t) ==> " << debugFind(t) << endl;
//      }
//      TNode sp = find(s);
//      TNode tp = find(t);
//      if(sp == tp) {
//        // propagation of equality
//        Debug("uf:prop") << "  uf-propagating " << eqn << endl;
//        ++d_propagations;
//        d_out->propagate(eqn);
//      } else {
//        Assert(sp == b || tp == b);
//        appendToEqList(b, eqn);
//        if(sp == b) {
//          map<TNode, TNode>::const_iterator k = alreadyDiseqs.find(tp);
//          if(k != alreadyDiseqs.end()) {
//            // propagation of disequality
//            // FIXME: this will propagate the same disequality on every
//            // subsequent merge, won't it??
//            Node deqn = (*k).second.notNode();
//            Debug("uf:prop") << "  uf-propagating " << deqn << endl;
//            ++d_propagations;
//            d_out->propagate(deqn);
//          }
//        } else {
//          map<TNode, TNode>::const_iterator k = alreadyDiseqs.find(sp);
//          if(k != alreadyDiseqs.end()) {
//            // propagation of disequality
//            // FIXME: this will propagate the same disequality on every
//            // subsequent merge, won't it??
//            Node deqn = (*k).second.notNode();
//            Debug("uf:prop") << "  uf-propagating " << deqn << endl;
//            ++d_propagations;
//            d_out->propagate(deqn);
//          }
//        }
//      }
//    }
//    Debug("uf") << "end eq-list." << endl;
//  }
}

void TheoryUFMorgan::appendToDiseqList(TNode of, TNode eq) {
  Debug("uf") << "appending " << eq << endl
              << "  to diseq list of " << of << endl;
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  Assert(of == debugFind(of));
  EqLists::iterator deq_i = d_disequalities.find(of);
  EqList* deq;
  if(deq_i == d_disequalities.end()) {
    deq = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_disequalities.insertDataFromContextMemory(of, deq);
  } else {
    deq = (*deq_i).second;
  }
  deq->push_back(eq);
  if(Debug.isOn("uf")) {
    Debug("uf") << "  size is now " << deq->size() << endl;
  }
}

void TheoryUFMorgan::appendToEqList(TNode of, TNode eq) {
  Debug("uf") << "appending " << eq << endl
              << "  to eq list of " << of << endl;
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  Assert(of == debugFind(of));
  EqLists::iterator eq_i = d_equalities.find(of);
  EqList* eql;
  if(eq_i == d_equalities.end()) {
    eql = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_equalities.insertDataFromContextMemory(of, eql);
  } else {
    eql = (*eq_i).second;
  }
  eql->push_back(eq);
  if(Debug.isOn("uf")) {
    Debug("uf") << "  size is now " << eql->size() << endl;
  }
}

void TheoryUFMorgan::addDisequality(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);

  TNode a = eq[0];
  TNode b = eq[1];

  appendToDiseqList(find(a), eq);
  appendToDiseqList(find(b), eq);
}

void TheoryUFMorgan::registerEqualityForPropagation(TNode eq) {
  // should NOT be in search at this point, this must be called during
  // preregistration

  // FIXME with lemmas on demand, this could miss future propagations,
  // since we are not necessarily at context level 0, but are updating
  // context-sensitive structures.

  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);

  TNode a = eq[0];
  TNode b = eq[1];

  appendToEqList(find(a), eq);
  appendToEqList(find(b), eq);
}

void TheoryUFMorgan::check(Effort level) {
  TimerStat::CodeTimer codeTimer(d_checkTimer);

  Debug("uf") << "uf: begin check(" << level << ")" << endl;

  while(!done()) {
    Assert(d_conflict.isNull());

    Node assertion = get();

    //d_activeAssertions.push_back(assertion);

    Debug("uf") << "uf check(): " << assertion << endl;

    switch(assertion.getKind()) {
    case kind::EQUAL:
    case kind::IFF:
      d_cc.addEquality(assertion);
      if(!d_conflict.isNull()) {
        Node conflict = constructConflict(d_conflict);
        d_conflict = Node::null();
        ++d_conflicts;
        d_out->conflict(conflict, false);
        return;
      }
      merge(assertion[0], assertion[1]);
      break;
    case kind::APPLY_UF:
      { // predicate

        // assert it's a predicate
        Assert(assertion.getOperator().getType().getRangeType().isBoolean());

        Node eq = NodeManager::currentNM()->mkNode(kind::IFF,
                                                   assertion, d_trueNode);
        d_cc.addTerm(assertion);
        d_cc.addEquality(eq);

        if(!d_conflict.isNull()) {
          Node conflict = constructConflict(d_conflict);
          d_conflict = Node::null();
          ++d_conflicts;
          d_out->conflict(conflict, false);
          return;
        }

        if(Debug.isOn("uf")) {
          Debug("uf") << "true == false ? "
                      << (find(d_trueNode) == find(d_falseNode)) << endl;
        }

        Assert(find(d_trueNode) != find(d_falseNode));

        merge(eq[0], eq[1]);
      }
      break;
    case kind::NOT:
      if(assertion[0].getKind() == kind::EQUAL ||
         assertion[0].getKind() == kind::IFF) {
        Node a = assertion[0][0];
        Node b = assertion[0][1];

        addDisequality(assertion[0]);

        d_cc.addTerm(a);
        d_cc.addTerm(b);

        if(Debug.isOn("uf")) {
          Debug("uf") << "       a  ==> " << a << endl
                      << "       b  ==> " << b << endl
                      << "  find(a) ==> " << debugFind(a) << endl
                      << "  find(b) ==> " << debugFind(b) << endl;
        }

        // There are two ways to get a conflict here.
        if(!d_conflict.isNull()) {
          // We get a conflict this way if we weren't watching a, b
          // before and we were just now notified (via
          // notifyCongruent()) when we called addTerm() above that
          // they are congruent.  We make this a separate case (even
          // though the check in the "else if.." below would also
          // catch it, so that we can clear out d_conflict.
          Node conflict = constructConflict(d_conflict);
          d_conflict = Node::null();
          ++d_conflicts;
          d_out->conflict(conflict, false);
          return;
        } else if(find(a) == find(b)) {
          // We get a conflict this way if we WERE previously watching
          // a, b and were notified previously (via notifyCongruent())
          // that they were congruent.
          Node conflict = constructConflict(assertion[0]);
          ++d_conflicts;
          d_out->conflict(conflict, false);
          return;
        }

        // If we get this far, there should be nothing conflicting due
        // to this disequality.
        Assert(!d_cc.areCongruent(a, b));
      } else {
        // negation of a predicate
        Assert(assertion[0].getKind() == kind::APPLY_UF);

        // assert it's a predicate
        Assert(assertion[0].getOperator().getType().getRangeType().isBoolean());

        Node eq = NodeManager::currentNM()->mkNode(kind::IFF,
                                                   assertion[0], d_falseNode);
        d_cc.addTerm(assertion[0]);
        d_cc.addEquality(eq);

        if(!d_conflict.isNull()) {
          Node conflict = constructConflict(d_conflict);
          d_conflict = Node::null();
          ++d_conflicts;
          d_out->conflict(conflict, false);
          return;
        }

        if(Debug.isOn("uf")) {
          Debug("uf") << "true == false ? "
                      << (find(d_trueNode) == find(d_falseNode)) << endl;
        }

        Assert(find(d_trueNode) != find(d_falseNode));

        merge(eq[0], eq[1]);
      }
      break;
    default:
      Unhandled(assertion.getKind());
    }

    /*
    if(Debug.isOn("uf")) {
      dump();
    }
    */
  }
  Assert(d_conflict.isNull());
  Debug("uf") << "uf check() done = " << (done() ? "true" : "false")
              << endl;

  /*
  for(CDList<Node>::const_iterator diseqIter = d_disequality.begin();
      diseqIter != d_disequality.end();
      ++diseqIter) {

    TNode left  = (*diseqIter)[0];
    TNode right = (*diseqIter)[1];
    if(Debug.isOn("uf")) {
      Debug("uf") << "testing left: " << left << endl
                  << "       right: " << right << endl
                  << "     find(L): " << debugFind(left) << endl
                  << "     find(R): " << debugFind(right) << endl
                  << "     areCong: " << d_cc.areCongruent(left, right)
                  << endl;
    }
    Assert((debugFind(left) == debugFind(right)) ==
           d_cc.areCongruent(left, right));
  }
  */

  Debug("uf") << "uf: end check(" << level << ")" << endl;
}

void TheoryUFMorgan::propagate(Effort level) {
  TimerStat::CodeTimer codeTimer(d_propagateTimer);

  Debug("uf") << "uf: begin propagate(" << level << ")" << endl;
  // propagation is done in check(), for now
  // FIXME need to find a slick way to propagate predicates
  Debug("uf") << "uf: end propagate(" << level << ")" << endl;
}

void TheoryUFMorgan::explain(TNode n) {
  TimerStat::CodeTimer codeTimer(d_explainTimer);

  Debug("uf") << "uf: begin explain([" << n << "])" << endl;
  Unimplemented();
  Debug("uf") << "uf: end explain([" << n << "])" << endl;
}

void TheoryUFMorgan::presolve() {
  TimerStat::CodeTimer codeTimer(d_presolveTimer);

  Debug("uf") << "uf: begin presolve()" << endl;
  Debug("uf") << "uf: end presolve()" << endl;
}

void TheoryUFMorgan::notifyRestart() {
  Debug("uf") << "uf: begin notifyDecisionLevelZero()" << endl;
  Debug("uf") << "uf: end notifyDecisionLevelZero()" << endl;
}

Node TheoryUFMorgan::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
  case kind::APPLY_UF:
    if(n.getType().isBoolean()) {
      if(d_cc.areCongruent(d_trueNode, n)) {
        return nodeManager->mkConst(true);
      } else if(d_cc.areCongruent(d_falseNode, n)) {
        return nodeManager->mkConst(false);
      }
    }
    return d_cc.normalize(n);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( d_valuation.getValue(n[0]) == d_valuation.getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}

void TheoryUFMorgan::staticLearning(TNode n, NodeBuilder<>& learned) {
  TimerStat::CodeTimer codeTimer(d_staticLearningTimer);

  vector<TNode> workList;
  workList.push_back(n);
  __gnu_cxx::hash_set<TNode, TNodeHashFunction> processed;

  while(!workList.empty()) {
    n = workList.back();

    bool unprocessedChildren = false;
    for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
      if(processed.find(*i) == processed.end()) {
        // unprocessed child
        workList.push_back(*i);
        unprocessedChildren = true;
      }
    }

    if(unprocessedChildren) {
      continue;
    }

    workList.pop_back();
    // has node n been processed in the meantime ?
    if(processed.find(n) != processed.end()) {
      continue;
    }
    processed.insert(n);

    // == DIAMONDS ==

    Debug("diamonds") << "===================== looking at" << endl
                      << n << endl;

    // binary OR of binary ANDs of EQUALities
    if(n.getKind() == kind::OR && n.getNumChildren() == 2 &&
       n[0].getKind() == kind::AND && n[0].getNumChildren() == 2 &&
       n[1].getKind() == kind::AND && n[1].getNumChildren() == 2 &&
       (n[0][0].getKind() == kind::EQUAL || n[0][0].getKind() == kind::IFF) &&
       (n[0][1].getKind() == kind::EQUAL || n[0][1].getKind() == kind::IFF) &&
       (n[1][0].getKind() == kind::EQUAL || n[1][0].getKind() == kind::IFF) &&
       (n[1][1].getKind() == kind::EQUAL || n[1][1].getKind() == kind::IFF)) {
      // now we have (a = b && c = d) || (e = f && g = h)

      Debug("diamonds") << "has form of a diamond!" << endl;

      TNode
        a = n[0][0][0], b = n[0][0][1],
        c = n[0][1][0], d = n[0][1][1],
        e = n[1][0][0], f = n[1][0][1],
        g = n[1][1][0], h = n[1][1][1];

      // test that one of {a, b} = one of {c, d}, and make "b" the
      // shared node (i.e. put in the form (a = b && b = d))
      // note we don't actually care about the shared ones, so the
      // "swaps" below are one-sided, ignoring b and c
      if(a == c) {
        a = b;
      } else if(a == d) {
        a = b;
        d = c;
      } else if(b == c) {
        // nothing to do
      } else if(b == d) {
        d = c;
      } else {
        // condition not satisfied
        Debug("diamonds") << "+ A fails" << endl;
        continue;
      }

      Debug("diamonds") << "+ A holds" << endl;

      // same: one of {e, f} = one of {g, h}, and make "f" the
      // shared node (i.e. put in the form (e = f && f = h))
      if(e == g) {
        e = f;
      } else if(e == h) {
        e = f;
        h = g;
      } else if(f == g) {
        // nothing to do
      } else if(f == h) {
        h = g;
      } else {
        // condition not satisfied
        Debug("diamonds") << "+ B fails" << endl;
        continue;
      }

      Debug("diamonds") << "+ B holds" << endl;

      // now we have (a = b && b = d) || (e = f && f = h)
      // test that {a, d} == {e, h}
      if( (a == e && d == h) ||
          (a == h && d == e) ) {
        // learn: n implies a == d
        Debug("diamonds") << "+ C holds" << endl;
        Node newEquality = a.getType().isBoolean() ? a.iffNode(d) : a.eqNode(d);
        Debug("diamonds") << "  ==> " << newEquality << endl;
        learned << n.impNode(newEquality);
      } else {
        Debug("diamonds") << "+ C fails" << endl;
      }
    }
  }
}

/*
void TheoryUFMorgan::dump() {
  if(!Debug.isOn("uf")) {
    return;
  }
  Debug("uf") << "============== THEORY_UF ==============" << endl;
  Debug("uf") << "Active assertions list:" << endl;
  for(context::CDList<Node>::const_iterator i = d_activeAssertions.begin();
      i != d_activeAssertions.end();
      ++i) {
    Debug("uf") << "    " << *i << endl;
  }
  Debug("uf") << "Congruence union-find:" << endl;
  for(UnionFind::const_iterator i = d_unionFind.begin();
      i != d_unionFind.end();
      ++i) {
    Debug("uf") << "    " << (*i).first << "  ==>  " << (*i).second
                << endl;
  }
  Debug("uf") << "Disequality lists:" << endl;
  for(EqLists::const_iterator i = d_disequalities.begin();
      i != d_disequalities.end();
      ++i) {
    Debug("uf") << "    " << (*i).first << ":" << endl;
    EqList* dl = (*i).second;
    for(EqList::const_iterator j = dl->begin();
        j != dl->end();
        ++j) {
      Debug("uf") << "        " << *j << endl;
    }
  }
  Debug("uf") << "=======================================" << endl;
}
*/

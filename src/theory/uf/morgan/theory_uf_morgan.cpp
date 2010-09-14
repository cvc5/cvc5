/*********************                                                        */
/*! \file theory_uf_morgan.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
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
#include "expr/kind.h"
#include "util/congruence_closure.h"

using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;
using namespace CVC4::theory::uf::morgan;

TheoryUFMorgan::TheoryUFMorgan(int id, Context* ctxt, OutputChannel& out) :
  TheoryUF(id, ctxt, out),
  d_assertions(ctxt),
  d_ccChannel(this),
  d_cc(ctxt, &d_ccChannel),
  d_unionFind(ctxt),
  d_disequalities(ctxt),
  d_disequality(ctxt),
  d_conflict(),
  d_trueNode(),
  d_falseNode(),
  d_activeAssertions(ctxt) {
  TypeNode boolType = NodeManager::currentNM()->booleanType();
  d_trueNode = NodeManager::currentNM()->mkVar("TRUE_UF", boolType);
  d_falseNode = NodeManager::currentNM()->mkVar("FALSE_UF", boolType);
  d_cc.addTerm(d_trueNode);
  d_cc.addTerm(d_falseNode);
}

TheoryUFMorgan::~TheoryUFMorgan() {
}

RewriteResponse TheoryUFMorgan::postRewrite(TNode n, bool topLevel) {
  if(topLevel) {
    Debug("uf") << "uf: begin rewrite(" << n << ")" << std::endl;
    Node ret(n);
    if(n.getKind() == kind::EQUAL ||
       n.getKind() == kind::IFF) {
      if(n[0] == n[1]) {
        ret = NodeManager::currentNM()->mkConst(true);
      }
    }
    Debug("uf") << "uf: end rewrite(" << n << ") : " << ret << std::endl;
    return RewriteComplete(ret);
  } else {
    return RewriteComplete(n);
  }
}

void TheoryUFMorgan::preRegisterTerm(TNode n) {
  Debug("uf") << "uf: preRegisterTerm(" << n << ")" << std::endl;
}

void TheoryUFMorgan::registerTerm(TNode n) {
  Debug("uf") << "uf: registerTerm(" << n << ")" << std::endl;
}

Node TheoryUFMorgan::constructConflict(TNode diseq) {
  Debug("uf") << "uf: begin constructConflict()" << std::endl;
  Debug("uf") << "uf:   using diseq == " << diseq << std::endl;

  Node explanation = d_cc.explain(diseq[0], diseq[1]);

  NodeBuilder<> nb(kind::AND);
  if(explanation.getKind() == kind::AND) {
    for(Node::iterator i = explanation.begin();
        i != explanation.end();
        ++i) {
      nb << *i;
    }
  } else {
    Assert(explanation.getKind() == kind::EQUAL ||
           explanation.getKind() == kind::IFF);
    nb << explanation;
  }
  nb << diseq.notNode();

  // by construction this should be true
  Assert(nb.getNumChildren() > 1);

  Node conflict = nb;
  Debug("uf") << "conflict constructed : " << conflict << std::endl;

  Debug("uf") << "uf: ending constructConflict()" << std::endl;

  return conflict;
}

TNode TheoryUFMorgan::find(TNode a) {
  UnionFind::iterator i = d_unionFind.find(a);
  if(i == d_unionFind.end()) {
    return a;
  } else {
    return d_unionFind[a] = find((*i).second);
  }
}

// no path compression
TNode TheoryUFMorgan::debugFind(TNode a) const {
  UnionFind::iterator i = d_unionFind.find(a);
  if(i == d_unionFind.end()) {
    return a;
  } else {
    return debugFind((*i).second);
  }
}

void TheoryUFMorgan::notifyCongruent(TNode a, TNode b) {
  Debug("uf") << "uf: notified of merge " << a << std::endl
              << "                  and " << b << std::endl;
  if(!d_conflict.isNull()) {
    // if already a conflict, we don't care
    return;
  }

  merge(a, b);
}

void TheoryUFMorgan::merge(TNode a, TNode b) {
  Assert(d_conflict.isNull());

  // make "a" the one with shorter diseqList
  DiseqLists::iterator deq_ia = d_disequalities.find(a);
  DiseqLists::iterator deq_ib = d_disequalities.find(b);
  if(deq_ia != d_disequalities.end()) {
    if(deq_ib == d_disequalities.end() ||
       (*deq_ia).second->size() > (*deq_ib).second->size()) {
      TNode tmp = a;
      a = b;
      b = tmp;
      Debug("uf") << "    swapping to make a shorter diseqList" << std::endl;
    }
  }
  a = find(a);
  b = find(b);
  Debug("uf") << "uf: uf reps are " << a << std::endl
              << "            and " << b << std::endl;

  if(a == b) {
    return;
  }

  d_unionFind[a] = b;

  DiseqLists::iterator deq_i = d_disequalities.find(a);
  if(deq_i != d_disequalities.end()) {
    // a set of other trees we are already disequal to
    // (for the optimization below)
    std::set<TNode> alreadyDiseqs;
    DiseqLists::iterator deq_ib = d_disequalities.find(b);
    if(deq_ib != d_disequalities.end()) {
      DiseqList* deq = (*deq_ib).second;
      for(DiseqList::const_iterator j = deq->begin(); j != deq->end(); ++j) {
        TNode deqn = *j;
        TNode s = deqn[0];
        TNode t = deqn[1];
        TNode sp = find(s);
        TNode tp = find(t);
        Assert(sp == b || tp == b);
        if(sp == b) {
          alreadyDiseqs.insert(tp);
        } else {
          alreadyDiseqs.insert(sp);
        }
      }
    }

    DiseqList* deq = (*deq_i).second;
    if(Debug.isOn("uf")) {
      Debug("uf") << "a == " << a << std::endl;
      Debug("uf") << "size of deq(a) is " << deq->size() << std::endl;
    }
    for(DiseqList::const_iterator j = deq->begin(); j != deq->end(); ++j) {
      Debug("uf") << "  deq(a) ==> " << *j << std::endl;
      TNode deqn = *j;
      Assert(deqn.getKind() == kind::EQUAL ||
             deqn.getKind() == kind::IFF);
      TNode s = deqn[0];
      TNode t = deqn[1];
      if(Debug.isOn("uf")) {
        Debug("uf") << "       s  ==> " << s << std::endl
                    << "       t  ==> " << t << std::endl
                    << "  find(s) ==> " << debugFind(s) << std::endl
                    << "  find(t) ==> " << debugFind(t) << std::endl;
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
          alreadyDiseqs.insert(tp);
        }
      } else {
        if(alreadyDiseqs.find(sp) == alreadyDiseqs.end()) {
          appendToDiseqList(b, deqn);
          alreadyDiseqs.insert(sp);
        }
      }
    }
    Debug("uf") << "end" << std::endl;
  }
}

void TheoryUFMorgan::appendToDiseqList(TNode of, TNode eq) {
  Debug("uf") << "appending " << eq << std::endl
              << "  to diseq list of " << of << std::endl;
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  Assert(of == debugFind(of));
  DiseqLists::iterator deq_i = d_disequalities.find(of);
  DiseqList* deq;
  if(deq_i == d_disequalities.end()) {
    deq = new(getContext()->getCMM()) DiseqList(true, getContext());
    d_disequalities.insertDataFromContextMemory(of, deq);
  } else {
    deq = (*deq_i).second;
  }
  deq->push_back(eq);
  if(Debug.isOn("uf")) {
    Debug("uf") << "  size is now " << deq->size() << std::endl;
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

void TheoryUFMorgan::check(Effort level) {
  Debug("uf") << "uf: begin check(" << level << ")" << std::endl;

  while(!done()) {
    Node assertion = get();

    d_activeAssertions.push_back(assertion);

    Debug("uf") << "uf check(): " << assertion << std::endl;

    switch(assertion.getKind()) {
    case kind::EQUAL:
    case kind::IFF:
      d_cc.addEquality(assertion);
      if(!d_conflict.isNull()) {
        Node conflict = constructConflict(d_conflict);
        d_conflict = Node::null();
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

        if(Debug.isOn("uf")) {
          Debug("uf") << "true == false ? "
                      << (find(d_trueNode) == find(d_falseNode)) << std::endl;
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
        d_disequality.push_back(assertion[0]);

        d_cc.addTerm(a);
        d_cc.addTerm(b);

        if(Debug.isOn("uf")) {
          Debug("uf") << "       a  ==> " << a << std::endl
                      << "       b  ==> " << b << std::endl
                      << "  find(a) ==> " << debugFind(a) << std::endl
                      << "  find(b) ==> " << debugFind(b) << std::endl;
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
          d_out->conflict(conflict, false);
          return;
        } else if(find(a) == find(b)) {
          // We get a conflict this way if we WERE previously watching
          // a, b and were notified previously (via notifyCongruent())
          // that they were congruent.
          Node conflict = constructConflict(assertion[0]);
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

        if(Debug.isOn("uf")) {
          Debug("uf") << "true == false ? "
                      << (find(d_trueNode) == find(d_falseNode)) << std::endl;
        }

        Assert(find(d_trueNode) != find(d_falseNode));

        merge(eq[0], eq[1]);
      }
      break;
    default:
      Unhandled(assertion.getKind());
    }

    if(Debug.isOn("uf")) {
      dump();
    }
  }
  Debug("uf") << "uf check() done = " << (done() ? "true" : "false") << std::endl;

  for(CDList<Node>::const_iterator diseqIter = d_disequality.begin();
      diseqIter != d_disequality.end();
      ++diseqIter) {

    TNode left  = (*diseqIter)[0];
    TNode right = (*diseqIter)[1];
    if(Debug.isOn("uf")) {
      Debug("uf") << "testing left: " << left << std::endl
                  << "       right: " << right << std::endl
                  << "     find(L): " << debugFind(left) << std::endl
                  << "     find(R): " << debugFind(right) << std::endl
                  << "     areCong: " << d_cc.areCongruent(left, right) << std::endl;
    }
    Assert((debugFind(left) == debugFind(right)) == d_cc.areCongruent(left, right));
  }

  Debug("uf") << "uf: end check(" << level << ")" << std::endl;
}

void TheoryUFMorgan::propagate(Effort level) {
  Debug("uf") << "uf: begin propagate(" << level << ")" << std::endl;
  Debug("uf") << "uf: end propagate(" << level << ")" << std::endl;
}

void TheoryUFMorgan::dump() {
  if(!Debug.isOn("uf")) {
    return;
  }
  Debug("uf") << "============== THEORY_UF ==============" << std::endl;
  Debug("uf") << "Active assertions list:" << std::endl;
  for(context::CDList<Node>::const_iterator i = d_activeAssertions.begin();
      i != d_activeAssertions.end();
      ++i) {
    Debug("uf") << "    " << *i << std::endl;
  }
  Debug("uf") << "Congruence union-find:" << std::endl;
  for(UnionFind::const_iterator i = d_unionFind.begin();
      i != d_unionFind.end();
      ++i) {
    Debug("uf") << "    " << (*i).first << "  ==>  " << (*i).second << std::endl;
  }
  Debug("uf") << "Disequality lists:" << std::endl;
  for(DiseqLists::const_iterator i = d_disequalities.begin();
      i != d_disequalities.end();
      ++i) {
    Debug("uf") << "    " << (*i).first << ":" << std::endl;
    DiseqList* dl = (*i).second;
    for(DiseqList::const_iterator j = dl->begin();
        j != dl->end();
        ++j) {
      Debug("uf") << "        " << *j << std::endl;
    }
  }
  Debug("uf") << "=======================================" << std::endl;
}

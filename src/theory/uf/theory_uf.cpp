/*********************                                                        */
/*! \file theory_uf.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is the interface to TheoryUF implementations
 **
 ** This is the interface to TheoryUF implementations.  All
 ** implementations of TheoryUF should inherit from this class.
 **/

#include "theory/uf/theory_uf.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

/** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
TheoryUF::TheoryUF(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
  Theory(THEORY_UF, c, u, out, valuation, logicInfo),
  d_notify(*this),
  d_equalityEngine(d_notify, c, "theory::uf::TheoryUF"),
  d_conflict(c, false),
  d_literalsToPropagate(c),
  d_literalsToPropagateIndex(c, 0),
  d_functionsTerms(c)
{
  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::APPLY_UF);
}/* TheoryUF::TheoryUF() */

static Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

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

void TheoryUF::check(Effort level) {

  while (!done() && !d_conflict) 
  {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("uf") << "TheoryUF::check(): processing " << fact << std::endl;

    // Do the work
    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];
    if (atom.getKind() == kind::EQUAL) {
      d_equalityEngine.assertEquality(atom, polarity, fact);
    } else {
      d_equalityEngine.assertPredicate(atom, polarity, fact);
    }
  }

}/* TheoryUF::check() */

void TheoryUF::preRegisterTerm(TNode node) {
  Debug("uf") << "TheoryUF::preRegisterTerm(" << node << ")" << std::endl;

  switch (node.getKind()) {
  case kind::EQUAL:
    // Add the trigger for equality
    d_equalityEngine.addTriggerEquality(node);
    break;
  case kind::APPLY_UF:
    // Maybe it's a predicate
    if (node.getType().isBoolean()) {
      // Get triggered for both equal and dis-equal
      d_equalityEngine.addTriggerPredicate(node);
    } else {
      // Function applications/predicates
      d_equalityEngine.addTerm(node);
    }
    // Remember the function and predicate terms
    d_functionsTerms.push_back(node);
    break;
  default:
    // Variables etc
    d_equalityEngine.addTerm(node);
    break;
  }
}/* TheoryUF::preRegisterTerm() */

bool TheoryUF::propagate(TNode literal) {
  Debug("uf::propagate") << "TheoryUF::propagate(" << literal  << ")" << std::endl;
  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("uf::propagate") << "TheoryUF::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }
  // Propagate out
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}/* TheoryUF::propagate(TNode) */

void TheoryUF::explain(TNode literal, std::vector<TNode>& assumptions) {
  // Do the work
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
  }
}

Node TheoryUF::explain(TNode literal) {
  Debug("uf") << "TheoryUF::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  explain(literal, assumptions);
  return mkAnd(assumptions);
}

void TheoryUF::presolve() {
  // TimerStat::CodeTimer codeTimer(d_presolveTimer);

  Debug("uf") << "uf: begin presolve()" << endl;
  if(Options::current()->ufSymmetryBreaker) {
    vector<Node> newClauses;
    d_symb.apply(newClauses);
    for(vector<Node>::const_iterator i = newClauses.begin();
        i != newClauses.end();
        ++i) {
      d_out->lemma(*i);
    }
  }
  Debug("uf") << "uf: end presolve()" << endl;
}

void TheoryUF::ppStaticLearn(TNode n, NodeBuilder<>& learned) {
  //TimerStat::CodeTimer codeTimer(d_staticLearningTimer);

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

  if(Options::current()->ufSymmetryBreaker) {
    d_symb.assertFormula(n);
  }
}/* TheoryUF::ppStaticLearn() */

EqualityStatus TheoryUF::getEqualityStatus(TNode a, TNode b) {

  // Check for equality (simplest)
  if (d_equalityEngine.areEqual(a, b)) {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }

  // Check for disequality
  if (d_equalityEngine.areDisequal(a, b, false)) {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }

  // All other terms we interpret as dis-equal in the model
  return EQUALITY_FALSE_IN_MODEL;
}

void TheoryUF::addSharedTerm(TNode t) {
  Debug("uf::sharing") << "TheoryUF::addSharedTerm(" << t << ")" << std::endl;
  d_equalityEngine.addTriggerTerm(t, THEORY_UF);
}

void TheoryUF::computeCareGraph() {

  if (d_sharedTerms.size() > 0) {

    vector< pair<TNode, TNode> > currentPairs;

    // Go through the function terms and see if there are any to split on
    unsigned functionTerms = d_functionsTerms.size();
    for (unsigned i = 0; i < functionTerms; ++ i) {

      TNode f1 = d_functionsTerms[i];
      Node op = f1.getOperator();

      for (unsigned j = i + 1; j < functionTerms; ++ j) {

        TNode f2 = d_functionsTerms[j];

        // If the operators are not the same, we can skip this pair
        if (f2.getOperator() != op) {
          continue;
        }

        Debug("uf::sharing") << "TheoryUf::computeCareGraph(): checking function " << f1 << " and " << f2 << std::endl;

        // If the terms are already known to be equal, we are also in good shape
        if (d_equalityEngine.areEqual(f1, f2)) {
          Debug("uf::sharing") << "TheoryUf::computeCareGraph(): equal, skipping" << std::endl;
          continue;
        }

        // We have two functions f(x1, ..., xn) and f(y1, ..., yn) no known to be equal
        // We split on the argument pairs that are are not known, unless there is some
        // argument pair that is already dis-equal.
        bool somePairIsDisequal = false;
        currentPairs.clear();
        for (unsigned k = 0; k < f1.getNumChildren(); ++ k) {

          TNode x = f1[k];
          TNode y = f2[k];

          Debug("uf::sharing") << "TheoryUf::computeCareGraph(): checking arguments " << x << " and " << y << std::endl;

          if (d_equalityEngine.areDisequal(x, y, false)) {
            // Mark that there is a dis-equal pair and break
            somePairIsDisequal = true;
            Debug("uf::sharing") << "TheoryUf::computeCareGraph(): disequal, disregarding all" << std::endl;
            break;
          }

          if (d_equalityEngine.areEqual(x, y)) {
            // We don't need this one
            Debug("uf::sharing") << "TheoryUf::computeCareGraph(): equal" << std::endl;
            continue;
          }

          if (!d_equalityEngine.isTriggerTerm(x, THEORY_UF) || !d_equalityEngine.isTriggerTerm(y, THEORY_UF)) {
            // Not connected to shared terms, we don't care
            continue;
          }

          // Get representative trigger terms
          TNode x_shared = d_equalityEngine.getTriggerTermRepresentative(x, THEORY_UF);
          TNode y_shared = d_equalityEngine.getTriggerTermRepresentative(y, THEORY_UF);

          EqualityStatus eqStatusDomain = d_valuation.getEqualityStatus(x_shared, y_shared);
          switch (eqStatusDomain) {
          case EQUALITY_FALSE_AND_PROPAGATED:
          case EQUALITY_FALSE:
          case EQUALITY_FALSE_IN_MODEL:
            somePairIsDisequal = true;
            continue;
            break;
          default:
            break;
            // nothing
          }

          // Otherwise, we need to figure it out
          Debug("uf::sharing") << "TheoryUf::computeCareGraph(): adding to care-graph" << std::endl;
          currentPairs.push_back(make_pair(x_shared, y_shared));
        }

        if (!somePairIsDisequal) {
          for (unsigned i = 0; i < currentPairs.size(); ++ i) {
            addCarePair(currentPairs[i].first, currentPairs[i].second);
          }
        }
      }
    }
  }
}/* TheoryUF::computeCareGraph() */

void TheoryUF::conflict(TNode a, TNode b) {
  if (Theory::theoryOf(a) == theory::THEORY_BOOL) {
    d_conflictNode = explain(a.iffNode(b));
  } else {
    d_conflictNode = explain(a.eqNode(b));
  }
  d_out->conflict(d_conflictNode);
  d_conflict = true;
}

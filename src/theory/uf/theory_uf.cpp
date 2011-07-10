/*********************                                                        */
/*! \file theory_uf.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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
#include "theory/uf/equality_engine_impl.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

using namespace std;

Node mkAnd(const std::vector<TNode>& conjunctions) {
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
}

void TheoryUF::check(Effort level) {

  while (!done() && !d_conflict) {
    // Get all the assertions
    TNode assertion = get();
    Debug("uf") << "TheoryUF::check(): processing " << assertion << std::endl;

    // Fo the work
    switch (assertion.getKind()) {
    case kind::EQUAL:
      d_equalityEngine.addEquality(assertion[0], assertion[1], assertion);
      break;
    case kind::APPLY_UF:
      d_equalityEngine.addEquality(assertion, d_true, assertion);
      break;
    case kind::NOT:
      if (assertion[0].getKind() == kind::APPLY_UF) {
        d_equalityEngine.addEquality(assertion[0], d_false, assertion);
      } else {
        // disequality
        TNode equality = assertion[0];
        if (d_equalityEngine.getRepresentative(equality[0]) == d_equalityEngine.getRepresentative(equality[1])) {
          std::vector<TNode> assumptions;
          assumptions.push_back(assertion);
          explain(equality, assumptions);
          d_conflictNode = mkAnd(assumptions);
          d_conflict = true;
        }
      }
      break;
    default:
      Unreachable();
    }
  }

  // If in conflict, output the conflict
  if (d_conflict) {
    Debug("uf") << "TheoryUF::check(): conflict " << d_conflictNode << std::endl;
    d_out->conflict(d_conflictNode);
    d_literalsToPropagate.clear();
  }

  // Otherwise we propagate in order to detect a weird conflict like
  // p, x = y
  // p -> f(x) != f(y) -- f(x) = f(y) gets added to the propagation list at preregistration time
  // but when f(x) != f(y) is deduced by the sat solver, so it's asserted, and we don't detect the conflict
  // until we go through the propagation list
  propagate(level);
}

void TheoryUF::propagate(Effort level) {
  Debug("uf") << "TheoryUF::propagate()" << std::endl;
  if (!d_conflict) {
    for (unsigned i = 0; i < d_literalsToPropagate.size(); ++ i) {
      TNode literal = d_literalsToPropagate[i];
      Debug("uf") << "TheoryUF::propagate(): propagating " << literal << std::endl;
      bool satValue;
      if (!d_valuation.hasSatValue(literal, satValue)) {
        d_out->propagate(literal);
      } else {
        if (!satValue) {
          Debug("uf") << "TheoryUF::propagate(): in conflict" << std::endl;
          std::vector<TNode> assumptions;
          if (literal != d_false) {
            TNode negatedLiteral = literal.getKind() == kind::NOT ? literal[0] : (TNode) literal.notNode();
            assumptions.push_back(negatedLiteral);
          }
          explain(literal, assumptions);
          d_conflictNode = mkAnd(assumptions);
          d_conflict = true;
          break;
        } else {
          Debug("uf") << "TheoryUF::propagate(): already asserted" << std::endl;
        }
      }
    }
  }
  d_literalsToPropagate.clear();
}

void TheoryUF::preRegisterTerm(TNode node) {
  Debug("uf") << "TheoryUF::preRegisterTerm(" << node << ")" << std::endl;

  switch (node.getKind()) {
  case kind::EQUAL:
    // Add the terms
    d_equalityEngine.addTerm(node[0]);
    d_equalityEngine.addTerm(node[1]);
    // Add the trigger
    d_equalityEngine.addTriggerEquality(node[0], node[1], node);
    break;
  case kind::APPLY_UF:
    // Function applications/predicates
    d_equalityEngine.addTerm(node);
    // Maybe it's a predicate
    if (node.getType().isBoolean()) {
      // Get triggered for both equal and dis-equal
      d_equalityEngine.addTriggerEquality(node, d_true, node);
      d_equalityEngine.addTriggerEquality(node, d_false, node.notNode());
    }
  default:
    // Variables etc
    d_equalityEngine.addTerm(node);
    break;
  }
}

bool TheoryUF::propagate(TNode literal) {
  Debug("uf") << "TheoryUF::propagate(" << literal  << ")" << std::endl;

  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("uf") << "TheoryUF::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }

  // See if the literal has been asserted already
  bool satValue = false;
  bool isAsserted = literal == d_false || d_valuation.hasSatValue(literal, satValue);

  // If asserted, we're done or in conflict
  if (isAsserted) {
    if (satValue) {
      Debug("uf") << "TheoryUF::propagate(" << literal << ") => already known" << std::endl;
      return true;
    } else {
      Debug("uf") << "TheoryUF::propagate(" << literal << ") => conflict" << std::endl;
      std::vector<TNode> assumptions;
      if (literal != d_false) {
        TNode negatedLiteral = literal.getKind() == kind::NOT ? literal[0] : (TNode) literal.notNode();
        assumptions.push_back(negatedLiteral);
      }
      explain(literal, assumptions);
      d_conflictNode = mkAnd(assumptions);
      d_conflict = true;
      return false;
    }
  }

  // Nothing, just enqueue it for propagation and mark it as asserted already
  Debug("uf") << "TheoryUF::propagate(" << literal << ") => enqueuing for propagation" << std::endl;
  d_literalsToPropagate.push_back(literal);

  return true;
}

void TheoryUF::explain(TNode literal, std::vector<TNode>& assumptions) {
  TNode lhs, rhs;
  switch (literal.getKind()) {
    case kind::EQUAL:
      lhs = literal[0];
      rhs = literal[1];
      break;
    case kind::APPLY_UF:
      lhs = literal;
      rhs = d_true;
      break;
    case kind::NOT:
      lhs = literal[0];
      rhs = d_false;
      break;
    case kind::CONST_BOOLEAN:
      // we get to explain true = false, since we set false to be the trigger of this
      lhs = d_true;
      rhs = d_false;
      break;
    default:
      Unreachable();
  }
  d_equalityEngine.getExplanation(lhs, rhs, assumptions);
}

void TheoryUF::explain(TNode literal) {
  Debug("uf") << "TheoryUF::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  explain(literal, assumptions);
  d_out->explanation(mkAnd(assumptions));
}

void TheoryUF::staticLearning(TNode n, NodeBuilder<>& learned) {
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
}

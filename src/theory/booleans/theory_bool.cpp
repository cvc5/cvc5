/*********************                                                        */
/*! \file theory_bool.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory of booleans.
 **
 ** The theory of booleans.
 **/

#include "theory/theory.h"
#include "theory/booleans/theory_bool.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/valuation.h"
#include "util/boolean_simplification.h"

#include <vector>
#include <stack>
#include "util/hash.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace booleans {

Node TheoryBool::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {
  case kind::VARIABLE:
    // case for Boolean vars is implemented in TheoryEngine (since it
    // appeals to the PropEngine to get the value)
    Unreachable();

  case kind::EQUAL: // 2 args
    // should be handled by IFF
    Unreachable();

  case kind::NOT: // 1 arg
    return nodeManager->mkConst(! d_valuation.getValue(n[0]).getConst<bool>());

  case kind::AND: { // 2+ args
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      if(! d_valuation.getValue(*i).getConst<bool>()) {
        return nodeManager->mkConst(false);
      }
    }
    return nodeManager->mkConst(true);
  }

  case kind::IFF: // 2 args
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<bool>() ==
                                 d_valuation.getValue(n[1]).getConst<bool>() );

  case kind::IMPLIES: // 2 args
    return nodeManager->mkConst( (! d_valuation.getValue(n[0]).getConst<bool>()) ||
                                 d_valuation.getValue(n[1]).getConst<bool>() );

  case kind::OR: { // 2+ args
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      if(d_valuation.getValue(*i).getConst<bool>()) {
        return nodeManager->mkConst(true);
      }
    }
    return nodeManager->mkConst(false);
  }

  case kind::XOR: // 2 args
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<bool>() !=
                                 d_valuation.getValue(n[1]).getConst<bool>() );

  case kind::ITE: // 3 args
    // all ITEs should be gone except (bool,bool,bool) ones
    Assert( n[1].getType() == nodeManager->booleanType() &&
            n[2].getType() == nodeManager->booleanType() );
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<bool>() ?
                                 d_valuation.getValue(n[1]).getConst<bool>() :
                                 d_valuation.getValue(n[2]).getConst<bool>() );

  default:
    Unhandled(n.getKind());
  }
}

static void
findAtoms(TNode in, vector<TNode>& atoms,
          hash_map<TNode, vector<TNode>, TNodeHashFunction>& backEdges) {
  Kind k = in.getKind();
  Assert(kindToTheoryId(k) == THEORY_BOOL);

  stack< pair<TNode, TNode::iterator> > trail;
  hash_set<TNode, TNodeHashFunction> seen;
  trail.push(make_pair(in, in.begin()));

  while(!trail.empty()) {
    pair<TNode, TNode::iterator>& pr = trail.top();
    Debug("simplify") << "looking at: " << pr.first << endl;
    if(pr.second == pr.first.end()) {
      trail.pop();
    } else {
      if(pr.second == pr.first.begin()) {
        Debug("simplify") << "first visit: " << pr.first << endl;
        // first time we've visited this node?
        if(seen.find(pr.first) == seen.end()) {
          Debug("simplify") << "+ haven't seen it yet." << endl;
          seen.insert(pr.first);
        } else {
          Debug("simplify") << "+ saw it before." << endl;
          trail.pop();
          continue;
        }
      }
      TNode n = *pr.second++;
      if(seen.find(n) == seen.end()) {
        Debug("simplify") << "back edge " << n << " to " << pr.first << endl;
        backEdges[n].push_back(pr.first);
        Kind nk = n.getKind();
        if(kindToTheoryId(nk) == THEORY_BOOL) {
          trail.push(make_pair(n, n.begin()));
        } else {
          Debug("simplify") << "atom: " << n << endl;
          atoms.push_back(n);
        }
      }
    }
  }
}

Node TheoryBool::simplify(TNode in, Substitutions& outSubstitutions) {
  const unsigned prev = outSubstitutions.size();

  if(kindToTheoryId(in.getKind()) != THEORY_BOOL) {
    Assert(in.getMetaKind() == kind::metakind::VARIABLE &&
           in.getType().isBoolean());
    return in;
  }

  // form back edges and atoms
  vector<TNode> atoms;
  hash_map<TNode, vector<TNode>, TNodeHashFunction> backEdges;
  Debug("simplify") << "finding atoms..." << endl << push;
  findAtoms(in, atoms, backEdges);
  Debug("simplify") << pop << "done finding atoms..." << endl;

  hash_map<TNode, Node, TNodeHashFunction> simplified;

  vector<Node> newFacts;
  CircuitPropagator circuit(atoms, backEdges);
  Debug("simplify") << "propagate..." << endl;
  if(circuit.propagate(in, true, newFacts)) {
    Notice() << "Found a conflict in nonclausal Boolean reasoning" << endl;
    return NodeManager::currentNM()->mkConst(false);
  }
  Debug("simplify") << "done w/ propagate..." << endl;

  for(vector<Node>::iterator i = newFacts.begin(), i_end = newFacts.end(); i != i_end; ++i) {
    TNode a = *i;
    if(a.getKind() == kind::NOT) {
      if(a[0].getMetaKind() == kind::metakind::VARIABLE ) {
        Debug("simplify") << "found bool unit ~" << a[0] << "..." << endl;
        outSubstitutions.push_back(make_pair(a[0], NodeManager::currentNM()->mkConst(false)));
      } else if(kindToTheoryId(a[0].getKind()) != THEORY_BOOL) {
        Debug("simplify") << "simplifying: " << a << endl;
        simplified[a] = d_valuation.simplify(a, outSubstitutions);
        Debug("simplify") << "done simplifying, got: " << simplified[a] << endl;
      }
    } else {
      if(a.getMetaKind() == kind::metakind::VARIABLE) {
        Debug("simplify") << "found bool unit " << a << "..." << endl;
        outSubstitutions.push_back(make_pair(a, NodeManager::currentNM()->mkConst(true)));
      } else if(kindToTheoryId(a.getKind()) != THEORY_BOOL) {
        Debug("simplify") << "simplifying: " << a << endl;
        simplified[a] = d_valuation.simplify(a, outSubstitutions);
        Debug("simplify") << "done simplifying, got: " << simplified[a] << endl;
      }
    }
  }

  Debug("simplify") << "substituting in root..." << endl;
  Node n = in.substitute(outSubstitutions.begin(), outSubstitutions.end());
  Debug("simplify") << "got: " << n << endl;
  if(Debug.isOn("simplify")) {
    Debug("simplify") << "new substitutions:" << endl;
    copy(outSubstitutions.begin() + prev, outSubstitutions.end(),
         ostream_iterator< pair<TNode, TNode> >(Debug("simplify"), "\n"));
    Debug("simplify") << "done." << endl;
  }
  if(outSubstitutions.size() > prev) {
    NodeBuilder<> b(kind::AND);
    b << n;
    for(Substitutions::iterator i = outSubstitutions.begin() + prev,
          i_end = outSubstitutions.end();
        i != i_end;
        ++i) {
      if((*i).first.getType().isBoolean()) {
        if((*i).second.getMetaKind() == kind::metakind::CONSTANT) {
          if((*i).second.getConst<bool>()) {
            b << (*i).first;
          } else {
            b << BooleanSimplification::negate((*i).first);
          }
        } else {
          b << (*i).first.iffNode((*i).second);
        }
      } else {
        b << (*i).first.eqNode((*i).second);
      }
    }
    n = b;
  }
  Debug("simplify") << "final boolean simplification returned: " << n << endl;
  return n;
}


}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

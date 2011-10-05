/*********************                                                        */
/*! \file theory_bool.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
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

  case kind::NOT: { // 1 arg
    Node v = d_valuation.getValue(n[0]);
    return v.isNull() ? Node::null() : nodeManager->mkConst(! v.getConst<bool>());
  }

  case kind::AND: { // 2+ args
    bool foundNull = false;
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      Node v = d_valuation.getValue(*i);
      if(v.isNull()) {
        foundNull = true;
      } else if(! v.getConst<bool>()) {
        return nodeManager->mkConst(false);
      }
    }
    return foundNull ? Node::null() : nodeManager->mkConst(true);
  }

  case kind::IFF: { // 2 args
    Node v0 = d_valuation.getValue(n[0]);
    Node v1 = d_valuation.getValue(n[1]);
    if(v0.isNull() || v1.isNull()) {
      return Node::null();
    }
    return nodeManager->mkConst( v0.getConst<bool>() == v1.getConst<bool>() );
  }

  case kind::IMPLIES: { // 2 args
    Node v0 = d_valuation.getValue(n[0]);
    Node v1 = d_valuation.getValue(n[1]);
    if(v0.isNull() && v1.isNull()) {
      return Node::null();
    }
    bool value = false;
    if(! v0.isNull()) {
      value = value || (! v0.getConst<bool>());
    }
    if(! v1.isNull()) {
      value = value || v1.getConst<bool>();
    }
    return nodeManager->mkConst(value);
  }

  case kind::OR: { // 2+ args
    bool foundNull = false;
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      Node v = d_valuation.getValue(*i);
      if(v.isNull()) {
        foundNull = true;
      } else if(v.getConst<bool>()) {
        return nodeManager->mkConst(true);
      }
    }
    return foundNull ? Node::null() : nodeManager->mkConst(false);
  }

  case kind::XOR: { // 2 args
    Node v0 = d_valuation.getValue(n[0]);
    Node v1 = d_valuation.getValue(n[1]);
    if(v0.isNull() || v1.isNull()) {
      return Node::null();
    }
    return nodeManager->mkConst( v0.getConst<bool>() != v1.getConst<bool>() );
  }

  case kind::ITE: { // 3 args
    // all ITEs should be gone except (bool,bool,bool) ones
    Assert( n[1].getType() == nodeManager->booleanType() &&
            n[2].getType() == nodeManager->booleanType() );
    Node v0 = d_valuation.getValue(n[0]);
    Node v1 = d_valuation.getValue(n[1]);
    Node v2 = d_valuation.getValue(n[2]);
    if(v0.isNull()) {
      return v1 == v2 ? v1 : Node::null();
    }
    return nodeManager->mkConst( v0.getConst<bool>() ? v1.getConst<bool>() : v2.getConst<bool>() );
  }

  default:
    Unhandled(n.getKind());
  }
}

Theory::SolveStatus TheoryBool::solve(TNode in, SubstitutionMap& outSubstitutions) {

  if (in.getKind() == kind::CONST_BOOLEAN && !in.getConst<bool>()) {
    // If we get a false literal, we're in conflict
    return SOLVE_STATUS_CONFLICT;
  }

  // Add the substitution from the variable to it's value
  if (in.getKind() == kind::NOT) {
    if (in[0].getKind() == kind::VARIABLE) {
      outSubstitutions.addSubstitution(in[0], NodeManager::currentNM()->mkConst<bool>(false));
    } else {
      return SOLVE_STATUS_UNSOLVED;
    }
  } else {
    if (in.getKind() == kind::VARIABLE) {
      outSubstitutions.addSubstitution(in, NodeManager::currentNM()->mkConst<bool>(true));
    } else {
      return SOLVE_STATUS_UNSOLVED;
    }
  }

  return SOLVE_STATUS_SOLVED;
}


}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

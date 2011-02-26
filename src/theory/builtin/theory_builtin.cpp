/*********************                                                        */
/*! \file theory_builtin.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the builtin theory.
 **
 ** Implementation of the builtin theory.
 **/

#include "theory/builtin/theory_builtin.h"
#include "theory/valuation.h"
#include "expr/kind.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace builtin {

Node TheoryBuiltin::getValue(TNode n, Valuation* valuation) {
  switch(n.getKind()) {

  case kind::VARIABLE:
    // no variables that the builtin theory is responsible for
    Unreachable();

  case kind::EQUAL: { // 2 args
    // has to be an EQUAL over tuples, since all others should be
    // handled elsewhere
    Assert(n[0].getKind() == kind::TUPLE &&
           n[1].getKind() == kind::TUPLE);
    return NodeManager::currentNM()->
      mkConst( getValue(n[0], valuation) == getValue(n[1], valuation) );
  }

  case kind::TUPLE: { // 2+ args
    NodeBuilder<> nb(kind::TUPLE);
    for(TNode::iterator i = n.begin(),
          iend = n.end();
        i != iend;
        ++i) {
      nb << valuation->getValue(*i);
    }
    return Node(nb);
  }

  default:
    // all other "builtins" should have been rewritten away or handled
    // by the valuation, or handled elsewhere.
    Unhandled(n.getKind());
  }
}

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory */
}/* CVC4 namespace */

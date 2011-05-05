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

Node TheoryBuiltin::simplify(TNode in, Substitutions& outSubstitutions) {
  if(in.getKind() == kind::EQUAL) {
    Node lhs = d_valuation.simplify(in[0], outSubstitutions);
    Node rhs = d_valuation.simplify(in[1], outSubstitutions);
    Node n = lhs.eqNode(rhs);
    if( n[0].getMetaKind() == kind::metakind::VARIABLE &&
        n[1].getMetaKind() == kind::metakind::CONSTANT ) {
      Debug("simplify:builtin") << "found new substitution! "
                                << n[0] << " => " << n[1] << endl;
      outSubstitutions.push_back(make_pair(n[0], n[1]));
      // with our substitutions we've subsumed the equality
      return NodeManager::currentNM()->mkConst(true);
    } else if( n[1].getMetaKind() == kind::metakind::VARIABLE &&
               n[0].getMetaKind() == kind::metakind::CONSTANT ) {
      Debug("simplify:builtin") << "found new substitution! "
                                << n[1] << " => " << n[0] << endl;
      outSubstitutions.push_back(make_pair(n[1], n[0]));
      // with our substitutions we've subsumed the equality
      return NodeManager::currentNM()->mkConst(true);
    }
  } else if(in.getKind() == kind::NOT && in[0].getKind() == kind::DISTINCT) {
    TNode::iterator found = in[0].end();
    for(TNode::iterator i = in[0].begin(), i_end = in[0].end(); i != i_end; ++i) {
      if((*i).getMetaKind() == kind::metakind::CONSTANT) {
        found = i;
        break;
      }
    }
    if(found != in[0].end()) {
      for(TNode::iterator i = in[0].begin(), i_end = in[0].end(); i != i_end; ++i) {
        if(i != found) {
          outSubstitutions.push_back(make_pair(*i, *found));
        }
      }
      // with our substitutions we've subsumed the (NOT (DISTINCT...))
      return NodeManager::currentNM()->mkConst(true);
    }
  }
  return in;
}

Node TheoryBuiltin::getValue(TNode n) {
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
      mkConst( getValue(n[0]) == getValue(n[1]) );
  }

  case kind::TUPLE: { // 2+ args
    NodeBuilder<> nb(kind::TUPLE);
    for(TNode::iterator i = n.begin(),
          iend = n.end();
        i != iend;
        ++i) {
      nb << d_valuation.getValue(*i);
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

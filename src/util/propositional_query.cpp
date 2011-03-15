/*********************                                                        */
/*! \file propositional_query.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A class for simple, quick, propositional
 ** satisfiability/validity checking
 **
 ** PropositionalQuery is a way for parts of CVC4 to do quick purely
 ** propositional satisfiability or validity checks on a Node.  These
 ** checks do no theory reasoning, and handle atoms as propositional
 ** variables, but can sometimes be useful for subqueries.
 **/

#include "util/propositional_query.h"

#include <map>
#include <algorithm>

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;

#ifdef CVC4_CUDD

#include <util.h>
#include <cudd.h>
#include <cuddObj.hh>

namespace CVC4 {

class BddInstance {
private:
  Cudd d_mgr;
  typedef std::map<Node, BDD> AtomToIDMap;
  AtomToIDMap d_atomToBddMap;

  unsigned d_atomId;

  BDD encodeNode(TNode t);
  BDD encodeAtom(TNode t);
  BDD encodeCombinator(TNode t);

  bool isAnAtom(TNode t) {
    switch(t.getKind()) {
    case NOT:
    case XOR:
    case IFF:
    case IMPLIES:
    case OR:
    case AND:
      return false;
    case ITE:
      return t.getType().isBoolean();
    default:
      return true;
    }
  }

  void setupAtoms(TNode t);

  void clear() {
    d_atomId = 0;
    d_atomToBddMap.clear();
  }

  Result d_result;

public:
  static const unsigned MAX_VARIABLES = 20;

  BddInstance(TNode t) : d_atomToBddMap(), d_atomId(0) {
    setupAtoms(t);

    Debug("bdd::sat") << t << endl;
    Debug("bdd::sat") << d_atomToBddMap.size() << endl;


    if(d_atomToBddMap.size() > MAX_VARIABLES) {
      d_result = Result(Result::SAT_UNKNOWN, Result::TIMEOUT);
    } else {
      BDD res = encodeNode(t);
      BDD falseBdd = d_mgr.bddZero();
      bool isUnsat = (res == falseBdd);

      clear();

      if(isUnsat) {
        d_result = Result::UNSAT;
      } else {
        d_result = Result::SAT;
      }
    }
  }

  Result getResult() const { return d_result; }

};/* class BddInstance */

}/* CVC4 namespace */

BDD BddInstance::encodeNode(TNode t) {
  if(isAnAtom(t)) {
    return encodeAtom(t);
  } else {
    return encodeCombinator(t);
  }
}

BDD BddInstance::encodeCombinator(TNode t) {
  switch(t.getKind()) {
  case XOR: {
    Assert(t.getNumChildren() == 2);
    return encodeNode(t[0]).Xor(encodeNode(t[1]));
  }

  case IFF: {
    Assert(t.getNumChildren() == 2);
    BDD left = encodeNode(t[0]);
    BDD right = encodeNode(t[1]);
    return (!left | right) & (left | !right);
  }

  case IMPLIES: {
    Assert(t.getNumChildren() == 2);
    BDD left = encodeNode(t[0]);
    BDD right = encodeNode(t[1]);
    return (!left | right);
  }

  case AND:
  case OR: {
    Assert(t.getNumChildren() >= 2);
    TNode::iterator i = t.begin(), end = t.end();
    BDD tmp = encodeNode(*i);
    ++i;
    for(; i != end; ++i) {
      BDD curr = encodeNode(*i);
      if(t.getKind() == AND) {
        tmp = tmp & curr;
      } else {
        tmp = tmp | curr;
      }
    }
    return tmp;
  }

  case ITE: {
    Assert(t.getType().isBoolean());
    BDD cnd = encodeNode(t[0]);
    BDD thenBranch = encodeNode(t[1]);
    BDD elseBranch = encodeNode(t[2]);
    return cnd.Ite(thenBranch, elseBranch);
  }

  case NOT:
    return ! encodeNode(t[0]);

  default:
    Unhandled(t.getKind());
  }
}

BDD BddInstance::encodeAtom(TNode t) {
  if(t.getKind() == kind::CONST_BOOLEAN) {
    if(t.getConst<bool>()) {
      return d_mgr.bddOne();
    } else {
      return d_mgr.bddZero();
    }
  }
  Assert(t.getKind() != kind::CONST_BOOLEAN);

  AtomToIDMap::iterator findT = d_atomToBddMap.find(t);

  Assert(d_atomToBddMap.find(t) != d_atomToBddMap.end());
  return findT->second;
}

void BddInstance::setupAtoms(TNode t) {
  if(t.getKind() == kind::CONST_BOOLEAN) {
    // do nothing
  } else if(isAnAtom(t)) {
    AtomToIDMap::iterator findT = d_atomToBddMap.find(t);
    if(findT == d_atomToBddMap.end()) {
      BDD var = d_mgr.bddVar();
      d_atomToBddMap.insert(make_pair(t, var));
      d_atomId++;
    }
  } else {
    for(TNode::iterator i = t.begin(), end = t.end(); i != end; ++i) {
      setupAtoms(*i);
    }
  }
}

Result PropositionalQuery::isSatisfiable(TNode q) {
  BddInstance instance(q);
  return instance.getResult();
}

Result PropositionalQuery::isTautology(TNode q) {
  Node negQ = q.notNode();
  Result satResult = isSatisfiable(negQ);
  return satResult.asValidityResult();
}

#else /* CVC4_CUDD */

// if CUDD wasn't available at build time, just return UNKNOWN everywhere.

Result PropositionalQuery::isSatisfiable(TNode q) {
  return Result(Result::SAT_UNKNOWN, Result::UNSUPPORTED);
}

Result PropositionalQuery::isTautology(TNode q) {
  return Result(Result::VALIDITY_UNKNOWN, Result::UNSUPPORTED);
}

#endif /* CVC4_CUDD */

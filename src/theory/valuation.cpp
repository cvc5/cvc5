/*********************                                                        */
/*! \file valuation.cpp
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
 ** \brief A "valuation" proxy for TheoryEngine
 **
 ** Implementation of Valuation class.
 **/

#include "expr/node.h"
#include "theory/valuation.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

Node Valuation::getValue(TNode n) const {
  return d_engine->getValue(n);
}

Node Valuation::getSatValue(TNode n) const{
  if(n.getKind() == kind::NOT) {
    Node atomRes = d_engine->getPropEngine()->getValue(n[0]);
    if(atomRes.getKind() == kind::CONST_BOOLEAN){
      return NodeManager::currentNM()->mkConst(!atomRes.getConst<bool>());
    }else{
      Assert(atomRes.isNull());
      return atomRes;
    }
  } else {
    return d_engine->getPropEngine()->getValue(n);
  }
}

Node Valuation::simplify(TNode in, Substitutions& outSubstitutions) {
  return d_engine->simplify(in, outSubstitutions);
}

Node Valuation::rewrite(TNode in) {
  return d_engine->preprocess(in);
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

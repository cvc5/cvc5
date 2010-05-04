/*********************                                                        */
/** theory_bool_type_rules.cpp
 ** Original author: dejan
 ** Major contributors: none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_BOOL_TYPE_RULES_H_
#define __CVC4__THEORY_BOOL_TYPE_RULES_H_

namespace CVC4 {
namespace theory {
namespace boolean {

class BooleanTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n)
      throw (TypeCheckingException) {
    TypeNode booleanType = nodeManager->booleanType();
    TNode::iterator child_it = n.begin();
    TNode::iterator child_it_end = n.end();
    for(; child_it != child_it_end; ++child_it)
      if((*child_it).getType() != booleanType) {
        throw TypeCheckingExceptionPrivate(n, "expecting a Boolean subexpression");
      }
    return booleanType;
  }
};

class IteTypeRule {
  public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n) throw (TypeCheckingException) {
    TypeNode booleanType = nodeManager->booleanType();
    if (n[0].getType() != booleanType) {
      throw TypeCheckingExceptionPrivate(n, "condition of ITE is not Boolean");
    }
    TypeNode iteType = n[1].getType();
    if (iteType != n[2].getType()) {
      throw TypeCheckingExceptionPrivate(n, "both branches of the ITE must be of the same type");
    }
    return iteType;
  }
};

} // boolean namespace
} // theory namespace
} // CVC4 namespace

#endif /* __CVC4__THEORY_BOOL_TYPE_RULES_H_ */

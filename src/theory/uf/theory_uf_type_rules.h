/*********************                                                        */
/** theory_uf_type_rules.h
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

#ifndef __CVC4__THEORY_UF_TYPE_RULES_H_
#define __CVC4__THEORY_UF_TYPE_RULES_H_

namespace CVC4 {
namespace theory {
namespace uf {

class UfTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n)
      throw (TypeCheckingException) {
    TNode f = n.getOperator();
    TypeNode fType = f.getType();
    if (n.getNumChildren() != fType.getNumChildren() - 1) {
      throw TypeCheckingExceptionPrivate(n, "number of arguments does not match the function type");
    }
    TNode::iterator argument_it = n.begin();
    TNode::iterator argument_it_end = n.end();
    TypeNode::iterator argument_type_it = fType.begin();
    for(; argument_it != argument_it_end; ++argument_it)
      if((*argument_it).getType() != *argument_type_it) {
        throw TypeCheckingExceptionPrivate(n, "argument types do not match the function type");
      }
    return fType.getRangeType();
  }
};

}
}
}


#endif /* THEORY_UF_TYPE_RULES_H_ */

/*********************                                                        */
/*! \file theory_uf_type_rules.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: cconway, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add brief comments here ]]
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__THEORY_UF_TYPE_RULES_H
#define __CVC4__THEORY__UF__THEORY_UF_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace uf {

class UfTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate) {
    TNode f = n.getOperator();
    TypeNode fType = f.getType(check);
    if( !fType.isFunction() ) {
      throw TypeCheckingExceptionPrivate(n, "operator does not have function type");
    }
    if( check ) {
      if (n.getNumChildren() != fType.getNumChildren() - 1) {
        throw TypeCheckingExceptionPrivate(n, "number of arguments does not match the function type");
      }
      TNode::iterator argument_it = n.begin();
      TNode::iterator argument_it_end = n.end();
      TypeNode::iterator argument_type_it = fType.begin();
      for(; argument_it != argument_it_end; ++argument_it) {
        if((*argument_it).getType() != *argument_type_it) {
          throw TypeCheckingExceptionPrivate(n, "argument types do not match the function type");
        }
      }
    }
    return fType.getRangeType();
  }
};/* class UfTypeRule */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_TYPE_RULES_H */

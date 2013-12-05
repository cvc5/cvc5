/*********************                                                        */
/*! \file theory_uf_type_rules.h
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Christopher L. Conway, Andrew Reynolds, Morgan Deters
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
      throw (TypeCheckingExceptionPrivate, AssertionException) {
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
      for(; argument_it != argument_it_end; ++argument_it, ++argument_type_it) {
        TypeNode currentArgument = (*argument_it).getType();
        TypeNode currentArgumentType = *argument_type_it;
        if(!currentArgument.isComparableTo(currentArgumentType)) {
          std::stringstream ss;
          ss << "argument type is not a subtype of the function's argument type:\n"
             << "argument:  " << *argument_it << "\n"
             << "has type:  " << (*argument_it).getType() << "\n"
             << "not subtype: " << *argument_type_it;
          throw TypeCheckingExceptionPrivate(n, ss.str());
        }
      }
    }
    return fType.getRangeType();
  }
};/* class UfTypeRule */

class CardinalityConstraintTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw(TypeCheckingExceptionPrivate) {
    if( check ) {
      TypeNode valType = n[1].getType(check);
      if( valType != nodeManager->integerType() ) {
        throw TypeCheckingExceptionPrivate(n, "cardinality constraint must be integer");
      }
    }
    return nodeManager->booleanType();
  }
};/* class CardinalityConstraintTypeRule */

class CombinedCardinalityConstraintTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw(TypeCheckingExceptionPrivate) {
    if( check ) {
      TypeNode valType = n[0].getType(check);
      if( valType != nodeManager->integerType() ) {
        throw TypeCheckingExceptionPrivate(n, "combined cardinality constraint must be integer");
      }
    }
    return nodeManager->booleanType();
  }
};/* class CardinalityConstraintTypeRule */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_TYPE_RULES_H */

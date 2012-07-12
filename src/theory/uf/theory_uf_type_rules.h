/*********************                                                        */
/*! \file theory_uf_type_rules.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: cconway, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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
        if(!currentArgument.isSubtypeOf(currentArgumentType)) {
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

class FunctionModelTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw(TypeCheckingExceptionPrivate) {
    TypeNode tn = n[0].getType(check);
    if( check ){
      if( n.getNumChildren()==2 ){
        if( n[0].getKind()!=kind::FUNCTION_CASE_SPLIT ){
          throw TypeCheckingExceptionPrivate(n, "improper function model representation : first child must be case split");
        }
        TypeNode tn2 = n[1].getType(check);
        if( tn!=tn2 ){
          std::stringstream ss;
          ss << "function model has inconsistent return types : " << tn << " " << tn2;
          throw TypeCheckingExceptionPrivate(n, ss.str());
        }
      }
    }
    return tn;
  }
};/* class FunctionModelTypeRule */

class FunctionCaseSplitTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw(TypeCheckingExceptionPrivate) {
    TypeNode retType = n[0][1].getType(check);
    if( check ){
      TypeNode argType = n[0][0].getType(check);
      for( size_t i=0; i<n.getNumChildren(); i++ ){
        TypeNode argType2 = n[i][0].getType(check);
        if( argType!=argType2 ){
          std::stringstream ss;
          ss << "function case split has inconsistent argument types : " << argType << " " << argType2;
          throw TypeCheckingExceptionPrivate(n, ss.str());
        }
        TypeNode retType2 = n[i][1].getType(check);
        if( retType!=retType2 ){
          std::stringstream ss;
          ss << "function case split has inconsistent return types : " << retType << " " << retType2;
          throw TypeCheckingExceptionPrivate(n, ss.str());
        }
      }
    }
    return retType;
  }
};/* class FunctionCaseSplitTypeRule */


class FunctionCaseTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw(TypeCheckingExceptionPrivate) {
    TypeNode retType = n[1].getType(check);
    if( check ){
      TypeNode argType = n[0].getType(check);
    }
    return retType;
  }
};/* class FunctionCaseTypeRule */


}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_TYPE_RULES_H */

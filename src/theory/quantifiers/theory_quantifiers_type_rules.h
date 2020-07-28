/*********************                                                        */
/*! \file theory_quantifiers_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory of quantifiers
 **
 ** Theory of quantifiers.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_TYPE_RULES_H
#define CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

struct QuantifierForallTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Debug("typecheck-q") << "type check for fa " << n << std::endl;
    Assert(n.getKind() == kind::FORALL && n.getNumChildren() > 0);
    if( check ){
      if( n[ 0 ].getType(check)!=nodeManager->boundVarListType() ){
        throw TypeCheckingExceptionPrivate(n, "first argument of universal quantifier is not bound var list");
      }
      if( n[ 1 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "body of universal quantifier is not boolean");
      }
      if( n.getNumChildren()==3 && n[2].getType(check)!=nodeManager->instPatternListType() ){
        throw TypeCheckingExceptionPrivate(n, "third argument of universal quantifier is not instantiation pattern list");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct QuantifierForallTypeRule */

struct QuantifierExistsTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Debug("typecheck-q") << "type check for ex " << n << std::endl;
    Assert(n.getKind() == kind::EXISTS && n.getNumChildren() > 0);
    if( check ){
      if( n[ 0 ].getType(check)!=nodeManager->boundVarListType() ){
        throw TypeCheckingExceptionPrivate(n, "first argument of existential quantifier is not bound var list");
      }
      if( n[ 1 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "body of existential quantifier is not boolean");
      }
      if( n.getNumChildren()==3 && n[2].getType(check)!=nodeManager->instPatternListType() ){
        throw TypeCheckingExceptionPrivate(n, "third argument of existential quantifier is not instantiation pattern list");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct QuantifierExistsTypeRule */

struct QuantifierBoundVarListTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::BOUND_VAR_LIST);
    if( check ){
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        if( n[i].getKind()!=kind::BOUND_VARIABLE ){
          throw TypeCheckingExceptionPrivate(n, "argument of bound var list is not bound variable");
        }
      }
    }
    return nodeManager->boundVarListType();
  }
};/* struct QuantifierBoundVarListTypeRule */

struct QuantifierInstPatternTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::INST_PATTERN);
    if( check ){
      TypeNode tn = n[0].getType(check);
      // this check catches the common mistake writing :pattern (f x) instead of :pattern ((f x))
      if( n[0].isVar() && n[0].getKind()!=kind::BOUND_VARIABLE && tn.isFunction() ){
        throw TypeCheckingExceptionPrivate(n[0], "Pattern must be a list of fully-applied terms.");
      }
    }
    return nodeManager->instPatternType();
  }
};/* struct QuantifierInstPatternTypeRule */

struct QuantifierInstNoPatternTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::INST_NO_PATTERN);
    return nodeManager->instPatternType();
  }
};/* struct QuantifierInstNoPatternTypeRule */

struct QuantifierInstAttributeTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::INST_ATTRIBUTE);
    return nodeManager->instPatternType();
  }
};/* struct QuantifierInstAttributeTypeRule */

struct QuantifierInstPatternListTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::INST_PATTERN_LIST);
    if( check ){
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        if( n[i].getKind()!=kind::INST_PATTERN && n[i].getKind()!=kind::INST_NO_PATTERN && n[i].getKind()!=kind::INST_ATTRIBUTE ){
          throw TypeCheckingExceptionPrivate(n, "argument of inst pattern list is not inst pattern");
        }
      }
    }
    return nodeManager->instPatternListType();
  }
};/* struct QuantifierInstPatternListTypeRule */

struct QuantifierInstClosureTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::INST_CLOSURE);
    if( check ){
      TypeNode tn = n[0].getType(check);
      if( tn.isBoolean() ){
        throw TypeCheckingExceptionPrivate(n, "argument of inst-closure must be non-boolean");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct QuantifierInstClosureTypeRule */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_TYPE_RULES_H */

/*********************                                                        */
/*! \file theory_sets_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory type rules.
 **
 ** Sets theory type rules.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SETS__THEORY_SETS_TYPE_RULES_H
#define __CVC4__THEORY__SETS__THEORY_SETS_TYPE_RULES_H

#include "theory/sets/normal_form.h"

namespace CVC4 {
namespace theory {
namespace sets {

class SetsTypeRule {
public:

  /**
   * Compute the type for (and optionally typecheck) a term belonging
   * to the theory of sets.
   *
   * @param check if true, the node's type should be checked as well
   * as computed.
   */
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check)
    throw (TypeCheckingExceptionPrivate) {

    // TODO: implement me!
    Unimplemented();

  }

};/* class SetsTypeRule */

struct SetsBinaryOperatorTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::UNION ||
           n.getKind() == kind::INTERSECTION ||
           n.getKind() == kind::SETMINUS);
    TypeNode setType = n[0].getType(check);
    if( check ) {
      if(!setType.isSet()) {
        throw TypeCheckingExceptionPrivate(n, "operator expects a set, first argument is not");
      }
      TypeNode secondSetType = n[1].getType(check);
      if(secondSetType != setType) {
        throw TypeCheckingExceptionPrivate(n, "operator expects two sets of the same type");
      }
    }
    return setType;
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n) {
    Assert(n.getKind() == kind::UNION ||
           n.getKind() == kind::INTERSECTION ||
           n.getKind() == kind::SETMINUS);
    if(n.getKind() == kind::UNION) {
      return NormalForm::checkNormalConstant(n);
    } else {
      return false;
    }
  }
};/* struct SetUnionTypeRule */

struct SubsetTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::SUBSET);
    TypeNode setType = n[0].getType(check);
    if( check ) {
      if(!setType.isSet()) {
        throw TypeCheckingExceptionPrivate(n, "set subset operating on non-set");
      }
      TypeNode secondSetType = n[1].getType(check);
      if(secondSetType != setType) {
        throw TypeCheckingExceptionPrivate(n, "set subset operating on sets of different types");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct SetSubsetTypeRule */

struct MemberTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::MEMBER);
    TypeNode setType = n[1].getType(check);
    if( check ) {
      if(!setType.isSet()) {
        throw TypeCheckingExceptionPrivate(n, "checking for membership in a non-set");
      }
      TypeNode elementType = n[0].getType(check);
      if(elementType != setType.getSetElementType()) {
        throw TypeCheckingExceptionPrivate(n, "member operating on sets of different types");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct MemberTypeRule */

struct SingletonTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::SINGLETON);
    return nodeManager->mkSetType(n[0].getType(check));
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n) {
    Assert(n.getKind() == kind::SINGLETON);
    return n[0].isConst();
  }
};/* struct SingletonTypeRule */

struct EmptySetTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::EMPTYSET);
    EmptySet emptySet = n.getConst<EmptySet>();
    Type setType = emptySet.getType();
    return TypeNode::fromType(setType);
  }
};/* struct EmptySetTypeRule */

struct CardTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::CARD);
    TypeNode setType = n[0].getType(check);
    if( check ) {
      if(!setType.isSet()) {
        throw TypeCheckingExceptionPrivate(n, "cardinality operates on a set, non-set object found");
      }
    }
    return nodeManager->integerType();
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n) {
    Assert(n.getKind() == kind::CARD);
    return false;
  }
};/* struct CardTypeRule */

struct InsertTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::INSERT);
    size_t numChildren = n.getNumChildren();
    Assert( numChildren >= 2 );
    TypeNode setType = n[numChildren-1].getType(check);
    if( check ) {
      if(!setType.isSet()) {
        throw TypeCheckingExceptionPrivate(n, "inserting into a non-set");
      }
      for(size_t i = 0; i < numChildren-1; ++i) {
        TypeNode elementType = n[i].getType(check);
        if(elementType != setType.getSetElementType()) {
          throw TypeCheckingExceptionPrivate
            (n, "type of element should be same as element type of set being inserted into");
        }
      }
    }
    return setType;
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n) {
    Assert(n.getKind() == kind::INSERT);
    return false;
  }
};/* struct InsertTypeRule */

struct SetsProperties {
  inline static Cardinality computeCardinality(TypeNode type) {
    Assert(type.getKind() == kind::SET_TYPE);
    Cardinality elementCard = 2;
    elementCard ^= type[0].getCardinality();
    return elementCard;
  }

  inline static bool isWellFounded(TypeNode type) {
    return type[0].isWellFounded();
  }

  inline static Node mkGroundTerm(TypeNode type) {
    Assert(type.isSet());
    return NodeManager::currentNM()->mkConst(EmptySet(type.toType()));
  }
};/* struct SetsProperties */

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_TYPE_RULES_H */

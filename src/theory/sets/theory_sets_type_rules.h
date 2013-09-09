#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SETS__THEORY_SETS_TYPE_RULES_H
#define __CVC4__THEORY__SETS__THEORY_SETS_TYPE_RULES_H

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

// TODO: Union, Intersection and Setminus should be combined to one check
struct SetUnionTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::UNION);
    TypeNode setType = n[0].getType(check);
    if( check ) {
      if(!setType.isSet()) {
        throw TypeCheckingExceptionPrivate(n, "set union operating on non-set");
      }
      TypeNode secondSetType = n[1].getType(check);
      if(secondSetType != setType) {
        throw TypeCheckingExceptionPrivate(n, "set union operating on sets of different types");
      }
    }
    return setType;
  }
};/* struct SetUnionTypeRule */

struct SetIntersectionTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::INTERSECTION);
    TypeNode setType = n[0].getType(check);
    if( check ) {
      if(!setType.isSet()) {
        throw TypeCheckingExceptionPrivate(n, "set intersection operating on non-set");
      }
      TypeNode secondSetType = n[1].getType(check);
      if(secondSetType != setType) {
        throw TypeCheckingExceptionPrivate(n, "set intersection operating on sets of different types");
      }
    }
    return setType;
  }
};/* struct SetIntersectionTypeRule */

struct SetSetminusTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::SETMINUS);
    TypeNode setType = n[0].getType(check);
    if( check ) {
      if(!setType.isSet()) {
        throw TypeCheckingExceptionPrivate(n, "set setminus operating on non-set");
      }
      TypeNode secondSetType = n[1].getType(check);
      if(secondSetType != setType) {
        throw TypeCheckingExceptionPrivate(n, "set setminus operating on sets of different types");
      }
    }
    return setType;
  }
};/* struct SetSetminusTypeRule */

struct SetSubsetTypeRule {
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

struct SetInTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::IN);
    TypeNode setType = n[1].getType(check);
    if( check ) {
      if(!setType.isSet()) {
        throw TypeCheckingExceptionPrivate(n, "checking for membership in a non-set");
      }
      TypeNode elementType = n[0].getType(check);
      if(elementType != setType.getSetElementType()) {
        throw TypeCheckingExceptionPrivate(n, "set in operating on sets of different types");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct SetInTypeRule */

struct SetSingletonTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::SET_SINGLETON);
    return nodeManager->mkSetType(n[0].getType(check));
  }
};/* struct SetInTypeRule */

struct SetConstTypeRule {
  inline static bool computeIsConst(NodeManager* nodeManager, TNode n) {
    switch(n.getKind()) {
    case kind::SET_SINGLETON:
      return n[0].isConst();
    case kind::UNION:
      return n[0].isConst() && n[1].isConst();
    default:
      Unhandled();
    }
  }
};

struct EmptySetTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {

    Assert(n.getKind() == kind::EMPTYSET);
    EmptySet emptySet = n.getConst<EmptySet>();
    Type setType = emptySet.getType();
    return TypeNode::fromType(setType);
  }
};


struct SetsProperties {
  inline static Cardinality computeCardinality(TypeNode type) {
    Assert(type.getKind() == kind::SET_TYPE);
    Cardinality elementCard = type[0].getCardinality();
    return elementCard;
  }

  inline static bool isWellFounded(TypeNode type) {
    return type[0].isWellFounded();
  }

  inline static Node mkGroundTerm(TypeNode type) {
    Assert(type.isSet());
    return NodeManager::currentNM()->mkConst(EmptySet(type.toType()));
  }
};

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_TYPE_RULES_H */

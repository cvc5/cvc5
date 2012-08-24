/*********************                                                        */
/*! \file theory_builtin_type_rules.h
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
 ** \brief Type rules for the builtin theory
 **
 ** Type rules for the builtin theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H
#define __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"
#include "expr/expr.h"

#include <sstream>

namespace CVC4 {
namespace theory {
namespace builtin {

class ApplyTypeRule {
  public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    TNode f = n.getOperator();
    TypeNode fType = f.getType(check);
    if( !fType.isFunction() && n.getNumChildren() > 0 ) {
      throw TypeCheckingExceptionPrivate(n, "operator does not have function type");
    }
    if( check ) {
      if(fType.isFunction()) {
        if(n.getNumChildren() != fType.getNumChildren() - 1) {
          throw TypeCheckingExceptionPrivate(n, "number of arguments does not match the function type");
        }
        TNode::iterator argument_it = n.begin();
        TNode::iterator argument_it_end = n.end();
        TypeNode::iterator argument_type_it = fType.begin();
        for(; argument_it != argument_it_end; ++argument_it, ++argument_type_it) {
          if((*argument_it).getType() != *argument_type_it) {
            std::stringstream ss;
            ss << "argument types do not match the function type:\n"
               << "argument:  " << *argument_it << "\n"
               << "has type:  " << (*argument_it).getType() << "\n"
               << "not equal: " << *argument_type_it;
            throw TypeCheckingExceptionPrivate(n, ss.str());
          }
        }
      } else {
        if( n.getNumChildren() > 0 ) {
          throw TypeCheckingExceptionPrivate(n, "number of arguments does not match the function type");
        }
      }
    }
    return fType.isFunction() ? fType.getRangeType() : fType;
  }
};/* class ApplyTypeRule */


class EqualityTypeRule {
  public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) throw (TypeCheckingExceptionPrivate, AssertionException) {
    TypeNode booleanType = nodeManager->booleanType();

    if( check ) {
      TypeNode lhsType = n[0].getType(check);
      TypeNode rhsType = n[1].getType(check);

      if ( TypeNode::leastCommonTypeNode(lhsType, rhsType).isNull() ) {
        std::stringstream ss;
        ss << "Subtypes must have a common type:" << std::endl;
        ss << "Equation: " << n << std::endl;
        ss << "Type 1: " << lhsType << std::endl;
        ss << "Type 2: " << rhsType << std::endl;

        throw TypeCheckingExceptionPrivate(n, ss.str());
      }

      if ( lhsType == booleanType && rhsType == booleanType ) {
        throw TypeCheckingExceptionPrivate(n, "equality between two boolean terms (use IFF instead)");
      }
    }
    return booleanType;
  }
};/* class EqualityTypeRule */


class DistinctTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    if( check ) {
      TNode::iterator child_it = n.begin();
      TNode::iterator child_it_end = n.end();
      TypeNode joinType = (*child_it).getType(check);
      for (++child_it; child_it != child_it_end; ++child_it) {
        TypeNode currentType = (*child_it).getType();
        joinType = TypeNode::leastCommonTypeNode(joinType, currentType);
        if (joinType.isNull()) {
          throw TypeCheckingExceptionPrivate(n, "Not all arguments are of the same type");
        }
      }
    }
    return nodeManager->booleanType();
  }
};/* class DistinctTypeRule */


class TupleTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    std::vector<TypeNode> types;
    for(TNode::iterator child_it = n.begin(), child_it_end = n.end();
        child_it != child_it_end;
        ++child_it) {
      types.push_back((*child_it).getType(check));
    }
    return nodeManager->mkTupleType(types);
  }
};/* class TupleTypeRule */

class UninterpretedConstantTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    return TypeNode::fromType(n.getConst<UninterpretedConstant>().getType());
  }
};/* class UninterpretedConstantTypeRule */

class StringConstantTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    Assert(n.getKind() == kind::CONST_STRING);
    return nodeManager->stringType();
  }
};/* class StringConstantTypeRule */

class SortProperties {
public:
  inline static bool isWellFounded(TypeNode type) {
    return true;
  }
  inline static Node mkGroundTerm(TypeNode type) {
    Assert(type.getKind() == kind::SORT_TYPE);
    return NodeManager::currentNM()->mkSkolem( type );
  }
};/* class SortProperties */

class FunctionProperties {
public:
  inline static Cardinality computeCardinality(TypeNode type) {
    // Don't assert this; allow other theories to use this cardinality
    // computation.
    //
    // Assert(type.getKind() == kind::FUNCTION_TYPE);

    Cardinality argsCard(1);
    // get the largest cardinality of function arguments/return type
    for(unsigned i = 0, i_end = type.getNumChildren() - 1; i < i_end; ++i) {
      argsCard *= type[i].getCardinality();
    }

    Cardinality valueCard = type[type.getNumChildren() - 1].getCardinality();

    return valueCard ^ argsCard;
  }
};/* class FuctionProperties */

class TupleProperties {
public:
  inline static Cardinality computeCardinality(TypeNode type) {
    // Don't assert this; allow other theories to use this cardinality
    // computation.
    //
    // Assert(type.getKind() == kind::TUPLE_TYPE);

    Cardinality card(1);
    for(TypeNode::iterator i = type.begin(),
          i_end = type.end();
        i != i_end;
        ++i) {
      card *= (*i).getCardinality();
    }

    return card;
  }

  inline static bool isWellFounded(TypeNode type) {
    // Don't assert this; allow other theories to use this
    // wellfoundedness computation.
    //
    // Assert(type.getKind() == kind::TUPLE_TYPE);

    for(TypeNode::iterator i = type.begin(),
          i_end = type.end();
        i != i_end;
        ++i) {
      if(! (*i).isWellFounded()) {
        return false;
      }
    }

    return true;
  }

  inline static Node mkGroundTerm(TypeNode type) {
    Assert(type.getKind() == kind::TUPLE_TYPE);

    std::vector<Node> children;
    for(TypeNode::iterator i = type.begin(),
          i_end = type.end();
        i != i_end;
        ++i) {
      children.push_back((*i).mkGroundTerm());
    }

    return NodeManager::currentNM()->mkNode(kind::TUPLE, children);
  }
};/* class TupleProperties */

class SubtypeProperties {
public:

  inline static Cardinality computeCardinality(TypeNode type) {
    Assert(type.getKind() == kind::SUBTYPE_TYPE);
    Unimplemented("Computing the cardinality for predicate subtype not yet supported.");
  }

  inline static bool isWellFounded(TypeNode type) {
    Assert(type.getKind() == kind::SUBTYPE_TYPE);
    Unimplemented("Computing the well-foundedness for predicate subtype not yet supported.");
  }

  inline static Node mkGroundTerm(TypeNode type) {
    Assert(type.getKind() == kind::SUBTYPE_TYPE);
    Unimplemented("Constructing a ground term for predicate subtype not yet supported.");
  }

};/* class SubtypeProperties */

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H */

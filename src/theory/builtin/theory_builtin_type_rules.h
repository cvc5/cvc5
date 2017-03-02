/*********************                                                        */
/*! \file theory_builtin_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
#include "theory/rewriter.h"

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
          if(!(*argument_it).getType().isComparableTo(*argument_type_it)) {
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
        ss << "Subexpressions must have a common base type:" << std::endl;
        ss << "Equation: " << n << std::endl;
        ss << "Type 1: " << lhsType << std::endl;
        ss << "Type 2: " << rhsType << std::endl;

        throw TypeCheckingExceptionPrivate(n, ss.str());
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

class SExprTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    std::vector<TypeNode> types;
    for(TNode::iterator child_it = n.begin(), child_it_end = n.end();
        child_it != child_it_end;
        ++child_it) {
      types.push_back((*child_it).getType(check));
    }
    return nodeManager->mkSExprType(types);
  }
};/* class SExprTypeRule */

class UninterpretedConstantTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    return TypeNode::fromType(n.getConst<UninterpretedConstant>().getType());
  }
};/* class UninterpretedConstantTypeRule */

class AbstractValueTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    // An UnknownTypeException means that this node has no type.  For now,
    // only abstract values are like this---and then, only if they are created
    // by the user and don't actually correspond to one that the SmtEngine gave
    // them previously.
    throw UnknownTypeException(n);
  }
};/* class AbstractValueTypeRule */

class LambdaTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    if( n[0].getType(check) != nodeManager->boundVarListType() ) {
      std::stringstream ss;
      ss << "expected a bound var list for LAMBDA expression, got `"
         << n[0].getType().toString() << "'";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    std::vector<TypeNode> argTypes;
    for(TNode::iterator i = n[0].begin(); i != n[0].end(); ++i) {
      argTypes.push_back((*i).getType());
    }
    TypeNode rangeType = n[1].getType(check);
    return nodeManager->mkFunctionType(argTypes, rangeType);
  }
};/* class LambdaTypeRule */

class ChainTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    Assert(n.getKind() == kind::CHAIN);

    if(!check) {
      return nodeManager->booleanType();
    }

    TypeNode tn;
    try {
      // Actually do the expansion to do the typechecking.
      // Shouldn't be extra work to do this, since the rewriter
      // keeps a cache.
      tn = nodeManager->getType(Rewriter::rewrite(n), check);
    } catch(TypeCheckingExceptionPrivate& e) {
      std::stringstream ss;
      ss << "Cannot typecheck the expansion of chained operator `" << n.getOperator() << "':"
         << std::endl;
      // indent the sub-exception for clarity
      std::stringstream ss2;
      ss2 << e;
      std::string eStr = ss2.str();
      for(size_t i = eStr.find('\n'); i != std::string::npos; i = eStr.find('\n', i)) {
        eStr.insert(++i, "| ");
      }
      ss << "| " << eStr;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    // This check is intentionally != booleanType() rather than
    // !(...isBoolean()): if we ever add a type compatible with
    // Boolean (pseudobooleans or whatever), we have to revisit
    // the above "!check" case where booleanType() is returned
    // directly.  Putting this check here will cause a failure if
    // it's ever relevant.
    if(tn != nodeManager->booleanType()) {
      std::stringstream ss;
      ss << "Chains can only be formed over predicates; "
         << "the operator here returns `" << tn << "', expected `"
         << nodeManager->booleanType() << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    return nodeManager->booleanType();
  }
};/* class ChainTypeRule */

class ChainedOperatorTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    Assert(n.getKind() == kind::CHAIN_OP);
    return nodeManager->getType(nodeManager->operatorOf(n.getConst<Chain>().getOperator()), check);
  }
};/* class ChainedOperatorTypeRule */

class SortProperties {
public:
  inline static bool isWellFounded(TypeNode type) {
    return true;
  }
  inline static Node mkGroundTerm(TypeNode type) {
    Assert(type.getKind() == kind::SORT_TYPE);
    return NodeManager::currentNM()->mkSkolem("groundTerm", type, "a ground term created for type " + type.toString());
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

class SExprProperties {
public:
  inline static Cardinality computeCardinality(TypeNode type) {
    // Don't assert this; allow other theories to use this cardinality
    // computation.
    //
    // Assert(type.getKind() == kind::SEXPR_TYPE);

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
    // Assert(type.getKind() == kind::SEXPR_TYPE);

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
    Assert(type.getKind() == kind::SEXPR_TYPE);

    std::vector<Node> children;
    for(TypeNode::iterator i = type.begin(),
          i_end = type.end();
        i != i_end;
        ++i) {
      children.push_back((*i).mkGroundTerm());
    }

    return NodeManager::currentNM()->mkNode(kind::SEXPR, children);
  }
};/* class SExprProperties */

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

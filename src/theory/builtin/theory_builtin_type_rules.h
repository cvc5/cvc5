/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Type rules for the builtin theory.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H
#define CVC5__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/builtin/theory_builtin_rewriter.h" // for array and lambda representation

#include <sstream>

namespace cvc5 {
namespace theory {
namespace builtin {

class EqualityTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    TypeNode booleanType = nodeManager->booleanType();

    if (check)
    {
      TypeNode lhsType = n[0].getType(check);
      TypeNode rhsType = n[1].getType(check);

      if (TypeNode::leastCommonTypeNode(lhsType, rhsType).isNull())
      {
        std::stringstream ss;
        ss << "Subexpressions must have a common base type:" << std::endl;
        ss << "Equation: " << n << std::endl;
        ss << "Type 1: " << lhsType << std::endl;
        ss << "Type 2: " << rhsType << std::endl;

        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
      // TODO : check isFirstClass for these types? (github issue #1202)
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
    if (check)
    {
      for (TNode c : n)
      {
        c.getType(check);
      }
    }
    return nodeManager->sExprType();
  }
};/* class SExprTypeRule */

class UninterpretedConstantTypeRule {
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
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
  // computes whether a lambda is a constant value, via conversion to array representation
  inline static bool computeIsConst(NodeManager* nodeManager, TNode n)
  {
    Assert(n.getKind() == kind::LAMBDA);
    //get array representation of this function, if possible
    Node na = TheoryBuiltinRewriter::getArrayRepresentationForLambda(n);
    if( !na.isNull() ){
      Assert(na.getType().isArray());
      Trace("lambda-const") << "Array representation for " << n << " is " << na << " " << na.getType() << std::endl;
      // must have the standard bound variable list
      Node bvl = NodeManager::currentNM()->getBoundVarListForFunctionType( n.getType() );
      if( bvl==n[0] ){
        //array must be constant
        if( na.isConst() ){
          Trace("lambda-const") << "*** Constant lambda : " << n;
          Trace("lambda-const") << " since its array representation : " << na << " is constant." << std::endl;
          return true;
        }else{
          Trace("lambda-const") << "Non-constant lambda : " << n << " since array is not constant." << std::endl;
        } 
      }else{
        Trace("lambda-const") << "Non-constant lambda : " << n << " since its varlist is not standard." << std::endl;
        Trace("lambda-const") << "  standard : " << bvl << std::endl;
        Trace("lambda-const") << "   current : " << n[0] << std::endl;
      } 
    }else{
      Trace("lambda-const") << "Non-constant lambda : " << n << " since it has no array representation." << std::endl;
    } 
    return false;
  }
};/* class LambdaTypeRule */

class WitnessTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    if (n[0].getType(check) != nodeManager->boundVarListType())
    {
      std::stringstream ss;
      ss << "expected a bound var list for WITNESS expression, got `"
         << n[0].getType().toString() << "'";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    if (n[0].getNumChildren() != 1)
    {
      std::stringstream ss;
      ss << "expected a bound var list with one argument for WITNESS expression";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    if (check)
    {
      TypeNode rangeType = n[1].getType(check);
      if (!rangeType.isBoolean())
      {
        std::stringstream ss;
        ss << "expected a body of a WITNESS expression to have Boolean type";
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
    // The type of a witness function is the type of its bound variable.
    return n[0][0].getType();
  }
}; /* class WitnessTypeRule */

class SortProperties {
 public:
  inline static bool isWellFounded(TypeNode type) {
    return true;
  }
  static Node mkGroundTerm(TypeNode type);
};/* class SortProperties */

class FunctionProperties {
 public:
  static Cardinality computeCardinality(TypeNode type);

  /** Function type is well-founded if its component sorts are */
  static bool isWellFounded(TypeNode type)
  {
    for (TypeNode::iterator i = type.begin(), i_end = type.end(); i != i_end;
         ++i)
    {
      if (!(*i).isWellFounded())
      {
        return false;
      }
    }
    return true;
  }
  /**
   * Ground term for function sorts is (lambda x. t) where x is the
   * canonical variable list for its type and t is the canonical ground term of
   * its range.
   */
  static Node mkGroundTerm(TypeNode type)
  {
    NodeManager* nm = NodeManager::currentNM();
    Node bvl = nm->getBoundVarListForFunctionType(type);
    Node ret = type.getRangeType().mkGroundTerm();
    return nm->mkNode(kind::LAMBDA, bvl, ret);
  }
};/* class FuctionProperties */

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H */

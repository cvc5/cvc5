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
    // by the user and don't actually correspond to one that the SolverEngine
    // gave them previously.
    throw UnknownTypeException(n);
  }
};/* class AbstractValueTypeRule */

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

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H */

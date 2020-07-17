/*********************                                                        */
/*! \file theory_arith_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Christopher L. Conway, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add brief comments here ]]
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__THEORY_ARITH_TYPE_RULES_H
#define CVC4__THEORY__ARITH__THEORY_ARITH_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace arith {


class ArithConstantTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::CONST_RATIONAL);
    if(n.getConst<Rational>().isIntegral()){
      return nodeManager->integerType();
    }else{
      return nodeManager->realType();
    }
  }
};/* class ArithConstantTypeRule */

class ArithOperatorTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    TypeNode integerType = nodeManager->integerType();
    TypeNode realType = nodeManager->realType();
    TNode::iterator child_it = n.begin();
    TNode::iterator child_it_end = n.end();
    bool isInteger = true;
    for(; child_it != child_it_end; ++child_it) {
      TypeNode childType = (*child_it).getType(check);
      if (!childType.isInteger()) {
        isInteger = false;
        if( !check ) { // if we're not checking, nothing left to do
          break;
        }
      }
      if( check ) {
        if(!childType.isReal()) {
          throw TypeCheckingExceptionPrivate(n, "expecting an arithmetic subterm");
        }
      }
    }
    switch(Kind k = n.getKind()) {
      case kind::TO_REAL:
        return realType;
      case kind::TO_INTEGER:
        return integerType;
      default: {
        bool isDivision = k == kind::DIVISION || k == kind::DIVISION_TOTAL;
        return (isInteger && !isDivision ? integerType : realType);
      }
    }
  }
};/* class ArithOperatorTypeRule */

class RealNullaryOperatorTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    // for nullary operators, we only computeType for check=true, since they are given TypeAttr() on creation
    Assert(check);
    TypeNode realType = n.getType();
    if(realType!=NodeManager::currentNM()->realType()) {
      throw TypeCheckingExceptionPrivate(n, "expecting real type");
    }
    return realType;
  }
};/* class RealNullaryOperatorTypeRule */

class IAndOpTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    if (n.getKind() != kind::IAND_OP)
    {
      InternalError() << "IAND_OP typerule invoked for IAND_OP kind";
    }
    TypeNode iType = nodeManager->integerType();
    std::vector<TypeNode> argTypes;
    argTypes.push_back(iType);
    argTypes.push_back(iType);
    return nodeManager->mkFunctionType(argTypes, iType);
  }
}; /* class IAndOpTypeRule */

class IAndTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    if (n.getKind() != kind::IAND)
    {
      InternalError() << "IAND typerule invoked for IAND kind";
    }
    if (check)
    {
      TypeNode arg1 = n[0].getType(check);
      TypeNode arg2 = n[1].getType(check);
      if (!arg1.isInteger() || !arg2.isInteger())
      {
        throw TypeCheckingExceptionPrivate(n, "expecting integer terms");
      }
    }
    return nodeManager->integerType();
  }
}; /* class BitVectorConversionTypeRule */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ARITH__THEORY_ARITH_TYPE_RULES_H */

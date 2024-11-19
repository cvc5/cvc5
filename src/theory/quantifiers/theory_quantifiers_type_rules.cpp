/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of quantifiers.
 */

#include "theory/quantifiers/theory_quantifiers_type_rules.h"

#include "theory/quantifiers/inst_strategy_pool.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

TypeNode QuantifierTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode QuantifierTypeRule::computeType(NodeManager* nodeManager,
                                         TNode n,
                                         bool check,
                                         std::ostream* errOut)
{
  Trace("typecheck-q") << "type check for fa " << n << std::endl;
  Assert((n.getKind() == Kind::FORALL || n.getKind() == Kind::EXISTS)
         && n.getNumChildren() > 0);
  if (check)
  {
    // bound variable lists, etc. cannot be abstracted
    if (n[0].getTypeOrNull() != nodeManager->boundVarListType())
    {
      if (errOut)
      {
        (*errOut) << "first argument of quantifier is not bound var list";
      }
      return TypeNode::null();
    }
    TypeNode bodyType = n[1].getTypeOrNull();
    if (!bodyType.isBoolean() && !bodyType.isFullyAbstract())
    {
      if (errOut)
      {
        (*errOut) << "body of quantifier is not boolean";
      }
      return TypeNode::null();
    }
    if (n.getNumChildren() == 3)
    {
      if (n[2].getTypeOrNull() != nodeManager->instPatternListType())
      {
        if (errOut)
        {
          (*errOut) << "third argument of quantifier is not instantiation "
                       "pattern list";
        }
        return TypeNode::null();
      }
      for (const Node& p : n[2])
      {
        if (p.getKind() != Kind::INST_POOL)
        {
          continue;
        }
        if (!InstStrategyPool::hasProductSemantics(n, p)
            && !InstStrategyPool::hasTupleSemantics(n, p))
        {
          if (errOut)
          {
            (*errOut)
                << "expected number of arguments to pool to be the same as the "
                   "number of bound variables of the quantified formula";
          }
          return TypeNode::null();
        }
      }
    }
  }
  return nodeManager->booleanType();
}

TypeNode QuantifierBoundVarListTypeRule::preComputeType(NodeManager* nm,
                                                        TNode n)
{
  return nm->boundVarListType();
}
TypeNode QuantifierBoundVarListTypeRule::computeType(NodeManager* nodeManager,
                                                     TNode n,
                                                     bool check,
                                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BOUND_VAR_LIST);
  if (check)
  {
    for (const Node& nc : n)
    {
      if (nc.getKind() != Kind::BOUND_VARIABLE)
      {
        if (errOut)
        {
          (*errOut) << "argument of bound var list is not bound variable";
        }
        return TypeNode::null();
      }
    }
  }
  return nodeManager->boundVarListType();
}

TypeNode QuantifierInstPatternTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->instPatternType();
}
TypeNode QuantifierInstPatternTypeRule::computeType(NodeManager* nodeManager,
                                                    TNode n,
                                                    bool check,
                                                    std::ostream* errOut)
{
  Assert(n.getKind() == Kind::INST_PATTERN);
  if (check)
  {
    TypeNode tn = n[0].getTypeOrNull();
    // this check catches the common mistake writing :pattern (f x) instead of
    // :pattern ((f x))
    if (n[0].isVar() && n[0].getKind() != Kind::BOUND_VARIABLE
        && tn.isFunction())
    {
      if (errOut)
      {
        (*errOut) << "Pattern must be a list of fully-applied terms.";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->instPatternType();
}

TypeNode QuantifierAnnotationTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->instPatternType();
}
TypeNode QuantifierAnnotationTypeRule::computeType(NodeManager* nodeManager,
                                                   TNode n,
                                                   bool check,
                                                   std::ostream* errOut)
{
  if (check)
  {
    Kind k = n.getKind();
    if (k == Kind::INST_ATTRIBUTE)
    {
      if (n.getNumChildren() > 1)
      {
        // first must be a keyword
        if (n[0].getKind() != Kind::CONST_STRING)
        {
          throw TypeCheckingExceptionPrivate(
              n[0], "Expecting a keyword at the head of INST_ATTRIBUTE.");
        }
      }
    }
    else if (k == Kind::INST_POOL)
    {
      // arguments must have set types
      for (const Node& nn : n)
      {
        if (!nn.getTypeOrNull().isSet())
        {
          throw TypeCheckingExceptionPrivate(n, "Expecting a set as argument.");
        }
      }
    }
    else if (k == Kind::INST_ADD_TO_POOL || k == Kind::SKOLEM_ADD_TO_POOL)
    {
      TypeNode tn = n[0].getTypeOrNull();
      TypeNode tn1 = n[1].getTypeOrNull();
      if (!tn1.isSet())
      {
        throw TypeCheckingExceptionPrivate(n, "Expecting a set as argument.");
      }
      if (tn1.getSetElementType() != tn)
      {
        if (errOut)
        {
          (*errOut) << "Expecting a keyword at the head of INST_ATTRIBUTE.";
        }
        return TypeNode::null();
      }
    }
  }
  return nodeManager->instPatternType();
}

TypeNode QuantifierInstPatternListTypeRule::preComputeType(NodeManager* nm,
                                                           TNode n)
{
  return nm->instPatternListType();
}
TypeNode QuantifierInstPatternListTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check, std::ostream* errOut)
{
  Assert(n.getKind() == Kind::INST_PATTERN_LIST);
  if (check)
  {
    for (const Node& nc : n)
    {
      Kind k = nc.getKind();
      if (k != Kind::INST_PATTERN && k != Kind::INST_NO_PATTERN
          && k != Kind::INST_ATTRIBUTE && k != Kind::INST_POOL
          && k != Kind::INST_ADD_TO_POOL && k != Kind::SKOLEM_ADD_TO_POOL)
      {
        if (errOut)
        {
          (*errOut) << "argument of inst pattern list is not a legal "
                       "quantifiers annotation";
        }
        return TypeNode::null();
      }
    }
  }
  return nodeManager->instPatternListType();
}

TypeNode QuantifierOracleFormulaGenTypeRule::preComputeType(NodeManager* nm,
                                                            TNode n)
{
  return nm->booleanType();
}
TypeNode QuantifierOracleFormulaGenTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check, std::ostream* errOut)
{
  Assert(n.getKind() == Kind::ORACLE_FORMULA_GEN);
  if (check)
  {
    if (!n[0].getTypeOrNull().isBoolean())
    {
      if (errOut)
      {
        (*errOut) << "expected Boolean for oracle interface assumption";
      }
      return TypeNode::null();
    }
    if (!n[1].getTypeOrNull().isBoolean())
    {
      if (errOut)
      {
        (*errOut) << "expected Boolean for oracle interface constraint";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  Assert((n.getKind() == kind::FORALL || n.getKind() == kind::EXISTS)
         && n.getNumChildren() > 0);
  if (check)
  {
    if (n[0].getType(check) != nodeManager->boundVarListType())
    {
      throw TypeCheckingExceptionPrivate(
          n, "first argument of quantifier is not bound var list");
    }
    if (n[1].getType(check) != nodeManager->booleanType())
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "body of quantifier is not boolean");
    }
    if (n.getNumChildren() == 3)
    {
      if (n[2].getType(check) != nodeManager->instPatternListType())
      {
        throw TypeCheckingExceptionPrivate(
            n,
            "third argument of quantifier is not instantiation "
            "pattern list");
      }
      for (const Node& p : n[2])
      {
        if (p.getKind() != kind::INST_POOL)
        {
          continue;
        }
        if (!InstStrategyPool::hasProductSemantics(n, p)
            && !InstStrategyPool::hasTupleSemantics(n, p))
        {
          throw TypeCheckingExceptionPrivate(
              n,
              "Pool annotation does not match the types of the variables of "
              "the quantified formula.");
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
  Assert(n.getKind() == kind::BOUND_VAR_LIST);
  if (check)
  {
    for (int i = 0; i < (int)n.getNumChildren(); i++)
    {
      if (n[i].getKind() != kind::BOUND_VARIABLE)
      {
        throw TypeCheckingExceptionPrivate(
            n, "argument of bound var list is not bound variable");
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
  Assert(n.getKind() == kind::INST_PATTERN);
  if (check)
  {
    TypeNode tn = n[0].getType(check);
    // this check catches the common mistake writing :pattern (f x) instead of
    // :pattern ((f x))
    if (n[0].isVar() && n[0].getKind() != kind::BOUND_VARIABLE
        && tn.isFunction())
    {
      throw TypeCheckingExceptionPrivate(
          n[0], "Pattern must be a list of fully-applied terms.");
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
    if (k == kind::INST_ATTRIBUTE)
    {
      if (n.getNumChildren() > 1)
      {
        // first must be a keyword
        if (n[0].getKind() != kind::CONST_STRING)
        {
          throw TypeCheckingExceptionPrivate(
              n[0], "Expecting a keyword at the head of INST_ATTRIBUTE.");
        }
      }
    }
    else if (k == kind::INST_POOL)
    {
      // arguments must have set types
      for (const Node& nn : n)
      {
        if (!nn.getType().isSet())
        {
          throw TypeCheckingExceptionPrivate(n, "Expecting a set as argument.");
        }
      }
    }
    else if (k == kind::INST_ADD_TO_POOL || k == kind::SKOLEM_ADD_TO_POOL)
    {
      TypeNode tn = n[0].getType();
      TypeNode tn1 = n[1].getType();
      if (!tn1.isSet())
      {
        throw TypeCheckingExceptionPrivate(n, "Expecting a set as argument.");
      }
      if (tn1.getSetElementType() != tn)
      {
        throw TypeCheckingExceptionPrivate(
            n, "Type of term must match the element type of the pool.");
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
  Assert(n.getKind() == kind::INST_PATTERN_LIST);
  if (check)
  {
    for (const Node& nc : n)
    {
      Kind k = nc.getKind();
      if (k != kind::INST_PATTERN && k != kind::INST_NO_PATTERN
          && k != kind::INST_ATTRIBUTE && k != kind::INST_POOL
          && k != kind::INST_ADD_TO_POOL && k != kind::SKOLEM_ADD_TO_POOL)
      {
        throw TypeCheckingExceptionPrivate(
            n,
            "argument of inst pattern list is not a legal quantifiers "
            "annotation");
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
  Assert(n.getKind() == kind::ORACLE_FORMULA_GEN);
  if (check)
  {
    if (!n[0].getType().isBoolean())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expected Boolean for oracle interface assumption");
    }
    if (!n[1].getType().isBoolean())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expected Boolean for oracle interface constraint");
    }
  }
  return nodeManager->booleanType();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

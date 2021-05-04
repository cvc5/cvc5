/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of quantifiers.
 */

#include "theory/quantifiers/theory_quantifiers_type_rules.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

TypeNode QuantifierTypeRule::computeType(NodeManager* nodeManager,
                                         TNode n,
                                         bool check)
{
  Debug("typecheck-q") << "type check for fa " << n << std::endl;
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
        if (p.getKind() == kind::INST_POOL
            && p.getNumChildren() != n[0].getNumChildren())
        {
          throw TypeCheckingExceptionPrivate(
              n,
              "expected number of arguments to pool to be the same as the "
              "number of bound variables of the quantified formula");
        }
      }
    }
  }
  return nodeManager->booleanType();
}

TypeNode QuantifierBoundVarListTypeRule::computeType(NodeManager* nodeManager,
                                                     TNode n,
                                                     bool check)
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

TypeNode QuantifierInstPatternTypeRule::computeType(NodeManager* nodeManager,
                                                    TNode n,
                                                    bool check)
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

TypeNode QuantifierAnnotationTypeRule::computeType(NodeManager* nodeManager,
                                                   TNode n,
                                                   bool check)
{
  return nodeManager->instPatternType();
}

TypeNode QuantifierInstPatternListTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check)
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

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing rules for the theory of strings and regexps.
 */
#include "theory/strings/theory_strings_type_rules.h"

#include <sstream>

#include "expr/node_manager.h"
#include "expr/sequence.h"
#include "options/strings_options.h"
#include "util/cardinality.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

bool isMaybeStringLike(const TypeNode& tn)
{
  if (tn.isString())
  {
    return true;
  }
  return tn.isMaybeKind(Kind::SEQUENCE_TYPE);
}

bool isMaybeInteger(const TypeNode& tn)
{
  return tn.isInteger() || tn.isFullyAbstract();
}

TypeNode StringConcatTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode StringConcatTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  TypeNode tret;
  for (const Node& nc : n)
  {
    TypeNode t = nc.getTypeOrNull();
    if (check)
    {
      if (!isMaybeStringLike(t))
      {
        if (errOut)
        {
          (*errOut) << "expecting string-like terms in concat";
        }
        return TypeNode::null();
      }
    }
    if (tret.isNull())
    {
      tret = t;
      continue;
    }
    tret = tret.leastUpperBound(t);
    if (tret.isNull())
    {
      if (errOut)
      {
        (*errOut) << "expecting comparable terms in concat";
      }
      return TypeNode::null();
    }
  }
  // note we could be fully abstract if all arguments are fully abstract,
  // this is due to the fact that string/sequence are not comparable.
  return tret;
}

TypeNode StringSubstrTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode StringSubstrTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  TypeNode t = n[0].getTypeOrNull();
  if (check)
  {
    if (!isMaybeStringLike(t))
    {
      if (errOut)
      {
        (*errOut) << "expecting a string-like term in substr";
      }
      return TypeNode::null();
    }
    TypeNode t2 = n[1].getTypeOrNull();
    if (!isMaybeInteger(t2))
    {
      if (errOut)
      {
        (*errOut) << "expecting an integer start term in substr";
      }
      return TypeNode::null();
    }
    t2 = n[2].getTypeOrNull();
    if (!isMaybeInteger(t2))
    {
      if (errOut)
      {
        (*errOut) << "expecting an integer length term in substr";
      }
      return TypeNode::null();
    }
  }
  // note that we could be fully abstract if the argument is fully abstract
  return t;
}

TypeNode StringUpdateTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode StringUpdateTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  TypeNode t = n[0].getTypeOrNull();
  TypeNode t3 = n[2].getTypeOrNull();
  TypeNode tret = t.leastUpperBound(t3);
  if (tret.isNull())
  {
    if (errOut)
    {
      (*errOut) << "expecting compatible string-like terms";
    }
    return TypeNode::null();
  }
  if (check)
  {
    // check that the return is maybe string-like
    if (!isMaybeStringLike(tret))
    {
      if (errOut)
      {
        (*errOut) << "expecting string-like terms in update";
      }
      return TypeNode::null();
    }
    TypeNode t2 = n[1].getTypeOrNull();
    if (!isMaybeInteger(t2))
    {
      if (errOut)
      {
        (*errOut) << "expecting an integer start term in update";
      }
      return TypeNode::null();
    }
  }
  return tret;
}

TypeNode StringAtTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode StringAtTypeRule::computeType(NodeManager* nodeManager,
                                       TNode n,
                                       bool check,
                                       std::ostream* errOut)
{
  TypeNode t = n[0].getTypeOrNull();
  if (check)
  {
    if (!isMaybeStringLike(t))
    {
      if (errOut)
      {
        (*errOut) << "expecting a string-like term in str.at";
      }
      return TypeNode::null();
    }
    TypeNode t2 = n[1].getTypeOrNull();
    if (!isMaybeInteger(t2))
    {
      if (errOut)
      {
        (*errOut) << "expecting an integer start term in str.at";
      }
      return TypeNode::null();
    }
  }
  return t;
}

TypeNode StringIndexOfTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->integerType();
}
TypeNode StringIndexOfTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  if (check)
  {
    TypeNode t = n[0].getTypeOrNull();
    if (!isMaybeStringLike(t))
    {
      if (errOut)
      {
        (*errOut) << "expecting a string-like term in indexof";
      }
      return TypeNode::null();
    }
    TypeNode t2 = n[1].getTypeOrNull();
    if (!t.isComparableTo(t2))
    {
      if (errOut)
      {
        (*errOut) << "expecting a term in second argument of indexof that is "
                     "the same type as the first argument";
      }
      return TypeNode::null();
    }
    t = n[2].getTypeOrNull();
    if (!isMaybeInteger(t))
    {
      if (errOut)
      {
        (*errOut) << "expecting an integer term in third argument of indexof";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->integerType();
}

TypeNode StringReplaceTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode StringReplaceTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  TypeNode t;
  for (const Node& nc : n)
  {
    TypeNode tc = nc.getTypeOrNull();
    if (check)
    {
      if (!isMaybeStringLike(tc))
      {
        if (errOut)
        {
          (*errOut) << "expecting a string-like term in replace";
        }
        return TypeNode::null();
      }
    }
    // if first child
    if (t.isNull())
    {
      t = tc;
      continue;
    }
    t = t.leastUpperBound(tc);
    if (t.isNull())
    {
      if (errOut)
      {
        (*errOut) << "expecting comparable string-like terms";
      }
      return TypeNode::null();
    }
  }
  return t;
}

TypeNode StringStrToBoolTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode StringStrToBoolTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check,
                                              std::ostream* errOut)
{
  if (check)
  {
    TypeNode firstType;
    for (const Node& nc : n)
    {
      TypeNode t = nc.getType(check);
      if (!isMaybeStringLike(t))
      {
        if (errOut)
        {
          (*errOut) << "expecting a string-like term in argument of "
                    << n.getKind();
        }
        return TypeNode::null();
      }
      if (firstType.isNull())
      {
        firstType = t;
      }
      else if (!t.isComparableTo(firstType))
      {
        if (errOut)
        {
          (*errOut) << "expecting string terms of the same type in "
                    << n.getKind();
        }
        return TypeNode::null();
      }
    }
  }
  return nodeManager->booleanType();
}

TypeNode StringStrToIntTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->integerType();
}
TypeNode StringStrToIntTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check,
                                             std::ostream* errOut)
{
  if (check)
  {
    TypeNode t = n[0].getTypeOrNull();
    if (!isMaybeStringLike(t))
    {
      if (errOut)
      {
        (*errOut) << "expecting a string-like term in argument of "
                  << n.getKind();
      }
      return TypeNode::null();
    }
  }
  return nodeManager->integerType();
}

TypeNode StringStrToStrTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode StringStrToStrTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check,
                                             std::ostream* errOut)
{
  TypeNode t = n[0].getTypeOrNull();
  if (check)
  {
    if (!isMaybeStringLike(t))
    {
      if (errOut)
      {
        (*errOut) << "expecting a string term in argument of " << n.getKind();
      }
      return TypeNode::null();
    }
  }
  return t;
}

TypeNode StringRelationTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode StringRelationTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check,
                                             std::ostream* errOut)
{
  if (check)
  {
    TypeNode t = n[0].getTypeOrNull();
    if (!isMaybeStringLike(t))
    {
      if (errOut)
      {
        (*errOut) << "expecting a string-like term in relation";
      }
      return TypeNode::null();
    }
    TypeNode t2 = n[1].getTypeOrNull();
    if (!t.isComparableTo(t2))
    {
      if (errOut)
      {
        (*errOut)
            << "expecting two terms of comparable string-like type in relation";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode RegExpRangeTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->regExpType();
}
TypeNode RegExpRangeTypeRule::computeType(NodeManager* nodeManager,
                                          TNode n,
                                          bool check,
                                          std::ostream* errOut)
{
  if (check)
  {
    TNode::iterator it = n.begin();
    for (int i = 0; i < 2; ++i)
    {
      TypeNode t = (*it).getTypeOrNull();
      if (!t.isString() && !t.isFullyAbstract())  // string-only
      {
        if (errOut)
        {
          (*errOut) << "expecting a string term in regexp range";
        }
        return TypeNode::null();
      }
      ++it;
    }
  }
  return nodeManager->regExpType();
}

TypeNode StringToRegExpTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->regExpType();
}
TypeNode StringToRegExpTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check,
                                             std::ostream* errOut)
{
  if (check)
  {
    TypeNode tn = n[0].getTypeOrNull();
    if (!tn.isString() && !tn.isFullyAbstract())
    {
      if (errOut)
      {
        (*errOut) << "expecting string term in string to regexp";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->regExpType();
}

bool StringToRegExpTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getKind() == Kind::STRING_TO_REGEXP);
  return n[0].isConst();
}

TypeNode ConstSequenceTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ConstSequenceTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  Assert(n.getKind() == Kind::CONST_SEQUENCE);
  return nodeManager->mkSequenceType(n.getConst<Sequence>().getType());
}

TypeNode SeqUnitTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode SeqUnitTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SEQ_UNIT);
  TypeNode argType = n[0].getTypeOrNull();
  return nodeManager->mkSequenceType(argType);
}

TypeNode SeqNthTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode SeqNthTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SEQ_NTH);
  TypeNode t = n[0].getTypeOrNull();
  if (check && !t.isMaybeKind(Kind::SEQUENCE_TYPE))
  {
    if (errOut)
    {
      (*errOut) << "expecting a string-like term in nth";
    }
    return TypeNode::null();
  }
  if (check)
  {
    TypeNode t2 = n[1].getTypeOrNull();
    if (!isMaybeInteger(t2))
    {
      if (errOut)
      {
        (*errOut) << "expecting an integer start term in nth";
      }
      return TypeNode::null();
    }
  }
  if (t.isAbstract())
  {
    // if selecting from abstract, we don't know the type
    return nodeManager->mkAbstractType(Kind::ABSTRACT_TYPE);
  }
  // must check sequence here to ensure not a string
  if (!t.isSequence())
  {
    if (errOut)
    {
      (*errOut) << "expecting a sequence term in nth";
    }
    return TypeNode::null();
  }
  return t.getSequenceElementType();
}

TypeNode SeqEmptyOfTypeTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}

TypeNode SeqEmptyOfTypeTypeRule::computeType(NodeManager* nm,
                                             TNode n,
                                             bool check,
                                             std::ostream* errOut)
{
  return nm->mkAbstractType(Kind::SEQUENCE_TYPE);
}

Cardinality SequenceProperties::computeCardinality(TypeNode type)
{
  Assert(type.getKind() == Kind::SEQUENCE_TYPE);
  return Cardinality::INTEGERS;
}
/** A sequence is well-founded if its element type is */
bool SequenceProperties::isWellFounded(TypeNode type)
{
  return type[0].isWellFounded();
}
/** Make ground term for sequence type (return the empty sequence) */
Node SequenceProperties::mkGroundTerm(TypeNode type)
{
  Assert(type.isSequence());
  // empty sequence
  std::vector<Node> seq;
  return NodeManager::currentNM()->mkConst(
      Sequence(type.getSequenceElementType(), seq));
}
}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

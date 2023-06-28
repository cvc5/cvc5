/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
    TypeNode t = nc.getType(check);
    if (tret.isNull())
    {
      tret = t;
      if (check)
      {
        if (!t.isStringLike())
        {
          throw TypeCheckingExceptionPrivate(
              n, "expecting string-like terms in concat");
        }
      }
      else
      {
        break;
      }
    }
    else if (t != tret)
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting all children to have the same type in concat");
    }
  }
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
  TypeNode t = n[0].getType(check);
  if (check)
  {
    if (!t.isStringLike())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting a string-like term in substr");
    }
    TypeNode t2 = n[1].getType(check);
    if (!t2.isInteger())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting an integer start term in substr");
    }
    t2 = n[2].getType(check);
    if (!t2.isInteger())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting an integer length term in substr");
    }
  }
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
  TypeNode t = n[0].getType(check);
  if (check)
  {
    if (!t.isStringLike())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting a string-like term in update");
    }
    TypeNode t2 = n[1].getType(check);
    if (!t2.isInteger())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting an integer start term in update");
    }
    t2 = n[2].getType(check);
    if (!t2.isStringLike())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting an string-like replace term in update");
    }
  }
  return t;
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
  TypeNode t = n[0].getType(check);
  if (check)
  {
    if (!t.isStringLike())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting a string-like term in str.at");
    }
    TypeNode t2 = n[1].getType(check);
    if (!t2.isInteger())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting an integer start term in str.at");
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
    TypeNode t = n[0].getType(check);
    if (!t.isStringLike())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting a string-like term in indexof");
    }
    TypeNode t2 = n[1].getType(check);
    if (t != t2)
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "expecting a term in second argument of indexof that is the same "
          "type as the first argument");
    }
    t = n[2].getType(check);
    if (!t.isInteger())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting an integer term in third argument of indexof");
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
  TypeNode t = n[0].getType(check);
  if (check)
  {
    if (!t.isStringLike())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting a string-like term in replace");
    }
    TypeNode t2 = n[1].getType(check);
    if (t != t2)
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "expecting a term in second argument of replace that is the same "
          "type as the first argument");
    }
    t2 = n[2].getType(check);
    if (t != t2)
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "expecting a term in third argument of replace that is the same "
          "type as the first argument");
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
    TypeNode t = n[0].getType(check);
    if (!t.isStringLike())
    {
      std::stringstream ss;
      ss << "expecting a string-like term in argument of " << n.getKind();
      throw TypeCheckingExceptionPrivate(n, ss.str());
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
    TypeNode t = n[0].getType(check);
    if (!t.isStringLike())
    {
      std::stringstream ss;
      ss << "expecting a string-like term in argument of " << n.getKind();
      throw TypeCheckingExceptionPrivate(n, ss.str());
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
  TypeNode t = n[0].getType(check);
  if (check)
  {
    if (!t.isStringLike())
    {
      std::stringstream ss;
      ss << "expecting a string term in argument of " << n.getKind();
      throw TypeCheckingExceptionPrivate(n, ss.str());
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
    TypeNode t = n[0].getType(check);
    if (!t.isStringLike())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting a string-like term in relation");
    }
    TypeNode t2 = n[1].getType(check);
    if (t != t2)
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting two terms of the same string-like type in relation");
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
      TypeNode t = (*it).getType(check);
      if (!t.isString())  // string-only
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting a string term in regexp range");
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
    if (!n[0].getType().isString())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting string term in string to regexp");
    }
  }
  return nodeManager->regExpType();
}

bool StringToRegExpTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getKind() == kind::STRING_TO_REGEXP);
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
  Assert(n.getKind() == kind::CONST_SEQUENCE);
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
  Assert(n.getKind() == kind::SEQ_UNIT);
  TypeNode argType = n[0].getType(check);
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
  Assert(n.getKind() == kind::SEQ_NTH);
  TypeNode t = n[0].getType(check);
  if (check && !t.isStringLike())
  {
    throw TypeCheckingExceptionPrivate(n,
                                       "expecting a string-like term in nth");
  }
  if (check)
  {
    TypeNode t2 = n[1].getType(check);
    if (!t2.isInteger())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting an integer start term in nth");
    }
  }
  if (t.isSequence())
  {
    return t.getSequenceElementType();
  }
  Assert(t.isString());
  return nodeManager->integerType();
}

Cardinality SequenceProperties::computeCardinality(TypeNode type)
{
  Assert(type.getKind() == kind::SEQUENCE_TYPE);
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

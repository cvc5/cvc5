/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {
namespace theory {
namespace strings {

TypeNode StringConcatTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check)
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

TypeNode StringSubstrTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check)
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

TypeNode StringUpdateTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check)
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

TypeNode StringAtTypeRule::computeType(NodeManager* nodeManager,
                                       TNode n,
                                       bool check)
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

TypeNode StringIndexOfTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check)
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

TypeNode StringReplaceTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check)
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

TypeNode StringStrToBoolTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check)
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

TypeNode StringStrToIntTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check)
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

TypeNode StringStrToStrTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check)
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

TypeNode StringRelationTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check)
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

TypeNode RegExpRangeTypeRule::computeType(NodeManager* nodeManager,
                                          TNode n,
                                          bool check)
{
  if (check)
  {
    TNode::iterator it = n.begin();
    unsigned ch[2];

    for (int i = 0; i < 2; ++i)
    {
      TypeNode t = (*it).getType(check);
      if (!t.isString())  // string-only
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting a string term in regexp range");
      }
      if (!(*it).isConst())
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting a constant string term in regexp range");
      }
      if ((*it).getConst<String>().size() != 1)
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting a single constant string term in regexp range");
      }
      unsigned ci = (*it).getConst<String>().front();
      ch[i] = ci;
      ++it;
    }
    if (ch[0] > ch[1])
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "expecting the first constant is less or equal to the second one in "
          "regexp range");
    }
  }
  return nodeManager->regExpType();
}

TypeNode ConstSequenceTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check)
{
  Assert(n.getKind() == kind::CONST_SEQUENCE);
  return nodeManager->mkSequenceType(n.getConst<Sequence>().getType());
}

TypeNode SeqUnitTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check)
{
  return nodeManager->mkSequenceType(n[0].getType(check));
}

TypeNode SeqNthTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
{
  TypeNode t = n[0].getType(check);
  TypeNode t1 = t.getSequenceElementType();
  if (check)
  {
    if (!t.isSequence())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting a sequence in nth");
    }
    TypeNode t2 = n[1].getType(check);
    if (!t2.isInteger())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting an integer start term in nth");
    }
  }
  return t1;
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
}  // namespace cvc5

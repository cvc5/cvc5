/*********************                                                        */
/*! \file theory_bags_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory type rules.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H
#define CVC4__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5 {

class NodeManager;

namespace theory {
namespace bags {

struct BinaryOperatorTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
  static bool computeIsConst(NodeManager* nodeManager, TNode n);
}; /* struct BinaryOperatorTypeRule */

struct SubBagTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct SubBagTypeRule */

struct CountTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct CountTypeRule */

struct DuplicateRemovalTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct DuplicateRemovalTypeRule */

struct MkBagTypeRule
{
  static TypeNode computeType(NodeManager* nm, TNode n, bool check);
  static bool computeIsConst(NodeManager* nodeManager, TNode n);
}; /* struct MkBagTypeRule */

struct IsSingletonTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct IsMkBagTypeRule */

struct EmptyBagTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct EmptyBagTypeRule */

struct CardTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct CardTypeRule */

struct ChooseTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct ChooseTypeRule */

struct FromSetTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct FromSetTypeRule */

struct ToSetTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
}; /* struct ToSetTypeRule */

struct BagsProperties
{
  static Cardinality computeCardinality(TypeNode type)
  {
    return Cardinality::INTEGERS;
  }

  static bool isWellFounded(TypeNode type) { return type[0].isWellFounded(); }

  static Node mkGroundTerm(TypeNode type)
  {
    Assert(type.isBag());
    return NodeManager::currentNM()->mkConst(EmptyBag(type));
  }
}; /* struct BagsProperties */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5

#endif /* CVC4__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H */

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
 * Typing and cardinality rules for the theory of datatypes.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H
#define CVC5__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5 {
namespace theory {
namespace datatypes {

struct DatatypeConstructorTypeRule {
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);

  static bool computeIsConst(NodeManager* nodeManager, TNode n);
};

struct DatatypeSelectorTypeRule {
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct DatatypeTesterTypeRule {
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct DatatypeUpdateTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct DatatypeAscriptionTypeRule {
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct ConstructorProperties {
  static Cardinality computeCardinality(TypeNode type);
};

struct TupleUpdateTypeRule {
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class TupleUpdateOpTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct RecordUpdateTypeRule {
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class RecordUpdateOpTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class DtSizeTypeRule {
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class DtBoundTypeRule {
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class DtSygusBoundTypeRule {
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class DtSyguEvalTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class MatchTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class MatchCaseTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class MatchBindCaseTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class TupleProjectTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nm, TNode n, bool check);
};

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H */

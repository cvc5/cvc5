/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tianyi Liang, Yoni Zohar
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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H
#define CVC5__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H

#include "expr/node.h"

namespace cvc5 {

class NodeManager;
class TypeNode;

namespace theory {
namespace strings {

class StringConcatTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class StringSubstrTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class StringUpdateTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class StringAtTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class StringIndexOfTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class StringReplaceTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class StringStrToBoolTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class StringStrToIntTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class StringStrToStrTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class StringRelationTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class RegExpRangeTypeRule {
public:
 static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class StringToRegExpTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);

  /**
   * Returns true if the argument to STRING_TO_REGEXP is a constant.
   *
   * In general, our implementation of isConst is incomplete for regular
   * expressions, i.e. it is possible to return isConst for more regular
   * expression terms.
   *
   * However, we at least require returning isConst true for STRING_TO_REGEXP
   * applied to constant strings, as the regular expression enumerator uses
   * these.
   */
  static bool computeIsConst(NodeManager* nodeManager, TNode n);
};

class ConstSequenceTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class SeqUnitTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class SeqNthTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Properties of the sequence type */
struct SequenceProperties
{
  static Cardinality computeCardinality(TypeNode type);
  /** A sequence is well-founded if its element type is */
  static bool isWellFounded(TypeNode type);
  /** Make ground term for sequence type (return the empty sequence) */
  static Node mkGroundTerm(TypeNode type);
}; /* struct SequenceProperties */

}  // namespace strings
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H */

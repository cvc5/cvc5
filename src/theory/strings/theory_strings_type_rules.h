/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Aina Niemetz
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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H
#define CVC5__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H

#include "expr/node.h"

namespace cvc5::internal {

class NodeManager;
class TypeNode;

namespace theory {
namespace strings {

class StringConcatTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class StringSubstrTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class StringUpdateTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class StringAtTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class StringIndexOfTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class StringReplaceTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class StringStrToBoolTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class StringStrToIntTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class StringStrToStrTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class StringRelationTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class RegExpRangeTypeRule {
public:
 static TypeNode preComputeType(NodeManager* nm, TNode n);

 static TypeNode computeType(NodeManager* nodeManager,
                             TNode n,
                             bool check,
                             std::ostream* errOut);
};

class StringToRegExpTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);

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
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class SeqUnitTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class SeqNthTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
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
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H */

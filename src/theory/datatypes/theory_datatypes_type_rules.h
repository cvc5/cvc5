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

/**
 * A constructor is associated with a type (-> T1 ... Tn T). The type rule
 * for constructors ensures that the arguments are T1 ... Tn and returns T.
 * If the constructor is for a parametric datatype, the above is generalized
 * so that the arguments of type S1 ... Sn are specializations of T1 ... Tn
 * for type substitution sigma, and returns T * sigma.
 */
struct DatatypeConstructorTypeRule {
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);

  /**
   * A constructor term is constant if it is an AST built from constructor
   * terms only. This check is computed recursively on n.
   */
  static bool computeIsConst(NodeManager* nodeManager, TNode n);
};

/**
 * A selector is associated with a type (-> T1 T2). The type rule
 * for selectors ensures that the argument is T1 and returns T2.
 * This rule is generalized for parametric datatypes.
 */
struct DatatypeSelectorTypeRule {
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * A tester is associated with a type (-> T1 Bool). The type rule
 * for testrs ensures that the argument is T1 and returns Bool.
 * This rule is generalized for parametric datatypes.
 */
struct DatatypeTesterTypeRule {
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * An updater is associated with a selector of type (-> T1 T2). The type
 * rule for updaters expects arguments of type T1 and T2 and returns T1.
 * This rule is generalized for parametric datatypes.
 */
struct DatatypeUpdateTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * APPLY_TYPE_ASCRIPTION is a dummy kind to specialize the type of a datatype
 * constructor, e.g. (as nil (List Int)). The type rule returns the ascribed
 * type.
 */
struct DatatypeAscriptionTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct ConstructorProperties
{
  static Cardinality computeCardinality(TypeNode type);
};

class DtSizeTypeRule {
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class DtBoundTypeRule {
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class DtSygusEvalTypeRule
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

/**
 * A codatatype bound variable is used for constructing values for codatatypes.
 * It stores an index and a type. The type rule returns that type.
 */
class CodatatypeBoundVariableTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H */

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
 * Typing and cardinality rules for the theory of datatypes.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H
#define CVC5__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {
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
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);

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
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * A tester is associated with a type (-> T1 Bool). The type rule
 * for testers ensures that the argument is T1 and returns Bool.
 * This rule is generalized for parametric datatypes.
 */
struct DatatypeTesterTypeRule {
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * An updater is associated with a selector of type (-> T1 T2). The type
 * rule for updaters expects arguments of type T1 and T2 and returns T1.
 * This rule is generalized for parametric datatypes.
 */
struct DatatypeUpdateTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * APPLY_TYPE_ASCRIPTION is a dummy kind to specialize the type of a datatype
 * constructor, e.g., (as nil (List Int)). The type rule returns the ascribed
 * type.
 */
struct DatatypeAscriptionTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

struct ConstructorProperties
{
  static Cardinality computeCardinality(TypeNode type);
};

/**
 * The datatype size function expects any datatype and returns the integer type.
 */
class DtSizeTypeRule {
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * The datatype bound predicate expects any datatype, a constant integer, and
 * returns the Boolean type.
 */
class DtBoundTypeRule {
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * The type rule for sygus evaluation functions. DT_SYGUS_EVAL expects
 * (1) a term of SyGuS datatype type T, whose SyGuS variable list is (x1 ...
 * xn), (2) terms t1 ... tn whose types are the same as x1 ... xn. The returned
 * type is the builtin type associated with T.
 */
class DtSygusEvalTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * The type rule for match. Recall that a match term:
 *   (match l (((cons h t) h) (nil 0)))
 * is represented by the AST
 *  (MATCH l
 *     (MATCH_BIND_CASE (BOUND_VAR_LIST h t) (cons h t) h)
 *     (MATCH_CASE nil 0))
 *
 * The type rule for match performs several well-formedness checks, including:
 * - The head is a datatype T,
 * - The remaining children are either MATCH_BIND_CASE or MATCH_CASE,
 * - The patterns for the cases are over the same datatype as the head term,
 * - The return types for the cases are the same,
 * - The patterns specified by the children are exhaustive for T.
 *
 * The type rule returns the return type of the cases.
 */
class MatchTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * The type rule for match case ensures the first child is a datatype term,
 * and returns the type of the second argument.
 */
class MatchCaseTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * The type rule for match bind case ensures the first child is a bound variable
 * list and the second child is a datatype. Returns the type of the third
 * argument.
 */
class MatchBindCaseTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Tuple project is indexed by a list of indices (n_1, ..., n_m). It ensures
 * that the argument is a tuple whose arity k is greater than each n_i for
 * i = 1, ..., m. If the argument is of type (Tuple T_1 ... T_k), then the
 * returned type is (Tuple T_{n_1} ... T_{n_m}).
 */
class TupleProjectTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nm,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * A codatatype bound variable is used for constructing values for codatatypes.
 * It stores an index and a type. The type rule returns that type.
 */
class CodatatypeBoundVariableTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H */

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
 * Typing and cardinality rules for the theory of UF.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__UF__THEORY_UF_TYPE_RULES_H
#define CVC5__THEORY__UF__THEORY_UF_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

/**
 * Type rule for applications of uninterpreted functions, which are associated
 * to types (-> T1 ... Tn T). This ensures the arguments of n have type
 * T1 ... Tn and returns T.
 */
class UfTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * The type rule for cardinality constraint operators, which is indexed by a
 * type and an integer. Ensures that type is an uninterpreted sort and the
 * integer is positive, and returns the builtin type.
 */
class CardinalityConstraintOpTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * The type rule for combined cardinality constraint operators, which is indexed
 * by an integer. Ensures that the integer is positive, and returns the builtin
 * type.
 */
class CombinedCardinalityConstraintOpTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for HO_APPLY terms. Ensures the first argument is a function type
 * (-> T1 ... Tn T), the second argument is T1, and returns (-> T2 ... Tn T) if
 * n > 1 or T otherwise.
 */
class HoApplyTypeRule
{
 public:
  // the typing rule for HO_APPLY terms

  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for lambdas. Ensures the first argument is a bound varible list
 * (x1 ... xn). Returns the function type (-> T1 ... Tn T) where T1...Tn are
 * the types of x1..xn and T is the type of the second argument.
 */
class LambdaTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* class LambdaTypeRule */

/**
 * Type rule for function array constants. Returns the function type stored
 * in the FUNCTION_ARRAY_CONST payload of the node.
 */
class FunctionArrayConstTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class FunctionProperties
{
 public:
  static Cardinality computeCardinality(TypeNode type);

  /** Function type is well-founded if its component sorts are */
  static bool isWellFounded(TypeNode type);
  /**
   * Ground term for function sorts is (lambda x. t) where x is the
   * canonical variable list for its type and t is the canonical ground term of
   * its range.
   */
  static Node mkGroundTerm(TypeNode type);
}; /* class FuctionProperties */

/** Returns builtin type */
class IntToBitVectorOpTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * If n's kind is BITVECTOR_TO_NAT, expects bit-vector argument, returns
 * integer type.
 * If n's kind is INT_TO_BITVECTOR, expects integer argument, returns
 * bit-vector of specified width.
 */
class BitVectorConversionTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__UF__THEORY_UF_TYPE_RULES_H */

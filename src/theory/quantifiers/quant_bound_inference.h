/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quantifiers bound inference.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUANT_BOUND_INFERENCE_H
#define CVC5__THEORY__QUANTIFIERS__QUANT_BOUND_INFERENCE_H

#include <vector>
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {

class RepSetIterator;

namespace quantifiers {

class BoundedIntegers;

/** Types of bounds that can be inferred for quantified formulas */
enum BoundVarType
{
  // a variable has a finite bound because it has finite cardinality
  BOUND_FINITE,
  // a variable has a finite bound because it is in an integer range, e.g.
  //   forall x. u <= x <= l => P(x)
  BOUND_INT_RANGE,
  // a variable has a finite bound because it is a member of a set, e.g.
  //   forall x. x in S => P(x)
  BOUND_SET_MEMBER,
  // a variable has a finite bound because only a fixed set of terms are
  // relevant for it in the domain of the quantified formula, e.g.
  //   forall x. ( x = t1 OR ... OR x = tn ) => P(x)
  BOUND_FIXED_SET,
  // a bound has not been inferred for the variable
  BOUND_NONE
};

/**
 * This class is the central utility for determining if the domain of a
 * quantified formula is finite, or whether its domain can be restricted to
 * a finite subdomain based on one of the above types.
 */
class QuantifiersBoundInference
{
 public:
  /**
   * @param cardMax The maximum cardinality we consider to be small enough
   * to "complete" below.
   * @param isFmf Whether finite model finding (for uninterpreted sorts) is
   * enabled.
   */
  QuantifiersBoundInference(unsigned cardMax, bool isFmf = false);
  /** finish initialize */
  void finishInit(BoundedIntegers* b);
  /** may complete type
   *
   * Returns true if the type tn is closed enumerable, is interpreted as a
   * finite type, and has cardinality less than some reasonable value
   * (currently < 1000). This method caches the results of whether each type
   * may be completed.
   */
  bool mayComplete(TypeNode tn);
  /**
   * Static version of the above method where maximum cardinality is
   * configurable.
   */
  static bool mayComplete(TypeNode tn, unsigned cardMax);
  /** does variable v of quantified formula q have a finite bound? */
  bool isFiniteBound(Node q, Node v);
  /** get bound var type
   *
   * This returns the type of bound that was inferred for variable v of
   * quantified formula q.
   */
  BoundVarType getBoundVarType(Node q, Node v);
  /**
   * Get the indices of bound variables, in the order they should be processed
   * in a RepSetIterator.
   *
   * For details, see BoundedIntegers::getBoundVarIndices.
   */
  void getBoundVarIndices(Node q, std::vector<size_t>& indices) const;
  /**
   * Get bound elements
   *
   * This gets the (finite) enumeration of the range of variable v of quantified
   * formula q and adds it into the vector elements in the context of the
   * iteration being performed by rsi. It returns true if it could successfully
   * determine this range.
   *
   * For details, see BoundedIntegers::getBoundElements.
   */
  bool getBoundElements(RepSetIterator* rsi,
                        bool initial,
                        Node q,
                        Node v,
                        std::vector<Node>& elements) const;

 private:
  /** The maximum cardinality for which we complete */
  unsigned d_cardMax;
  /** Whether finite model finding is enabled */
  bool d_isFmf;
  /** may complete */
  std::unordered_map<TypeNode, bool> d_may_complete;
  /** The bounded integers module, which may help infer bounds */
  BoundedIntegers* d_bint;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__QUANT_BOUND_INFERENCE_H */

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of conversion between approximate and dependent types.
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALF__ALF_DEPENDENT_TYPE_CONVERTER_H
#define CVC4__PROOF__ALF__ALF_DEPENDENT_TYPE_CONVERTER_H

#include "expr/node_converter.h"
#include "proof/alf/alf_node_converter.h"

namespace cvc5::internal {
namespace proof {

/**
 * Converts an (approximate) type into a dependent one.
 *
 * This is used for printing RARE rules in ALF. For example, the RARE rule:
 *
 * (define-cond-rule bv-extract-concat-1
 *   ((x ?BitVec) (xs ?BitVec :list) (y ?BitVec) (i Int) (j Int))
 *   (<= j (@bvsize x))
 *   (extract j i (concat xs y x))
 *   (extract j i x))
 *
 * becomes the ALF rule:
 *
 * (declare-rule bv-extract-concat-1
 *   ((@n0 Int) (@n1 Int) (@n2 Int) (x (BitVec @n0)) (xs (BitVec @n1) :list)
 *    (y (BitVec @n2)) (i Int) (j Int))
 *  :premises ((= (<= j (@bvsize x)) true))
 *  :args (x xs y i j)
 *  :conclusion (= (extract j i (concat xs y x)) (extract j i x))
 * )
 *
 * This converter is responsible for converting an approximate type into a Node
 * that is printed as the equivalent dependent type. For example, given
 * ?BitVec as input, it returns a node that prints as (BitVec @n0) where @n0
 * is a free parameter introduced in the conversion. Each free parameter
 * introduced in this way is unique.
 *
 * Examples:
 *    ?BitVec --> (BitVec @n0) where @n0 is an integer variable.
 *    (Array ? ?) ---> (Array @T0 @T1) where @T0, @T1 are type variables
 *    (Set (Set ?)) ---> (Set (Set @T0))
 *    ?FloatingPoint ---> (FloatingPoint @n0 @n1)
 *    ?Tuple --> @T0, where note tuples do not have fixed arity so they are
 *               approximated as a type variable.
 *
 * Note that approximate functions and approximate tuples are the only two types
 * that are not converted precisely in this translation.
 */
class AlfDependentTypeConverter
{
 public:
  AlfDependentTypeConverter(NodeManager* nm, BaseAlfNodeConverter& tproc);
  /**
   * Convert the approximate type tn to a node that prints the dependent
   * type that is equivalent to tn, possibly with free parameters.
   * @param tn The type to convert.
   * @return The node that prints the dependent type equivalent to tn.
   */
  Node process(const TypeNode& tn);
  /**
   * @return The free parameters introduced by calls to the above.
   */
  const std::vector<Node>& getFreeParameters() const;

 private:
  /** Pointer to node manager */
  NodeManager* d_nm;
  /** The parent converter, used for getting internal symbols and utilities */
  BaseAlfNodeConverter& d_tproc;
  /** The free parameters introduced by this pass */
  std::vector<Node> d_params;
  /** Counters for allocating unique types and integers */
  size_t d_typeCounter;
  size_t d_intCounter;
  /** The type of ALF sorts, which can appear in terms */
  TypeNode d_sortType;
  /** Kind to name */
  std::map<Kind, std::string> d_kindToName;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif

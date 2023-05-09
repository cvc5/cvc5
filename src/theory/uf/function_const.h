/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for function constants
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__UF__FUNCTION_CONST_H
#define CVC5__THEORY__UF__FUNCTION_CONST_H

#include <unordered_map>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

/** Conversion between lambda and array constants */
class FunctionConst
{
 public:
  /** Get function type for array type
   *
   * This returns the function type of terms returned by the function
   * getLambdaForArrayRepresentation( t, bvl ),
   * where t.getType()=atn.
   *
   * bvl should be a bound variable list whose variables correspond in-order
   * to the index types of the (curried) Array type. For example, a bound
   * variable list bvl whose variables have types (Int, Real) can be given as
   * input when paired with atn = (Array Int (Array Real Bool)), or (Array Int
   * (Array Real (Array Bool Bool))). This function returns (-> Int Real Bool)
   * and (-> Int Real (Array Bool Bool)) respectively in these cases.
   * On the other hand, the above bvl is not a proper input for
   * atn = (Array Int (Array Bool Bool)) or (Array Int Int).
   * If the types of bvl and atn do not match, we throw an assertion failure.
   */
  static TypeNode getFunctionTypeForArrayType(TypeNode atn, Node bvl);
  /** Get array type for function type
   *
   * This returns the array type of terms returned by
   * getArrayRepresentationForLambda( t ), where t.getType()=ftn.
   */
  static TypeNode getArrayTypeForFunctionType(TypeNode ftn);
  /**
   * Returns a node of kind LAMBDA that is equivalent to n, or null otherwise.
   *
   * This is the identity function for lambda terms and runs the conversion
   * for constant array functions, and null for all other nodes. For details,
   * see the method getLambdaForArrayRepresentation.
   */
  static Node toLambda(TNode n);
  /**
   * Extracts the array constant from the payload of a a function array constant
   *
   *
   * Given a lambda expression n, returns an array term that corresponds to n.
   * This does the opposite direction of the examples described above the
   * method getLambdaForArrayRepresentation.
   *
   * We limit the return values of this method to be almost constant functions,
   * that is, arrays of the form:
   *   (store ... (store (storeall _ b) i1 e1) ... in en)
   * where b, i1, e1, ..., in, en are constants.
   * Notice however that the return value of this form need not be an
   * array such that isConst is true.
   *
   * If it is not possible to construct an array of this form that corresponds
   * to n, this method returns null.
   */
  static Node toArrayConst(TNode n);

 private:
  /**
   * Given an array constant a, returns a lambda expression that it corresponds
   * to, with bound variable list bvl.
   * Examples:
   *
   * (store (storeall (Array Int Int) 2) 0 1)
   * becomes
   * ((lambda x. (ite (= x 0) 1 2))
   *
   * (store (storeall (Array Int (Array Int Int)) (storeall (Array Int Int) 4))
   * 0 (store (storeall (Array Int Int) 3) 1 2)) becomes (lambda xy. (ite (= x
   * 0) (ite (= x 1) 2 3) 4))
   *
   * (store (store (storeall (Array Int Bool) false) 2 true) 1 true)
   * becomes
   * (lambda x. (ite (= x 1) true (ite (= x 2) true false)))
   *
   * Notice that the return body of the lambda is rewritten to ensure that the
   * representation is canonical. Hence the last
   * example will in fact be returned as:
   * (lambda x. (ite (= x 1) true (= x 2)))
   */
  static Node getLambdaForArrayRepresentation(TNode a, TNode bvl);
  /** recursive helper for getLambdaForArrayRepresentation */
  static Node getLambdaForArrayRepresentationRec(
      TNode a,
      TNode bvl,
      unsigned bvlIndex,
      std::unordered_map<TNode, Node>& visited);
  /** recursive helper for toArrayConst */
  static Node getArrayRepresentationForLambdaRec(TNode n, TypeNode retType);
};

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__UF__FUNCTION_CONST_H */

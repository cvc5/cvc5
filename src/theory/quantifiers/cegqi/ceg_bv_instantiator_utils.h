/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of ceg_bv_instantiator.
 */

#include "cvc5_private.h"

#ifndef CVC5__BV_INSTANTIATOR_UTILS_H
#define CVC5__BV_INSTANTIATOR_UTILS_H

#include "expr/attribute.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

struct BvLinearAttributeId
{
};
using BvLinearAttribute = expr::Attribute<BvLinearAttributeId, bool>;

class BvInstantiatorUtil : protected EnvObj
{
 public:
  BvInstantiatorUtil(Env& env);
  /**
   * Determine coefficient of pv in term n, where n has the form pv, -pv, pv *
   * t, or -pv * t. Extracting the coefficient of multiplications only succeeds
   * if the multiplication are normalized with normalizePvMult.
   *
   * If sucessful it returns
   *   1    if n ==  pv,
   *  -1    if n == -pv,
   *   t    if n ==  pv * t,
   *  -t    if n == -pv * t.
   * If n is not a linear term, a null node is returned.
   */
  Node getPvCoeff(TNode pv, TNode n) const;

  /**
   * Normalizes the children of a BITVECTOR_MULT w.r.t. pv. contains_pv marks
   * terms in which pv occurs.
   * For example,
   *
   *  a * -pv * b * c
   *
   * is rewritten to
   *
   *  pv * -(a * b * c)
   *
   * Returns the normalized node if the resulting term is linear w.r.t. pv and
   * a null node otherwise. If pv does not occur in children it returns a
   * multiplication over children.
   */
  Node normalizePvMult(TNode pv,
                       const std::vector<Node>& children,
                       std::unordered_map<Node, bool>& contains_pv) const;

  /**
   * Normalizes the children of a BITVECTOR_ADD w.r.t. pv. contains_pv marks
   * terms in which pv occurs.
   * For example,
   *
   *  a * pv + b + c * -pv
   *
   * is rewritten to
   *
   *  pv * (a - c) + b
   *
   * Returns the normalized node if the resulting term is linear w.r.t. pv and
   * a null node otherwise. If pv does not occur in children it returns an
   * addition over children.
   */
  Node normalizePvPlus(Node pv,
                       const std::vector<Node>& children,
                       std::unordered_map<Node, bool>& contains_pv) const;

  /**
   * Linearize an equality w.r.t. pv such that pv only occurs once. contains_pv
   * marks terms in which pv occurs.
   * For example, equality
   *
   *   -pv * a + b = c + pv
   *
   * rewrites to
   *
   *   pv * (-a - 1) = c - b.
   */
  Node normalizePvEqual(Node pv,
                        const std::vector<Node>& children,
                        std::unordered_map<Node, bool>& contains_pv) const;

 private:
  /** Checks whether n is a linear plus */
  bool isLinearPlus(TNode n,
                    TNode pv,
                    std::unordered_map<Node, bool>& contains_pv) const;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
#endif

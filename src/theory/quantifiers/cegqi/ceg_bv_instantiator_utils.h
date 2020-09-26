/*********************                                                        */
/*! \file ceg_bv_instantiator_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Aina Niemetz, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of ceg_bv_instantiator
 **/

#include "cvc4_private.h"

#ifndef CVC4__BV_INSTANTIATOR_UTILS_H
#define CVC4__BV_INSTANTIATOR_UTILS_H

#include "expr/attribute.h"
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

struct BvLinearAttributeId
{
};
using BvLinearAttribute = expr::Attribute<BvLinearAttributeId, bool>;

namespace utils {

/**
 * Determine coefficient of pv in term n, where n has the form pv, -pv, pv * t,
 * or -pv * t. Extracting the coefficient of multiplications only succeeds if
 * the multiplication are normalized with normalizePvMult.
 *
 * If sucessful it returns
 *   1    if n ==  pv,
 *  -1    if n == -pv,
 *   t    if n ==  pv * t,
 *  -t    if n == -pv * t.
 * If n is not a linear term, a null node is returned.
 */
Node getPvCoeff(TNode pv, TNode n);

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
Node normalizePvMult(
    TNode pv,
    const std::vector<Node>& children,
    std::unordered_map<Node, bool, NodeHashFunction>& contains_pv);

/**
 * Normalizes the children of a BITVECTOR_PLUS w.r.t. pv. contains_pv marks
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
Node normalizePvPlus(
    Node pv,
    const std::vector<Node>& children,
    std::unordered_map<Node, bool, NodeHashFunction>& contains_pv);

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
Node normalizePvEqual(
    Node pv,
    const std::vector<Node>& children,
    std::unordered_map<Node, bool, NodeHashFunction>& contains_pv);

}  // namespace utils
}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
#endif

/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inverse rules for bit-vector operators.
 */

#include "cvc5_private.h"

#ifndef CVC5__BV_INVERTER_UTILS_H
#define CVC5__BV_INVERTER_UTILS_H

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace utils {

/* Get invertibility condition for BITVECTOR_ULT and BITVECTOR_UGT. */
Node getICBvUltUgt(bool pol, Kind k, Node x, Node t);

/* Get invertibility condition for BITVECTOR_SLT and BITVECTOR_SGT. */
Node getICBvSltSgt(bool pol, Kind k, Node x, Node t);

/* Get invertibility condition for BITVECTOR_MUL. */
Node getICBvMult(
    bool pol, Kind litk, Kind k, unsigned idx, Node x, Node s, Node t);

/* Get invertibility condition for BITVECTOR_UREM. */
Node getICBvUrem(
    bool pol, Kind litk, Kind k, unsigned idx, Node x, Node s, Node t);

/* Get invertibility condition for BITVECTOR_UDIV. */
Node getICBvUdiv(
    bool pol, Kind litk, Kind k, unsigned idx, Node x, Node s, Node t);

/* Get invertibility condition for BITVECTOR_AND and BITVECTOR_OR. */
Node getICBvAndOr(
    bool pol, Kind litk, Kind k, unsigned idx, Node x, Node s, Node t);

/* Get invertibility condition for BITVECTOR_LSHR. */
Node getICBvLshr(
    bool pol, Kind litk, Kind k, unsigned idx, Node x, Node s, Node t);

/* Get invertibility condition for BITVECTOR_ASHR. */
Node getICBvAshr(
    bool pol, Kind litk, Kind k, unsigned idx, Node x, Node s, Node t);

/* Get invertibility condition for BITVECTOR_SHL. */
Node getICBvShl(
    bool pol, Kind litk, Kind k, unsigned idx, Node x, Node s, Node t);

/* Get invertibility condition for BITVECTOR_CONCAT. */
Node getICBvConcat(
    bool pol, Kind litk, unsigned idx, Node x, Node sv_t, Node t);

/* Get invertibility condition for BITVECTOR_SEXT. */
Node getICBvSext(bool pol, Kind litk, unsigned idx, Node x, Node sv_t, Node t);

}  // namespace utils
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
#endif

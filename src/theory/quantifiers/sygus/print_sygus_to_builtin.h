/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sygus to builtin
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS__PRINT_SYGUS_TO_BUILTIN_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS__PRINT_SYGUS_TO_BUILTIN_H

#include <map>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Similar to sygusToBuiltin in sygus_datatypes_utils, but additionally
 * annotates terms with the grammar that orginate from.
 *
 * Note that this method generates a node that is of kind RAW_SYMBOL. It should
 * only be printed, and not inspected.
 *
 * For example, for this grammar:
 * (synth-fun f () Int
 *   ((a Int) (b Int))
 *   ((a Int (1 (+ a b) ))
 *    (b Int (1 3)))
 *
 * Given input the sygus datatype term (a_PLUS a_1 b_1), this method returns
 * a node that prints as:
 *   (! (+ (! 1 :gterm a) (! 1 :gterm b)) :gterm a)
 */
Node getPrintableSygusToBuiltin(Node n);

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS__TYPE_INFO_H */

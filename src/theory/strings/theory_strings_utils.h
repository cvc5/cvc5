/*********************                                                        */
/*! \file theory_strings_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Util functions for theory strings.
 **
 ** Util functions for theory strings.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__THEORY_STRINGS_UTILS_H
#define CVC4__THEORY__STRINGS__THEORY_STRINGS_UTILS_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace strings {
namespace utils {

/**
 * Make the conjunction of nodes in a. Removes duplicate conjuncts, returns
 * true if a is empty, and a single literal if a has size 1.
 */
Node mkAnd(std::vector<Node>& a);

/**
 * Gets the "vector form" of term n, adds it to c.
 *
 * For example:
 * when n = str.++( x, y ), c is { x, y }
 * when n = str.++( x, str.++( y, z ), w ), c is { x, str.++( y, z ), w )
 * when n = x, c is { x }
 *
 * Also applies to regular expressions (re.++ above).
 */
void getConcat(Node n, std::vector<Node>& c);

/**
 * Make the concatentation from vector c
 * The kind k is either STRING_CONCAT or REGEXP_CONCAT.
 */
Node mkConcat(Kind k, std::vector<Node>& c);

}  // namespace utils
}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif

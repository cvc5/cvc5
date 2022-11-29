/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A type checker.
 */

#include "cvc5_private.h"

// ordering dependence
#include "expr/node.h"

#ifndef CVC5__EXPR__TYPE_CHECKER_H
#define CVC5__EXPR__TYPE_CHECKER_H

namespace cvc5::internal {
namespace expr {

class TypeChecker {
public:
 static TypeNode computeType(NodeManager* nodeManager,
                             TNode n,
                             bool check = false);

 static bool computeIsConst(NodeManager* nodeManager, TNode n);

};/* class TypeChecker */

}  // namespace expr
}  // namespace cvc5::internal

#endif /* CVC5__EXPR__TYPE_CHECKER_H */

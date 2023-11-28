/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
 /**
  * Precompute type.
  *
  * This returns the type of n if it can be determined *without* looking at
  * the types of its children. For example, the preComputeType rule for AND
  * may return Boolean type, since AND always has type Boolean regardless of
  * its children. Returning a type for this method does not ensure that n
  * is a well-sorted type.
  *
  * Notice that by convention, the method preComputeType is not be given for
  * kinds that have no children. Instead, the method computeType should be
  * implemented instead.
  *
  * @return the type tn (if can be inferred) for n. If TypeNode::null, then
  * we did not infer the type of n, and will call computeType.
  */
 static TypeNode preComputeType(NodeManager* nodeManager, TNode n);
 /**
  * Compute type.
  *
  * Return the type of n. This method can assume that the types of the children
  * of n are available (via Node::getType()).
  *
  * @param nodeManager The current node manager
  * @param n The node to type check
  * @param check If this is true, we ensure that n is a well-formed term. If
  * it is not, then we return TypeNode::null and write an error message on
  * errOut (if provided)
  * @param errOut (if non-null) an output stream to write error information to.
  * Note that a user of this method may wish to provide a null stream for
  * performance reasons, in the case we are internally constructing a node for
  * the purposes of checking whether it is well-typed, but do not care about
  * reporting an error message.
  * @return the type tn for n, or TypeNode::null if we determined that n is
  * not well-sorted.
  */
 static TypeNode computeType(NodeManager* nodeManager,
                             TNode n,
                             bool check = false,
                             std::ostream* errOut = nullptr);

 static bool computeIsConst(NodeManager* nodeManager, TNode n);

};/* class TypeChecker */

}  // namespace expr
}  // namespace cvc5::internal

#endif /* CVC5__EXPR__TYPE_CHECKER_H */

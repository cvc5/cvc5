/*********************                                                        */
/*! \file rewrite_db_term_process.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewrite database term processor
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__REWRITE_DB_TERM_PROCESS__H
#define CVC4__THEORY__REWRITE_DB_TERM_PROCESS__H

#include <map>
#include <unordered_map>
#include "expr/node.h"

namespace CVC4 {
namespace theory {

/**
 * The AST structure of terms in the proof checker and in CVC4 is different.
 * This class converts between the two expected AST structures. These
 * differences include:
 * (1) CVC4 has n-ary associative operators; the proof checker assumes binary
 * applications only,
 * (2) CVC4 has (word) string literals; the proof checker assumes these are
 * concatenations of constants, e.g. "ABC" is (str.++ "A" (str.++ "B" "C")).
 *
 */
class RewriteDbTermProcess
{
 public:
  /** convert to internal
   *
   * This converts the node n to the internal shape that it would be in
   * the proof checker. This means that n-ary applications are converted
   * to (left-associative) chains.
   */
  Node toInternal(Node n);
  /** convert to external
   *
   * Inverse of the above translation
   */
  Node toExternal(Node n);

 private:
  /** Map from nodes to their internal representation */
  std::unordered_map<Node, Node, NodeHashFunction> d_internal;
  std::unordered_map<Node, Node, NodeHashFunction> d_external;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__REWRITE_DB_TERM_PROCESS__H */

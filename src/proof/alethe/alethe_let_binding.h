/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for Alethe let binding
 */
#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALETHE_LET_BINDING_H
#define CVC5__PROOF__ALETHE_LET_BINDING_H

#include "printer/let_binding.h"

namespace cvc5::internal {

namespace proof {

/** The Alethe-specific let binder.
 *
 * Differently from the regular let binder, where all letified subterms are
 * replaced by a fresh variable, the Alethe let binder replaces the first
 * occurrence of a term n (first visited on a post-order traversal) by a fresh
 * variable whose name is "(! n :named v)", in which `v` is another fresh
 * variable. The subsequent occurrences of `n` are replaced by `v`.
 */
class AletheLetBinding : public LetBinding
{
 public:
  AletheLetBinding(uint32_t thresh);

  /**
   * Convert n based on the state of the let binding.
   *
   * The conversion is done as summarized as above, but the name of the fresh
   * variable `v` is prefixed by `prefix`.
   *
   * @param n The node to convert
   * @param prefix The prefix of variables to convert
   * @return the converted node.
   */
  Node convert(Node n, const std::string& prefix);

 private:
  /** The set of terms that have already been "decleared", i.e., already had
   * their first occurrence replaced. */
  std::unordered_set<Node> d_declared;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ALETHE_LET_BINDING_H */

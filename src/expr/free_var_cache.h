/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for allocating a list of free variables
 */
#include "cvc5_private.h"

#ifndef CVC5__EXPR__FREE_VAR_CACHE_H
#define CVC5__EXPR__FREE_VAR_CACHE_H

#include <vector>

#include "expr/node.h"

namespace cvc5::internal {

/**
 * A class for allocating a list of free variables for provided types.
 */
class FreeVarCache
{
 public:
  /** get free variable
   *
   * This class caches a list of free variables for each type, which are
   * used, for instance, for constructing canonical forms of terms with free
   * variables. This function returns the i^th free variable for type tn.
   */
  TNode getFreeVar(const TypeNode& tn, size_t i);
  /** get free variable and increment
   *
   * This function returns the next free variable for type tn, and increments
   * the counter in var_count for that type.
   */
  TNode getFreeVarInc(const TypeNode& tn,
                      std::map<TypeNode, size_t>& var_count);
  /** returns true if n is a cached free variable (in d_fv). */
  bool isFreeVar(const Node& n) const;
  /** returns the identifier for a cached free variable. */
  size_t getFreeVarId(const Node& n) const;
  /** returns true if n has a cached free variable (in d_fv). */
  bool hasFreeVar(const Node& n) const;

 private:
  /** a cache of fresh variables for each type */
  std::map<TypeNode, std::vector<Node> > d_fv;
  /**
   * Maps free variables to a unique identifier for their type, which is their
   * index in the vector d_fv for their type.
   */
  std::map<Node, size_t> d_fvId;
  /** All variables allocated by this class */
  std::vector<Node> d_allVars;
};

}  // namespace cvc5::internal

#endif

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
 * A class for allocating a list of free variables
 */
#include "cvc5_private.h"

#ifndef CVC5__EXPR__FREE_VAR_CACHE_H
#define CVC5__EXPR__FREE_VAR_CACHE_H

#include <vector>

#include "expr/node.h"

namespace cvc5::internal {

/**
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
  /**
   * Same as above, but allocates variables of type tn based on stn. This can
   * be used e.g. if we want to maintain multiple lists of variables of type
   * tn for different stn.
   */
  TNode getFreeVar(const TypeNode& tn, size_t i, const TypeNode& stn);
  /** get free variable and increment
   *
   * This function returns the next free variable for type tn, and increments
   * the counter in var_count for that type.
   */
  TNode getFreeVarInc(const TypeNode& tn,
                      std::map<TypeNode, size_t>& var_count);
  /**
   * Same as above, but allocates variables of type tn based on stn. This can
   * be used e.g. if we want to maintain multiple lists of variables of type
   * tn for different stn.
   */
  TNode getFreeVarInc(const TypeNode& tn,
                      std::map<TypeNode, size_t>& var_count,
                      const TypeNode& stn);
  /** returns true if n is a cached free variable (in d_fv). */
  bool isFreeVar(const Node& n) const;
  /** returns the identifier for a cached free variable. */
  size_t getFreeVarId(const Node& n) const;
  /** returns true if n has a cached free variable (in d_fv). */
  bool hasFreeVar(const Node& n) const;

 private:
  /** a cache of fresh variables for each type
   *
   * We store two versions of this list:
   *   index 0: mapping from builtin types to fresh variables of that type,
   *   index 1: mapping from sygus types to fresh varaibles of the type they
   *            encode.
   */
  std::map<TypeNode, std::vector<Node> > d_fv;
  /**
   * Maps free variables to a unique identifier for their builtin type. Notice
   * that, e.g. free variables of type Int and those that are of a sygus
   * datatype type that encodes Int must have unique identifiers. This is
   * to ensure that sygusToBuiltin for non-ground terms maps variables to
   * unique variabales.
   */
  std::map<Node, size_t> d_fvId;
  /** All variables allocated by this class */
  std::vector<Node> d_allVars;
};

}  // namespace cvc5::internal

#endif

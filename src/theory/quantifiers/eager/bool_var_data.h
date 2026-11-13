/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Per-Boolean-variable data of the eager E-matching core.
 *
 * Ported from Z3: src/smt/smt_bool_var_data.h.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__BOOL_VAR_DATA_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__BOOL_VAR_DATA_H

namespace cvc5::internal {
namespace theory::quantifiers::eager {

/** The data the core keeps for each Boolean variable. */
struct BoolVarData
{
 private:
  /** true if the variable is an equality atom */
  uint32_t d_eq : 1;
  /** has an enode associated with it */
  uint32_t d_enode : 1;
  /** true if the variable is attached to a quantifier */
  uint32_t d_quantifier : 1;
  /** the scope level at which the variable was internalized */
  uint32_t d_iscopeLvl : 23;

 public:
  /** The scope level at which the variable was internalized. */
  uint32_t getInternLevel() const { return d_iscopeLvl; }

  /** True if the variable is an equality, a quantifier, or has an enode. */
  bool isAtom() const { return d_eq || d_quantifier || d_enode; }

  /** True if the variable has an enode associated with it. */
  bool isENode() const { return d_enode; }

  /** Record that the variable has an enode. */
  void setENodeFlag() { d_enode = true; }

  /** Clear the enode flag; invoked from the trail. */
  void resetENodeFlag() { d_enode = false; }

  /** True if the variable is attached to a quantifier. */
  bool isQuantifier() const { return d_quantifier; }

  /** Record that the variable is attached to a quantifier. */
  void setQuantifierFlag() { d_quantifier = true; }

  /** True if the variable is an equality atom. */
  bool isEq() const { return d_eq; }

  /** Record that the variable is an equality atom. */
  void setEqFlag() { d_eq = true; }

  /** Initialize the data of a variable internalized at scope iscopeLvl. */
  void init(uint32_t iscopeLvl)
  {
    d_iscopeLvl = iscopeLvl;
    d_eq = false;
    d_enode = false;
    d_quantifier = false;
  }
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__BOOL_VAR_DATA_H */

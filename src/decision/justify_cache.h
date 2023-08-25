/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A cache to remember what is justified
 */

#include "cvc5_private.h"

#ifndef CVC5__DECISION__JUSTIFY_CACHE_H
#define CVC5__DECISION__JUSTIFY_CACHE_H

#include "context/cdinsert_hashmap.h"
#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"

namespace cvc5::internal {
namespace decision {

/**
 * A mapping storing the justification values of nodes which uses the SAT solver
 * and CNF stream to lookup the value of literals.
 */
class JustifyCache
{
 public:
  /** Constructor */
  JustifyCache(context::Context* c,
               prop::CDCLTSatSolver* ss,
               prop::CnfStream* cs);
  /**
   * Returns the value TRUE/FALSE for n, or UNKNOWN otherwise.
   *
   * We return a value for n only if we have justified its values based on its
   * children. For example, we return UNKNOWN for n of the form (and A B) if
   * A and B have UNKNOWN value, even if the SAT solver has assigned a value for
   * (internal) node n. If n itself is a theory literal, we lookup its value
   * in the SAT solver if it is not already cached.
   */
  prop::SatValue lookupValue(TNode n);
  /**
   * Set that n is justified with the given value. This should be set when:
   * - n is a theory literal assigned to the given value,
   * - n evaluates to value based on the justification values of its children.
   * The value of n should not be set more than once.
   */
  void setValue(const Node& n, prop::SatValue value);
  /**
   * Does n already have a justification value stored in this class?
   */
  bool hasValue(TNode n) const;

 private:
  /** Mapping from non-negated nodes to their SAT value */
  context::CDInsertHashMap<Node, prop::SatValue> d_justified;
  /** Pointer to the SAT solver */
  prop::CDCLTSatSolver* d_satSolver;
  /** Pointer to the CNF stream */
  prop::CnfStream* d_cnfStream;
};

}  // namespace decision
}  // namespace cvc5::internal

#endif /* CVC5__DECISION__JUSTIFY_CACHE_H */

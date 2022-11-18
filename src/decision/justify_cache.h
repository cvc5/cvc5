/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
 */
class JustifyCache
{
 public:
  /** Constructor */
  JustifyCache(context::Context* c,
               prop::CDCLTSatSolverInterface* ss,
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
  bool hasValue(TNode n);
  /**
   * Set justified
   */
  void setValue(const Node& n, prop::SatValue value);

 private:
  /** Mapping from non-negated nodes to their SAT value */
  context::CDInsertHashMap<Node, prop::SatValue> d_justified;
  /** Pointer to the SAT solver */
  prop::CDCLTSatSolverInterface* d_satSolver;
  /** Pointer to the CNF stream */
  prop::CnfStream* d_cnfStream;
};

}  // namespace decision
}  // namespace cvc5::internal

#endif /* CVC5__DECISION__JUSTIFY_CACHE_H */

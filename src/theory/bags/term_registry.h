/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags state object.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__TERM_REGISTRY_H
#define CVC5__THEORY__BAGS__TERM_REGISTRY_H

#include <map>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

class InferenceManager;
class SolverState;

/**
 * Term registry, the purpose of this class is to maintain a database of
 * commonly used terms, and mappings from bags to their "proxy variables".
 */
class TermRegistry : protected EnvObj
{
  typedef context::CDHashMap<Node, Node> NodeMap;

 public:
  TermRegistry(Env& env, SolverState& state, InferenceManager& im);

  /**
   * Returns the existing empty bag for type tn
   * or creates a new one and returns it.
   **/
  Node getEmptyBag(TypeNode tn);

 private:
  /** The inference manager */
  InferenceManager& d_im;
  /** Map from bag terms to their proxy variables */
  NodeMap d_proxy;
  /** Backwards map of above */
  NodeMap d_proxy_to_term;
  /** Map from types to empty bag of that type */
  std::map<TypeNode, Node> d_emptybag;
}; /* class Term */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__TERM_REGISTRY_H */

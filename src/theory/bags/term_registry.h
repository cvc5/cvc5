/*********************                                                        */
/*! \file term_registry.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags state object
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__TERM_REGISTRY_H
#define CVC4__THEORY__BAGS__TERM_REGISTRY_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"

namespace CVC4 {
namespace theory {
namespace bags {

/**
 * Term registry, the purpose of this class is to maintain a database of
 * commonly used terms, and mappings from bags to their "proxy variables".
 */
class TermRegistry
{
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeMap;

 public:
  TermRegistry(SolverState& state, InferenceManager& im);

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
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__TERM_REGISTRY_H */

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sets state object.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SETS__TERM_REGISTRY_H
#define CVC5__THEORY__SETS__TERM_REGISTRY_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "proof/eager_proof_generator.h"
#include "smt/env_obj.h"
#include "theory/sets/inference_manager.h"
#include "theory/sets/skolem_cache.h"
#include "theory/sets/solver_state.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

/**
 * Term registry, the purpose of this class is to maintain a database of
 * commonly used terms, and mappings from sets to their "proxy variables".
 */
class TermRegistry : protected EnvObj
{
  typedef context::CDHashMap<Node, Node> NodeMap;

 public:
  TermRegistry(Env& env,
               SolverState& state,
               InferenceManager& im,
               SkolemCache& skc);
  /** get the proxy variable for set n
   *
   * Proxy variables are used to communicate information that otherwise would
   * not be possible due to rewriting. For example, the literal
   *   card( singleton( 0 ) ) = 1
   * is rewritten to true. Instead, to communicate this fact (e.g. to other
   * theories), we require introducing a proxy variable x for singleton( 0 ).
   * Then:
   *   card( x ) = 1 ^ x = singleton( 0 )
   * communicates the equivalent of the above literal.
   */
  Node getProxy(Node n);
  /** Get the empty set of type tn */
  Node getEmptySet(TypeNode tn);
  /** Get the universe set of type tn if it exists or create a new one */
  Node getUnivSet(TypeNode tn);
  /** debug print set */
  void debugPrintSet(Node s, const char* c) const;

 private:
  /** Send simple lemma internal */
  void sendSimpleLemmaInternal(Node n, InferenceId id);
  /** The inference manager */
  InferenceManager& d_im;
  /** Reference to the skolem cache */
  SkolemCache& d_skCache;
  /** Map from set terms to their proxy variables */
  NodeMap d_proxy;
  /** Backwards map of above */
  NodeMap d_proxy_to_term;
  /** Map from types to empty set of that type */
  std::map<TypeNode, Node> d_emptyset;
  /** Map from types to universe set of that type */
  std::map<TypeNode, Node> d_univset;
  /** Eager proof generator for purification lemmas */
  std::unique_ptr<EagerProofGenerator> d_epg;
}; /* class TheorySetsPrivate */

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SETS__TERM_REGISTRY_H */

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
 * The distinct extension of TheoryUF.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__UF__DISTINCT_EXTENSION_H
#define CVC5__THEORY__UF__DISTINCT_EXTENSION_H

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "proof/eager_proof_generator.h"
#include "smt/env_obj.h"
#include "theory/theory.h"
#include "theory/theory_inference_manager.h"
#include "theory/theory_model.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

class DistinctProofGenerator;

/**
 * Lazy handling of distinct. This subsolver manages distinct constraints by
 * tracking if the equivalence class of two children of positively asserted
 * distinct are merged. It also reduces negatively asserted distincts if
 * necessary based on the constructed model.
 */
class DistinctExtension : protected EnvObj
{
 public:
  DistinctExtension(Env& env, TheoryState& state, TheoryInferenceManager& im);
  /** Check, called after the fact queue of the theory is processed. */
  void check(Theory::Effort level);
  /** Do we need a last call check? */
  bool needsCheckLastEffort();
  /** Assert distinct, may return a conflict */
  void assertDistinct(TNode atom, bool pol, TNode fact);
  /**
   * Called when t1 and t2 merge, may return a conflict if there exists a
   * distinct constraint with children (s1...sn) where si is in the equivalence
   * class of t1 and sj is in the equivalence class of t2. This is recognized
   * based on the comment below.
   */
  void eqNotifyMerge(TNode t1, TNode t2);

 private:
  Node d_false;
  /** Reference to the state object */
  TheoryState& d_state;
  /** Reference to the inference manager */
  TheoryInferenceManager& d_im;
  /** maps nodes to an index in a vector */
  using NodeUIntMap = context::CDHashMap<Node, size_t>;
  // For lazy handling of distinct. We map equivalence classes to a set of
  // distinct constraints that they occur in. For example, if we have an
  // equivalence class {a, b} where a is the representative, and
  // distinct(b,c,d) distinct(e,f,a) are constraints, then for example:
  // d_ndistinct[a] = 2,
  // d_eqcToDistinct[a] = {distinct(b,c,d), distinct(e,f,a)},
  // d_eqcToDMem[a] = {b,a}
  // Similarly if {d} is an equivalence class, then
  // d_ndistinct[d] = 1,
  // d_eqcToDistinct[d] = {distinct(b,c,d)},
  // d_eqcToDMem[d] = {d}
  // If {a,b} and {d} merge, we recognize a conflict since distinct(b,c,d) is
  // in both lists (d_eqcToDistinct[a] and d_eqcToDistinct[d]), where b=d is
  // the explanation for the conflict, accessible via d_eqcToDMem. In particular
  // d_eqcToDMem[a] indicates that b is the child of distinct(b,c,d) that is
  // in the equivalence class of a, and similarly d_eqcToDMem[d] indicates that
  // d is the child of distinct(b,c,d) that is in the equivalence class of d.
  /**
   * The number of entries in d_eqcToDistinct/d_eqcToDMem that are valid in the
   * current SAT context.
   * We track this because d_eqcToDistinct/d_eqcToDMem are *not* stored in a
   * context dependent manner for efficiency, but whose entries are valid only
   * in the current SAT context. For example, in a SAT context we could have
   * allocated 3 entries in d_eqcToDistinct[a] and d_eqcToDMem[a]. When
   * we backtrack, d_ndistinct[a] could be equal to 1, while these two vectors
   * will still have size 3, meaning that only the first element in these lists
   * should be considered.
   */
  NodeUIntMap d_ndistinct;
  /**
   * Mapping from equivalence classes to the list of distincts that they belong
   * to.
   */
  std::map<Node, std::vector<Node>> d_eqcToDistinct;
  /**
   * The corresponding term in the equivalence class, for each entry in
   * d_eqcToDistinct, as described in the comment above.
   */
  std::map<Node, std::vector<Node>> d_eqcToDMem;
  /** The set of asserted negated distinct constraints */
  context::CDList<Node> d_negDistinct;
  /** The number of constraints in the above list we have reduced. */
  context::CDO<size_t> d_negDistinctIndex;
  /** The set of asserted positive distinct constraints */
  context::CDList<Node> d_posDistinct;
  /**
   * A proof generator for distinct constraints, which is used to given proofs
   * for lemmas on demand.
   */
  std::shared_ptr<DistinctProofGenerator> d_dproof;
  /**
   * Eager proof generator, which stores SAT-context dependent proof steps that
   * conclude false based on facts in the equality engine.
   */
  std::shared_ptr<EagerProofGenerator> d_epg;
  /**
   * The pending conflict if one exists. These are of the form described in
   * InferenceId::UF_DISTINCT_DEQ. Pending conflicts are necessary since we
   * may discover a conflict when two equivalence classes merge, but we should
   * wait until the equality engine is finished merging before reporting the
   * conflict.
   */
  context::CDO<Node> d_pendingConflict;
};

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

#endif

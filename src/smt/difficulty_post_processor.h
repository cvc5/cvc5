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
 * Implementation of module for processing the difficulty of input assumptions
 * based on proof nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__DIFFICULTY_POST_PROCESSOR_H
#define CVC5__SMT__DIFFICULTY_POST_PROCESSOR_H

#include <map>

#include "proof/proof_node_updater.h"

namespace cvc5::internal {
namespace smt {

/**
 * A postprocess callback that computes difficulty based on the structure
 * of the proof. In particular, this class assesses what the source of an
 * assertion was by considering the shape of the proof. For instance, if
 * assertion A entails x=t, and this was used to derive a substitution
 * { x -> t } to assertion B, then B is the source of B*{ x -> t }. The
 * difficulty of this assertion is carried to B and not A. The reason is that
 * A can be understood as a definition, and is eliminated, whereas B was
 * persistent if B*{ x -> t } was a prepreprocessed assertion.
 *
 * Note that this postprocess callback is intended to be run on the proof
 * of a single preprocessed assertion C. If C was derived by proof with
 * free assumptions A_1, ..., A_n, then for each A_i that is a "source" as
 * described above, we increment the difficulty of A_i by the difficulty value
 * assigned to C.
 *
 * This means that the user of this method should:
 * (1) assign the current difficulty we are incrementing (setCurrentDifficulty),
 * (2) process the proof using a proof node updater with this callback.
 * The final difficulty map is accumulated in d_accMap, which can be accessed
 * at any time via getDifficultyMap.
 */
class DifficultyPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  DifficultyPostprocessCallback();
  ~DifficultyPostprocessCallback() {}
  /**
   * Set current difficulty of the next proof to process to the (integer)
   * value stored in Node d. This value will be assigned to all the free
   * assumptions of the proof we traverse next. This value is stored in
   * d_currDifficulty.
   *
   * @return true if the difficulty value was successfully extracted
   */
  bool setCurrentDifficulty(Node d);
  /**
   * Should proof pn be updated? This is used to selectively traverse to e.g.
   * the source of an assertion.
   */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /** Get the (acculumated) difficulty map for the last processed proof node */
  void getDifficultyMap(std::map<Node, Node>& dmap) const;

 private:
  /**
   * The current difficulty of the assertion whose proof of preprocessing
   * we are considering.
   */
  uint64_t d_currDifficulty;
  /** The current accumulated difficulty map */
  std::map<Node, uint64_t> d_accMap;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing difficulty
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__DIFFICULTY_POST_PROCESSOR_H
#define CVC5__SMT__DIFFICULTY_POST_PROCESSOR_H

#include <map>
#include <sstream>
#include <unordered_set>

#include "proof/proof_node_updater.h"

namespace cvc5 {

class Env;

namespace smt {

/**
 */
class DifficultyPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  DifficultyPostprocessCallback(Env& env);
  ~DifficultyPostprocessCallback() {}
  /** Set current difficulty */
  void setCurrentDifficulty(Node d);
  /** Should proof pn be updated? */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;

 private:
  /** Reference to the env class */
  Env& d_env;
  /**
   * The current difficulty of the assertion whose proof of preprocessing
   * we are considering.
   */
  uint64_t d_currDifficulty;
};

}  // namespace smt
}  // namespace cvc5

#endif

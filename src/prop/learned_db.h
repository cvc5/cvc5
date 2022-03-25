/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Stores learned information
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__LEARNED_DB_H
#define CVC5__PROP__LEARNED_DB_H

#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdo.h"
#include "expr/node.h"

namespace cvc5 {
namespace prop {

/**
 */
class LearnedDb
{
  using NodeSet = context::CDHashSet<Node>;
 public:
  LearnedDb(context::Context * c);
  ~LearnedDb();
  /** Add learned literal */
  void addLearnedLiteral(const Node& lit, bool isInternal);
  /** Get the zero-level assertions */
  std::vector<Node> getLearnedZeroLevelLiterals(bool isInternal = false) const;
 private:
  /** Set of learnable literals that hold at level 0 */
  NodeSet d_levelZeroAssertsLearned;

  /** Set of internal literals that hold at level 0 */
  NodeSet d_levelZeroInternalAssertsLearned;
};

}  // namespace prop
}  // namespace cvc5

#endif

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
 * Stores learned information
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__LEARNED_DB_H
#define CVC5__PROP__LEARNED_DB_H

#include <cvc5/cvc5_types.h>

#include "context/cdhashset.h"
#include "context/cdo.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace prop {

/**
 * This class stores high-level information learned during a run of the
 * PropEngine. This includes the set of learned literals for each category
 * (modes::LearnedLitType).
 */
class LearnedDb
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  LearnedDb(context::Context* c);
  ~LearnedDb();
  /** Add learned literal of the given type */
  void addLearnedLiteral(const Node& lit, modes::LearnedLitType ltype);
  /** Get the learned literals for the given type */
  std::vector<Node> getLearnedLiterals(
      modes::LearnedLitType ltype = modes::LEARNED_LIT_INPUT) const;
  /** Get number of learned literals for the given type */
  size_t getNumLearnedLiterals(
      modes::LearnedLitType ltype = modes::LEARNED_LIT_INPUT) const;
  /** To string debug */
  std::string toStringDebug() const;

 private:
  /** Get literal set, const and non-const versions */
  context::CDHashSet<Node>& getLiteralSet(modes::LearnedLitType ltype);
  const context::CDHashSet<Node>& getLiteralSet(
      modes::LearnedLitType ltype) const;
  /** To string debug for type of literals */
  std::string toStringDebugType(modes::LearnedLitType ltype) const;
  /** preprocess solved lits */
  NodeSet d_preprocessSolvedLits;
  /** preprocess lits */
  NodeSet d_preprocessLits;
  /** Input lits */
  NodeSet d_inputLits;
  /** Solvable lits */
  NodeSet d_solvableLits;
  /** Constant propagation lits */
  NodeSet d_cpropLits;
  /** Internal lits */
  NodeSet d_internalLits;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif

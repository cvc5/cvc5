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
 * Each category excludes those above it.
 */
enum class LearnedLitType
{
  // a top-level literal during preprocess
  PREPROCESS,
  // a literal from the preprocessed input
  INPUT,
  // a solvable literal
  SOLVABLE,
  // all literals
  INTERNAL
};
/** Converts a learned literal type to a string. */
const char* toString(LearnedLitType ltype);
/** Writes a learned literal type to a stream. */
std::ostream& operator<<(std::ostream& out, LearnedLitType ltype);

/**
 */
class LearnedDb
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  LearnedDb(context::Context* c);
  ~LearnedDb();
  /** Add learned literal */
  void addLearnedLiteral(const Node& lit, LearnedLitType ltype);
  /** Get the zero-level assertions */
  std::vector<Node> getLearnedLiterals(
      LearnedLitType ltype = LearnedLitType::INPUT) const;
  /** Get number of learned literals */
  size_t getNumLearnedLiterals(
      LearnedLitType ltype = LearnedLitType::INPUT) const;

 private:
  /** Get literal set, const and non-const versions */
  context::CDHashSet<Node>& getLiteralSet(LearnedLitType ltype);
  const context::CDHashSet<Node>& getLiteralSet(LearnedLitType ltype) const;
  /** preprocess lits */
  NodeSet d_preprocessLits;
  /** Input lits */
  NodeSet d_inputLits;
  /** Solvable lits */
  NodeSet d_solvableLits;
  /** Internal lits */
  NodeSet d_internalLits;
};

}  // namespace prop
}  // namespace cvc5

#endif

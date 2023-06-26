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

#include "prop/learned_db.h"

#include <sstream>

namespace cvc5::internal {
namespace prop {

LearnedDb::LearnedDb(context::Context* c)
    : d_preprocessSolvedLits(c),
      d_preprocessLits(c),
      d_inputLits(c),
      d_solvableLits(c),
      d_cpropLits(c),
      d_internalLits(c)
{
}

LearnedDb::~LearnedDb() {}

void LearnedDb::addLearnedLiteral(const Node& lit, modes::LearnedLitType ltype)
{
  NodeSet& lset = getLiteralSet(ltype);
  lset.insert(lit);
}

std::vector<Node> LearnedDb::getLearnedLiterals(
    modes::LearnedLitType ltype) const
{
  const NodeSet& lset = getLiteralSet(ltype);
  std::vector<Node> ret;
  for (const Node& n : lset)
  {
    ret.push_back(n);
  }
  return ret;
}
size_t LearnedDb::getNumLearnedLiterals(modes::LearnedLitType ltype) const
{
  const NodeSet& lset = getLiteralSet(ltype);
  return lset.size();
}

context::CDHashSet<Node>& LearnedDb::getLiteralSet(modes::LearnedLitType ltype)
{
  switch (ltype)
  {
    case modes::LEARNED_LIT_PREPROCESS_SOLVED: return d_preprocessSolvedLits;
    case modes::LEARNED_LIT_PREPROCESS: return d_preprocessLits;
    case modes::LEARNED_LIT_INPUT: return d_inputLits;
    case modes::LEARNED_LIT_SOLVABLE: return d_solvableLits;
    case modes::LEARNED_LIT_CONSTANT_PROP: return d_cpropLits;
    default: Assert(ltype == modes::LEARNED_LIT_INTERNAL); break;
  }
  return d_internalLits;
}

const context::CDHashSet<Node>& LearnedDb::getLiteralSet(
    modes::LearnedLitType ltype) const
{
  switch (ltype)
  {
    case modes::LEARNED_LIT_PREPROCESS_SOLVED: return d_preprocessSolvedLits;
    case modes::LEARNED_LIT_PREPROCESS: return d_preprocessLits;
    case modes::LEARNED_LIT_INPUT: return d_inputLits;
    case modes::LEARNED_LIT_SOLVABLE: return d_solvableLits;
    case modes::LEARNED_LIT_CONSTANT_PROP: return d_cpropLits;
    default: Assert(ltype == modes::LEARNED_LIT_INTERNAL); break;
  }
  return d_internalLits;
}

std::string LearnedDb::toStringDebug() const
{
  std::stringstream ss;
  ss << toStringDebugType(modes::LEARNED_LIT_PREPROCESS_SOLVED);
  ss << toStringDebugType(modes::LEARNED_LIT_PREPROCESS);
  ss << toStringDebugType(modes::LEARNED_LIT_INPUT);
  ss << toStringDebugType(modes::LEARNED_LIT_SOLVABLE);
  ss << toStringDebugType(modes::LEARNED_LIT_CONSTANT_PROP);
  ss << toStringDebugType(modes::LEARNED_LIT_INTERNAL);
  return ss.str();
}

std::string LearnedDb::toStringDebugType(modes::LearnedLitType ltype) const
{
  std::stringstream ss;
  const NodeSet& lset = getLiteralSet(ltype);
  if (!lset.empty())
  {
    ss << "#Learned literals (" << ltype << ") = " << lset.size() << std::endl;
  }
  return ss.str();
}

}  // namespace prop
}  // namespace cvc5::internal

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

#include "prop/learned_db.h"

#include <sstream>

namespace cvc5 {
namespace prop {

const char* toString(LearnedLitType ltype)
{
  switch (ltype)
  {
    case LearnedLitType::PREPROCESS_SOLVED: return "PREPROCESS_SOLVED";
    case LearnedLitType::PREPROCESS: return "PREPROCESS";
    case LearnedLitType::INPUT: return "INPUT";
    case LearnedLitType::SOLVABLE: return "SOLVABLE";
    case LearnedLitType::INTERNAL: return "INTERNAL";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, LearnedLitType ltype)
{
  out << toString(ltype);
  return out;
}

LearnedDb::LearnedDb(context::Context* c)
    : d_preprocessSolvedLits(c),
      d_preprocessLits(c),
      d_inputLits(c),
      d_solvableLits(c),
      d_internalLits(c)
{
}

LearnedDb::~LearnedDb() {}

void LearnedDb::addLearnedLiteral(const Node& lit, LearnedLitType ltype)
{
  NodeSet& lset = getLiteralSet(ltype);
  lset.insert(lit);
}

std::vector<Node> LearnedDb::getLearnedLiterals(LearnedLitType ltype) const
{
  const NodeSet& lset = getLiteralSet(ltype);
  std::vector<Node> ret;
  for (const Node& n : lset)
  {
    ret.push_back(n);
  }
  return ret;
}
size_t LearnedDb::getNumLearnedLiterals(LearnedLitType ltype) const
{
  const NodeSet& lset = getLiteralSet(ltype);
  return lset.size();
}

context::CDHashSet<Node>& LearnedDb::getLiteralSet(LearnedLitType ltype)
{
  switch (ltype)
  {
    case LearnedLitType::PREPROCESS_SOLVED: return d_preprocessSolvedLits;
    case LearnedLitType::PREPROCESS: return d_preprocessLits;
    case LearnedLitType::INPUT: return d_inputLits;
    case LearnedLitType::SOLVABLE: return d_solvableLits;
    default: Assert(LearnedLitType::INTERNAL); break;
  }
  return d_internalLits;
}

const context::CDHashSet<Node>& LearnedDb::getLiteralSet(
    LearnedLitType ltype) const
{
  switch (ltype)
  {
    case LearnedLitType::PREPROCESS_SOLVED: return d_preprocessSolvedLits;
    case LearnedLitType::PREPROCESS: return d_preprocessLits;
    case LearnedLitType::INPUT: return d_inputLits;
    case LearnedLitType::SOLVABLE: return d_solvableLits;
    default: Assert(LearnedLitType::INTERNAL); break;
  }
  return d_internalLits;
}

std::string LearnedDb::toStringDebug() const
{
  std::stringstream ss;
  ss << toStringDebugType(LearnedLitType::PREPROCESS_SOLVED);
  ss << toStringDebugType(LearnedLitType::PREPROCESS);
  ss << toStringDebugType(LearnedLitType::INPUT);
  ss << toStringDebugType(LearnedLitType::SOLVABLE);
  ss << toStringDebugType(LearnedLitType::INTERNAL);
  return ss.str();
}

std::string LearnedDb::toStringDebugType(LearnedLitType ltype) const
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
}  // namespace cvc5

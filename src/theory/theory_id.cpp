/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "theory/theory_id.h"

#include <sstream>

#include "base/check.h"
#include "lib/ffs.h"

namespace cvc5::internal {
namespace theory {

TheoryId& operator++(TheoryId& id)
{
  return id = static_cast<TheoryId>(static_cast<int>(id) + 1);
}

std::string toString(TheoryId theoryId)
{
  switch (theoryId)
  {
    case THEORY_BUILTIN: return "THEORY_BUILTIN"; break;
    case THEORY_BOOL: return "THEORY_BOOL"; break;
    case THEORY_UF: return "THEORY_UF"; break;
    case THEORY_ARITH: return "THEORY_ARITH"; break;
    case THEORY_BV: return "THEORY_BV"; break;
    case THEORY_FF: return "THEORY_FF"; break;
    case THEORY_FP: return "THEORY_FP"; break;
    case THEORY_ARRAYS: return "THEORY_ARRAYS"; break;
    case THEORY_DATATYPES: return "THEORY_DATATYPES"; break;
    case THEORY_SAT_SOLVER: return "THEORY_SAT_SOLVER"; break;
    case THEORY_SEP: return "THEORY_SEP"; break;
    case THEORY_SETS: return "THEORY_SETS"; break;
    case THEORY_BAGS: return "THEORY_BAGS"; break;
    case THEORY_STRINGS: return "THEORY_STRINGS"; break;
    case THEORY_QUANTIFIERS: return "THEORY_QUANTIFIERS"; break;
    default: break;
  }
  return "UNKNOWN_THEORY";
}

std::ostream& operator<<(std::ostream& out, TheoryId theoryId)
{
  out << toString(theoryId);
  return out;
}

std::string getStatsPrefix(TheoryId theoryId)
{
  switch (theoryId)
  {
    case THEORY_BUILTIN: return "theory::builtin::"; break;
    case THEORY_BOOL: return "theory::bool::"; break;
    case THEORY_UF: return "theory::uf::"; break;
    case THEORY_ARITH: return "theory::arith::"; break;
    case THEORY_BV: return "theory::bv::"; break;
    case THEORY_FF: return "theory::ff::"; break;
    case THEORY_FP: return "theory::fp::"; break;
    case THEORY_ARRAYS: return "theory::arrays::"; break;
    case THEORY_DATATYPES: return "theory::datatypes::"; break;
    case THEORY_SEP: return "theory::sep::"; break;
    case THEORY_SETS: return "theory::sets::"; break;
    case THEORY_BAGS: return "theory::bags::"; break;
    case THEORY_STRINGS: return "theory::strings::"; break;
    case THEORY_QUANTIFIERS: return "theory::quantifiers::"; break;

    default: break;
  }
  return "unknown::";
}

TheoryId TheoryIdSetUtil::setPop(TheoryIdSet& set)
{
  uint32_t i = ffs(set);  // Find First Set (bit)
  if (i == 0)
  {
    return THEORY_LAST;
  }
  TheoryId id = static_cast<TheoryId>(i - 1);
  set = setRemove(id, set);
  return id;
}

size_t TheoryIdSetUtil::setSize(TheoryIdSet set)
{
  size_t count = 0;
  while (setPop(set) != THEORY_LAST)
  {
    ++count;
  }
  return count;
}

size_t TheoryIdSetUtil::setIndex(TheoryId id, TheoryIdSet set)
{
  Assert(setContains(id, set));
  size_t count = 0;
  while (setPop(set) != id)
  {
    ++count;
  }
  return count;
}

TheoryIdSet TheoryIdSetUtil::setInsert(TheoryId theory, TheoryIdSet set)
{
  return set | (1 << theory);
}

TheoryIdSet TheoryIdSetUtil::setRemove(TheoryId theory, TheoryIdSet set)
{
  return setDifference(set, setInsert(theory));
}

bool TheoryIdSetUtil::setContains(TheoryId theory, TheoryIdSet set)
{
  return set & (1 << theory);
}

TheoryIdSet TheoryIdSetUtil::setComplement(TheoryIdSet a)
{
  return (~a) & AllTheories;
}

TheoryIdSet TheoryIdSetUtil::setIntersection(TheoryIdSet a, TheoryIdSet b)
{
  return a & b;
}

TheoryIdSet TheoryIdSetUtil::setUnion(TheoryIdSet a, TheoryIdSet b)
{
  return a | b;
}

TheoryIdSet TheoryIdSetUtil::setDifference(TheoryIdSet a, TheoryIdSet b)
{
  return (~b) & a;
}

std::string TheoryIdSetUtil::setToString(TheoryIdSet theorySet)
{
  std::stringstream ss;
  ss << "[";
  for (unsigned theoryId = 0; theoryId < THEORY_LAST; ++theoryId)
  {
    TheoryId tid = static_cast<TheoryId>(theoryId);
    if (setContains(tid, theorySet))
    {
      ss << tid << " ";
    }
  }
  ss << "]";
  return ss.str();
}

}  // namespace theory
}  // namespace cvc5::internal

/*********************                                                        */
/*! \file dimacs.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief DIMACS SAT Problem Format
 **
 ** Defines serialization for SAT problems as DIMACS
 **/

#include "proof/dimacs.h"

#include "base/check.h"

#include <iostream>

namespace CVC4 {
namespace proof {

// Prints the literal as a (+) or (-) int
// Not operator<< b/c that represents negation as ~
std::ostream& textOut(std::ostream& o, const prop::SatLiteral& l)
{
  if (l.isNegated())
  {
    o << "-";
  }
  return o << l.getSatVariable() + 1;
}

// Prints the clause as a space-separated list of ints
// Not operator<< b/c that represents negation as ~
std::ostream& textOut(std::ostream& o, const prop::SatClause& c)
{
  for (const auto& l : c)
  {
    textOut(o, l) << " ";
  }
  return o << "0";
}

void printDimacs(std::ostream& o,
                 const std::unordered_map<ClauseId, prop::SatClause>& clauses,
                 const std::vector<ClauseId>& usedIndices)
{
  size_t maxVar = 0;
  for (const ClauseId i : usedIndices)
  {
    const prop::SatClause& c = clauses.at(i);
    for (const auto& l : c)
    {
      if (l.getSatVariable() + 1 > maxVar)
      {
        maxVar = l.getSatVariable() + 1;
      }
    }
  }
  o << "p cnf " << maxVar << " " << usedIndices.size() << '\n';
  for (const ClauseId i : usedIndices)
  {
    const prop::SatClause& c = clauses.at(i);
    for (const auto& l : c)
    {
      if (l.isNegated())
      {
        o << '-';
      }
      o << l.getSatVariable() + 1 << " ";
    }
    o << "0\n";
  }
}

std::vector<prop::SatClause> parseDimacs(std::istream& in)
{
  std::string tag;
  uint64_t nVars;
  uint64_t nClauses;

  in >> tag;
  Assert(in.good());
  Assert(tag == "p");

  in >> tag;
  Assert(in.good());
  Assert(tag == "cnf");

  in >> nVars;
  Assert(nVars >= 0);

  in >> nClauses;
  Assert(nClauses >= 0);

  std::vector<prop::SatClause> cnf;
  for (uint64_t i = 0; i < nClauses; ++i)
  {
    cnf.emplace_back();
    int64_t lit;
    in >> lit;
    Assert(in.good());
    while (lit != 0)
    {
      cnf.back().emplace_back(std::abs(lit) - 1, lit < 0);
      in >> lit;
      Assert(static_cast<uint64_t>(std::abs(lit)) <= nVars);
      Assert(in.good());
    }
  }

  return cnf;
}

}  // namespace proof
}  // namespace CVC4

/*********************                                                        */
/*! \file dimacs_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief DIMACS SAT Problem Format
 **
 ** Defines serialization for SAT problems as DIMACS
 **/

#include "proof/dimacs_printer.h"

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

void printDimacs(
    std::ostream& o,
    const std::vector<std::pair<ClauseId, prop::SatClause>>& usedClauses)
{
  size_t maxVar = 0;
  for (const auto& c : usedClauses)
  {
    for (const auto& l : c.second)
    {
      if (l.getSatVariable() + 1 > maxVar)
      {
        maxVar = l.getSatVariable() + 1;
      }
    }
  }
  o << "p cnf " << maxVar << " " << usedClauses.size() << '\n';
  for (const auto& idAndClause : usedClauses)
  {
    for (const auto& l : idAndClause.second)
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

}  // namespace proof
}  // namespace CVC4

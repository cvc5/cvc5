/*********************                                                        */
/*! \file dimacs_printer.h
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

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__DIMACS_PRINTER_H
#define __CVC4__PROOF__DIMACS_PRINTER_H

#include <iosfwd>
#include <memory>

#include "proof/clause_id.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {
namespace proof {

/**
 * Prints the literal as a (+) or (-) int
 * Not operator<< b/c that represents negation as ~
 *
 * @param o where to print
 * @param l the literal to print
 *
 * @return the original stream
 */
std::ostream& textOut(std::ostream& o, const prop::SatLiteral& l);

/**
 * Prints the clause as a space-separated list of ints
 * Not operator<< b/c that represents literal negation as ~
 *
 * @param o where to print
 * @param c the clause to print
 *
 * @return the original stream
 */
std::ostream& textOut(std::ostream& o, const prop::SatClause& c);

/**
 * Prints a CNF formula in DIMACS format
 *
 * @param o where to print to
 * @param usedClauses the CNF formula
 */
void printDimacs(
    std::ostream& o,
    const std::vector<std::pair<ClauseId, prop::SatClause>>& usedClauses);

}  // namespace proof
}  // namespace CVC4

#endif  // __CVC4__PROOF__DIMACS_PRINTER_H

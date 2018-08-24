/*********************                                                        */
/*! \file lfsc_proof_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Prints proofs in the LFSC format
 **
 ** Prints proofs in the LFSC format.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__LFSC_PROOF_PRINTER_H
#define __CVC4__PROOF__LFSC_PROOF_PRINTER_H

#include <iosfwd>
#include <string>
#include <vector>

#include "proof/clause_id.h"
#include "proof/proof_manager.h"
#include "proof/sat_proof.h"
#include "proof/sat_proof_implementation.h"
#include "util/proof.h"

namespace CVC4 {
namespace proof {

class LFSCProofPrinter
{
 public:
  /**
   * Prints the resolution proof for an assumption conflict.
   *
   * @param satProof The record of the reasoning done by the SAT solver
   * @param id The clause to print a proof for
   * @param out The stream to print to
   * @param paren A stream for the closing parentheses
   */
  template <class Solver>
  static void printAssumptionsResolution(TSatProof<Solver>* satProof,
                                         ClauseId id,
                                         std::ostream& out,
                                         std::ostream& paren);

  /**
   * Prints the resolution proofs for learned clauses that have been used to
   * deduce unsat.
   *
   * @param satProof The record of the reasoning done by the SAT solver
   * @param out The stream to print to
   * @param paren A stream for the closing parentheses
   */
  template <class Solver>
  static void printResolutions(TSatProof<Solver>* satProof,
                               std::ostream& out,
                               std::ostream& paren);

  /**
   * Prints the resolution proof for the empty clause.
   *
   * @param satProof The record of the reasoning done by the SAT solver
   * @param out The stream to print to
   * @param paren A stream for the closing parentheses
   */
  template <class Solver>
  static void printResolutionEmptyClause(TSatProof<Solver>* satProof,
                                         std::ostream& out,
                                         std::ostream& paren);

 private:
  /**
   * Maps a clause id to a string identifier used in the LFSC proof.
   *
   * @param satProof The record of the reasoning done by the SAT solver
   * @param id The clause to map to a string
   */
  template <class Solver>
  static std::string clauseName(TSatProof<Solver>* satProof, ClauseId id);

  /**
   * Prints the resolution proof for a given clause.
   *
   * @param satProof The record of the reasoning done by the SAT solver
   * @param id The clause to print a proof for
   * @param out The stream to print to
   * @param paren A stream for the closing parentheses
   */
  template <class Solver>
  static void printResolution(TSatProof<Solver>* satProof,
                              ClauseId id,
                              std::ostream& out,
                              std::ostream& paren);
};

}  // namespace proof
}  // namespace CVC4

#endif /* __CVC4__PROOF__LFSC_PROOF_PRINTER_H */

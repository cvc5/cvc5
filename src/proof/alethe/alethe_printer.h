/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for printing Alethe proof nodes
 */

#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALETHE_PROOF_PRINTER_H
#define CVC4__PROOF__ALETHE_PROOF_PRINTER_H

#include "proof/proof_node.h"

namespace cvc5 {

namespace proof {

class AletheProofPrinter
{
 public:
  AletheProofPrinter();
  ~AletheProofPrinter() {}
  /**
   * This method prints a proof node that has been transformed into the Alethe
   * proof format
   *
   * @param out The stream to write to
   * @param pfn The proof node to be printed
   */
  void alethePrinter(std::ostream& out, std::shared_ptr<ProofNode> pfn);

 private:
  /** Used for printing the node after the initial anchor has been printed */
  std::string alethePrinterInternal(std::ostream& out,
                                    std::shared_ptr<ProofNode> pfn);
  /** The current level of nesting, which increases if a subproof is entered */
  int nested_level;
  /** Current step id */
  int step_id;
  /** The current prefix which is updated whenever a subproof is encountered
   * E.g. prefix = "t19.t2." */
  std::string prefix;
  /** A list of assumption lists, one for every level of the nested proof node
   */
  std::vector<std::unordered_map<Node, int>> assumptions;
  /** A list of step lists, one for every level of the nested proof node */
  std::vector<std::unordered_map<Node, int>> steps;
};

}  // namespace proof

}  // namespace cvc5

#endif /* CVC4__PROOF__ALETHE_PROOF_PRINTER_H */

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

/**
 * The Alethe printer, which prints proof nodes in a Alethe proof, according to
 * the proof rules defined in alethe_proof_rule.h.
 *
 * It expects to print proof nodes that have processed by the Alethe proof post
 * processor.
 */
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
  void print(std::ostream& out, std::shared_ptr<ProofNode> pfn);

 private:
  /** Used for printing the node after the initial Alethe anchor has been
   * printed
   *
   * The initial anchor introduces the initial assumptions of the problem, which
   * correspond to the problem assertions.
   */
  std::string printInternal(std::ostream& out,
                                    std::shared_ptr<ProofNode> pfn,
				    std::unordered_map<Node,std::string> assumptions,
				    std::unordered_map<Node,std::string> steps,
				    std::string current_prefix,
				    int* current_step_id);
  /** The current level of nesting, which increases if a subproof is entered */
  /** Current step id */
  /** The current prefix which is updated whenever a subproof is encountered
   *
   * E.g. the prefix "t19.t2." is used when we are under a subproof started at
   * step "t19" and another at "t2" without leaving the first subproof. */
  /** A list of assumption lists, one for every level of the nested proof node
   */
  /** A list of step lists, one for every level of the nested proof node */
};

}  // namespace proof

}  // namespace cvc5

#endif /* CVC4__PROOF__ALETHE_PROOF_PRINTER_H */

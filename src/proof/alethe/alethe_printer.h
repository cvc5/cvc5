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
   *
   * @param out The stream to write to
   * @param pfn The proof node to be printed
   * @param assumptions The list of assumptions made before the current step,
   * that are visible as premises to that step
   * @param steps The list of steps occurring before the current step, that are
   * visible as premises to that step
   * @param current_prefix The current prefix which is updated whenever a
   * subproof is encountered E.g., the prefix "t19.t2." is used when we are
   * under a subproof started at step "t19" and another at "t2" without leaving
   * the first subproof.
   * @param current_step_id The id of a step within a subproof (without the
   * prefix).
   * @return The full id (including the prefix) of the last step of pfn.
   */
  std::string printInternal(
      std::ostream& out,
      std::shared_ptr<ProofNode> pfn,
      std::unordered_map<Node, std::string>& assumptions,
      std::unordered_map<std::shared_ptr<ProofNode>, std::string>& steps,
      std::string current_prefix,
      uint32_t& current_step_id);
};

}  // namespace proof

}  // namespace cvc5

#endif /* CVC4__PROOF__ALETHE_PROOF_PRINTER_H */

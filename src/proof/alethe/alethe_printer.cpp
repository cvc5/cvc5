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
 * The module for printing Alethe proof nodes.
 */

#include "proof/alethe/alethe_printer.h"

#include <iostream>
#include <unordered_map>

#include "proof/alethe/alethe_proof_rule.h"

namespace cvc5 {

namespace proof {

void AletheProofPrinter::print(std::ostream& out,
                               std::shared_ptr<ProofNode> pfn)
{
  Trace("alethe-printer") << "- Print proof in Alethe format. " << std::endl;
  std::unordered_map<Node, std::string> assumptions;
  const std::vector<Node>& args = pfn->getArguments();
  // Special handling for the first scope
  // Print assumptions and add them to the list but do not print anchor.
  for (size_t i = 3, size = args.size(); i < size; i++)
  {
    Trace("alethe-printer") << "... print assumption " << args[i] << std::endl;
    out << "(assume a" << i - 3 << " " << args[i] << ")\n";
    assumptions[args[i]] = "a" + std::to_string(i - 3);
  }

  // Then, print the rest of the proof node
  int start_t = 1;
  printInternal(out, pfn->getChildren()[0], assumptions, {}, "", start_t);
}

std::string AletheProofPrinter::printInternal(
    std::ostream& out,
    std::shared_ptr<ProofNode> pfn,
    std::unordered_map<Node, std::string> assumptions,
    std::unordered_map<Node, std::string> steps,
    std::string current_prefix,
    int& current_step_id)
{
  return "";
}

}  // namespace proof

}  // namespace cvc5

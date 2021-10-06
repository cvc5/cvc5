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

AletheProofPrinter::AletheProofPrinter(bool extended) : d_extended(extended)
{
  nested_level = 0;
  step_id = 1;
  prefix = "";
  assumptions.push_back({});
  steps.push_back({});
}

void AletheProofPrinter::alethePrinter(std::ostream& out,
                                       std::shared_ptr<ProofNode> pfn)
{
  Trace("alethe-printer") << "- Print proof in Alethe format. " << std::endl;

  // Special handling for the first scope
  // Print assumptions and add them to the list but do not print anchor.
  for (unsigned long int i = 3, size = pfn->getArguments().size(); i < size;
       i++)
  {
    Trace("alethe-printer")
        << "... print assumption " << pfn->getArguments()[i] << std::endl;
    out << "(assume a" << std::to_string(i - 3) << " " << pfn->getArguments()[i]
        << ")\n";
    assumptions[0][pfn->getArguments()[i]] = i - 3;
  }

  // Then, print the rest of the proof node
  alethePrinterInternal(out, pfn->getChildren()[0]);
}

std::string AletheProofPrinter::alethePrinterInternal(
    std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  return "";
}

}  // namespace proof

}  // namespace cvc5

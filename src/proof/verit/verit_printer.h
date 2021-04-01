/*********************                                                        */
/*! \file verit_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Hanna Lachnitt
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing veriT proof nodes
 **/

#include <memory>

#include "cvc4_private.h"
#include "expr/proof_node_updater.h"
#include "proof/verit/verit_proof_rule.cpp"

#ifndef CVC4__PROOF__VERIT_PROOF_PRINTER_H
#define CVC4__PROOF__VERIT_PROOF_PRINTER_H

#include <iostream>

namespace cvc5 {

namespace proof {

// TEMP ad-hoc code to test conversion
static int veritPrintInternal(std::ostream& out,
                              std::shared_ptr<ProofNode> pfn,
                              int i)
{
  int temp = i;
  std::vector<int> childIds;
  i++;

  std::string last_step;
  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString()))
      == VeritRule::ANCHOR)
  {
    out << "(anchor :step " << last_step << ":args ";
    for (size_t ii = 2; ii < pfn->getArguments().size(); ii++)
    {
      out << " " << pfn->getArguments()[ii];
    }
    out << ")\n";
  }

  for (auto child : pfn->getChildren())
  {
    childIds.push_back(i);
    i = veritPrintInternal(out, child, i);
  }

  last_step = i;

  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString()))
      == VeritRule::ASSUME)
  {
    out << "(assume t" << temp << " " << pfn->getArguments()[1] << ")"
        << std::endl;
    return i;
  }

  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString()))
      == VeritRule::ANCHOR)
  {
    return i;
  }

  if (pfn->getArguments().size() == 2)
  {
    out << "(step t" << temp << " " << pfn->getArguments()[1] << " :rule "
        << veritRuletoString(static_cast<VeritRule>(
               std::stoul(pfn->getArguments()[0].toString())));
    if (childIds.size() >= 1)
    {
      out << " :premises";
      for (auto j : childIds)
      {
        out << " t" << j;
      }
    }
    out << ")\n";
  }
  else if (pfn->getArguments().size() > 2)
  {
    out << "(step t" << temp << " " << pfn->getArguments()[1] << " :rule "
        << veritRuletoString(static_cast<VeritRule>(
               std::stoul(pfn->getArguments()[0].toString())))
        << " :args";
    for (size_t ii = 2; ii < pfn->getArguments().size(); ii++)
    {
      out << " " << pfn->getArguments()[ii];
    }
    if (childIds.size() >= 1)
    {
      out << " :premises";
      for (auto j : childIds)
      {
        out << " t" << j;
      }
    }
    out << ")\n";
  }
  else
  {
    out << "Not translated yet\n";
  }
  return i;
}

static void veritPrinter(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  // should traverse proof node, print each as a proof step, according to the
  // VERIT_RULE id in the veritRule enum

  out << "\n";
  out << "\n";
  out << "Print veriT proof: " << std::endl;
  // Do not print outermost scope
  veritPrintInternal(out, pfn->getChildren()[0], 0);
  // Print outermost scope
  // veritPrintInternal(out,pfn,0);
  out << "\n";
}

}  // namespace proof

}  // namespace cvc5

#endif

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

AletheProofPrinter::AletheProofPrinter() {}

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
  uint32_t start_t = 1;
  printInternal(out, pfn->getChildren()[0], assumptions, {}, "", start_t);
}

std::string AletheProofPrinter::printInternal(
    std::ostream& out,
    std::shared_ptr<ProofNode> pfn,
    const std::unordered_map<Node, std::string>& assumptions,
    const std::unordered_map<Node, std::string>& steps,
    std::string current_prefix,
    uint32_t& current_step_id)
{
  int step_id = current_step_id;
  std::vector<std::string> current_assumptions;
  const std::vector<Node>& args = pfn->getArguments();
  std::unordered_map<Node, std::string> new_assumptions = assumptions;
  std::unordered_map<Node, std::string> new_steps = steps;

  // If the proof node is untranslated a problem might have occured during
  // postprocessing
  if (args.size() < 3 || pfn->getRule() != PfRule::ALETHE_RULE)
  {
    Trace("alethe-printer")
        << "... printing failed! Encountered untranslated Node. "
        << pfn->getResult() << " " << pfn->getRule() << " "
        << " / " << args << std::endl;
    return "";
  }

  // Get the alethe proof rule
  AletheRule arule = getAletheRule(args[0]);

  // In case the rule is an anchor it is printed before its children.
  if (arule == AletheRule::ANCHOR_SUBPROOF || arule == AletheRule::ANCHOR_BIND)
  {
    // Look up if subproof has already been printed
    auto it = steps.find(args[2]);
    if (it != steps.end())
    {
      Trace("alethe-printer")
          << "... subproof is already printed " << pfn->getResult() << " "
          << arule << " / " << args << std::endl;
      return it->second;
    }

    // Otherwise, print anchor
    std::string current_t =
        current_prefix + "t" + std::to_string(current_step_id);
    Trace("alethe-printer")
        << "... print anchor " << pfn->getResult() << " " << arule << " "
        << " / " << args << std::endl;
    out << "(anchor :step " << current_t;

    // Append index of anchor to prefix so that all steps in the subproof use it
    current_prefix.append("t" + std::to_string(current_step_id) + ".");

    // Reset the current step id s.t. the numbering inside the subproof starts
    // with 1
    current_step_id = 1;

    // If the subproof is a bind the arguments need to be printed as
    // assignments, i.e. args=[(= v0 v1)] is printed as (:= (v0 Int) v1).
    if (arule == AletheRule::ANCHOR_BIND)
    {
      out << " :args (";
      for (size_t j = 3, size = args.size(); j < size; j++)
      {
        out << "(:= (" << args[j][0] << " " << args[j][0].getType() << ") "
            << args[j][1] << ")" << (j != args.size() - 1 ? " " : "");
      }
      out << ")";
    }
    // In all other cases there are no arguments
    out << ")\n";

    // If the subproof is a genuine subproof the arguments are printed as
    // assumptions. To be able to discharge the assumptions afterwards we need
    // to store them.
    if (arule == AletheRule::ANCHOR_SUBPROOF)
    {
      for (size_t i = 3, size = args.size(); i < size; i++)
      {
        std::string assumption_name =
            current_prefix + "a" + std::to_string(i - 3);
        Trace("alethe-printer")
            << "... print assumption " << args[i] << std::endl;
        out << "(assume " << assumption_name << " " << args[i] << ")\n";
        new_assumptions[args[i]] = assumption_name;
        current_assumptions.push_back(assumption_name);
      }
    }
  }

  // Assumptions are printed at the anchor and therefore have to be in the list
  // of assumptions when an assume is reached.
  else if (arule == AletheRule::ASSUME)
  {
    Trace("alethe-printer")
        << "... reached assumption " << pfn->getResult() << " " << arule << " "
        << " / " << args << " " << std::endl;

    auto it = assumptions.find(args[2]);
    if (it != assumptions.end())
    {
      Trace("alethe-printer") << "... found assumption in list "
                              << ": " << args[2] << "/" << assumptions
                              << "     " << it->second << std::endl;
      return it->second;
    }

    Trace("alethe-printer") << "... printing failed! Encountered assumption "
                               "that has not been printed! "
                            << args[2] << "/" << assumptions << std::endl;
    return "";
  }

  // Print children
  std::vector<std::string> child_prefixes;

  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  for (const std::shared_ptr<ProofNode>& child : children)
  {
    std::string child_prefix = printInternal(out,
                                             child,
                                             new_assumptions,
                                             new_steps,
                                             current_prefix,
                                             current_step_id);
    new_steps[args[2]] = child_prefix;
    child_prefixes.push_back(child_prefix);
  }

  // If the rule is a subproof a final subproof step needs to be printed
  if (arule == AletheRule::ANCHOR_SUBPROOF || arule == AletheRule::ANCHOR_BIND)
  {
    Trace("alethe-printer") << "... print anchor node " << pfn->getResult()
                            << " " << arule << " / " << args << std::endl;

    current_prefix.pop_back();
    out << "(step " << current_prefix << " " << args[2] << " :rule " << arule;

    new_steps[args[2]] = current_prefix;

    // Reset step id to the number before the subproof + 1
    current_step_id = step_id + 1;

    // Discharge assumptions in the case of subproof
    // The assumptions of this level have been stored in current_assumptions
    if (arule == AletheRule::ANCHOR_SUBPROOF)
    {
      out << " :discharge (";
      for (size_t j = 0, size = current_assumptions.size(); j < size; j++)
      {
        out << current_assumptions[j]
            << (j != current_assumptions.size() - 1 ? " " : "");
      }
      out << ")";
    }
    out << ")\n";
    return current_prefix;
  }

  // If the current step is already printed return its id
  auto it = new_steps.find(args[2]);
  if (it != new_steps.end())
  {
    Trace("alethe-printer")
        << "... step is already printed " << pfn->getResult() << " " << arule
        << " / " << args << std::endl;
    return it->second;
  }

  // Print current step
  Trace("alethe-printer") << "... print node " << pfn->getResult() << " "
                          << arule << " / " << args << std::endl;
  std::string current_t =
      current_prefix + "t" + std::to_string(current_step_id);
  out << "(step " << current_t << " " << args[2] << " :rule " << arule;
  current_step_id++;
  if (args.size() > 3)
  {
    out << " :args (";
    for (size_t i = 3, size = args.size(); i < size; i++)
    {
      if (arule == AletheRule::FORALL_INST)
      {
        out << "(:= " << args[i][0] << " " << args[i][1] << ")";
      }
      else
      {
        out << args[i];
      }
      if (i != args.size() - 1)
      {
        out << " ";
      }
    }
    out << ")";
  }
  if (pfn->getChildren().size() >= 1)
  {
    out << " :premises (";
    for (size_t i = 0, size = child_prefixes.size(); i < size; i++)
    {
      out << child_prefixes[i] << (i != size - 1? " " : "");
    }
    out << "))\n";
  }
  else
  {
    out << ")\n";
  }
  return current_t;
}

}  // namespace proof

}  // namespace cvc5

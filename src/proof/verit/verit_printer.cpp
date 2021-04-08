/*********************                                                        */
/*! \file verit_printer.cpp
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

#include "proof/verit/verit_printer.h"

namespace CVC4 {

namespace proof {

VeritProofPrinter::VeritProofPrinter(bool extended) : d_extended(extended)
{
  assumption_level = 0;
  step_id = 1;
  prefix = "";
  assumptions.resize(1);
  steps.resize(1);
}

void VeritProofPrinter::veritPrinter(std::ostream& out,
                                     std::shared_ptr<ProofNode> pfn)
{
  Trace("verit-printer") << "- Print proof in veriT format. " << std::endl;

  // Special handling for the first scope
  // Print assumptions and add them to the list
  for (unsigned long int i = 0; i < pfn->getArguments().size(); i++)
  {
    Trace("verit-printer") << "... print assumption " << pfn->getArguments()[i]
                           << std::endl;
    out << "(assume a" << std::to_string(i) << " " << pfn->getArguments()[i]
        << ")\n";
    assumptions[0][pfn->getArguments()[i].toString()] = i;
  }

  //Then, print the rest of the proof node
  veritPrinterInternal(out, pfn->getChildren()[0]);
}

std::string VeritProofPrinter::veritPrinterInternal(
    std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  int current_step_id = step_id;

  // If the proof node is untranslated a problem might have occured during postprocessing
  if (pfn->getArguments().size() < 3 || pfn->getRule() != PfRule::VERIT_RULE)
  {
    Trace("verit-printer")
        << "... printing failed! Encountered untranslated Node. "
        << pfn->getResult() << " " << toString(pfn->getRule()) << " "
        << " / " << pfn->getArguments() << std::endl;
    return "";
  }

  // Get the verit proof rule
  VeritRule vrule =
      static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString()));

  // In case the rule is an anchor it is printed before its children. The
  // arguments of the anchor are printed as assumptions
  // TODO: We might want to give ANCHOR_SUBPROOF another argument which is the conclusion.
  // Then, we can search if this step was already printed
  if (vrule == VeritRule::ANCHOR_SUBPROOF)
  {
    // Start a new list of assumptions in the new local scope
    assumption_level++;
    assumptions.resize(assumption_level + 1);
    steps.resize(assumption_level + 1);

    // Print anchor
    Trace("verit-printer") << "... print anchor " << pfn->getResult() << " "
                           << veritRuletoString(vrule) << " "
                           << " / " << pfn->getArguments()
                           << std::endl;
    out << "(anchor :step " << prefix << "t" << step_id << " :args (";
    for (unsigned long int j = 3; j < pfn->getArguments().size(); j++)
    {
      out << pfn->getArguments()[j].toString();
      if (j != pfn->getArguments().size() - 1)
      {
        out << " ";
      }
    }
    out << "))\n";
    prefix.append("t" + std::to_string(step_id) + ".");
    step_id++;

    // Print assumptions
    for (unsigned long int i = 3; i < pfn->getArguments().size(); i++)
    {
      Trace("verit-printer")
          << "... print assumption " << pfn->getArguments()[i] << std::endl;
      out << "(assume " << prefix << "a" << std::to_string(i - 3) << " "
          << pfn->getArguments()[i] << ")\n";
      assumptions[assumption_level][pfn->getArguments()[i].toString()] = i-3;
    }

    // Store step_id until children are printed to resume counter at current
    // position
    current_step_id = step_id;  // TODO: move up?
    step_id = 1;

    /*for (unsigned long int i = 3; i < pfn->getArguments().size(); i++)
    {
      Trace("verit-printer")
          << "... print assumption " << pfn->getArguments()[i] << std::endl;
      out << "(step " << prefix << "t" << std::to_string(step_id) << " "
          << "(cl " << pfn->getArguments()[i] << ") :rule refl)\n";
      steps[assumption_level][pfn->getArguments()[i].toString()] = step_id;
      step_id++;
    }*/

  }

  // Assumptions are printed at the anchor and therefore have to be in the list
  // of assumptions when an assume is reached
  if (vrule == VeritRule::ASSUME)
  {
    Trace("verit-printer") << "... reached assumption " << pfn->getResult()
                           << " " << veritRuletoString(vrule) << " "
                           << " / " << pfn->getArguments() << std::endl;
    /*Trace("verit-printer") << "... search assumption in list "
                           << pfn->getArguments()[2] << "/"
                           << assumptions[assumption_level] << std::endl;*/

    auto it = assumptions[assumption_level].find(pfn->getArguments()[2].toString());

    if(it != assumptions[assumption_level].end()){
      return prefix + "a" + std::to_string(it->second);
    }

    /* TODO: Only in non-extended mode
     * NodeManager* nm = NodeManager::currentNM();

    if(pfn->getResult().getKind() == kind::EQUAL){
      Node symmNode = nm->mkNode(kind::EQUAL,pfn->getArguments()[2][1],pfn->getArguments()[2][0]);
      return prefix + "a" + std::to_string(assumptions[assumption_level].find(symmNode.toString())->second);
    }*/

    //TODO: Error Trace
    return "";
  }

  // First print children
  std::vector<std::string> child_prefixes;
  for (auto child : pfn->getChildren())
  {
    child_prefixes.push_back(veritPrinterInternal(out, child));
  }

  // If rule is SYMM or REORDER the rule should not be printed in non-extended mode
  if (vrule == VeritRule::REORDER || (!d_extended && vrule == VeritRule::SYMM)) //TODO: I changed this temporary
  {
    Trace("verit-printer") << "... non-extended mode skip child "
                           << pfn->getResult() << " "
                           << veritRuletoString(vrule) << " / "
                           << pfn->getArguments() << std::endl;
    return child_prefixes[0];
  }

  //If the rule is a subproof a subproof step needs to be printed
  if (vrule == VeritRule::ANCHOR_SUBPROOF)
  {
    Trace("verit-printer") << "... print node " << pfn->getResult() << " "
                           << veritRuletoString(vrule) << " / "
                           << pfn->getArguments() << std::endl;
    // Remove last .
    prefix.pop_back();
    out << "(step " << prefix << " " << pfn->getArguments()[2] << " :rule "
        << veritRuletoString(vrule) << " :discharge (";
    for (unsigned long int j = 0; j < assumptions[assumption_level].size();
         j++)  // TODO: I am not sure what should be printed here.
    {
      out << prefix << ".a" + std::to_string(j);
      if (j != assumptions[assumption_level].size() - 1)
      {
        out << " ";
      }
    }
    out << "))\n";
    std::string current_t = prefix;
    prefix = prefix.substr(0, prefix.find_last_of("t"));

    step_id = current_step_id;
    assumptions[assumption_level].clear();
    assumption_level--;
    return current_t;
  }

  // If the current step is already printed return its id
  auto it = steps[assumption_level].find(pfn->getArguments()[2].toString());

  if(it != steps[assumption_level].end()){
    Trace("verit-printer") << "... step is already printed " << pfn->getResult() << " "
                           << veritRuletoString(vrule) << " / "
                           << pfn->getArguments() << std::endl;
    return prefix + "t" + std::to_string(it->second);
  }

  // Print current step
  Trace("verit-printer") << "... print node " << pfn->getResult() << " "
                           << veritRuletoString(vrule) << " / "
                           << pfn->getArguments() << std::endl;
  std::string current_t;
  current_t = "t" + std::to_string(step_id);
  steps[assumption_level][pfn->getArguments()[2].toString()] = step_id;
  out << "(step " << prefix << current_t + " ";
  out << pfn->getArguments()[2].toString() + " :rule "
             + veritRuletoString(vrule);
  if (pfn->getArguments().size() > 3)
  {
    out << " :args (";
    for (unsigned long int i = 3; i < pfn->getArguments().size(); i++)
    {
      if(vrule == VeritRule::FORALL_INST){
        out << "(:= " << pfn->getArguments()[i][1].toString() << " " << pfn->getArguments()[i][0].toString() << ")";
      }
      else{
        out << pfn->getArguments()[i].toString();
      }
      if (i != pfn->getArguments().size() - 1)
      {
          out << " ";
      }
    }
    out << ")";
  }
  if (pfn->getChildren().size() >= 1)
  {
    out << " :premises (";
    for (unsigned long int i = 0; i < child_prefixes.size(); i++)
    {
      out << child_prefixes[i];
      if (i != child_prefixes.size() - 1)
      {
        out << " ";
      }
    }
    out << "))\n";
  }
  else
  {
    out << ")\n";
  }
  ++step_id;
  return prefix + current_t;
}



}  // namespace proof

}  // namespace CVC4

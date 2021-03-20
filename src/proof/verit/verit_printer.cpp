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
  assumptions.push_back({});
}

void VeritProofPrinter::veritPrinter(std::ostream& out,
                                     std::shared_ptr<ProofNode> pfn)
{
  Trace("verit-printer") << "- Print proof in veriT format. " << std::endl;

  // Print assumptions and add them to the list
  for (unsigned long int i = 0; i < pfn->getArguments().size(); i++)
  {
    Trace("verit-printer") << "... print assumption " << pfn->getArguments()[i]
                           << std::endl;
    out << "(assume a" << std::to_string(i) << " " << pfn->getArguments()[i]
        << ")\n";
    assumptions[0].push_back(pfn->getArguments()[i]);
  }

  veritPrinterInternal(out, pfn->getChildren()[0]);
}

std::string VeritProofPrinter::veritPrinterInternal(
    std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  int current_step_id = step_id;

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
  if (vrule == VeritRule::ANCHOR_SUBPROOF)
  {
    // Start a new list of assumptions in the new local scope
    assumption_level++;
    assumptions.resize(assumption_level + 1);

    // Print anchor
    Trace("verit-printer") << "... print anchor " << pfn->getResult() << " "
                           << veritRuletoString(vrule) << " "
                           << " / " << pfn->getArguments()
                           << std::endl;  // pfn->getChildren()
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
      assumptions[assumption_level].push_back(pfn->getArguments()[i]);
    }

    // Store step_id until children are printed to resume counter at current
    // position
    current_step_id = step_id;  // TODO: move up?
    step_id = 1;
  }

  // Assumptions are printed at the anchor and therefore have to be in the list
  // of assumptions when an assume is reached The id of an assume is its position
  // in the list.
  if (vrule == VeritRule::ASSUME)
  {
    Trace("verit-printer") << "... reached assumption " << pfn->getResult()
                           << " " << veritRuletoString(vrule) << " "
                           << " / " << pfn->getArguments() << std::endl;
    Trace("verit-printer") << "... search assumption in list "
                           << pfn->getArguments()[2] << "/"
                           << assumptions[assumption_level] << std::endl;
    if(d_extended){
	    return prefix + "a"
           + std::to_string(std::find(assumptions[assumption_level].begin(),
                                      assumptions[assumption_level].end(),
                                      pfn->getArguments()[2])
                            - assumptions[assumption_level].begin());
    }
    else{
       for(unsigned long int i=0; i < assumptions[assumption_level].size(); i++){
	  if(assumptions[assumption_level][i] == pfn->getArguments()[2]){
             return prefix + "a" + std::to_string(i);
	  }
	  else if(pfn->getResult().getKind() == kind::EQUAL){
	    if(assumptions[assumption_level][i][1] == pfn->getArguments()[2][0] && assumptions[assumption_level][i][0] == pfn->getArguments()[2][1]) {
               return prefix + "a" + std::to_string(i);
	    }
	  }
       }
       return "";
    }
  }

  std::vector<std::string> child_prefixes;
  // First print children
  for (auto child : pfn->getChildren())
  {
    child_prefixes.push_back(veritPrinterInternal(out, child));
  }

  // In this cases the rule should not be printed.
  if (!d_extended && (vrule == VeritRule::REORDER || vrule == VeritRule::SYMM))
  {
    Trace("verit-printer") << "... non-extended mode skip child "
                           << pfn->getResult() << " "
                           << veritRuletoString(vrule) << " / "
                           << pfn->getArguments() << std::endl;
    return child_prefixes[0];
  }

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

  // Print current step
  Trace("verit-printer") << "... print node " << pfn->getResult() << " "
                           << veritRuletoString(vrule) << " / "
                           << pfn->getArguments() << std::endl;
  std::string current_t;
  current_t = "t" + std::to_string(step_id);
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

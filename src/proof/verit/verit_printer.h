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
#include <string>

#include "cvc4_private.h"
#include "expr/proof_node_updater.h"
#include "proof/verit/verit_proof_rule.cpp"

#ifndef CVC4__PROOF__VERIT_PROOF_PRINTER_H
#define CVC4__PROOF__VERIT_PROOF_PRINTER_H

#include <iostream>

namespace CVC4 {

namespace proof {


// TEMP ad-hoc code to test conversion
static std::string veritPrintName(std::vector<int> ids,
                                  int i)
{
  std::string name;
  for(int id:ids){
    name.push_back('t');
    name.append(std::to_string(id));
    name.push_back('.');
  }
  name.push_back('t');
  name.append(std::to_string(i));
  return name;
}

// TEMP ad-hoc code to test conversion
static int veritPrintInternal(std::ostream& out,
                              std::shared_ptr<ProofNode> pfn,
			      std::vector<int> &ids,
                              int i=1,
			      bool firstScope=false)
{
  // The id of the current proof node
  int current_id = i;
  // Ids of the childrens of this proof node that are used to print the premises
  std::vector<int> childIds;

  std::vector<std::string> assump;

  //In case the rule is an anchor
  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())) == VeritRule::ANCHOR_SCOPE)
  {
    // The arguments are printed as assumptions before the
    for(int j = 2; j < pfn->getArguments().size(); j++){
      out << "(assume " << veritPrintName(ids,i) << " " << pfn->getArguments()[j] << ")\n";
      i++;
    }
    out << "(anchor :step " << veritPrintName(ids,i) << " :args (";
    for (int j = 2; j < pfn->getArguments().size(); j++)
    {
      out << pfn->getArguments()[j];
      if(j != pfn->getArguments().size()-1){out << " ";}
    }
    out << "))\n";
    ids.push_back(i);
    i = 1;
  }


  //Print Children
  for (int j = 0; j < pfn->getChildren().size(); j++)
  {
    std::shared_ptr<ProofNode> child = pfn->getChildren()[j];
    i = veritPrintInternal(out, child, ids, i);
    childIds.push_back(i-1);
  }

  //In case the rule is an assume
  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())) == VeritRule::ASSUME)
  {
    out << "(input " << veritPrintName(ids,i) << " " << pfn->getArguments()[1] << ")"
        << std::endl;
    assump.push_back(veritPrintName(ids,i));
    return i+1;
  }

  //In case the rule is an anchor
  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())) == VeritRule::ANCHOR_SCOPE)
  {
    auto last = ids.back();
    ids.pop_back();
    out << "(step " << veritPrintName(ids,last) << " " << pfn->getArguments()[1] << " :rule "
	<< veritRuletoString(static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())));
    for(std::string ass: assump){//TODO: Find way to print assumptions
      out << " " << ass;
    }
    out << ")\n";
    return i;
  }

  //Print current step
  if (pfn->getArguments().size() >= 2)
  {
    out << "(step " << veritPrintName(ids,i) << " ";
    if(pfn->getArguments()[1][1] == Node::null()){
      out << "(cl)";
    }
    else{
      out << pfn->getArguments()[1];
    }
    out << " :rule " << veritRuletoString(static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())));
    if (pfn->getArguments().size() > 2){
      out << " :args";
      for (int i = 2; i < pfn->getArguments().size(); i++)
      {
        out << " " << pfn->getArguments()[i];
      }
    }
    if (childIds.size() >= 1)
    {
      out << " :premises";
      for (auto j : childIds)
      {
        out << " " << veritPrintName(ids,j);
      }
    }
    out << ")\n";
  }
  else
  {
    out << "Not translated yet\n";
  }




  return i+1;
}

static void veritPrinter(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  // should traverse proof node, print each as a proof step, according to the
  // VERIT_RULE id in the veritRule enum

  out << "\n";
  out << "\n";
  out << "Print veriT proof: " << std::endl;
  // Do not print outermost scope
  //veritPrintInternal(out, pfn->getChildren()[0], 0);
  // Print outermost scope
  std::vector<int> ids;
  veritPrintInternal(out,pfn,ids,1);
  out << "\n";
  out << "\n";
}

}  // namespace proof

}  // namespace CVC4

#endif

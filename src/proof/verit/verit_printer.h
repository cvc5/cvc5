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

namespace CVC4 {

namespace proof {

// TEMP ad-hoc code to test conversion
static int veritPrintInternal(std::ostream& out,
                              std::shared_ptr<ProofNode> pfn,
                              int i)
{
  int temp = i;
  std::vector<int> childIds;
  i++;

  std::string last_step = "";
  //In case the rule is an assume
  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())) == VeritRule::ASSUME)
  {
    out << "(assume t" << temp << " " << pfn->getArguments()[1] << ")"
        << std::endl;
    return i;
  }


  //In case the rule is an anchor
  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())) == VeritRule::ANCHOR)
  {
    out << "(anchor :step " << last_step << ":args ";
    for (int i = 2; i < pfn->getArguments().size(); i++)
    {
      out << " " << pfn->getArguments()[i];
    }
    out << ")\n";
  }


  //Print Children
  for (auto child : pfn->getChildren())
  {
    if(static_cast<VeritRule>(std::stoul(child->getArguments()[0].toString())) == VeritRule::OR
	&&
      static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())) == VeritRule::RESOLUTION)
    {   bool temp = false;
	if(child->getChildren().size() >= 1){
	if(static_cast<VeritRule>(std::stoul(child->getChildren()[0]->getArguments()[0].toString())) != VeritRule::ASSUME){
	  for(auto child2: pfn->getChildren()){
	    if(child2->getResult() == child->getChildren()[0]->getResult()[1].negate() ){ 
	      temp = true;
              childIds.push_back(i+1);
	      break;
	    }
          }}
	}
       if(!temp){childIds.push_back(i);}

	    std::cout << "test5" << std::endl;
    }
    else{
      childIds.push_back(i);
    }
    i = veritPrintInternal(out, child, i);
  }

  last_step = i;

  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())) == VeritRule::ANCHOR
      || static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())) == VeritRule::ASSUME)
  {
    return i;
  }


  //Print current step
  if (pfn->getArguments().size() >= 2)
  {
    out << "(step t" << temp << " ";
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

}  // namespace CVC4

#endif

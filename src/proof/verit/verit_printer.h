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
                                  int i,
				  bool isAssump)
{
  std::string name;
  for(int id:ids){
    name.push_back('t');
    name.append(std::to_string(id));
    name.push_back('.');
  }
  if(isAssump){name.push_back('h');}
  else{name.push_back('t');}
  name.append(std::to_string(i));
  return name;
}

// TEMP ad-hoc code to test conversion
static std::vector<int> veritPrintInternal(std::ostream& out,
                              std::shared_ptr<ProofNode> pfn,
			      std::vector<int> &ids,
                              int i,
			      int h,
			      bool &firstScope)
{
  // The id of the current proof node
  int current_id = i;
  // Ids of the childrens of this proof node that are used to print the premises
  std::vector<int> childIds;

  //In case the rule is an anchor
  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())) == VeritRule::ANCHOR_SCOPE)
  {
    // The arguments are printed as assumptions before the
    for(int j = 2; j < pfn->getArguments().size(); j++){
      out << "(assume " << veritPrintName(ids,h,true) << " " << pfn->getArguments()[j] << ")\n";
      h++;
    }
    out << "(anchor :step " << veritPrintName(ids,i,false) << " :args (";
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
    std::vector<int> res = veritPrintInternal(out, child, ids, i, h, firstScope);
    i = res[0];
    h = res[1];
    childIds.push_back(i-1);
  }

  //In case the rule is an assume
  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())) == VeritRule::ASSUME)
  {
    out << "(input " << veritPrintName(ids,i,false) << " " << pfn->getArguments()[1] << ")"
        << std::endl;
    return {i+1,h};
  }

  //In case the rule is an anchor
  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())) == VeritRule::ANCHOR_SCOPE)
  {
    auto last = ids.back();
    ids.pop_back();
    out << "(step " << veritPrintName(ids,last,false) << " " << pfn->getArguments()[1] << " :rule "
	<< veritRuletoString(static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())));
    //TODO: Print premises
    out << ")\n";
    i = last+2;
    if(firstScope){
      out << "(step " << veritPrintName(ids,i-1,false) << " (cl false) :rule resolution :premises " << veritPrintName(ids,i-2,false);
      for(int j = 1; j < h; j++){
        out << " " << veritPrintName(ids,j,true);
      }
      out<< ")\n";
      out << "(step " << veritPrintName(ids,i,false) << " (cl (not (false))) :rule false" << ")\n";
      out << "(step " << veritPrintName(ids,i+1,false) << " (cl) :rule resolution :premises " << veritPrintName(ids,i-1,false)
	      << " "<< veritPrintName(ids,i,false)<<")\n";
      firstScope = false;
      return {i+1,h};
    }//TODO: WHAT IF NOT FIRST SCOPE WHAT ABOUT ASSUMPTIONS?
    return {i,h};
  }

  if(!firstScope){return {i,h};}

  //Print current step
  if (pfn->getArguments().size() >= 2)
  {
    out << "(step " << veritPrintName(ids,i,false) << " ";
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
        out << " " << veritPrintName(ids,j,false);
      }
    }
    out << ")\n";
  }
  else
  {
    out << "Not translated yet\n";
  }

  return {i+1,h};
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
  bool firstScope = true;
  veritPrintInternal(out,pfn,ids,1,1,firstScope);
  out << "\n";
  out << "\n";
}

}  // namespace proof

}  // namespace CVC4

#endif

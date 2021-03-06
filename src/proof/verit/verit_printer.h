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
//#include "proof/verit/verit_proof_rule.cpp"
#include "proof/verit/verit_proof_checker.h"

#ifndef CVC4__PROOF__VERIT_PROOF_PRINTER_H
#define CVC4__PROOF__VERIT_PROOF_PRINTER_H

#include <iostream>

namespace CVC4 {

namespace proof {

/**
 * Prints an index for a step or an assume. E.g. if the current id is 1 in a
 * subproof with prefix t3.t4 it returns the string t13.t4.t1. If the current
 * step is an assumption it prints t3.t4.h1
 *
 * @param ids Nested ids of the current subproof,
 * @param i The id of the current step,
 * @param isAssump True, if the current step is an assumption,
 * @return A string consisting of the ids of the subproof followed by the
 * current step printed either as assumption (a) or step (t).
 */
static std::string veritPrintName(std::vector<int> ids, int i, bool isAssump)
{
  std::string name;
  for(int id:ids){
    name.push_back('t');
    name.append(std::to_string(id));
    name.push_back('.');
  }
  if (isAssump)
  {
    name.push_back('a');
  }
  else
  {
    name.push_back('t');
  }
  name.append(std::to_string(i));
  return name;
}

/**
 *
 * @param out,
 * @param pfn,
 * @param ids,
 * @param i,
 * @param h,
 * @return
 */
static std::vector<int> veritPrintInternal(std::ostream& out,
                                           std::shared_ptr<ProofNode> pfn,
                                           std::vector<int>& ids,
                                           int i,
                                           int h)
{
  if (pfn->getRule() == PfRule::SYMM)
  {
    return {i, h};
  }
  else if (pfn->getRule() != PfRule::VERIT_RULE)
  {
    std::cout << "Not translated yet, rule is: " << pfn->getRule() << std::endl;
    return {i, h};
  }
  // std::cout << " verit rule " <<
  // veritRuletoString(static_cast<VeritRule>(
  // std::stoul(pfn->getArguments()[0].toString())));
  // std::cout << " res " << pfn->getResult() << std::endl;
  // The id of the current proof node
  int current_i = i;
  // The id of the latest assumption
  int current_h = h;
  // Ids of the childrens of this proof node that are used to print the premises
  std::vector<int> childIds;


  if (pfn->getArguments().size() >= 3 && pfn->getRule() == PfRule::VERIT_RULE)
  {
  // In case the rule is an anchor add anchor step before children are printed
  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString()))
      == VeritRule::ANCHOR_SUBPROOF)
  {
    out << "(anchor :step " << veritPrintName(ids, i, false) << " :args (";
    for (int j = 3; j < pfn->getArguments().size(); j++)
    {
      out << pfn->getArguments()[j];
      if(j != pfn->getArguments().size()-1){out << " ";}
    }
    out << "))\n";
    ids.push_back(i);
    i = 1;
    h = 1;
  }

  // In case the rule is an assume add assume
  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString()))
      == VeritRule::ASSUME)
  {
    out << "(assume " << veritPrintName(ids, h, true) << " "
        << pfn->getArguments()[2] << ")" << std::endl;
    return {i, h + 1};
  }

  //Print Children
  for (int j = 0; j < pfn->getChildren().size(); j++)
  {
    std::shared_ptr<ProofNode> child = pfn->getChildren()[j];
    std::vector<int> res = veritPrintInternal(out, child, ids, i, h);
    i = res[0];
    h = res[1];
    if (static_cast<VeritRule>(std::stoul(child->getArguments()[0].toString()))
        == VeritRule::ASSUME)
    {
      childIds.push_back(h);
    }
    else
    {
      childIds.push_back(i);
    }
  }

  // In case the rule is an anchor add subproof step after children are printed
  if (static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString()))
      == VeritRule::ANCHOR_SUBPROOF)
  {
    auto last = ids.back();
    ids.pop_back();
    out << "(step " << veritPrintName(ids, last, false) << " "
        << pfn->getArguments()[2] << " :rule "
        << veritRuletoString(static_cast<VeritRule>(
               std::stoul(pfn->getArguments()[0].toString())))
        << " :discharge (";
    ids.push_back(last);
    for (int j = 1; j < current_h; j++)
    {  // TODO: Does this also work with nested anchors?
      out << veritPrintName(ids, j, true);
      if (j != current_h - 1)
      {
        out << " ";
      }
    }
    ids.pop_back();
    // TODO: Print premises
    out << "))\n";
    i = current_i;
    h = current_h;
    return {i + 1, h};
  }


  //Print current step

    out << "(step " << veritPrintName(ids, i, false) << " ";

    if (pfn->getArguments()[2].end() - pfn->getArguments()[2].begin() >= 2)
    {
        out << pfn->getArguments()[2];
    }
    else
    {
      out << pfn->getArguments()[2];
    }

    out << " :rule " << veritRuletoString(static_cast<VeritRule>(std::stoul(pfn->getArguments()[0].toString())));
    if (pfn->getArguments().size() > 3)
    {
      out << " :args";
      for (int i = 3; i < pfn->getArguments().size(); i++)
      {
        out << " " << pfn->getArguments()[i];
      }
    }
    if (childIds.size() >= 1)
    {
      out << " :premises (";
      for (int j = 0; j < childIds.size(); j++)
      {
        if (static_cast<VeritRule>(
                std::stoul(pfn->getChildren()[j]->getArguments()[0].toString()))
            == VeritRule::ASSUME)
        {
          out << veritPrintName(ids, childIds[j] - 1, true);
        }
        else
        {
          out << veritPrintName(ids, childIds[j] - 1, false);
        }
        if (j != childIds.size() - 1)
        {
          out << " ";
        }
      }
      out << ")";
    }
    out << ")\n";
  }
  else
  {
    out << "Not translated yet\n";  // TODO: Give out undefined
  }

  return {i + 1, h};
}

/**
 * This method updates the proof rule application by splitting on the given
 * rule and translating it into a proof node in terms of the veriT rules.
 *
 * @param res The expected result of the application,
 * @param rule The id of the veriT rule,
 * @param children The children of the application,
 * @param args The arguments of the application,
 * @param cdp The proof to add to,
 * @return True if the step could be added, or null if not.
 */
static void veritPrinter(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  //out << "\n";
  //out << "\n";
  std::vector<int> ids;
  veritPrintInternal(out, pfn, ids, 1, 0);
  //out << "\n";
  //out << "Check proof? (0/1)" << "\n";
  bool check;
  std::cin >> check;
  if (check)
  {
    veritProofChecker(pfn, out);
  }
}

}  // namespace proof

}  // namespace CVC4

#endif

/*********************                                                        */
/*! \file dot_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Diego Camargos
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implemantation of the module for printing dot proofs
 **/

#include "proof/dot/dot_printer.h"

#include <sstream>
#include "expr/proof_node_manager.h"

namespace cvc5 {
namespace proof {

void DotPrinter::cleanQuotes(std::string& s)
{
  std::string rep("\\\"");
  for (size_t pos = 0; (pos = s.find("\"", pos)) != std::string::npos;
       pos += rep.length())
  {
    s.replace(pos, rep.length() - 1, rep);
  }
}

void DotPrinter::print(std::ostream& out, const ProofNode* pn)
{
  uint64_t ruleID = 0;

  out << "digraph proof {\n";
  DotPrinter::printInternal(out, pn, ruleID);
  out << "}\n";
}

void DotPrinter::printInternal(std::ostream& out,
                               const ProofNode* pn,
                               uint64_t& ruleID)
{
  uint64_t currentRuleID = ruleID;
  std::ostringstream currentArguments, resultStr;
  DotPrinter::ruleArguments(currentArguments, pn);
  const std::vector<std::shared_ptr<ProofNode>>& children = pn->getChildren();

  out << "\t\"" << currentRuleID << "\" [ shape = \"box\", label = \""
      << pn->getRule();

  // guarantee that arguments do not have unescaped quotes
  std::string astring = currentArguments.str();
  cleanQuotes(astring);

  out << astring << "\"];\n\t\"" << currentRuleID
      << "c\" [ shape = \"ellipse\", label = \"";

  // guarantee that conclusion does not have unescaped quotes
  resultStr << pn->getResult();
  astring = resultStr.str();
  cleanQuotes(astring);

  out << astring << "\" ];\n\t\"" << currentRuleID << "\" -> \""
      << currentRuleID << "c\";\n";

  for (const std::shared_ptr<ProofNode>& c : children)
  {
    ++ruleID;
    out << "\t\"" << ruleID << "c\" -> \"" << currentRuleID << "\";\n";
    printInternal(out, c.get(), ruleID);
  }
}

void DotPrinter::ruleArguments(std::ostringstream& currentArguments,
                               const ProofNode* pn)
{
  const std::vector<Node>& args = pn->getArguments();
  if (!args.size())
  {
    return;
  }
  currentArguments << " :args (" << args[0];
  for (size_t i = 1, size = args.size(); i < size; i++)
  {
    currentArguments << ", " << args[i];
  }
  currentArguments << ")";
}

}  // namespace proof
}  // namespace cvc5

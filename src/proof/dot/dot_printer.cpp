/******************************************************************************
 * Top contributors (to current version):
 *   Diego Della Rocca de Camargos
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implemantation of the module for printing dot proofs.
 */

#include "proof/dot/dot_printer.h"

#include <sstream>

#include "expr/proof_checker.h"
#include "expr/proof_node_manager.h"
#include "printer/smt2/smt2_printer.h"
#include "theory/builtin/proof_checker.h"

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
  PfRule r = pn->getRule();

  out << "\t\"" << currentRuleID << "\" [ shape = \"box\", label = \"" << r;

  std::ostringstream currentArguments, resultStr;
  const std::vector<std::shared_ptr<ProofNode>>& children = pn->getChildren();
  DotPrinter::ruleArguments(currentArguments, pn);
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
  PfRule r = pn->getRule();
  // don't process arguments of rules whose conclusion is in the arguments
  if (!args.size() || r == PfRule::ASSUME || r == PfRule::REORDERING
      || r == PfRule::REFL)
  {
    return;
  }
  currentArguments << " :args [ ";

  // if cong, special process
  if (r == PfRule::CONG)
  {
    AlwaysAssert(args.size() == 1 || args.size() == 2);
    // if two arguments, ignore first and print second
    if (args.size() == 2)
    {
      currentArguments << args[1];
    }
    else
    {
      Kind k;
      ProofRuleChecker::getKind(args[0], k);
      currentArguments << printer::smt2::Smt2Printer::smtKindString(k);
    }
  }
  // if th_rw, likewise
  else if (r == PfRule::THEORY_REWRITE)
  {
    // print the second argument
    theory::TheoryId id;
    theory::builtin::BuiltinProofRuleChecker::getTheoryId(args[1], id);
    std::ostringstream ss;
    ss << id;
    std::string s = ss.str();
    // delete "THEORY_" prefix
    s.erase(0, 7);
    currentArguments << s;
  }
  else
  {
    currentArguments << args[0];
    for (size_t i = 1, size = args.size(); i < size; i++)
    {
      currentArguments << ", " << args[i];
    }
  }
  currentArguments << " ]";
}

}  // namespace proof
}  // namespace cvc5

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

#include "options/expr_options.h"
#include "printer/smt2/smt2_printer.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_manager.h"
#include "theory/builtin/proof_checker.h"

namespace cvc5 {
namespace proof {

DotPrinter::DotPrinter()
    : d_lbind(options::defaultDagThresh() ? options::defaultDagThresh() + 1 : 0)
{
}

DotPrinter::~DotPrinter() {}

std::string DotPrinter::sanitizeStringDoubleQuotes(const std::string& s)
{
  std::string newS;
  newS.reserve(s.size());
  for (const char c : s)
  {
    switch (c)
    {
      case '\"': newS += "\\\\\\\""; break;
      case '>': newS += "\\>"; break;
      case '<': newS += "\\<"; break;
      case '{': newS += "\\{"; break;
      case '}': newS += "\\}"; break;
      case '|': newS += "\\|"; break;
      default: newS += c; break;
    }
  }

  return newS;
}

std::string DotPrinter::sanitizeString(const std::string& s)
{
  std::string newS;
  newS.reserve(s.size());
  for (const char c : s)
  {
    switch (c)
    {
      case '\"': newS += "\\\""; break;
      case '>': newS += "\\>"; break;
      case '<': newS += "\\<"; break;
      case '{': newS += "\\{"; break;
      case '}': newS += "\\}"; break;
      case '|': newS += "\\|"; break;
      default: newS += c; break;
    }
  }

  return newS;
}

void DotPrinter::countSubproofs(const ProofNode* pn)
{
  std::vector<const ProofNode*> visit;
  std::unordered_map<const ProofNode*, bool> visited;
  std::unordered_map<const ProofNode*, bool>::iterator it;
  const ProofNode* cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = false;
      visit.push_back(cur);
      const std::vector<std::shared_ptr<ProofNode>>& children =
          cur->getChildren();
      for (const std::shared_ptr<ProofNode>& c : children)
      {
        visit.push_back(c.get());
      }
    }
    else if (!it->second)
    {
      visited[cur] = true;
      size_t counter = 1;
      const std::vector<std::shared_ptr<ProofNode>>& children =
          cur->getChildren();
      for (const std::shared_ptr<ProofNode>& c : children)
      {
        counter += d_subpfCounter[c.get()];
      }
      d_subpfCounter[cur] = counter;
    }
  } while (!visit.empty());
}

void DotPrinter::letifyResults(const ProofNode* pn)
{
  std::vector<const ProofNode*> visit;
  std::unordered_set<const ProofNode*> visited;
  std::unordered_set<const ProofNode*>::iterator it;
  const ProofNode* cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      d_lbind.process(cur->getResult());
      visited.insert(cur);
      const std::vector<std::shared_ptr<ProofNode>>& children =
          cur->getChildren();
      for (const std::shared_ptr<ProofNode>& c : children)
      {
        visit.push_back(c.get());
      }
    }
  } while (!visit.empty());
}

void DotPrinter::print(std::ostream& out, const ProofNode* pn)
{
  uint64_t ruleID = 0;
  countSubproofs(pn);
  letifyResults(pn);

  // The dot attribute rankdir="BT" sets the direction of the graph layout,
  // placing the root node at the top. The "node [shape..." attribute sets the
  // shape of all nodes to record.
  out << "digraph proof {\n\trankdir=\"BT\";\n\tnode [shape=record];\n";
  // print let map
  std::vector<Node> letList;
  d_lbind.letify(letList);
  if (!letList.empty())
  {
    out << "\tcomment=\"{\\\"letMap\\\" : {";
    bool first = true;
    for (TNode n : letList)
    {
      size_t id = d_lbind.getId(n);
      Assert(id != 0);
      if (!first)
      {
        out << ", ";
      }
      else
      {
        first = false;
      }
      out << "\\\"let" << id << "\\\" : \\\"";
      std::ostringstream nStr;
      nStr << d_lbind.convert(n, "let", false);
      std::string astring = nStr.str();
      // we double the scaping of quotes because "simple scape" is ambiguous
      // with the scape of the delimiter of the value in the key-value map
      out << sanitizeStringDoubleQuotes(astring) << "\\\"";
    }
    out << "}}\";\n";
  }
  DotPrinter::printInternal(out, pn, ruleID, 0, false);
  out << "}\n";
}

void DotPrinter::printInternal(std::ostream& out,
                               const ProofNode* pn,
                               uint64_t& ruleID,
                               uint64_t scopeCounter,
                               bool inPropositionalView)
{
  uint64_t currentRuleID = ruleID;
  const std::vector<std::shared_ptr<ProofNode>>& children = pn->getChildren();
  std::ostringstream currentArguments, resultStr, classes, colors;

  out << "\t" << currentRuleID << " [ label = \"{";

  resultStr << d_lbind.convert(pn->getResult(), "let");
  std::string astring = resultStr.str();
  out << sanitizeString(astring);

  PfRule r = pn->getRule();
  DotPrinter::ruleArguments(currentArguments, pn);
  astring = currentArguments.str();
  out << "|" << r << sanitizeString(astring) << "}\"";
  classes << ", class = \"";
  colors << "";

  // set classes and colors, based on the view that the rule belongs
  switch (r)
  {
    case PfRule::SCOPE:
      if (scopeCounter < 1)
      {
        classes << " basic";
        colors << ", color = blue ";
        inPropositionalView = true;
      }
      scopeCounter++;
      break;
    case PfRule::ASSUME:
      // a node can belong to more than one view, so these if's must not be
      // exclusive
      if (scopeCounter < 2)
      {
        classes << " basic";
        colors << ", color = blue ";
      }
      if (inPropositionalView)
      {
        classes << " propositional";
        colors << ", fillcolor = aquamarine4, style = filled ";
      }
      break;
    case PfRule::CHAIN_RESOLUTION:
    case PfRule::FACTORING:
    case PfRule::REORDERING:
      if (inPropositionalView)
      {
        classes << " propositional";
        colors << ", fillcolor = aquamarine4, style = filled ";
      }
      break;
    default: inPropositionalView = false;
  }
  classes << " \"";
  out << classes.str() << colors.str();
  // add number of subchildren
  std::map<const ProofNode*, size_t>::const_iterator it =
      d_subpfCounter.find(pn);
  out << ", comment = \"{\\\"subProofQty\\\":" << it->second << "}\"";
  out << " ];\n";

  for (const std::shared_ptr<ProofNode>& c : children)
  {
    ++ruleID;
    out << "\t" << ruleID << " -> " << currentRuleID << ";\n";
    printInternal(out, c.get(), ruleID, scopeCounter, inPropositionalView);
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
      currentArguments << d_lbind.convert(args[1], "let");
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
    currentArguments << d_lbind.convert(args[0], "let");
    for (size_t i = 1, size = args.size(); i < size; i++)
    {
      currentArguments << ", " << d_lbind.convert(args[i], "let");
    }
  }
  currentArguments << " ]";
}

}  // namespace proof
}  // namespace cvc5

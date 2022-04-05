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

#include <algorithm>
#include <sstream>

#include "options/expr_options.h"
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "printer/smt2/smt2_printer.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_manager.h"
#include "theory/builtin/proof_checker.h"

namespace cvc5::internal {
namespace proof {

DotPrinter::DotPrinter()
    : d_lbind(options::defaultDagThresh() ? options::defaultDagThresh() + 1
                                          : 0),
      d_ruleID(0)
{
  const std::string acronyms[5] = {"SAT", "CNF", "TL", "PP", "IN"};
  const std::string colors[5] = {"purple", "yellow", "green", "brown", "blue"};
  d_subgraphsStr = new std::ostringstream[5];

  for (int i = 0; i < 5; i++)
  {
    d_subgraphsStr[i] << "\n\tsubgraph cluster_" << acronyms[i]
                      << " {\n\t\tlabel=\"" << acronyms[i]
                      << "\"\n\t\tbgcolor=\"" << colors[i] << "\"\n\t\t";
  }
}

DotPrinter::~DotPrinter() { delete[] d_subgraphsStr; }

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

  std::map<size_t, uint64_t> proofLet;
  DotPrinter::printInternal(
      out, pn, proofLet, NodeClusterType::NOT_DEFINED, 0, false);

  if (options::printDotClusters())
  {
    // Print the sub-graphs
    for (int i = 0; i < 5; i++)
    {
      out << d_subgraphsStr[i].str() << "\n\t};";
    }
  }
  out << "\n}\n";
}

uint64_t DotPrinter::printInternal(std::ostream& out,
                                   const ProofNode* pn,
                                   std::map<size_t, uint64_t>& pfLet,
                                   NodeClusterType parentType,
                                   uint64_t scopeCounter,
                                   bool inPropositionalView)
{
  uint64_t currentRuleID = d_ruleID;

  // Print DAG option enabled
  if (options::proofDotDAG())
  {
    ProofNodeHashFunction hasher;
    size_t currentHash = hasher(pn);
    auto proofIt = pfLet.find(currentHash);

    // If this node has been already counted
    if (proofIt != pfLet.end())
    {
      return proofIt->second;
    }

    pfLet[currentHash] = currentRuleID;
  }

  NodeClusterType nodeType = NodeClusterType::NOT_DEFINED;
  if (options::printDotClusters())
  {
    // Define the type of this node
    nodeType = defineNodeType(pn, parentType);
    if ((int)nodeType)
    {
      d_subgraphsStr[(int)nodeType - 1] << d_ruleID << " ";
    }
  }

  d_ruleID++;

  printNodeInfo(out, pn, currentRuleID, scopeCounter, inPropositionalView);

  PfRule r = pn->getRule();

  const std::vector<std::shared_ptr<ProofNode>>& children = pn->getChildren();
  for (const std::shared_ptr<ProofNode>& c : children)
  {
    uint64_t childId = printInternal(
        out, c.get(), pfLet, nodeType, scopeCounter, inPropositionalView);
    out << "\t" << childId << " -> " << currentRuleID << ";\n";
  }

  // If it's a scope, then remove from the stack
  if (isSCOPE(r) && options::printDotClusters())
  {
    d_scopesArgs.pop_back();
  }

  return currentRuleID;
}

void DotPrinter::printNodeInfo(std::ostream& out,
                               const ProofNode* pn,
                               uint64_t currentRuleID,
                               uint64_t& scopeCounter,
                               bool& inPropositionalView)
{
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
  out << ", comment = \"{\\\"subProofQty\\\":" << it->second << "}\" ];\n";
}

NodeClusterType DotPrinter::defineNodeType(const ProofNode* pn,
                                           NodeClusterType last)
{
  PfRule rule = pn->getRule();
  if (isSCOPE(rule))
  {
    d_scopesArgs.push_back(pn->getArguments());
  }

  // If is the first node
  if (!d_ruleID)
  {
    return NodeClusterType::FIRST_SCOPE;
  }

  // If the rule is in the SAT range and the last node was: FF or SAT
  if (isSat(rule) && last <= NodeClusterType::SAT)
  {
    return NodeClusterType::SAT;
  }
  // If is a ASSUME
  else if (isASSUME(rule))
  {
    if (isInput(pn))
    {
      return NodeClusterType::INPUT;
    }
    else
    {
      return last;
    }
  }
  // the last node was: FS, SAT or CNF
  else if (last <= NodeClusterType::CNF)
  {
    // If the rule is in the CNF range
    if (isCNF(rule))
    {
      return NodeClusterType::CNF;
    }
    // If the first rule after a CNF is a scope
    else if (isSCOPE(rule))
    {
      return NodeClusterType::THEORY_LEMMA;
    }
    // Is not a scope
    else
    {
      return NodeClusterType::PRE_PROCESSING;
    }
  }
  // If the last rule was pre processing
  else if (last == NodeClusterType::PRE_PROCESSING)
  {
    return NodeClusterType::PRE_PROCESSING;
  }
  // If the last rule was theory lemma
  else if (last == NodeClusterType::THEORY_LEMMA)
  {
    return NodeClusterType::THEORY_LEMMA;
  }

  return NodeClusterType::NOT_DEFINED;
}

inline bool DotPrinter::isInput(const ProofNode* pn)
{
  auto& thisAssumeArg = pn->getArguments()[0];
  auto& firstScope = d_scopesArgs[0].get();

  // Verifies if the arg of this assume are in the first scope
  auto it = std::find(firstScope.begin(), firstScope.end(), thisAssumeArg);
  if (it == firstScope.end())
  {
    return false;
  }

  // Verifies if the arg of this assume is at any of the other scopes
  for (int i = d_scopesArgs.size() - 1; i > 0; i--)
  {
    auto& args = d_scopesArgs[i].get();
    it = std::find(args.begin(), args.end(), thisAssumeArg);

    if (it != args.end())
    {
      return false;
    }
  }

  return true;
}

inline bool DotPrinter::isSat(const PfRule& rule)
{
  return PfRule::CHAIN_RESOLUTION <= rule
         && rule <= PfRule::MACRO_RESOLUTION_TRUST;
}

inline bool DotPrinter::isCNF(const PfRule& rule)
{
  return PfRule::NOT_NOT_ELIM <= rule && rule <= PfRule::CNF_ITE_NEG3;
}

inline bool DotPrinter::isSCOPE(const PfRule& rule)
{
  return PfRule::SCOPE == rule;
}

inline bool DotPrinter::isASSUME(const PfRule& rule)
{
  return PfRule::ASSUME == rule;
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
}  // namespace cvc5::internal

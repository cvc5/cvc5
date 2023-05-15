/******************************************************************************
 * Top contributors (to current version):
 *   Vinícius Braga Freire, Haniel Barbosa, Diego Della Rocca de Camargos
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "theory/builtin/proof_checker.h"

namespace cvc5::internal {
namespace proof {

DotPrinter::DotPrinter(Env& env)
    : EnvObj(env),
      d_lbind(options().printer.dagThresh ? options().printer.dagThresh + 1 : 0),
      d_ruleID(0)
{
  const std::string acronyms[5] = {"SAT", "CNF", "TL", "PP", "IN"};
  const std::string colors[5] = {"purple", "yellow", "green", "brown", "blue"};

  for (unsigned i = 0; i < 5; i++)
  {
    d_subgraphsStr.push_back(std::ostringstream());
    d_subgraphsStr[i] << "\n\tsubgraph cluster_" << acronyms[i]
                      << " {\n\t\tlabel=\"" << acronyms[i]
                      << "\"\n\t\tbgcolor=\"" << colors[i] << "\"\n\t\t";
  }
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
  std::map<size_t, uint64_t> firstScopeLet;
  std::unordered_map<const ProofNode*, bool> cfaMap;
  std::vector<size_t> ancestorHashs;

  DotPrinter::printInternal(out,
                            pn,
                            proofLet,
                            firstScopeLet,
                            cfaMap,
                            ancestorHashs,
                            ProofNodeClusterType::NOT_DEFINED);

  if (options().proof.printDotClusters)
  {
    // Print the sub-graphs
    for (unsigned i = 0; i < 5; i++)
    {
      out << d_subgraphsStr[i].str() << "\n\t};";
    }
  }
  out << "\n}\n";
}

uint64_t DotPrinter::printInternal(
    std::ostream& out,
    const ProofNode* pn,
    std::map<size_t, uint64_t>& pfLetClosed,
    std::map<size_t, uint64_t>& pfLetOpen,
    std::unordered_map<const ProofNode*, bool>& cfaMap,
    std::vector<size_t>& ancestorHashs,
    ProofNodeClusterType parentType)
{
  uint64_t currentRuleID = d_ruleID;

  // Print DAG option enabled
  if (options().proof.printDotAsDAG)
  {
    ProofNodeHashFunction hasher;
    size_t currentHash = hasher(pn);

    std::vector<size_t>::iterator oldEnd = ancestorHashs.end();
    // Search if the current hash is in the vector
    std::vector<size_t>::iterator it =
        std::find(ancestorHashs.begin(), ancestorHashs.end(), currentHash);

    // Register the current proof node hash in the ancestor vector
    ancestorHashs.push_back(currentHash);

    // we only consider sharing when this would not introduce a cycle, which
    // would be the case if this hash is occurring under a proof node with the
    // same hash (this can happen since our hash computation only takes into
    // account the immediate descendants of a proof node, the limit of hash
    // representation notwithstanding)
    if (it == oldEnd)
    {
      auto openProofIt = pfLetOpen.find(currentHash);

      if (openProofIt != pfLetOpen.end())
      {
        return openProofIt->second;
      }

      auto proofIt = pfLetClosed.find(currentHash);
      // If this node has been already saved to the global cache of closed proof
      // nodes
      if (proofIt != pfLetClosed.end())
      {
        Assert(!expr::containsAssumption(pn, cfaMap));
        return proofIt->second;
      }
      // If this proof node is closed, we add it to the global cache
      if (!expr::containsAssumption(pn, cfaMap))
      {
        pfLetClosed[currentHash] = currentRuleID;
      }
      pfLetOpen[currentHash] = currentRuleID;
    }
  }

  ProofNodeClusterType proofNodeType = ProofNodeClusterType::NOT_DEFINED;
  if (options().proof.printDotClusters)
  {
    // Define the type of this node
    proofNodeType = defineProofNodeType(pn, parentType);
    if (proofNodeType != ProofNodeClusterType::FIRST_SCOPE
        && proofNodeType != ProofNodeClusterType::NOT_DEFINED)
    {
      d_subgraphsStr[static_cast<int>(proofNodeType) - 1] << d_ruleID << " ";
    }
  }

  printProofNodeInfo(out, pn);

  d_ruleID++;

  PfRule r = pn->getRule();

  // Scopes trigger a traversal with a new local cache for proof nodes
  if (isSCOPE(r) && currentRuleID)
  {
    // create a new pfLet
    std::map<size_t, uint64_t> thisScopeLet;
    uint64_t childId = printInternal(out,
                                     pn->getChildren()[0].get(),
                                     pfLetClosed,
                                     thisScopeLet,
                                     cfaMap,
                                     ancestorHashs,
                                     proofNodeType);
    out << "\t" << childId << " -> " << currentRuleID << ";\n";
    if (options().proof.printDotAsDAG)
    {
      ancestorHashs.pop_back();
    }
  }
  else
  {
    const std::vector<std::shared_ptr<ProofNode>>& children = pn->getChildren();
    for (const std::shared_ptr<ProofNode>& c : children)
    {
      uint64_t childId = printInternal(out,
                                       c.get(),
                                       pfLetClosed,
                                       pfLetOpen,
                                       cfaMap,
                                       ancestorHashs,
                                       proofNodeType);
      out << "\t" << childId << " -> " << currentRuleID << ";\n";
      if (options().proof.printDotAsDAG)
      {
        ancestorHashs.pop_back();
      }
    }
  }

  // If it's a scope, then remove from the stack
  if (isSCOPE(r) && options().proof.printDotClusters)
  {
    d_scopesArgs.pop_back();
  }

  return currentRuleID;
}

void DotPrinter::printProofNodeInfo(std::ostream& out, const ProofNode* pn)
{
  std::ostringstream currentArguments, resultStr, classes, colors;

  out << "\t" << d_ruleID << " [ label = \"{";

  resultStr << d_lbind.convert(pn->getResult(), "let");
  std::string astring = resultStr.str();
  out << sanitizeString(astring);

  PfRule r = pn->getRule();
  DotPrinter::ruleArguments(currentArguments, pn);
  astring = currentArguments.str();
  out << "|" << r << sanitizeString(astring) << "}\"";

  // add number of subchildren
  std::map<const ProofNode*, size_t>::const_iterator it =
      d_subpfCounter.find(pn);
  out << ", comment = \"{\\\"subProofQty\\\":" << it->second << "}\" ];\n";
}

ProofNodeClusterType DotPrinter::defineProofNodeType(const ProofNode* pn,
                                                     ProofNodeClusterType last)
{
  PfRule rule = pn->getRule();
  if (isSCOPE(rule))
  {
    d_scopesArgs.push_back(pn->getArguments());
  }

  // If is the first node
  if (!d_ruleID)
  {
    return ProofNodeClusterType::FIRST_SCOPE;
  }
  // If the rule is in the SAT range and the last node was: FF or SAT
  if (last <= ProofNodeClusterType::SAT && isSat(rule))
  {
    return ProofNodeClusterType::SAT;
  }
  // If is a ASSUME
  if (isASSUME(rule))
  {
    if (isInput(pn))
    {
      return ProofNodeClusterType::INPUT;
    }
    return last;
  }
  // the last node was: FS, SAT or CNF
  if (last <= ProofNodeClusterType::CNF)
  {
    // If the rule is in the CNF range
    if (isCNF(rule))
    {
      return ProofNodeClusterType::CNF;
    }
    // If the first rule after a CNF is in the TL range
    if (isTheoryLemma(rule))
    {
      return ProofNodeClusterType::THEORY_LEMMA;
    }
    // Is not a scope
    return ProofNodeClusterType::PRE_PROCESSING;
  }
  // If the last rule was pre processing
  if (last == ProofNodeClusterType::PRE_PROCESSING)
  {
    return ProofNodeClusterType::PRE_PROCESSING;
  }
  // If the last rule was theory lemma
  if (last == ProofNodeClusterType::THEORY_LEMMA)
  {
    return ProofNodeClusterType::THEORY_LEMMA;
  }

  return ProofNodeClusterType::NOT_DEFINED;
}

inline bool DotPrinter::isInput(const ProofNode* pn)
{
  const TNode& thisAssumeArg = pn->getArguments()[0];
  auto& firstScope = d_scopesArgs[0].get();

  // Verifies if the arg of this assume are in the first scope
  if (std::find(firstScope.begin(), firstScope.end(), thisAssumeArg)
      == firstScope.end())
  {
    return false;
  }

  // Verifies if the arg of this assume is at any of the other scopes
  for (size_t i = d_scopesArgs.size() - 1; i > 0; i--)
  {
    auto& args = d_scopesArgs[i].get();

    if (std::find(args.begin(), args.end(), thisAssumeArg) != args.end())
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

inline bool DotPrinter::isTheoryLemma(const PfRule& rule)
{
  return rule == PfRule::SCOPE || rule == PfRule::THEORY_LEMMA
         || (PfRule::CNF_ITE_NEG3 < rule && rule < PfRule::LFSC_RULE);
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

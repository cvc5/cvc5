/*********************                                                        */
/*! \file lfsc_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lfsc proof nodes
 **/

#include "proof/lfsc/lfsc_printer.h"

#include "expr/node_algorithm.h"

namespace CVC4 {
namespace proof {

void LfscPrinter::print(std::ostream& out,
                        const std::vector<Node>& assertions,
                        const ProofNode* pn)
{
  // closing parentheses
  std::stringstream cparen;

  // [1] compute and print the declarations
  std::unordered_set<Node, NodeHashFunction> syms;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<Node> iasserts;
  for (const Node& a : assertions)
  {
    expr::getSymbols(a, syms, visited);
    iasserts.push_back(LfscTermProcess::toInternal(a));
  }
  // [1a] user declared sorts
  std::unordered_set<TypeNode, TypeNodeHashFunction> sts;
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    if (st.isSort() && sts.find(st) == sts.end())
    {
      sts.insert(st);
      out << "(declare " << st << " sort)" << std::endl;
    }
  }
  // [1b] user declare function symbols
  for (const Node& s : syms)
  {
    out << "(declare " << s << " ";
    print(out, s.getType());
    out << ")";
  }

  // TODO: compute the term lets
  uint32_t counter = 0;
  std::map<Node, uint32_t> letMap;

  // the assumption identifier mapping
  std::map<Node, uint32_t> passumeMap;

  // [2] print the assertions, with letification
  out << "(check" << std::endl;
  cparen << ")";
  for (size_t i = 0, nasserts = iasserts.size(); i < nasserts; i++)
  {
    Node ia = iasserts[i];
    out << "(% ";
    printAssumeId(out, i);
    out << " ";
    printInternal(out, ia, letMap);
    out << std::endl;
    cparen << ")";
    // mark as an assumption
    passumeMap[ia] = i;
  }

  // [3] print the annotation
  out << "(: (holds false)" << std::endl;
  cparen << ")";

  // [4] print the proof body
  printProofLetify(out, pn, letMap, passumeMap);

  out << cparen.str();
}

void LfscPrinter::print(std::ostream& out, const ProofNode* pn)
{
  // TODO: compute term lets
  std::map<Node, uint32_t> letMap;
  // empty passume map
  std::map<Node, uint32_t> passumeMap;
  printProofLetify(out, pn, letMap, passumeMap);
}

void LfscPrinter::printProofLetify(std::ostream& out,
                                   const ProofNode* pn,
                                   std::map<Node, uint32_t>& letMap,
                                   std::map<Node, uint32_t>& passumeMap)
{
  // closing parentheses
  std::stringstream cparen;

  // [1] compute and print the proof lets
  uint32_t pcounter = 0;
  std::vector<const ProofNode*> pletList;
  std::map<const ProofNode*, uint32_t> pletMap;
  computeProofLet(pn, pletList, pletMap, pcounter);
  // define the let proofs
  out << "; Let-ified proofs:" << std::endl;
  std::map<const ProofNode*, uint32_t>::iterator itp;
  for (const ProofNode* p : pletList)
  {
    itp = pletMap.find(p);
    Assert(itp != pletMap.end());
    out << "(plet _ _ ";
    printProofInternal(out, p, letMap, pletMap, passumeMap);
    out << " (\\ ";
    printProofId(out, itp->second);
    out << std::endl;
    cparen << "))";
  }
  out << std::endl;

  // [2] print the proof body
  printProofInternal(out, pn, letMap, pletMap, passumeMap);

  out << cparen.str();
}

void LfscPrinter::printProofInternal(
    std::ostream& out,
    const ProofNode* pn,
    std::map<Node, uint32_t>& letMap,
    std::map<const ProofNode*, uint32_t>& pletMap,
    std::map<Node, uint32_t>& passumeMap)
{
  // the stack
  std::vector<PExpr> visit;
  // whether we have process children
  std::map<const ProofNode*, bool> processedChildren;
  // helper iterators
  std::map<const ProofNode*, bool>::iterator pit;
  std::map<const ProofNode*, uint32_t>::iterator pletIt;
  std::map<Node, uint32_t>::iterator passumeIt;
  Node curn;
  const ProofNode* cur;
  visit.push_back(PExpr(pn));
  do
  {
    curn = visit.back().d_node;
    cur = visit.back().d_pnode;
    visit.pop_back();
    // proofs
    if (cur != nullptr)
    {
      pit = processedChildren.find(cur);
      if (pit == processedChildren.end())
      {
        // maybe it is letified
        pletIt = pletMap.find(cur);
        if (pletIt != pletMap.end())
        {
          // a letified proof
          printProofId(out, pletIt->second);
        }
        else if (cur->getRule() == PfRule::ASSUME)
        {
          // an assumption, must have a name
          passumeIt = passumeMap.find(cur->getResult());
          Assert(passumeIt != passumeMap.end());
          printAssumeId(out, passumeIt->second);
        }
        else
        {
          // a normal rule application, compute the proof arguments
          processedChildren[cur] = false;
          computeProofArgs(cur, visit);
          // print the rule name
          out << "(";
          printRule(out, cur);
        }
      }
      else if (!pit->second)
      {
        processedChildren[cur] = true;
        out << ")" << std::endl;
      }
    }
    else if (!curn.isNull())
    {
      printInternal(out, curn, letMap);
    }
    else
    {
      // a hole
      out << "_ ";
    }
  } while (!visit.empty());
}

void LfscPrinter::computeProofArgs(const ProofNode* pn,
                                   std::vector<PExpr>& pargs)
{
  // TODO
}

void LfscPrinter::print(std::ostream& out, Node n)
{
  Node ni = LfscTermProcess::toInternal(n);
  printLetify(out, ni);
}

void LfscPrinter::printLetify(std::ostream& out, Node n)
{
  // closing parentheses
  std::stringstream cparen;

  std::vector<Node> letList;
  std::map<Node, uint32_t> letMap;
  uint32_t counter = 0;
  computeLet(n, letList, letMap, counter);

  // [1] print the letification
  std::map<Node, uint32_t>::iterator it;
  for (size_t i = 0, nlets = letList.size(); i < nlets; i++)
  {
    Node nl = letList[i];
    it = letMap.find(nl);
    Assert(it != letMap.end());
  }

  // [2] print the body
  printInternal(out, n, letMap);

  out << cparen.str();
}

void LfscPrinter::printInternal(std::ostream& out,
                                Node n,
                                const std::map<Node, uint32_t>& letMap)
{
}

void LfscPrinter::print(std::ostream& out, TypeNode n) {}

void LfscPrinter::printInternal(std::ostream& out, TypeNode n) {}

void LfscPrinter::computeLet(Node n,
                             std::vector<Node>& letList,
                             std::map<Node, uint32_t>& letMap,
                             uint32_t& counter)
{
  Assert(letList.empty() && letMap.empty());
  std::vector<Node> visitList;
  std::map<Node, uint32_t> count;
  computeCounts(n, visitList, count);
  // Now populate the letList and letMap
  convertCountToLet(visitList, count, letList, letMap, counter);
}

void LfscPrinter::computeCounts(Node n,
                                std::vector<Node>& visitList,
                                std::map<Node, uint32_t>& count)
{
  std::map<Node, uint32_t>::iterator it;
  std::vector<Node> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    it = count.find(cur);
    if (it == count.end())
    {
      count[cur] = 0;
      visitList.push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else
    {
      count[cur]++;
      visit.pop_back();
    }
  } while (!visit.empty());
}

void LfscPrinter::convertCountToLet(const std::vector<Node>& visitList,
                                    const std::map<Node, uint32_t>& count,
                                    std::vector<Node>& letList,
                                    std::map<Node, uint32_t>& letMap,
                                    uint32_t& counter)
{
  Assert(letList.empty() && letMap.empty());
  // Assign ids for those whose count is > 1, traverse in reverse order
  // so that deeper proofs are assigned lower identifiers
  std::map<Node, uint32_t>::const_iterator itc;
  for (std::vector<Node>::const_reverse_iterator it = visitList.rbegin();
       it != visitList.rend();
       ++it)
  {
    itc = count.find(*it);
    Assert(itc != count.end());
    if (itc->second > 1)
    {
      letList.push_back(*it);
      letMap[*it] = counter;
      counter++;
    }
  }
}

void LfscPrinter::computeProofLet(const ProofNode* pn,
                                  std::vector<const ProofNode*>& pletList,
                                  std::map<const ProofNode*, uint32_t>& pletMap,
                                  uint32_t& pcounter)
{
  Assert(pletList.empty() && pletMap.empty());
  std::vector<const ProofNode*> visitList;
  std::map<const ProofNode*, uint32_t> pcount;
  computeProofCounts(pn, visitList, pcount);
  // Now populate the pletList and pletMap
  convertProofCountToLet(visitList, pcount, pletList, pletMap, pcounter);
}

void LfscPrinter::computeProofCounts(
    const ProofNode* pn,
    std::vector<const ProofNode*>& visitList,
    std::map<const ProofNode*, uint32_t>& pcount)
{
  std::map<const ProofNode*, uint32_t>::iterator it;
  std::vector<const ProofNode*> visit;
  const ProofNode* cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    it = pcount.find(cur);
    if (it == pcount.end())
    {
      pcount[cur] = 0;
      visitList.push_back(cur);
      const std::vector<std::shared_ptr<ProofNode>>& pc = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : pc)
      {
        visit.push_back(cp.get());
      }
    }
    else
    {
      pcount[cur]++;
      visit.pop_back();
    }
  } while (!visit.empty());
}

void LfscPrinter::convertProofCountToLet(
    const std::vector<const ProofNode*>& visitList,
    const std::map<const ProofNode*, uint32_t>& pcount,
    std::vector<const ProofNode*>& pletList,
    std::map<const ProofNode*, uint32_t>& pletMap,
    uint32_t& pcounter)
{
  Assert(pletList.empty() && pletMap.empty());
  // Assign ids for those whose count is > 1, traverse in reverse order
  // so that deeper proofs are assigned lower identifiers
  std::map<const ProofNode*, uint32_t>::const_iterator itc;
  for (std::vector<const ProofNode*>::const_reverse_iterator itp =
           visitList.rbegin();
       itp != visitList.rend();
       ++itp)
  {
    itc = pcount.find(*itp);
    Assert(itc != pcount.end());
    if (itc->second > 1)
    {
      pletList.push_back(*itp);
      pletMap[*itp] = pcounter;
      pcounter++;
    }
  }
}

void LfscPrinter::printRule(std::ostream& out, const ProofNode* pn)
{
  // TODO: proper conversion
  out << pn->getRule();
}

void LfscPrinter::printId(std::ostream& out, uint32_t id) { out << "@t" << id; }

void LfscPrinter::printProofId(std::ostream& out, uint32_t id)
{
  out << "@p" << id;
}

void LfscPrinter::printAssumeId(std::ostream& out, uint32_t id)
{
  out << "@a" << id;
}

}  // namespace proof
}  // namespace CVC4

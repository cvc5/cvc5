/*********************                                                        */
/*! \file proof_node_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof node manager
 **/

#include "expr/proof_node_manager.h"

#include "expr/proof.h"
#include "expr/proof_node_algorithm.h"

using namespace CVC4::kind;

namespace CVC4 {

ProofNodeManager::ProofNodeManager(ProofChecker* pc) : d_checker(pc) {}

std::shared_ptr<ProofNode> ProofNodeManager::mkNode(
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args,
    Node expected)
{
  Node res = checkInternal(id, children, args, expected);
  if (res.isNull())
  {
    // if it was invalid, then we return the null node
    return nullptr;
  }
  // otherwise construct the proof node and set its proven field
  std::shared_ptr<ProofNode> pn =
      std::make_shared<ProofNode>(id, children, args);
  pn->d_proven = res;
  return pn;
}

std::shared_ptr<ProofNode> ProofNodeManager::mkAssume(Node fact)
{
  Assert(!fact.isNull());
  Assert(fact.getType().isBoolean());
  return mkNode(PfRule::ASSUME, {}, {fact}, fact);
}

std::shared_ptr<ProofNode> ProofNodeManager::mkScope(
    std::shared_ptr<ProofNode> pf,
    std::vector<Node>& assumps,
    bool ensureClosed,
    bool doMinimize,
    Node expected)
{
  if (!ensureClosed)
  {
    return mkNode(PfRule::SCOPE, {pf}, assumps, expected);
  }
  Trace("pnm-scope") << "ProofNodeManager::mkScope " << assumps << std::endl;
  // we first ensure the assumptions are flattened
  std::unordered_set<Node, NodeHashFunction> ac{assumps.begin(), assumps.end()};

  // The free assumptions of the proof
  std::map<Node, std::vector<ProofNode*>> famap;
  expr::getFreeAssumptionsMap(pf.get(), famap);
  std::unordered_set<Node, NodeHashFunction> acu;
  for (const std::pair<const Node, std::vector<ProofNode*>>& fa : famap)
  {
    Node a = fa.first;
    if (ac.find(a) != ac.end())
    {
      // already covered by an assumption
      acu.insert(a);
      continue;
    }
    Trace("pnm-scope") << "- try matching free assumption " << a << "\n";
    // otherwise it may be due to symmetry?
    Node aeqSym = CDProof::getSymmFact(a);
    Trace("pnm-scope") << "  - try sym " << aeqSym << "\n";
    if (!aeqSym.isNull())
    {
      if (ac.count(aeqSym))
      {
        Trace("pnm-scope") << "- reorient assumption " << aeqSym << " via " << a
                           << " for " << fa.second.size() << " proof nodes"
                           << std::endl;
        std::shared_ptr<ProofNode> pfaa = mkAssume(aeqSym);
        for (ProofNode* pfs : fa.second)
        {
          Assert(pfs->getResult() == a);
          // must correct the orientation on this leaf
          std::vector<std::shared_ptr<ProofNode>> children;
          children.push_back(pfaa);
          std::vector<Node> args;
          args.push_back(a);
          updateNode(pfs, PfRule::MACRO_SR_PRED_TRANSFORM, children, args);
        }
        Trace("pnm-scope") << "...finished" << std::endl;
        acu.insert(aeqSym);
        continue;
      }
    }
    // All free assumptions should be arguments to SCOPE.
    std::stringstream ss;
    pf->printDebug(ss);
    ss << std::endl << "Free assumption: " << a << std::endl;
    for (const Node& aprint : ac)
    {
      ss << "- assumption: " << aprint << std::endl;
    }
    Unreachable() << "Generated a proof that is not closed by the scope: "
                  << ss.str() << std::endl;
  }
  if (acu.size() < ac.size())
  {
    // All assumptions should match a free assumption; if one does not, then
    // the explanation could have been smaller.
    for (const Node& a : ac)
    {
      if (acu.find(a) == acu.end())
      {
        Notice() << "ProofNodeManager::mkScope: assumption " << a
                 << " does not match a free assumption in proof" << std::endl;
      }
    }
  }
  if (doMinimize && acu.size() < ac.size())
  {
    assumps.clear();
    assumps.insert(assumps.end(), acu.begin(), acu.end());
  }
  else if (ac.size() < assumps.size())
  {
    // remove duplicates to avoid redundant literals in clauses
    assumps.clear();
    assumps.insert(assumps.end(), ac.begin(), ac.end());
  }
  Node minExpected;
  NodeManager* nm = NodeManager::currentNM();
  Node exp;
  Node conc = pf->getResult();
  if (assumps.empty())
  {
    Assert(!conc.isConst());
    minExpected = conc;
  }
  else
  {
    exp = assumps.size() == 1 ? assumps[0] : nm->mkNode(AND, assumps);
    if (conc.isConst() && !conc.getConst<bool>())
    {
      minExpected = exp.notNode();
    }
    else
    {
      minExpected = nm->mkNode(IMPLIES, exp, conc);
    }
  }
  return mkNode(PfRule::SCOPE, {pf}, assumps, minExpected);
}

bool ProofNodeManager::updateNode(
    ProofNode* pn,
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args)
{
  return updateNodeInternal(pn, id, children, args, true);
}

bool ProofNodeManager::updateNode(ProofNode* pn, ProofNode* pnr)
{
  if (pn->getResult() != pnr->getResult())
  {
    return false;
  }
  // can shortcut re-check of rule
  return updateNodeInternal(
      pn, pnr->getRule(), pnr->getChildren(), pnr->getArguments(), false);
}

Node ProofNodeManager::checkInternal(
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args,
    Node expected)
{
  Node res;
  if (d_checker)
  {
    // check with the checker, which takes expected as argument
    res = d_checker->check(id, children, args, expected);
    Assert(!res.isNull())
        << "ProofNodeManager::checkInternal: failed to check proof";
  }
  else
  {
    // otherwise we trust the expected value, if it exists
    Assert(!expected.isNull()) << "ProofNodeManager::checkInternal: no checker "
                                  "or expected value provided";
    res = expected;
  }
  return res;
}

ProofChecker* ProofNodeManager::getChecker() const { return d_checker; }

bool ProofNodeManager::updateNodeInternal(
    ProofNode* pn,
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args,
    bool needsCheck)
{
  // ---------------- check for cyclic
  std::unordered_map<const ProofNode*, bool> visited;
  std::unordered_map<const ProofNode*, bool>::iterator it;
  std::vector<const ProofNode*> visit;
  for (const std::shared_ptr<ProofNode>& cp : children)
  {
    visit.push_back(cp.get());
  }
  const ProofNode* cur;
  while (!visit.empty())
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = true;
      if (cur == pn)
      {
        std::stringstream ss;
        ss << "ProofNodeManager::updateNode: attempting to make cyclic proof! "
           << id << " " << pn->getResult() << ", children = " << std::endl;
        for (const std::shared_ptr<ProofNode>& cp : children)
        {
          ss << "  " << cp->getRule() << " " << cp->getResult() << std::endl;
        }
        ss << "Full children:" << std::endl;
        for (const std::shared_ptr<ProofNode>& cp : children)
        {
          ss << "  - ";
          cp->printDebug(ss);
          ss << std::endl;
        }
        Unreachable() << ss.str();
      }
      for (const std::shared_ptr<ProofNode>& cp : cur->d_children)
      {
        visit.push_back(cp.get());
      }
    }
  }
  // ---------------- end check for cyclic

  // should have already computed what is proven
  Assert(!pn->d_proven.isNull())
      << "ProofNodeManager::updateProofNode: invalid proof provided";
  if (needsCheck)
  {
    // We expect to prove the same thing as before
    Node res = checkInternal(id, children, args, pn->d_proven);
    if (res.isNull())
    {
      // if it was invalid, then we do not update
      return false;
    }
    // proven field should already be the same as the result
    Assert(res == pn->d_proven);
  }

  // we update its value
  pn->setValue(id, children, args);
  return true;
}

}  // namespace CVC4

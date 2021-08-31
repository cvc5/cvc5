/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof node manager.
 */

#include "proof/proof_node_manager.h"

#include <sstream>

#include "options/proof_options.h"
#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "proof/proof_node_algorithm.h"
#include "theory/rewriter.h"

using namespace cvc5::kind;

namespace cvc5 {

ProofNodeManager::ProofNodeManager(ProofChecker* pc) : d_checker(pc)
{
  d_true = NodeManager::currentNM()->mkConst(true);
}

std::shared_ptr<ProofNode> ProofNodeManager::mkNode(
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args,
    Node expected)
{
  Trace("pnm") << "ProofNodeManager::mkNode " << id << " {" << expected.getId()
               << "} " << expected << "\n";
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

std::shared_ptr<ProofNode> ProofNodeManager::mkTrans(
    const std::vector<std::shared_ptr<ProofNode>>& children, Node expected)
{
  Assert(!children.empty());
  if (children.size() == 1)
  {
    Assert(expected.isNull() || children[0]->getResult() == expected);
    return children[0];
  }
  return mkNode(PfRule::TRANS, children, {}, expected);
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
  std::unordered_set<Node> ac{assumps.begin(), assumps.end()};
  // map from the rewritten form of assumptions to the original. This is only
  // computed in the rare case when we need rewriting to match the
  // assumptions. An example of this is for Boolean constant equalities in
  // scoped proofs from the proof equality engine.
  std::unordered_map<Node, Node> acr;
  // whether we have compute the map above
  bool computedAcr = false;

  // The free assumptions of the proof
  std::map<Node, std::vector<std::shared_ptr<ProofNode>>> famap;
  expr::getFreeAssumptionsMap(pf, famap);
  std::unordered_set<Node> acu;
  for (const std::pair<const Node, std::vector<std::shared_ptr<ProofNode>>>&
           fa : famap)
  {
    Node a = fa.first;
    if (ac.find(a) != ac.end())
    {
      // already covered by an assumption
      acu.insert(a);
      continue;
    }
    // trivial assumption
    if (a == d_true)
    {
      Trace("pnm-scope") << "- justify trivial True assumption\n";
      for (std::shared_ptr<ProofNode> pfs : fa.second)
      {
        Assert(pfs->getResult() == a);
        updateNode(pfs.get(), PfRule::MACRO_SR_PRED_INTRO, {}, {a});
      }
      Trace("pnm-scope") << "...finished" << std::endl;
      acu.insert(a);
      continue;
    }
    Trace("pnm-scope") << "- try matching free assumption " << a << "\n";
    // otherwise it may be due to symmetry?
    Node aeqSym = CDProof::getSymmFact(a);
    Trace("pnm-scope") << "  - try sym " << aeqSym << "\n";
    Node aMatch;
    if (!aeqSym.isNull() && ac.count(aeqSym))
    {
      Trace("pnm-scope") << "- reorient assumption " << aeqSym << " via " << a
                         << " for " << fa.second.size() << " proof nodes"
                         << std::endl;
      aMatch = aeqSym;
    }
    else
    {
      // Otherwise, may be derivable by rewriting. Note this is used in
      // ensuring that proofs from the proof equality engine that involve
      // equality with Boolean constants are closed.
      if (!computedAcr)
      {
        computedAcr = true;
        for (const Node& acc : ac)
        {
          Node accr = theory::Rewriter::rewrite(acc);
          if (accr != acc)
          {
            acr[accr] = acc;
          }
        }
      }
      Node ar = theory::Rewriter::rewrite(a);
      std::unordered_map<Node, Node>::iterator itr = acr.find(ar);
      if (itr != acr.end())
      {
        aMatch = itr->second;
      }
    }

    // if we found a match either by symmetry or rewriting, then we connect
    // the assumption here.
    if (!aMatch.isNull())
    {
      std::shared_ptr<ProofNode> pfaa = mkAssume(aMatch);
      // must correct the orientation on this leaf
      std::vector<std::shared_ptr<ProofNode>> children;
      children.push_back(pfaa);
      for (std::shared_ptr<ProofNode> pfs : fa.second)
      {
        Assert(pfs->getResult() == a);
        // use SYMM if possible
        if (aMatch == aeqSym)
        {
          updateNode(pfs.get(), PfRule::SYMM, children, {});
        }
        else
        {
          updateNode(pfs.get(), PfRule::MACRO_SR_PRED_TRANSFORM, children, {a});
        }
      }
      Trace("pnm-scope") << "...finished" << std::endl;
      acu.insert(aMatch);
      continue;
    }
    // If we did not find a match, it is an error, since all free assumptions
    // should be arguments to SCOPE.
    std::stringstream ss;

    bool dumpProofTraceOn = Trace.isOn("dump-proof-error");
    if (dumpProofTraceOn)
    {
      ss << "The proof : " << *pf << std::endl;
    }
    ss << std::endl << "Free assumption: " << a << std::endl;
    for (const Node& aprint : ac)
    {
      ss << "- assumption: " << aprint << std::endl;
    }
    if (!dumpProofTraceOn)
    {
      ss << "Use -t dump-proof-error for details on proof" << std::endl;
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
  if (assumps.empty())
  {
    // SCOPE with no arguments is a no-op, just return original
    return pf;
  }
  Node conc = pf->getResult();
  exp = assumps.size() == 1 ? assumps[0] : nm->mkNode(AND, assumps);
  if (conc.isConst() && !conc.getConst<bool>())
  {
    minExpected = exp.notNode();
  }
  else
  {
    minExpected = nm->mkNode(IMPLIES, exp, conc);
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
  Assert(pn != nullptr);
  Assert(pnr != nullptr);
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

std::shared_ptr<ProofNode> ProofNodeManager::clone(
    std::shared_ptr<ProofNode> pn)
{
  const ProofNode* orig = pn.get();
  std::unordered_map<const ProofNode*, std::shared_ptr<ProofNode>> visited;
  std::unordered_map<const ProofNode*, std::shared_ptr<ProofNode>>::iterator it;
  std::vector<const ProofNode*> visit;
  std::shared_ptr<ProofNode> cloned;
  visit.push_back(orig);
  const ProofNode* cur;
  while (!visit.empty())
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = nullptr;
      const std::vector<std::shared_ptr<ProofNode>>& children =
          cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : children)
      {
        visit.push_back(cp.get());
      }
      continue;
    }
    visit.pop_back();
    if (it->second.get() == nullptr)
    {
      std::vector<std::shared_ptr<ProofNode>> cchildren;
      const std::vector<std::shared_ptr<ProofNode>>& children =
          cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : children)
      {
        it = visited.find(cp.get());
        Assert(it != visited.end());
        Assert(it->second != nullptr);
        cchildren.push_back(it->second);
      }
      cloned = std::make_shared<ProofNode>(
          cur->getRule(), cchildren, cur->getArguments());
      visited[cur] = cloned;
      // we trust the above cloning does not change what is proven
      cloned->d_proven = cur->d_proven;
    }
  }
  Assert(visited.find(orig) != visited.end());
  return visited[orig];
}

bool ProofNodeManager::updateNodeInternal(
    ProofNode* pn,
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args,
    bool needsCheck)
{
  Assert(pn != nullptr);
  // ---------------- check for cyclic
  if (options::proofEagerChecking())
  {
    std::unordered_set<const ProofNode*> visited;
    for (const std::shared_ptr<ProofNode>& cpc : children)
    {
      if (expr::containsSubproof(cpc.get(), pn, visited))
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

}  // namespace cvc5

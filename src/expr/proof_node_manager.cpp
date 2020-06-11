/*********************                                                        */
/*! \file proof_node_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof node manager
 **/

#include "expr/proof_node_manager.h"

#include "expr/proof.h"

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

std::shared_ptr<ProofNode> ProofNodeManager::mkNode(
    PfRule id,
    std::shared_ptr<ProofNode> child1,
    const std::vector<Node>& args,
    Node expected)
{
  std::vector<std::shared_ptr<ProofNode>> children;
  children.push_back(child1);
  return mkNode(id, children, args, expected);
}

std::shared_ptr<ProofNode> ProofNodeManager::mkAssume(Node fact)
{
  Assert(!fact.isNull());
  Assert(fact.getType().isBoolean());
  std::vector<std::shared_ptr<ProofNode>> children;
  std::vector<Node> args;
  args.push_back(fact);
  return mkNode(PfRule::ASSUME, children, args, fact);
}

std::shared_ptr<ProofNode> ProofNodeManager::mkScope(
    std::shared_ptr<ProofNode> pf,
    std::vector<Node>& assumps,
    bool ensureClosed,
    bool doMinimize,
    Node expected)
{
  std::vector<std::shared_ptr<ProofNode>> pfChildren;
  pfChildren.push_back(pf);
  if (!ensureClosed)
  {
    return mkNode(PfRule::SCOPE, pfChildren, assumps, expected);
  }
  Trace("pnm-scope") << "ProofNodeManager::mkScope " << assumps << std::endl;
  // we first ensure the assumptions are flattened
  std::unordered_set<Node, NodeHashFunction> ac;
  for (const TNode& a : assumps)
  {
    ac.insert(a);
  }
  // The free assumptions of the proof
  std::map<Node, std::vector<ProofNode*>> famap;
  pf->getFreeAssumptionsMap(famap);
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
    // otherwise it may be due to the predicate equality business?
    //
    // the assumption can be e.g. (= false (= t1 t2)) in which case the
    // necessary proof to be built is
    //
    //     --------------- ASSUME
    //     (not (= t1 t2))
    //  -------------------- FALSE_INTRO
    //  (= (= t1 t2) false)
    //  -------------------- SYMM
    //  (= false (= t1 t2))
    bool pol, flipEqualityPredIntro;
    Node aPred = CDProof::getPredicateFact(a, pol, flipEqualityPredIntro);
    Trace("pnm-scope") << "  - try predicate fact " << aPred << "\n";
    if (!aPred.isNull())
    {
      // Whether the predicate also needs to be flipped to a get a bound
      // assumption.
      bool flipPred = false;
      // Whether we've found a path to a bound assumption.
      bool foundMatch = false;
      Node symPred;
      if (ac.count(aPred))
      {
        foundMatch = true;
      }
      else
      {
        symPred = CDProof::getSymmFact(aPred);
        if (!symPred.isNull() && ac.count(symPred))
        {
          foundMatch = true;
          flipPred = true;
        }
      }
      if (foundMatch)
      {
        Trace("pnm-scope") << "- introduce explicit predicate " << aPred
                           << " via " << (flipEqualityPredIntro ? "[reoriented] " : "") << a
                           << " for " << fa.second.size() << " proof nodes"
                           << std::endl;
        std::shared_ptr<ProofNode> pfaa = mkAssume(flipPred ? symPred : aPred);
        // Potentially apply symmetry to the real assumption
        if (flipPred)
        {
          pfaa = mkNode(PfRule::SYMM, pfaa, {}, aPred);
        }
        // maybe reorient equality, in which case update the pointer to the
        // justification of the assumption
        if (flipEqualityPredIntro)
        {
          pfaa = mkNode(pol ? PfRule::TRUE_INTRO : PfRule::FALSE_INTRO,
                        pfaa,
                        {},
                        a[1].eqNode(a[0]));
        }
        PfRule updateRule =
            flipEqualityPredIntro ? PfRule::SYMM
                 : (pol ? PfRule::TRUE_INTRO : PfRule::FALSE_INTRO);
        for (ProofNode* pfs : fa.second)
        {
          Assert(pfs->getResult() == a);
          updateNode(pfs, updateRule, {pfaa}, {});
        }
        Trace("pnm-scope") << "...finished" << std::endl;
        acu.insert(aPred);
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
    AlwaysAssert(false) << "Generated a proof that is not closed by the scope: "
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
    // always must remove duplicates
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
  return mkNode(PfRule::SCOPE, pfChildren, assumps, minExpected);
}

bool ProofNodeManager::updateNode(
    ProofNode* pn,
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args)
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
        AlwaysAssert(false) << ss.str();
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
  // We expect to prove the same thing as before
  Node res = checkInternal(id, children, args, pn->d_proven);
  if (res.isNull())
  {
    // if it was invalid, then we do not update
    return false;
  }

  // we update its value
  pn->setValue(id, children, args);
  // proven field should already be the same as the result
  Assert(res == pn->d_proven);
  return true;
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

}  // namespace CVC4

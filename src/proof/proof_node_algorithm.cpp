/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof node algorithm utilities.
 */

#include "proof/proof_node_algorithm.h"

#include "expr/aci_norm.h"
#include "expr/algorithm/flatten.h"
#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "proof/proof_rule_checker.h"
#include "theory/arith/arith_poly_norm.h"
#include "theory/builtin/generic_op.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace expr {

namespace {

Node mkNodeWithChildren(const Node& n, const std::vector<Node>& children)
{
  NodeManager* nm = n.getNodeManager();
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    std::vector<Node> cchildren;
    cchildren.reserve(children.size() + 1);
    cchildren.push_back(n.getOperator());
    cchildren.insert(cchildren.end(), children.begin(), children.end());
    return nm->mkNode(n.getKind(), cchildren);
  }
  return nm->mkNode(n.getKind(), children);
}

std::vector<Node> getAssocChildren(const Node& n)
{
  std::vector<Node> children;
  if (theory::quantifiers::TermUtil::isAssoc(n.getKind()))
  {
    std::vector<TNode> tchildren;
    algorithm::flatten(n, tchildren);
    children.insert(children.end(), tchildren.begin(), tchildren.end());
  }
  else
  {
    children.insert(children.end(), n.begin(), n.end());
  }
  return children;
}

class CommChildProofCache
{
 public:
  CommChildProofCache(Env& env,
                      bool allowPredIntro,
                      EqualityNodeLessCallback orderChildren)
      : d_env(env),
        d_allowPredIntro(allowPredIntro),
        d_orderChildren(orderChildren)
  {
  }

  std::shared_ptr<ProofNode> getProof(const Node& a, const Node& b)
  {
    if (a == b)
    {
      return nullptr;
    }
    Node eq = a.eqNode(b);
    auto its = d_success.find(eq);
    if (its != d_success.end())
    {
      return its->second;
    }
    if (d_fail.find(eq) != d_fail.end())
    {
      return nullptr;
    }
    CDProof cdp(d_env);
    if (!proveEqualityWithRewriteSteps(
            d_env, cdp, a, b, d_allowPredIntro, d_orderChildren))
    {
      d_fail.insert(eq);
      return nullptr;
    }
    std::shared_ptr<ProofNode> pf = cdp.getProofFor(eq);
    if (pf == nullptr)
    {
      d_fail.insert(eq);
      return nullptr;
    }
    d_success[eq] = pf;
    return pf;
  }

 private:
  Env& d_env;
  bool d_allowPredIntro;
  EqualityNodeLessCallback d_orderChildren;
  std::map<Node, std::shared_ptr<ProofNode>> d_success;
  std::unordered_set<Node> d_fail;
};

struct OrderedCommChild
{
  size_t d_index;
  Node d_child;
};

bool matchCommChildrenOrdered(const std::vector<Node>& lhsChildren,
                              const std::vector<Node>& rhsChildren,
                              const EqualityNodeLessCallback& orderChildren,
                              CommChildProofCache& cache,
                              std::vector<int>& match,
                              std::vector<std::shared_ptr<ProofNode>>& proofs)
{
  std::vector<OrderedCommChild> lhsOrdered;
  std::vector<OrderedCommChild> rhsOrdered;
  lhsOrdered.reserve(lhsChildren.size());
  rhsOrdered.reserve(rhsChildren.size());
  for (size_t i = 0, size = lhsChildren.size(); i < size; ++i)
  {
    lhsOrdered.push_back({i, lhsChildren[i]});
    rhsOrdered.push_back({i, rhsChildren[i]});
  }
  auto cmp = [&orderChildren](const OrderedCommChild& a,
                              const OrderedCommChild& b) {
    return orderChildren(a.d_child, b.d_child);
  };
  std::stable_sort(lhsOrdered.begin(), lhsOrdered.end(), cmp);
  std::stable_sort(rhsOrdered.begin(), rhsOrdered.end(), cmp);
  for (size_t i = 0, size = lhsOrdered.size(); i < size; ++i)
  {
    const Node& lhsChild = lhsOrdered[i].d_child;
    const Node& rhsChild = rhsOrdered[i].d_child;
    if (!lhsChild.getType().isComparableTo(rhsChild.getType()))
    {
      return false;
    }
    size_t li = lhsOrdered[i].d_index;
    match[li] = static_cast<int>(rhsOrdered[i].d_index);
    if (lhsChild == rhsChild)
    {
      continue;
    }
    proofs[li] = cache.getProof(lhsChild, rhsChild);
    if (proofs[li] == nullptr)
    {
      return false;
    }
  }
  return true;
}

bool matchCommChildren(const std::vector<Node>& lhsChildren,
                       const std::vector<Node>& rhsChildren,
                       CommChildProofCache& cache,
                       std::vector<int>& match,
                       std::vector<std::shared_ptr<ProofNode>>& proofs,
                       std::vector<bool>& used)
{
  size_t next = lhsChildren.size();
  std::vector<int> candidates;
  for (size_t i = 0, size = lhsChildren.size(); i < size; ++i)
  {
    if (match[i] != -1)
    {
      continue;
    }
    std::vector<int> curr;
    for (size_t j = 0, rsize = rhsChildren.size(); j < rsize; ++j)
    {
      if (used[j]
          || !lhsChildren[i].getType().isComparableTo(rhsChildren[j].getType()))
      {
        continue;
      }
      if (lhsChildren[i] == rhsChildren[j]
          || cache.getProof(lhsChildren[i], rhsChildren[j]) != nullptr)
      {
        curr.push_back(static_cast<int>(j));
      }
    }
    if (curr.empty())
    {
      return false;
    }
    if (next == lhsChildren.size() || curr.size() < candidates.size())
    {
      next = i;
      candidates = std::move(curr);
      if (candidates.size() == 1)
      {
        break;
      }
    }
  }
  if (next == lhsChildren.size())
  {
    return true;
  }
  for (int j : candidates)
  {
    match[next] = j;
    used[j] = true;
    if (lhsChildren[next] != rhsChildren[j])
    {
      proofs[next] = cache.getProof(lhsChildren[next], rhsChildren[j]);
      if (proofs[next] == nullptr)
      {
        used[j] = false;
        match[next] = -1;
        continue;
      }
    }
    if (matchCommChildren(lhsChildren, rhsChildren, cache, match, proofs, used))
    {
      return true;
    }
    proofs[next].reset();
    used[j] = false;
    match[next] = -1;
  }
  return false;
}

bool proveCommEqualityWithRewriteSteps(
    Env& env,
    CDProof& cdp,
    const Node& lhs,
    const Node& rhs,
    bool allowPredIntro,
    const EqualityNodeLessCallback& orderChildren)
{
  Kind k = lhs.getKind();
  if (k != rhs.getKind() || !theory::quantifiers::TermUtil::isAssoc(k)
      || !theory::quantifiers::TermUtil::isComm(k))
  {
    return false;
  }
  std::vector<Node> lhsChildren = getAssocChildren(lhs);
  std::vector<Node> rhsChildren = getAssocChildren(rhs);
  if (lhsChildren.size() != rhsChildren.size() || lhsChildren.empty())
  {
    return false;
  }
  Node flhs = lhsChildren.size() == lhs.getNumChildren()
                  ? lhs
                  : mkNodeWithChildren(lhs, lhsChildren);
  Node frhs = rhsChildren.size() == rhs.getNumChildren()
                  ? rhs
                  : mkNodeWithChildren(rhs, rhsChildren);

  CommChildProofCache cache(env, allowPredIntro, orderChildren);
  std::vector<int> match(lhsChildren.size(), -1);
  std::vector<std::shared_ptr<ProofNode>> proofs(lhsChildren.size(), nullptr);
  bool matched = false;
  if (orderChildren)
  {
    matched = matchCommChildrenOrdered(
        lhsChildren, rhsChildren, orderChildren, cache, match, proofs);
  }
  else
  {
    std::vector<bool> used(rhsChildren.size(), false);
    matched =
        matchCommChildren(lhsChildren, rhsChildren, cache, match, proofs, used);
  }
  if (!matched)
  {
    return false;
  }

  std::vector<Node> rhsMatchedChildren;
  rhsMatchedChildren.reserve(rhsChildren.size());
  std::vector<Node> premises(lhsChildren.size(), Node::null());
  for (size_t i = 0, size = lhsChildren.size(); i < size; ++i)
  {
    int mj = match[i];
    Assert(mj >= 0);
    rhsMatchedChildren.push_back(rhsChildren[mj]);
    if (lhsChildren[i] == rhsChildren[mj])
    {
      continue;
    }
    Node eqc = lhsChildren[i].eqNode(rhsChildren[mj]);
    cdp.addProof(proofs[i]);
    premises[i] = eqc;
  }
  Node mrhs = mkNodeWithChildren(frhs, rhsMatchedChildren);
  Node feq = flhs.eqNode(mrhs);
  if (flhs != mrhs)
  {
    Node eqc = proveCong(env, &cdp, flhs, premises);
    if (eqc != feq)
    {
      return false;
    }
  }

  Node eq = lhs.eqNode(rhs);
  std::vector<Node> transEq;
  if (lhs != flhs)
  {
    Node lflat = lhs.eqNode(flhs);
    cdp.addStep(lflat, ProofRule::ACI_NORM, {}, {lflat});
    transEq.push_back(lflat);
  }
  if (flhs != mrhs)
  {
    transEq.push_back(feq);
  }
  if (mrhs != frhs)
  {
    Node req = frhs.eqNode(mrhs);
    cdp.addStep(req, ProofRule::ACI_NORM, {}, {req});
    Node reqs = mrhs.eqNode(frhs);
    cdp.addStep(reqs, ProofRule::SYMM, {req}, {});
    transEq.push_back(reqs);
  }
  if (frhs != rhs)
  {
    Node rflat = rhs.eqNode(frhs);
    cdp.addStep(rflat, ProofRule::ACI_NORM, {}, {rflat});
    Node rflats = frhs.eqNode(rhs);
    cdp.addStep(rflats, ProofRule::SYMM, {rflat}, {});
    transEq.push_back(rflats);
  }
  if (transEq.empty())
  {
    return eq == feq;
  }
  if (transEq.size() == 1)
  {
    return transEq[0] == eq;
  }
  return cdp.addStep(eq, ProofRule::TRANS, transEq, {});
}

}  // namespace

void getFreeAssumptions(ProofNode* pn, std::vector<Node>& assump)
{
  std::map<Node, std::vector<std::shared_ptr<ProofNode>>> amap;
  std::shared_ptr<ProofNode> spn = std::make_shared<ProofNode>(
      pn->getRule(), pn->getChildren(), pn->getArguments());
  getFreeAssumptionsMap(spn, amap);
  for (const std::pair<const Node, std::vector<std::shared_ptr<ProofNode>>>& p :
       amap)
  {
    assump.push_back(p.first);
  }
}

void getFreeAssumptionsMap(
    std::shared_ptr<ProofNode> pn,
    std::map<Node, std::vector<std::shared_ptr<ProofNode>>>& amap)
{
  // proof should not be cyclic
  std::unordered_set<ProofNode*> visited;
  std::unordered_set<ProofNode*>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  std::shared_ptr<ProofNode> cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur.get());
    const std::vector<Node>& cargs = cur->getArguments();
    if (it == visited.end())
    {
      visited.insert(cur.get());
      ProofRule id = cur->getRule();
      if (id == ProofRule::ASSUME)
      {
        Assert(cargs.size() == 1);
        Node f = cargs[0];
        amap[f].push_back(cur);
      }
      else
      {
        const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
        if (id == ProofRule::SCOPE)
        {
          // make a recursive call, which is bound in depth by the number of
          // nested SCOPE (never expected to be more than 1 or 2).
          std::map<Node, std::vector<std::shared_ptr<ProofNode>>> amapTmp;
          expr::getFreeAssumptionsMap(cs[0], amapTmp);
          for (std::pair<const Node, std::vector<std::shared_ptr<ProofNode>>>&
                   a : amapTmp)
          {
            if (std::find(cargs.begin(), cargs.end(), a.first) == cargs.end())
            {
              std::vector<std::shared_ptr<ProofNode>>& pfs = amap[a.first];
              pfs.insert(pfs.end(), a.second.begin(), a.second.end());
            }
          }
          continue;
        }
        // traverse on children
        visit.insert(visit.end(), cs.begin(), cs.end());
      }
    }
  } while (!visit.empty());
}

void getSubproofRule(std::shared_ptr<ProofNode> pn,
                     ProofRule r,
                     std::vector<std::shared_ptr<ProofNode>>& pfs)
{
  std::unordered_set<ProofRule> rs{r};
  getSubproofRules(pn, rs, pfs);
}

void getSubproofRules(std::shared_ptr<ProofNode> pn,
                      std::unordered_set<ProofRule> rs,
                      std::vector<std::shared_ptr<ProofNode>>& pfs)
{
  // proof should not be cyclic
  std::unordered_set<ProofNode*> visited;
  std::unordered_set<ProofNode*>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  std::shared_ptr<ProofNode> cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur.get());
    if (it == visited.end())
    {
      visited.insert(cur.get());
      if (rs.find(cur->getRule()) != rs.end())
      {
        pfs.push_back(cur);
      }
      else
      {
        const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
        // traverse on children
        visit.insert(visit.end(), cs.begin(), cs.end());
      }
    }
  } while (!visit.empty());
}

bool containsAssumption(const ProofNode* pn,
                        std::unordered_map<const ProofNode*, bool>& caMap,
                        const std::unordered_set<Node>& allowed)
{
  std::unordered_map<const ProofNode*, bool> visited;
  std::unordered_map<const ProofNode*, bool>::iterator it;
  std::vector<const ProofNode*> visit;
  visit.push_back(pn);
  bool foundAssumption = false;
  const ProofNode* cur;
  while (!visit.empty())
  {
    cur = visit.back();
    visit.pop_back();
    // have we already computed?
    it = caMap.find(cur);
    if (it != caMap.end())
    {
      // if cached, we set found assumption to true if applicable and continue
      if (it->second)
      {
        foundAssumption = true;
      }
      continue;
    }
    it = visited.find(cur);
    if (it == visited.end())
    {
      ProofRule r = cur->getRule();
      if (r == ProofRule::ASSUME)
      {
        bool ret = allowed.find(cur->getArguments()[0]) == allowed.end();
        visited[cur] = ret;
        caMap[cur] = ret;
        foundAssumption = ret;
      }
      else if (!foundAssumption)
      {
        // if we haven't found an assumption yet, recurse. Otherwise, we will
        // not bother computing whether this subproof contains an assumption
        // since we know its parent already contains one by another child.
        visited[cur] = false;
        visit.push_back(cur);
        const std::vector<std::shared_ptr<ProofNode>>& children =
            cur->getChildren();
        for (const std::shared_ptr<ProofNode>& cp : children)
        {
          visit.push_back(cp.get());
        }
      }
    }
    else if (!it->second)
    {
      visited[cur] = true;
      // we contain an assumption if we've found an assumption in a child
      caMap[cur] = foundAssumption;
    }
  }
  return caMap[cur];
}
bool containsAssumption(const ProofNode* pn,
                        std::unordered_map<const ProofNode*, bool>& caMap)
{
  std::unordered_set<Node> allowed;
  return containsAssumption(pn, caMap, allowed);
}

bool containsAssumption(const ProofNode* pn)
{
  std::unordered_map<const ProofNode*, bool> caMap;
  std::unordered_set<Node> allowed;
  return containsAssumption(pn, caMap, allowed);
}

bool containsSubproof(ProofNode* pn, ProofNode* pnc)
{
  std::unordered_set<const ProofNode*> visited;
  return containsSubproof(pn, pnc, visited);
}

bool containsSubproof(ProofNode* pn,
                      ProofNode* pnc,
                      std::unordered_set<const ProofNode*>& visited)
{
  std::unordered_map<const ProofNode*, bool>::iterator it;
  std::vector<const ProofNode*> visit;
  visit.push_back(pn);
  const ProofNode* cur;
  while (!visit.empty())
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur == pnc)
      {
        return true;
      }
      const std::vector<std::shared_ptr<ProofNode>>& children =
          cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : children)
      {
        visit.push_back(cp.get());
      }
    }
  }
  return false;
}

ProofRule getCongRule(const Node& n, std::vector<Node>& args)
{
  Kind k = n.getKind();
  ProofRule r = ProofRule::CONG;
  switch (k)
  {
    case Kind::DISTINCT: r = ProofRule::PAIRWISE_CONG; break;
    case Kind::APPLY_UF:
    case Kind::FLOATINGPOINT_LT:
    case Kind::FLOATINGPOINT_LEQ:
    case Kind::FLOATINGPOINT_GT:
    case Kind::FLOATINGPOINT_GEQ:
    case Kind::NULLABLE_LIFT:
    case Kind::APPLY_INDEXED_SYMBOLIC:
      // takes arbitrary but we use CONG
      break;
    case Kind::HO_APPLY:
      // Use HO_CONG, since HO_APPLY is encoded as native function application.
      // This requires no arguments so we return.
      r = ProofRule::HO_CONG;
      break;
    case Kind::APPLY_CONSTRUCTOR:
      // tuples are n-ary, others are fixed
      r = n.getType().isTuple() ? ProofRule::NARY_CONG : ProofRule::CONG;
      break;
    default:
      if (NodeManager::isNAryKind(k))
      {
        // n-ary operators that are not handled as exceptions above use
        // NARY_CONG
        r = ProofRule::NARY_CONG;
      }
      break;
  }
  if (r != ProofRule::HO_CONG)
  {
    args.push_back(n);
  }
  return r;
}

Node proveCong(Env& env,
               CDProof* cdp,
               const Node& n,
               const std::vector<Node>& premises)
{
  std::vector<Node> cpremises = premises;
  std::vector<Node> cargs;
  ProofRule cr = getCongRule(n, cargs);
  cpremises.resize(n.getNumChildren());
  // congruence on closures omit the first argument
  if (n.isClosure())
  {
    cpremises.erase(cpremises.begin(), cpremises.begin() + 1);
  }
  // add REFL if a premise is not provided
  for (size_t i = 0, npremises = cpremises.size(); i < npremises; i++)
  {
    if (cpremises[i].isNull())
    {
      Node refl = n[i].eqNode(n[i]);
      cdp->addStep(refl, ProofRule::REFL, {}, {n[i]});
      cpremises[i] = refl;
    }
  }
  ProofChecker* pc = env.getProofNodeManager()->getChecker();
  Node eq = pc->checkDebug(cr, cpremises, cargs);
  if (!eq.isNull())
  {
    cdp->addStep(eq, cr, cpremises, cargs);
  }
  return eq;
}

bool proveEqualityWithRewriteSteps(
    Env& env,
    CDProof& cdp,
    const Node& a,
    const Node& b,
    bool allowPredIntro,
    const EqualityNodeLessCallback& orderChildren)
{
  // the set of equalities we have visited
  std::unordered_set<Node> visited;
  // equalities that we have use ACI_NORM on at pre-rewrite
  std::unordered_set<Node> visitedAciNorm;
  // the list of equalities to visit
  std::vector<Node> visit;
  visit.push_back(a.eqNode(b));
  while (!visit.empty())
  {
    Node eq = visit.back();
    visit.pop_back();
    if (cdp.hasStep(eq))
    {
      // already proven, skip
      continue;
    }
    const Node& lhs = eq[0];
    const Node& rhs = eq[1];
    if (visited.insert(eq).second)
    {
      // We first check if lhs == rhs is directly provable by refl, aci norm,
      // or arith/bv poly norm.
      if (lhs == rhs)
      {
        cdp.addStep(eq, ProofRule::REFL, {}, {lhs});
        continue;
      }
      if (expr::isACINorm(lhs, rhs))
      {
        cdp.addStep(eq, ProofRule::ACI_NORM, {}, {eq});
        continue;
      }
      if (lhs.getType() == rhs.getType())
      {
        TypeNode tn = lhs.getType();
        if (tn.isBitVector()
            && theory::arith::PolyNorm::isArithPolyNorm(lhs, rhs))
        {
          cdp.addStep(eq, ProofRule::BV_POLY_NORM, {}, {eq});
          continue;
        }
        if (tn.isRealOrInt()
            && theory::arith::PolyNorm::isArithPolyNorm(lhs, rhs))
        {
          cdp.addStep(eq, ProofRule::ARITH_POLY_NORM, {}, {eq});
          continue;
        }
      }
      // otherwise, we normalize based on AC reasoning if possible, which may
      // allow us to align children when recursing.
      Node an = expr::getACINormalForm(lhs);
      Node bn = expr::getACINormalForm(rhs);
      if (an != lhs || bn != rhs)
      {
        visitedAciNorm.insert(eq);
        visit.push_back(eq);
        if (an != bn)
        {
          visit.push_back(an.eqNode(bn));
        }
        continue;
      }
      // if AC reasoning is not available, we attempt to recurse on children
      // and reconstruct via congruence.
      if (lhs.getKind() != rhs.getKind()
          || lhs.getNumChildren() != rhs.getNumChildren()
          || lhs.getNumChildren() == 0)
      {
        Node eqr = env.rewriteViaMethod(eq);
        if (allowPredIntro && eqr.isConst() && eqr.getConst<bool>())
        {
          cdp.addStep(eq, ProofRule::MACRO_SR_PRED_INTRO, {}, {eq});
          continue;
        }
        return false;
      }
      if (lhs.isClosure() && lhs[0] != rhs[0])
      {
        // closures do not work if their variable lists are different.
        Node eqr = env.rewriteViaMethod(eq);
        if (allowPredIntro && eqr.isConst() && eqr.getConst<bool>())
        {
          cdp.addStep(eq, ProofRule::MACRO_SR_PRED_INTRO, {}, {eq});
          continue;
        }
        return false;
      }
      if (theory::quantifiers::TermUtil::isComm(lhs.getKind())
          && proveCommEqualityWithRewriteSteps(
              env, cdp, lhs, rhs, allowPredIntro, orderChildren))
      {
        continue;
      }
      visit.push_back(eq);
      for (size_t i = lhs.getNumChildren(); i > 0; --i)
      {
        size_t index = i - 1;
        if (lhs[index] != rhs[index])
        {
          visit.push_back(lhs[index].eqNode(rhs[index]));
        }
      }
      continue;
    }
    if (visitedAciNorm.find(eq) != visitedAciNorm.end())
    {
      Node an = expr::getACINormalForm(lhs);
      Node bn = expr::getACINormalForm(rhs);
      // if so, we put together a proof of transitivity
      // -------- ACI_NORM  --------------- ... ----------- ACI_NORM, SYMM
      // lhs = aci(lhs)     aci(lhs)=aci(rhs)   aci(rhs) = rhs
      // ----------------------------------------------------- TRANS
      // lhs = rhs
      std::vector<Node> transEq;
      if (lhs != an)
      {
        Node aeq = lhs.eqNode(an);
        cdp.addStep(aeq, ProofRule::ACI_NORM, {}, {aeq});
        transEq.push_back(aeq);
      }
      if (an != bn)
      {
        transEq.push_back(an.eqNode(bn));
      }
      if (rhs != bn)
      {
        Node beq = rhs.eqNode(bn);
        cdp.addStep(beq, ProofRule::ACI_NORM, {}, {beq});
        Node beqs = bn.eqNode(rhs);
        cdp.addStep(beqs, ProofRule::SYMM, {beq}, {});
        transEq.push_back(beqs);
      }
      Assert(!transEq.empty());
      if (transEq.size() == 1)
      {
        if (transEq[0] != eq)
        {
          return false;
        }
      }
      else if (!cdp.addStep(eq, ProofRule::TRANS, transEq, {}))
      {
        return false;
      }
      continue;
    }
    // otherwise, we are reconstructing a proof of congruence from proven
    // equalities of children.
    std::vector<Node> premises(lhs.getNumChildren(), Node::null());
    Assert(lhs.getNumChildren() > 0);
    for (size_t i = 0, nchildren = lhs.getNumChildren(); i < nchildren; i++)
    {
      if (lhs[i] == rhs[i])
      {
        continue;
      }
      Node eqi = lhs[i].eqNode(rhs[i]);
      premises[i] = eqi;
    }
    Node eqc = proveCong(env, &cdp, lhs, premises);
    if (eqc != eq)
    {
      Node eqr = env.rewriteViaMethod(eq);
      if (allowPredIntro && eqr.isConst() && eqr.getConst<bool>())
      {
        cdp.addStep(eq, ProofRule::MACRO_SR_PRED_INTRO, {}, {eq});
        continue;
      }
      return false;
    }
  }
  return true;
}

}  // namespace expr
}  // namespace cvc5::internal

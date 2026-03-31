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
#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "proof/proof_rule_checker.h"
#include "theory/arith/arith_poly_norm.h"
#include "theory/builtin/generic_op.h"

namespace cvc5::internal {
namespace expr {

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
    Env& env, CDProof& cdp, const Node& a, const Node& b, bool allowPredIntro)
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
      // if not, but if the equality still rewrites to true, and we are
      // permitting sr_pred_intro subgoals, then we conclude.
      Node eqr = env.rewriteViaMethod(eq);
      if (allowPredIntro && eqr.isConst() && eqr.getConst<bool>())
      {
        cdp.addStep(eq, ProofRule::MACRO_SR_PRED_INTRO, {}, {eq});
        continue;
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
        return false;
      }
      size_t startChild = 0;
      if (lhs.isClosure())
      {
        // closures do not work if their variable lists are different.
        if (lhs[0] != rhs[0])
        {
          return false;
        }
        startChild = 1;
      }
      visit.push_back(eq);
      for (size_t i = lhs.getNumChildren(); i > startChild; --i)
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
    Assert(cur.d_state == EqProofState::FINISH_CONG);
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
      return false;
    }
  }
  return true;
}

}  // namespace expr
}  // namespace cvc5::internal

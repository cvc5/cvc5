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

bool proveEqualityWithRewriteSteps(Env& env,
                                   CDProof& cdp,
                                   const Node& a,
                                   const Node& b,
                                   bool allowPredIntro)
{
  enum class EqProofState
  {
    ENTER,
    FINISH_ACI_NORM,
    FINISH_CLOSURE,
    FINISH_CONG,
  };
  enum class EqProofStatus
  {
    ACTIVE,
    PROVED,
    FAILED,
  };
  struct EqProofFrame
  {
    Node d_a;
    Node d_b;
    EqProofState d_state;
  };

  std::unordered_map<Node, EqProofStatus> status;
  std::vector<EqProofFrame> visit;
  auto schedule = [&](const Node& lhs, const Node& rhs) {
    Node eq = lhs.eqNode(rhs);
    if (status.find(eq) == status.end())
    {
      status.emplace(eq, EqProofStatus::ACTIVE);
      visit.push_back({lhs, rhs, EqProofState::ENTER});
    }
  };

  schedule(a, b);
  while (!visit.empty())
  {
    EqProofFrame cur = visit.back();
    visit.pop_back();
    const Node& lhs = cur.d_a;
    const Node& rhs = cur.d_b;
    Node eq = lhs.eqNode(rhs);
    auto sit = status.find(eq);
    Assert(sit != status.end());
    if (cur.d_state == EqProofState::ENTER)
    {
      if (lhs == rhs)
      {
        cdp.addStep(eq, ProofRule::REFL, {}, {lhs});
        sit->second = EqProofStatus::PROVED;
        continue;
      }
      if (expr::isACINorm(lhs, rhs))
      {
        cdp.addStep(eq, ProofRule::ACI_NORM, {}, {eq});
        sit->second = EqProofStatus::PROVED;
        continue;
      }
      if (lhs.getType() == rhs.getType())
      {
        TypeNode tn = lhs.getType();
        if (tn.isBitVector() && theory::arith::PolyNorm::isArithPolyNorm(lhs, rhs))
        {
          cdp.addStep(eq, ProofRule::BV_POLY_NORM, {}, {eq});
          sit->second = EqProofStatus::PROVED;
          continue;
        }
        if (tn.isRealOrInt()
            && theory::arith::PolyNorm::isArithPolyNorm(lhs, rhs))
        {
          cdp.addStep(eq, ProofRule::ARITH_POLY_NORM, {}, {eq});
          sit->second = EqProofStatus::PROVED;
          continue;
        }
      }
      Node eqr = env.rewriteViaMethod(eq);
      if (allowPredIntro && eqr.isConst() && eqr.getConst<bool>())
      {
        cdp.addStep(eq, ProofRule::MACRO_SR_PRED_INTRO, {}, {eq});
        sit->second = EqProofStatus::PROVED;
        continue;
      }
      Node an = expr::getACINormalForm(lhs);
      Node bn = expr::getACINormalForm(rhs);
      if (an != lhs || bn != rhs)
      {
        if (lhs != an)
        {
          Node aeq = lhs.eqNode(an);
          cdp.addStep(aeq, ProofRule::ACI_NORM, {}, {aeq});
        }
        visit.push_back({lhs, rhs, EqProofState::FINISH_ACI_NORM});
        if (an != bn)
        {
          schedule(an, bn);
        }
        continue;
      }
      if (lhs.getKind() != rhs.getKind()
          || lhs.getNumChildren() != rhs.getNumChildren())
      {
        sit->second = EqProofStatus::FAILED;
        continue;
      }
      if (lhs.isClosure())
      {
        if (lhs[0] != rhs[0])
        {
          sit->second = EqProofStatus::FAILED;
          continue;
        }
        visit.push_back({lhs, rhs, EqProofState::FINISH_CLOSURE});
        for (size_t i = lhs.getNumChildren(); i > 1; --i)
        {
          size_t index = i - 1;
          if (lhs[index] != rhs[index])
          {
            schedule(lhs[index], rhs[index]);
          }
        }
        continue;
      }
      visit.push_back({lhs, rhs, EqProofState::FINISH_CONG});
      for (size_t i = lhs.getNumChildren(); i > 0; --i)
      {
        size_t index = i - 1;
        if (lhs[index] != rhs[index])
        {
          schedule(lhs[index], rhs[index]);
        }
      }
      continue;
    }
    if (cur.d_state == EqProofState::FINISH_ACI_NORM)
    {
      Node an = expr::getACINormalForm(lhs);
      Node bn = expr::getACINormalForm(rhs);
      if (an != bn)
      {
        auto nit = status.find(an.eqNode(bn));
        if (nit == status.end() || nit->second != EqProofStatus::PROVED)
        {
          sit->second = EqProofStatus::FAILED;
          continue;
        }
      }
      std::vector<Node> transEq;
      if (lhs != an)
      {
        transEq.push_back(lhs.eqNode(an));
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
      if (transEq.empty())
      {
        sit->second = EqProofStatus::PROVED;
      }
      else if (transEq.size() == 1)
      {
        sit->second =
            transEq[0] == eq ? EqProofStatus::PROVED : EqProofStatus::FAILED;
      }
      else
      {
        sit->second = cdp.addStep(eq, ProofRule::TRANS, transEq, {})
                          ? EqProofStatus::PROVED
                          : EqProofStatus::FAILED;
      }
      continue;
    }
    if (cur.d_state == EqProofState::FINISH_CLOSURE)
    {
      std::vector<Node> cpremises;
      bool failed = false;
      for (size_t i = 1, nchildren = lhs.getNumChildren(); i < nchildren; i++)
      {
        Node eqi = lhs[i].eqNode(rhs[i]);
        if (lhs[i] == rhs[i])
        {
          cdp.addStep(eqi, ProofRule::REFL, {}, {lhs[i]});
        }
        else
        {
          auto cit = status.find(eqi);
          if (cit == status.end() || cit->second != EqProofStatus::PROVED)
          {
            failed = true;
            break;
          }
        }
        cpremises.push_back(eqi);
      }
      if (failed)
      {
        sit->second = EqProofStatus::FAILED;
        continue;
      }
      std::vector<Node> cargs;
      ProofRule cr = getCongRule(lhs, cargs);
      sit->second = cdp.addStep(eq, cr, cpremises, cargs)
                        ? EqProofStatus::PROVED
                        : EqProofStatus::FAILED;
      continue;
    }
    Assert(cur.d_state == EqProofState::FINISH_CONG);
    std::vector<Node> premises(lhs.getNumChildren(), Node::null());
    bool changed = false;
    bool failed = false;
    size_t nchildren = lhs.getNumChildren();
    if (nchildren>0)
    {
      for (size_t i = 0; i < nchildren; i++)
      {
        if (lhs[i] == rhs[i])
        {
          continue;
        }
        Node eqi = lhs[i].eqNode(rhs[i]);
        auto cit = status.find(eqi);
        if (cit == status.end() || cit->second != EqProofStatus::PROVED)
        {
          failed = true;
          break;
        }
        premises[i] = eqi;
        changed = true;
      }
    }
    else
    {
      failed = true;
    }
    if (failed)
    {
      sit->second = EqProofStatus::FAILED;
      continue;
    }
    Assert (changed);
    Node eqc = proveCong(env, &cdp, lhs, premises);
    sit->second = eqc == eq ? EqProofStatus::PROVED : EqProofStatus::FAILED;
  }
  return status[a.eqNode(b)] == EqProofStatus::PROVED;
}

}  // namespace expr
}  // namespace cvc5::internal

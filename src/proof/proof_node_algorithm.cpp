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
                                   const Node& b)
{
  Node eq = a.eqNode(b);
  if (a == b)
  {
    cdp.addStep(eq, ProofRule::REFL, {}, {a});
    return true;
  }
  if (expr::isACINorm(a, b))
  {
    cdp.addStep(eq, ProofRule::ACI_NORM, {}, {eq});
    return true;
  }
  if (a.getType() == b.getType())
  {
    TypeNode tn = a.getType();
    if (tn.isBitVector() && theory::arith::PolyNorm::isArithPolyNorm(a, b))
    {
      cdp.addStep(eq, ProofRule::BV_POLY_NORM, {}, {eq});
      return true;
    }
    if (tn.isRealOrInt() && theory::arith::PolyNorm::isArithPolyNorm(a, b))
    {
      cdp.addStep(eq, ProofRule::ARITH_POLY_NORM, {}, {eq});
      return true;
    }
  }
  Node eqr = env.rewriteViaMethod(eq);
  if (eqr.isConst() && eqr.getConst<bool>())
  {
    cdp.addStep(eq, ProofRule::MACRO_SR_PRED_INTRO, {}, {eq});
    return true;
  }
  Node an = expr::getACINormalForm(a);
  Node bn = expr::getACINormalForm(b);
  if (an != a || bn != b)
  {
    std::vector<Node> transEq;
    if (a != an)
    {
      Node aeq = a.eqNode(an);
      cdp.addStep(aeq, ProofRule::ACI_NORM, {}, {aeq});
      transEq.push_back(aeq);
    }
    if (!proveEqualityWithRewriteSteps(env, cdp, an, bn))
    {
      return false;
    }
    if (an != bn)
    {
      transEq.push_back(an.eqNode(bn));
    }
    if (b != bn)
    {
      Node beq = b.eqNode(bn);
      cdp.addStep(beq, ProofRule::ACI_NORM, {}, {beq});
      Node beqs = bn.eqNode(b);
      cdp.addStep(beqs, ProofRule::SYMM, {beq}, {});
      transEq.push_back(beqs);
    }
    if (transEq.empty())
    {
      return true;
    }
    if (transEq.size() == 1)
    {
      return transEq[0] == eq;
    }
    cdp.addStep(eq, ProofRule::TRANS, transEq, {});
    return true;
  }
  if (a.getKind() != b.getKind() || a.getNumChildren() != b.getNumChildren())
  {
    return false;
  }
  if (a.isClosure())
  {
    if (a[0] != b[0])
    {
      return false;
    }
    std::vector<Node> cpremises;
    for (size_t i = 1, nchildren = a.getNumChildren(); i < nchildren; i++)
    {
      Node eqi = a[i].eqNode(b[i]);
      if (a[i] == b[i])
      {
        cdp.addStep(eqi, ProofRule::REFL, {}, {a[i]});
      }
      else if (!proveEqualityWithRewriteSteps(env, cdp, a[i], b[i]))
      {
        return false;
      }
      cpremises.push_back(eqi);
    }
    std::vector<Node> cargs;
    ProofRule cr = getCongRule(a, cargs);
    return cdp.addStep(eq, cr, cpremises, cargs);
  }
  std::vector<Node> premises(a.getNumChildren(), Node::null());
  bool changed = false;
  for (size_t i = 0, nchildren = a.getNumChildren(); i < nchildren; i++)
  {
    if (a[i] == b[i])
    {
      continue;
    }
    if (!proveEqualityWithRewriteSteps(env, cdp, a[i], b[i]))
    {
      return false;
    }
    premises[i] = a[i].eqNode(b[i]);
    changed = true;
  }
  if (!changed)
  {
    cdp.addStep(eq, ProofRule::REFL, {}, {a});
    return true;
  }
  Node eqc = proveCong(env, &cdp, a, premises);
  return eqc == eq;
}

}  // namespace expr
}  // namespace cvc5::internal

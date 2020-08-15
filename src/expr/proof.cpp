/*********************                                                        */
/*! \file proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof
 **/

#include "expr/proof.h"

using namespace CVC4::kind;

namespace CVC4 {

CDProof::CDProof(ProofNodeManager* pnm, context::Context* c, std::string name)
    : d_manager(pnm), d_context(), d_nodes(c ? c : &d_context), d_name(name)
{
}

CDProof::~CDProof() {}

std::shared_ptr<ProofNode> CDProof::getProofFor(Node fact)
{
  std::shared_ptr<ProofNode> pf = getProofSymm(fact);
  if (pf != nullptr)
  {
    return pf;
  }
  // add as assumption
  std::vector<Node> pargs = {fact};
  std::vector<std::shared_ptr<ProofNode>> passume;
  std::shared_ptr<ProofNode> pfa =
      d_manager->mkNode(PfRule::ASSUME, passume, pargs, fact);
  d_nodes.insert(fact, pfa);
  Assert(pfa->getResult() == fact);
  return pfa;
}

std::shared_ptr<ProofNode> CDProof::getProof(Node fact) const
{
  NodeProofNodeMap::iterator it = d_nodes.find(fact);
  if (it != d_nodes.end())
  {
    return (*it).second;
  }
  return nullptr;
}

std::shared_ptr<ProofNode> CDProof::getProofSymm(Node fact)
{
  Trace("cdproof") << "CDProof::getProofSymm: " << fact << std::endl;
  std::shared_ptr<ProofNode> pf = getProof(fact);
  if (pf != nullptr && !isAssumption(pf.get()))
  {
    Trace("cdproof") << "...existing non-assume " << pf->getRule() << std::endl;
    return pf;
  }
  Node symFact = getSymmFact(fact);
  if (symFact.isNull())
  {
    Trace("cdproof") << "...no possible symm" << std::endl;
    // no symmetry possible, return original proof (possibly assumption)
    return pf;
  }
  // See if a proof exists for the opposite direction, if so, add the step.
  // Notice that SYMM is also disallowed.
  std::shared_ptr<ProofNode> pfs = getProof(symFact);
  if (pfs != nullptr)
  {
    // The symmetric fact exists, and the current one either does not, or is
    // an assumption. We make a new proof that applies SYMM to pfs.
    std::vector<std::shared_ptr<ProofNode>> pschild;
    pschild.push_back(pfs);
    std::vector<Node> args;
    if (pf == nullptr)
    {
      Trace("cdproof") << "...fresh make symm" << std::endl;
      std::shared_ptr<ProofNode> psym =
          d_manager->mkNode(PfRule::SYMM, pschild, args, fact);
      Assert(psym != nullptr);
      d_nodes.insert(fact, psym);
      return psym;
    }
    else if (!isAssumption(pfs.get()))
    {
      // if its not an assumption, make the connection
      Trace("cdproof") << "...update symm" << std::endl;
      // update pf
      bool sret = d_manager->updateNode(pf.get(), PfRule::SYMM, pschild, args);
      AlwaysAssert(sret);
    }
  }
  else
  {
    Trace("cdproof") << "...no symm, return "
                     << (pf == nullptr ? "null" : "non-null") << std::endl;
  }
  // return original proof (possibly assumption)
  return pf;
}

bool CDProof::addStep(Node expected,
                      PfRule id,
                      const std::vector<Node>& children,
                      const std::vector<Node>& args,
                      bool ensureChildren,
                      CDPOverwrite opolicy)
{
  Trace("cdproof") << "CDProof::addStep: " << identify() << " : " << id << " "
                   << expected << ", ensureChildren = " << ensureChildren
                   << ", overwrite policy = " << opolicy << std::endl;
  Trace("cdproof-debug") << "CDProof::addStep: " << identify()
                         << " : children: " << children << "\n";
  Trace("cdproof-debug") << "CDProof::addStep: " << identify()
                         << " : args: " << args << "\n";
  // NOTE: we should explicitly forbid ASSUME/SYMM?

  // We must always provide expected to this method
  Assert(!expected.isNull());

  std::shared_ptr<ProofNode> pprev = getProofSymm(expected);
  if (pprev != nullptr)
  {
    if (!shouldOverwrite(pprev.get(), id, opolicy))
    {
      // we should not overwrite the current step
      Trace("cdproof") << "...success, no overwrite" << std::endl;
      return true;
    }
    Trace("cdproof") << "existing proof " << pprev->getRule()
                     << ", overwrite..." << std::endl;
    // we will overwrite the existing proof node by updating its contents below
  }
  // collect the child proofs, for each premise
  std::vector<std::shared_ptr<ProofNode>> pchildren;
  for (const Node& c : children)
  {
    Trace("cdproof") << "- get child " << c << std::endl;
    std::shared_ptr<ProofNode> pc = getProofSymm(c);
    if (pc == nullptr)
    {
      if (ensureChildren)
      {
        // failed to get a proof for a child, fail
        Trace("cdproof") << "...fail, no child" << std::endl;
        return false;
      }
      Trace("cdproof") << "--- add assume" << std::endl;
      // otherwise, we initialize it as an assumption
      std::vector<Node> pcargs = {c};
      std::vector<std::shared_ptr<ProofNode>> pcassume;
      pc = d_manager->mkNode(PfRule::ASSUME, pcassume, pcargs, c);
      // assumptions never fail to check
      Assert(pc != nullptr);
      d_nodes.insert(c, pc);
    }
    pchildren.push_back(pc);
  }

  // TODO: this isnt necessary if we forbid SYMM from user
  // the user may have provided SYMM of an assumption
  if (id == PfRule::SYMM)
  {
    Assert(pchildren.size() == 1);
    if (isAssumption(pchildren[0].get()))
    {
      // the step we are constructing is a (symmetric fact of an) assumption, so
      // there is no use adding it to the proof.
      return true;
    }
  }

  bool ret = true;
  // create or update it
  std::shared_ptr<ProofNode> pthis;
  if (pprev == nullptr)
  {
    Trace("cdproof") << "  new node " << expected << "..." << std::endl;
    pthis = d_manager->mkNode(id, pchildren, args, expected);
    if (pthis == nullptr)
    {
      // failed to construct the node, perhaps due to a proof checking failure
      Trace("cdproof") << "...fail, proof checking" << std::endl;
      return false;
    }
    d_nodes.insert(expected, pthis);
  }
  else
  {
    Trace("cdproof") << "  update node " << expected << "..." << std::endl;
    // update its value
    pthis = pprev;
    // We return the value of updateNode here. This means this method may return
    // false if this call failed, regardless of whether we already have a proof
    // step for expected.
    ret = d_manager->updateNode(pthis.get(), id, pchildren, args);
  }
  if (ret)
  {
    // the result of the proof node should be expected
    Assert(pthis->getResult() == expected);

    // notify new proof
    notifyNewProof(expected);
  }

  Trace("cdproof") << "...return " << ret << std::endl;
  return ret;
}

void CDProof::notifyNewProof(Node expected)
{
  // ensure SYMM proof is also linked to an existing proof, if it is an
  // assumption.
  Node symExpected = getSymmFact(expected);
  if (!symExpected.isNull())
  {
    Trace("cdproof") << "  check connect symmetry " << symExpected << std::endl;
    // if it exists, we may need to update it
    std::shared_ptr<ProofNode> pfs = getProof(symExpected);
    if (pfs != nullptr)
    {
      Trace("cdproof") << "  connect via getProofSymm method..." << std::endl;
      // call the get function with symmetry, which will do the update
      std::shared_ptr<ProofNode> pfss = getProofSymm(symExpected);
    }
    else
    {
      Trace("cdproof") << "  no connect" << std::endl;
    }
  }
}

bool CDProof::addStep(Node expected,
                      const ProofStep& step,
                      bool ensureChildren,
                      CDPOverwrite opolicy)
{
  return addStep(expected,
                 step.d_rule,
                 step.d_children,
                 step.d_args,
                 ensureChildren,
                 opolicy);
}

bool CDProof::addSteps(const ProofStepBuffer& psb,
                       bool ensureChildren,
                       CDPOverwrite opolicy)
{
  const std::vector<std::pair<Node, ProofStep>>& steps = psb.getSteps();
  for (const std::pair<Node, ProofStep>& ps : steps)
  {
    if (!addStep(ps.first, ps.second, ensureChildren, opolicy))
    {
      return false;
    }
  }
  return true;
}

bool CDProof::addProof(std::shared_ptr<ProofNode> pn,
                       CDPOverwrite opolicy,
                       bool doCopy)
{
  if (!doCopy)
  {
    // If we aren't doing a deep copy, we either store pn or link its top
    // node into the existing pointer
    Node curFact = pn->getResult();
    Trace("cdproof") << "CDProof::addProof: add proof (no copy), fact "
                     << curFact << std::endl;
    std::shared_ptr<ProofNode> cur = getProofSymm(curFact);
    if (cur == nullptr)
    {
      Trace("cdproof") << "...simple, add " << this << " since no proof of "
                       << curFact << std::endl;
      // Assert that the checker of this class agrees with (the externally
      // provided) pn. This ensures that if pn was checked by a different
      // checker than the one of the manager in this class, then it is double
      // checked here, so that this class maintains the invariant that all of
      // its nodes in d_nodes have been checked by the underlying checker.
      Assert(d_manager->getChecker() == nullptr
             || d_manager->getChecker()->check(pn.get(), curFact) == curFact);
      // just store the proof for fact
      d_nodes.insert(curFact, pn);
    }
    else if (shouldOverwrite(cur.get(), pn->getRule(), opolicy))
    {
      // We update cur to have the structure of the top node of pn. Notice that
      // the interface to update this node will ensure that the proof apf is a
      // proof of the assumption. If it does not, then pn was wrong.
      if (!d_manager->updateNode(
              cur.get(), pn->getRule(), pn->getChildren(), pn->getArguments()))
      {
        Trace("cdproof") << "...overwrite, fail" << std::endl;
        return false;
      }
      Trace("cdproof") << "...overwrite, success" << std::endl;
    }
    else
    {
      Trace("cdproof") << "...no overwrite" << std::endl;
    }
    // also need to connect via SYMM if necessary
    notifyNewProof(curFact);
    return true;
  }
  std::unordered_map<ProofNode*, bool> visited;
  std::unordered_map<ProofNode*, bool>::iterator it;
  std::vector<ProofNode*> visit;
  ProofNode* cur;
  Node curFact;
  visit.push_back(pn.get());
  bool retValue = true;
  do
  {
    cur = visit.back();
    curFact = cur->getResult();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      // visit the children
      visited[cur] = false;
      visit.push_back(cur);
      const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& c : cs)
      {
        visit.push_back(c.get());
      }
    }
    else if (!it->second)
    {
      // we always call addStep, which may or may not overwrite the
      // current step
      std::vector<Node> pexp;
      const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& c : cs)
      {
        Assert(!c->getResult().isNull());
        pexp.push_back(c->getResult());
      }
      // can ensure children at this point
      bool res = addStep(
          curFact, cur->getRule(), pexp, cur->getArguments(), true, opolicy);
      // should always succeed
      Assert(res);
      retValue = retValue && res;
      visited[cur] = true;
    }
  } while (!visit.empty());

  return retValue;
}

bool CDProof::hasStep(Node fact)
{
  std::shared_ptr<ProofNode> pf = getProof(fact);
  if (pf != nullptr && !isAssumption(pf.get()))
  {
    return true;
  }
  Node symFact = getSymmFact(fact);
  if (symFact.isNull())
  {
    return false;
  }
  pf = getProof(symFact);
  if (pf != nullptr && !isAssumption(pf.get()))
  {
    return true;
  }
  return false;
}

ProofNodeManager* CDProof::getManager() const { return d_manager; }

bool CDProof::shouldOverwrite(ProofNode* pn, PfRule newId, CDPOverwrite opol)
{
  Assert(pn != nullptr);
  // we overwrite only if opol is CDPOverwrite::ALWAYS, or if
  // opol is CDPOverwrite::ASSUME_ONLY and the previously
  // provided proof pn was an assumption and the currently provided step is not
  return opol == CDPOverwrite::ALWAYS
         || (opol == CDPOverwrite::ASSUME_ONLY && isAssumption(pn)
             && newId != PfRule::ASSUME);
}

bool CDProof::isAssumption(ProofNode* pn)
{
  PfRule rule = pn->getRule();
  if (rule == PfRule::ASSUME)
  {
    return true;
  }
  else if (rule == PfRule::SYMM)
  {
    const std::vector<std::shared_ptr<ProofNode>>& pc = pn->getChildren();
    Assert(pc.size() == 1);
    return pc[0]->getRule() == PfRule::ASSUME;
  }
  return false;
}

bool CDProof::isSame(TNode f, TNode g)
{
  if (f == g)
  {
    return true;
  }
  Kind fk = f.getKind();
  Kind gk = g.getKind();
  if (fk == EQUAL && gk == EQUAL && f[0] == g[1] && f[1] == g[0])
  {
    // symmetric equality
    return true;
  }
  if (fk == NOT && gk == NOT && f[0][0] == g[0][1] && f[0][1] == g[0][0])
  {
    // symmetric disequality
    return true;
  }
  return false;
}

Node CDProof::getSymmFact(TNode f)
{
  bool polarity = f.getKind() != NOT;
  TNode fatom = polarity ? f : f[0];
  if (fatom.getKind() != EQUAL || fatom[0] == fatom[1])
  {
    return Node::null();
  }
  Node symFact = fatom[1].eqNode(fatom[0]);
  return polarity ? symFact : symFact.notNode();
}

Node CDProof::factorReorderElimDoubleNeg(Node n, CDProof* p)
{
  Trace("proof-norm")
      << "PropEngine::factorReorderElimDoubleNeg: normalize node: " << n
      << "\n";
  if (n.getKind() != kind::OR)
  {
    return CDProof::elimDoubleNegLit(n, p);
  }
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> children{n.begin(), n.end()};
  std::vector<Node> childrenEqs;
  // eliminate double neg for each lit. Do it first because it may expose
  // duplicates
  bool hasDoubleNeg = false;
  for (unsigned i = 0; i < children.size(); ++i)
  {
    if (children[i].getKind() == kind::NOT
        && children[i][0].getKind() == kind::NOT)
    {
      hasDoubleNeg = true;
      childrenEqs.push_back(children[i].eqNode(children[i][0][0]));
      if (p)
      {
        p->addStep(childrenEqs.back(),
                   PfRule::MACRO_SR_PRED_INTRO,
                   {},
                   {childrenEqs.back()});
      }
      // update child
      children[i] = children[i][0][0];
    }
    else
    {
      childrenEqs.push_back(children[i].eqNode(children[i]));
      if (p)
      {
        p->addStep(childrenEqs.back(), PfRule::REFL, {}, {children[i]});
      }
    }
  }
  if (hasDoubleNeg)
  {
    Node oldn = n;
    n = nm->mkNode(kind::OR, children);
    Trace("proof-norm")
        << "PropEngine::factorReorderElimDoubleNeg: eliminate double negs: "
        << oldn << " ==> " << n << "\n";
    if (p)
    {
      // Create a congruence step to justify replacement of each doubly negated
      // literal. This is done to avoid having to use MACRO_SR_PRED_TRANSFORM
      // from the old clause to the new one, which, under the standard rewriter,
      // may not hold. An example is
      //
      //   ---------------------------------------------------------------------
      //   (or (or (not x2) x1 x2) (not (not x2))) = (or (or (not x2) x1 x2) x2)
      //
      // which fails due to factoring not happening after flattening.
      //
      // Using congruence only the
      //
      //  ------------------ MACRO_SR_PRED_INTRO
      //  (not (not t)) = t
      //
      // steps are added, which, since double negation is eliminated in a
      // pre-rewrite in the Boolean rewriter, will always hold under the
      // standard rewriter.
      Node congEq = oldn.eqNode(n);
      p->addStep(congEq,
                 PfRule::CONG,
                 childrenEqs,
                 {ProofRuleChecker::mkKindNode(kind::OR)});
      // add an equality resolution step to derive normalize clause
      p->addStep(n, PfRule::EQ_RESOLVE, {oldn, congEq}, {});
    }
  }
  children.clear();
  // remove duplicates while keeping the order of children
  std::unordered_set<TNode, TNodeHashFunction> clauseSet;
  unsigned size = n.getNumChildren();
  for (unsigned i = 0; i < size; ++i)
  {
    if (clauseSet.count(n[i]))
    {
      continue;
    }
    children.push_back(n[i]);
    clauseSet.insert(n[i]);
  }
  // if factoring changed
  if (children.size() < size)
  {
    Node factored = children.empty()
                        ? nm->mkConst<bool>(false)
                        : children.size() == 1 ? children[0]
                                               : nm->mkNode(kind::OR, children);
    // don't overwrite what already has a proof step to avoid cycles
    if (p)
    {
      p->addStep(
          factored, PfRule::FACTORING, {n}, {}, false, CDPOverwrite::NEVER);
    }
    n = factored;
  }
  Trace("proof-norm") << "factorReorderElimDoubleNeg: factored node: " << n
                          << ", factored children " << children << "\n";
  // nothing to order
  if (children.size() < 2)
  {
    return n;
  }
  // order
  std::sort(children.begin(), children.end());
  Trace("proof-norm") << "factorReorderElimDoubleNeg: sorted children: "
                          << children << "\n";
  Node ordered = nm->mkNode(kind::OR, children);
  // if ordering changed
  if (p && ordered != n)
  {
    // don't overwrite what already has a proof step to avoid cycles
    p->addStep(ordered,
               PfRule::REORDERING,
               {n},
               {ordered},
               false,
               CDPOverwrite::NEVER);
  }
  Trace("proof-norm") << "factorReorderElimDoubleNeg: ordered node: "
                          << ordered << "\n";
  return ordered;
}

Node CDProof::elimDoubleNegLit(Node n, CDProof* p)
{
  // eliminate double neg
  if (n.getKind() == kind::NOT && n[0].getKind() == kind::NOT)
  {
    Trace("proof-norm")
        << "PropEngine::elimDoubleNegLit: eliminate double neg: " << n << ", "
        << n[0][0] << "\n";
    p->addStep(n[0][0], PfRule::MACRO_SR_PRED_TRANSFORM, {n}, {n[0][0]});
    return n[0][0];
  }
  Trace("proof-norm") << "PropEngine::elimDoubleNegLit: nothing to do\n";
  return n;
}

std::string CDProof::identify() const { return d_name; }

}  // namespace CVC4

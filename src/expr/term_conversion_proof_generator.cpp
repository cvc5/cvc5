/*********************                                                        */
/*! \file term_conversion_proof_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term conversion proof generator utility
 **/

#include "expr/term_conversion_proof_generator.h"

using namespace CVC4::kind;

namespace CVC4 {

TConvProofGenerator::TConvProofGenerator(ProofNodeManager* pnm,
                                         context::Context* c)
    : d_proof(pnm, nullptr, c), d_rewriteMap(c ? c : &d_context)
{
}

TConvProofGenerator::~TConvProofGenerator() {}

void TConvProofGenerator::addRewriteStep(Node t, Node s, ProofGenerator* pg)
{
  // should not rewrite term more than once
  Assert(!hasRewriteStep(t));
  Node eq = t.eqNode(s);
  d_proof.addLazyStep(eq, pg);
  d_rewriteMap[t] = s;
}

void TConvProofGenerator::addRewriteStep(Node t, Node s, ProofStep ps)
{
  // should not rewrite term more than once
  Assert(!hasRewriteStep(t));
  Node eq = t.eqNode(s);
  d_proof.addStep(eq, ps);
  d_rewriteMap[t] = s;
}

void TConvProofGenerator::addRewriteStep(Node t,
                                         Node s,
                                         PfRule id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args)
{
  // should not rewrite term more than once
  Assert(!hasRewriteStep(t));
  Node eq = t.eqNode(s);
  d_proof.addStep(eq, id, children, args);
  d_rewriteMap[t] = s;
}

bool TConvProofGenerator::hasRewriteStep(Node t) const
{
  return !getRewriteStep(t).isNull();
}

std::shared_ptr<ProofNode> TConvProofGenerator::getProofFor(Node f)
{
  Trace("tconv-pf-gen") << "TConvProofGenerator::getProofFor: " << f
                        << std::endl;
  if (f.getKind() != EQUAL)
  {
    Trace("tconv-pf-gen") << "... fail, non-equality" << std::endl;
    Assert(false);
    return nullptr;
  }
  std::shared_ptr<ProofNode> pf = getProofForRewriting(f[0]);
  if (pf == nullptr)
  {
    // failed to generate proof
    Trace("tconv-pf-gen") << "...failed to get proof" << std::endl;
    Assert(false);
    return pf;
  }
  if (pf->getResult() != f)
  {
    Trace("tconv-pf-gen") << "...failed, mismatch: returned proof concludes "
                          << pf->getResult() << std::endl;
    Assert(false);
    return nullptr;
  }
  Trace("tconv-pf-gen") << "... success" << std::endl;
  return pf;
}

std::shared_ptr<ProofNode> TConvProofGenerator::getProofForRewriting(Node t)
{
  // we use the existing proofs
  PRefProofGenerator prg(&d_proof);
  LazyCDProof pf(d_proof.getManager(), &prg);
  NodeManager* nm = NodeManager::currentNM();
  // Invariant: if visited[t] = s or rewritten[t] = s and t,s are distinct,
  // then pf is able to generate a proof of t=s.
  // the final rewritten form of terms
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  // the rewritten form of terms we have processed so far
  std::unordered_map<TNode, Node, TNodeHashFunction> rewritten;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator itr;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(t);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
      // did we rewrite the current node (possibly at pre-rewrite)?
      Node rcur = getRewriteStep(cur);
      if (!rcur.isNull())
      {
        // d_proof should have a proof of cur = rcur. Hence there is nothing
        // to do here, as pf will reference prg to get the proof from d_proof.
        // It may be the case that rcur also rewrites, thus we cannot assign
        // the final rewritten form for cur yet. Instead we revisit cur after
        // finishing visiting rcur.
        rewritten[cur] = rcur;
        visit.push_back(cur);
        visit.push_back(rcur);
      }
      else
      {
        visit.push_back(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second.isNull())
    {
      itr = rewritten.find(cur);
      if (itr != rewritten.end())
      {
        // if it was rewritten, check the status of the rewritten node,
        // which should be finished now
        Node rcur = itr->second;
        Assert(cur != rcur);
        // the final rewritten form of cur is the final form of rcur
        Node rcurFinal = visited[rcur];
        if (rcurFinal != rcur)
        {
          // must connect via TRANS
          std::vector<Node> pfChildren;
          pfChildren.push_back(cur.eqNode(rcur));
          pfChildren.push_back(rcur.eqNode(rcurFinal));
          Node result = cur.eqNode(rcurFinal);
          pf.addStep(result, PfRule::TRANS, pfChildren, {});
        }
        visited[cur] = rcurFinal;
      }
      else
      {
        Node ret = cur;
        bool childChanged = false;
        std::vector<Node> children;
        if (cur.getMetaKind() == metakind::PARAMETERIZED)
        {
          children.push_back(cur.getOperator());
        }
        for (const Node& cn : cur)
        {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          childChanged = childChanged || cn != it->second;
          children.push_back(it->second);
        }
        if (childChanged)
        {
          ret = nm->mkNode(cur.getKind(), children);
          rewritten[cur] = ret;
          // congruence to show (cur = ret)
          std::vector<Node> pfChildren;
          for (size_t i = 0, size = cur.getNumChildren(); i < size; i++)
          {
            if (cur[i] == ret[i])
            {
              // ensure REFL proof for unchanged children
              pf.addStep(cur[i].eqNode(cur[i]), PfRule::REFL, {}, {cur[i]});
            }
            pfChildren.push_back(cur[i].eqNode(ret[i]));
          }
          std::vector<Node> pfArgs;
          Kind k = cur.getKind();
          if (kind::metaKindOf(k) == kind::metakind::PARAMETERIZED)
          {
            pfArgs.push_back(cur.getOperator());
          }
          else
          {
            pfArgs.push_back(nm->operatorOf(k));
          }
          Node result = cur.eqNode(ret);
          pf.addStep(result, PfRule::CONG, pfChildren, pfArgs);
        }
        // did we rewrite ret (at post-rewrite)?
        Node rret = getRewriteStep(ret);
        if (!rret.isNull())
        {
          if (cur != ret)
          {
            visit.push_back(cur);
          }
          // d_proof should have a proof of ret = rret, hence nothing to do
          // here, for the same reasons as above. It also may be the case that
          // rret rewrites, hence we must revisit ret.
          rewritten[ret] = rret;
          visit.push_back(ret);
          visit.push_back(rret);
        }
        else
        {
          // it is final
          visited[cur] = ret;
        }
      }
    }
  } while (!visit.empty());
  Assert(visited.find(t) != visited.end());
  Assert(!visited.find(t)->second.isNull());
  // make the overall proof
  Node teq = t.eqNode(visited[t]);
  return pf.mkProof(teq);
}

Node TConvProofGenerator::getRewriteStep(Node t) const
{
  NodeNodeMap::const_iterator it = d_rewriteMap.find(t);
  if (it == d_rewriteMap.end())
  {
    return Node::null();
  }
  return (*it).second;
}
std::string TConvProofGenerator::identify() const
{
  return "TConvProofGenerator";
}

}  // namespace CVC4

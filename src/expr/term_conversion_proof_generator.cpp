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

std::ostream& operator<<(std::ostream& out, TConvPolicy tcpol)
{
  switch (tcpol)
  {
    case TConvPolicy::FIXPOINT: out << "FIXPOINT"; break;
    case TConvPolicy::ONCE: out << "ONCE"; break;
    default: out << "TConvPolicy:unknown"; break;
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, TConvCachePolicy tcpol)
{
  switch (tcpol)
  {
    case TConvCachePolicy::STATIC: out << "STATIC"; break;
    case TConvCachePolicy::DYNAMIC: out << "DYNAMIC"; break;
    case TConvCachePolicy::NEVER: out << "NEVER"; break;
    default: out << "TConvCachePolicy:unknown"; break;
  }
  return out;
}

TConvProofGenerator::TConvProofGenerator(ProofNodeManager* pnm,
                                         context::Context* c,
                                         TConvPolicy pol,
                                         TConvCachePolicy cpol,
                                         std::string name)
    : d_proof(pnm, nullptr, c, name + "::LazyCDProof"),
      d_rewriteMap(c ? c : &d_context),
      d_policy(pol),
      d_cpolicy(cpol),
      d_name(name)
{
}

TConvProofGenerator::~TConvProofGenerator() {}

void TConvProofGenerator::addRewriteStep(Node t, Node s, ProofGenerator* pg)
{
  Node eq = registerRewriteStep(t, s);
  if (!eq.isNull())
  {
    d_proof.addLazyStep(eq, pg);
  }
}

void TConvProofGenerator::addRewriteStep(Node t, Node s, ProofStep ps)
{
  Node eq = registerRewriteStep(t, s);
  if (!eq.isNull())
  {
    d_proof.addStep(eq, ps);
  }
}

void TConvProofGenerator::addRewriteStep(Node t,
                                         Node s,
                                         PfRule id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args)
{
  Node eq = registerRewriteStep(t, s);
  if (!eq.isNull())
  {
    d_proof.addStep(eq, id, children, args);
  }
}

bool TConvProofGenerator::hasRewriteStep(Node t) const
{
  return !getRewriteStep(t).isNull();
}

Node TConvProofGenerator::registerRewriteStep(Node t, Node s)
{
  if (t == s)
  {
    return Node::null();
  }
  // should not rewrite term to two different things
  if (!getRewriteStep(t).isNull())
  {
    Assert(getRewriteStep(t) == s);
    return Node::null();
  }
  d_rewriteMap[t] = s;
  if (d_cpolicy == TConvCachePolicy::DYNAMIC)
  {
    // clear the cache
    d_cache.clear();
  }
  return t.eqNode(s);
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
  // we use the existing proofs
  LazyCDProof lpf(
      d_proof.getManager(), &d_proof, nullptr, d_name + "::LazyCDProof");
  Node conc = getProofForRewriting(f[0], lpf);
  if (conc != f)
  {
    Trace("tconv-pf-gen") << "...failed, mismatch: returned proof concludes "
                          << conc << ", expected " << f << std::endl;
    Assert(false);
    return nullptr;
  }
  Trace("tconv-pf-gen") << "... success" << std::endl;
  return lpf.getProofFor(f);
}

Node TConvProofGenerator::getProofForRewriting(Node t, LazyCDProof& pf)
{
  NodeManager* nm = NodeManager::currentNM();
  // Invariant: if visited[t] = s or rewritten[t] = s and t,s are distinct,
  // then pf is able to generate a proof of t=s.
  // the final rewritten form of terms
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  // the rewritten form of terms we have processed so far
  std::unordered_map<TNode, Node, TNodeHashFunction> rewritten;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator itr;
  std::map<Node, std::shared_ptr<ProofNode> >::iterator itc;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(t);
  do
  {
    cur = visit.back();
    visit.pop_back();
    // has the proof for cur been cached?
    itc = d_cache.find(cur);
    if (itc != d_cache.end())
    {
      Node res = itc->second->getResult();
      Assert(res.getKind() == EQUAL);
      visited[cur] = res[1];
      pf.addProof(itc->second);
      continue;
    }
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = Node::null();
      // did we rewrite the current node (possibly at pre-rewrite)?
      Node rcur = getRewriteStep(cur);
      if (!rcur.isNull())
      {
        // d_proof has a proof of cur = rcur. Hence there is nothing
        // to do here, as pf will reference d_proof to get its proof.
        if (d_policy == TConvPolicy::FIXPOINT)
        {
          // It may be the case that rcur also rewrites, thus we cannot assign
          // the final rewritten form for cur yet. Instead we revisit cur after
          // finishing visiting rcur.
          rewritten[cur] = rcur;
          visit.push_back(cur);
          visit.push_back(rcur);
        }
        else
        {
          Assert(d_policy == TConvPolicy::ONCE);
          // not rewriting again, rcur is final
          visited[cur] = rcur;
          doCache(cur, rcur, pf);
        }
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
        // only can generate partially rewritten nodes when rewrite again is
        // true.
        Assert(d_policy != TConvPolicy::ONCE);
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
        doCache(cur, rcurFinal, pf);
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
        Node rret;
        // only if not ONCE policy, which only does pre-rewrite
        if (d_policy != TConvPolicy::ONCE)
        {
          rret = getRewriteStep(ret);
        }
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
          doCache(cur, ret, pf);
        }
      }
    }
  } while (!visit.empty());
  Assert(visited.find(t) != visited.end());
  Assert(!visited.find(t)->second.isNull());
  // return the conclusion of the overall proof
  return t.eqNode(visited[t]);
}

void TConvProofGenerator::doCache(Node cur, Node r, LazyCDProof& pf)
{
  if (d_cpolicy != TConvCachePolicy::NEVER)
  {
    Node eq = cur.eqNode(r);
    d_cache[cur] = pf.getProofFor(eq);
  }
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
std::string TConvProofGenerator::identify() const { return d_name; }

}  // namespace CVC4

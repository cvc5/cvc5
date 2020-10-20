/*********************                                                        */
/*! \file term_conversion_proof_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term conversion proof generator utility
 **/

#include "expr/term_conversion_proof_generator.h"

#include "expr/term_context_stack.h"

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
                                         std::string name,
                                         TermContext* tccb,
                                         bool rewriteOps)
    : d_proof(pnm, nullptr, c, name + "::LazyCDProof"),
      d_rewriteMap(c ? c : &d_context),
      d_policy(pol),
      d_cpolicy(cpol),
      d_name(name),
      d_tcontext(tccb),
      d_rewriteOps(rewriteOps)
{
}

TConvProofGenerator::~TConvProofGenerator() {}

void TConvProofGenerator::addRewriteStep(
    Node t, Node s, ProofGenerator* pg, bool isClosed, uint32_t tctx)
{
  Node eq = registerRewriteStep(t, s, tctx);
  if (!eq.isNull())
  {
    d_proof.addLazyStep(eq, pg, isClosed);
  }
}

void TConvProofGenerator::addRewriteStep(Node t,
                                         Node s,
                                         ProofStep ps,
                                         uint32_t tctx)
{
  Node eq = registerRewriteStep(t, s, tctx);
  if (!eq.isNull())
  {
    AlwaysAssert(ps.d_rule != PfRule::ASSUME);
    d_proof.addStep(eq, ps);
  }
}

void TConvProofGenerator::addRewriteStep(Node t,
                                         Node s,
                                         PfRule id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args,
                                         uint32_t tctx)
{
  Node eq = registerRewriteStep(t, s, tctx);
  if (!eq.isNull())
  {
    AlwaysAssert(id != PfRule::ASSUME);
    d_proof.addStep(eq, id, children, args);
  }
}

bool TConvProofGenerator::hasRewriteStep(Node t, uint32_t tctx) const
{
  return !getRewriteStep(t, tctx).isNull();
}

Node TConvProofGenerator::getRewriteStep(Node t, uint32_t tctx) const
{
  Node thash = t;
  if (d_tcontext != nullptr)
  {
    thash = TCtxNode::computeNodeHash(t, tctx);
  }
  return getRewriteStepInternal(thash);
}

Node TConvProofGenerator::registerRewriteStep(Node t, Node s, uint32_t tctx)
{
  if (t == s)
  {
    return Node::null();
  }
  Node thash = t;
  if (d_tcontext != nullptr)
  {
    thash = TCtxNode::computeNodeHash(t, tctx);
  }
  else
  {
    // don't use term context ids if not using term context
    Assert(tctx == 0);
  }
  // should not rewrite term to two different things
  if (!getRewriteStepInternal(thash).isNull())
  {
    Assert(getRewriteStepInternal(thash) == s);
    return Node::null();
  }
  d_rewriteMap[thash] = s;
  if (d_cpolicy == TConvCachePolicy::DYNAMIC)
  {
    // clear the cache
    d_cache.clear();
  }
  return t.eqNode(s);
}

std::shared_ptr<ProofNode> TConvProofGenerator::getProofFor(Node f)
{
  Trace("tconv-pf-gen") << "TConvProofGenerator::getProofFor: " << identify()
                        << ": " << f << std::endl;
  if (f.getKind() != EQUAL)
  {
    std::stringstream serr;
    serr << "TConvProofGenerator::getProofFor: " << identify()
         << ": fail, non-equality " << f;
    Unhandled() << serr.str();
    Trace("tconv-pf-gen") << serr.str() << std::endl;
    return nullptr;
  }
  // we use the existing proofs
  LazyCDProof lpf(
      d_proof.getManager(), &d_proof, nullptr, d_name + "::LazyCDProof");
  if (f[0] == f[1])
  {
    // assertion failure in debug
    Assert(false) << "TConvProofGenerator::getProofFor: " << identify()
                  << ": don't ask for trivial proofs";
    lpf.addStep(f, PfRule::REFL, {}, {f[0]});
  }
  else
  {
    Node conc = getProofForRewriting(f[0], lpf, d_tcontext);
    if (conc != f)
    {
      Assert(conc.getKind() == EQUAL && conc[0] == f[0]);
      std::stringstream serr;
      serr << "TConvProofGenerator::getProofFor: " << toStringDebug()
           << ": failed, mismatch (see -t tconv-pf-gen-debug for details)"
           << std::endl;
      serr << "                  source: " << f[0] << std::endl;
      serr << "expected after rewriting: " << f[1] << std::endl;
      serr << "  actual after rewriting: " << conc[1] << std::endl;

      if (Trace.isOn("tconv-pf-gen-debug"))
      {
        Trace("tconv-pf-gen-debug") << "Printing rewrite steps..." << std::endl;
        serr << "Rewrite steps: " << std::endl;
        for (NodeNodeMap::const_iterator it = d_rewriteMap.begin();
             it != d_rewriteMap.end();
             ++it)
        {
          serr << (*it).first << " -> " << (*it).second << std::endl;
        }
      }
      Unhandled() << serr.str();
      return nullptr;
    }
  }
  std::shared_ptr<ProofNode> pfn = lpf.getProofFor(f);
  Trace("tconv-pf-gen") << "... success" << std::endl;
  Assert (pfn!=nullptr);
  Trace("tconv-pf-gen-debug") << "... proof is " << *pfn << std::endl;
  return pfn;
}

Node TConvProofGenerator::getProofForRewriting(Node t,
                                               LazyCDProof& pf,
                                               TermContext* tctx)
{
  NodeManager* nm = NodeManager::currentNM();
  // Invariant: if visited[hash(t)] = s or rewritten[hash(t)] = s and t,s are
  // distinct, then pf is able to generate a proof of t=s. We must
  // Node in the domains of the maps below due to hashing creating new (SEXPR)
  // nodes.

  // the final rewritten form of terms
  std::unordered_map<Node, Node, TNodeHashFunction> visited;
  // the rewritten form of terms we have processed so far
  std::unordered_map<Node, Node, TNodeHashFunction> rewritten;
  std::unordered_map<Node, Node, TNodeHashFunction>::iterator it;
  std::unordered_map<Node, Node, TNodeHashFunction>::iterator itr;
  std::map<Node, std::shared_ptr<ProofNode> >::iterator itc;
  Trace("tconv-pf-gen-rewrite")
      << "TConvProofGenerator::getProofForRewriting: " << toStringDebug()
      << std::endl;
  Trace("tconv-pf-gen-rewrite") << "Input: " << t << std::endl;
  // if provided, we use term context for cache
  std::shared_ptr<TCtxStack> visitctx;
  // otherwise, visit is used if we don't have a term context
  std::vector<TNode> visit;
  Node tinitialHash;
  if (tctx != nullptr)
  {
    visitctx = std::make_shared<TCtxStack>(tctx);
    visitctx->pushInitial(t);
    tinitialHash = TCtxNode::computeNodeHash(t, tctx->initialValue());
  }
  else
  {
    visit.push_back(t);
    tinitialHash = t;
  }
  Node cur;
  uint32_t curCVal = 0;
  Node curHash;
  do
  {
    // pop the top element
    if (tctx != nullptr)
    {
      std::pair<Node, uint32_t> curPair = visitctx->getCurrent();
      cur = curPair.first;
      curCVal = curPair.second;
      curHash = TCtxNode::computeNodeHash(cur, curCVal);
      visitctx->pop();
    }
    else
    {
      cur = visit.back();
      curHash = cur;
      visit.pop_back();
    }
    Trace("tconv-pf-gen-rewrite") << "* visit : " << curHash << std::endl;
    // has the proof for cur been cached?
    itc = d_cache.find(curHash);
    if (itc != d_cache.end())
    {
      Node res = itc->second->getResult();
      Assert(res.getKind() == EQUAL);
      Assert(!res[1].isNull());
      visited[curHash] = res[1];
      pf.addProof(itc->second);
      continue;
    }
    it = visited.find(curHash);
    if (it == visited.end())
    {
      Trace("tconv-pf-gen-rewrite") << "- previsit" << std::endl;
      visited[curHash] = Node::null();
      // did we rewrite the current node (possibly at pre-rewrite)?
      Node rcur = getRewriteStepInternal(curHash);
      if (!rcur.isNull())
      {
        Trace("tconv-pf-gen-rewrite")
            << "*** " << curHash << " prerewrites to " << rcur << std::endl;
        // d_proof has a proof of cur = rcur. Hence there is nothing
        // to do here, as pf will reference d_proof to get its proof.
        if (d_policy == TConvPolicy::FIXPOINT)
        {
          // It may be the case that rcur also rewrites, thus we cannot assign
          // the final rewritten form for cur yet. Instead we revisit cur after
          // finishing visiting rcur.
          rewritten[curHash] = rcur;
          if (tctx != nullptr)
          {
            visitctx->push(cur, curCVal);
            visitctx->push(rcur, curCVal);
          }
          else
          {
            visit.push_back(cur);
            visit.push_back(rcur);
          }
        }
        else
        {
          Assert(d_policy == TConvPolicy::ONCE);
          Trace("tconv-pf-gen-rewrite") << "-> (once, prewrite) " << curHash
                                        << " = " << rcur << std::endl;
          // not rewriting again, rcur is final
          Assert(!rcur.isNull());
          visited[curHash] = rcur;
          doCache(curHash, cur, rcur, pf);
        }
      }
      else if (tctx != nullptr)
      {
        visitctx->push(cur, curCVal);
        // visit operator if apply uf
        if (d_rewriteOps && cur.getKind() == APPLY_UF)
        {
          visitctx->pushOp(cur, curCVal);
        }
        visitctx->pushChildren(cur, curCVal);
      }
      else
      {
        visit.push_back(cur);
        // visit operator if apply uf
        if (d_rewriteOps && cur.getKind() == APPLY_UF)
        {
          visit.push_back(cur.getOperator());
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second.isNull())
    {
      itr = rewritten.find(curHash);
      if (itr != rewritten.end())
      {
        // only can generate partially rewritten nodes when rewrite again is
        // true.
        Assert(d_policy != TConvPolicy::ONCE);
        // if it was rewritten, check the status of the rewritten node,
        // which should be finished now
        Node rcur = itr->second;
        Trace("tconv-pf-gen-rewrite")
            << "- postvisit, previously rewritten to " << rcur << std::endl;
        Node rcurHash = rcur;
        if (tctx != nullptr)
        {
          rcurHash = TCtxNode::computeNodeHash(rcur, curCVal);
        }
        Assert(cur != rcur);
        // the final rewritten form of cur is the final form of rcur
        Node rcurFinal = visited[rcurHash];
        Assert(!rcurFinal.isNull());
        if (rcurFinal != rcur)
        {
          // must connect via TRANS
          std::vector<Node> pfChildren;
          pfChildren.push_back(cur.eqNode(rcur));
          pfChildren.push_back(rcur.eqNode(rcurFinal));
          Node result = cur.eqNode(rcurFinal);
          pf.addStep(result, PfRule::TRANS, pfChildren, {});
        }
        Trace("tconv-pf-gen-rewrite")
            << "-> (rewritten postrewrite) " << curHash << " = " << rcurFinal
            << std::endl;
        visited[curHash] = rcurFinal;
        doCache(curHash, cur, rcurFinal, pf);
      }
      else
      {
        Trace("tconv-pf-gen-rewrite") << "- postvisit" << std::endl;
        Node ret = cur;
        Node retHash = curHash;
        bool childChanged = false;
        std::vector<Node> children;
        Kind ck = cur.getKind();
        if (d_rewriteOps && ck == APPLY_UF)
        {
          // the operator of APPLY_UF is visited
          Node cop = cur.getOperator();
          if (tctx != nullptr)
          {
            uint32_t coval = tctx->computeValueOp(cur, curCVal);
            Node coHash = TCtxNode::computeNodeHash(cop, coval);
            it = visited.find(coHash);
          }
          else
          {
            it = visited.find(cop);
          }
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          childChanged = childChanged || cop != it->second;
          children.push_back(it->second);
        }
        else if (cur.getMetaKind() == metakind::PARAMETERIZED)
        {
          // all other parametrized operators are unchanged
          children.push_back(cur.getOperator());
        }
        // get the results of the children
        if (tctx != nullptr)
        {
          for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
          {
            Node cn = cur[i];
            uint32_t cnval = tctx->computeValue(cur, curCVal, i);
            Node cnHash = TCtxNode::computeNodeHash(cn, cnval);
            it = visited.find(cnHash);
            Assert(it != visited.end());
            Assert(!it->second.isNull());
            childChanged = childChanged || cn != it->second;
            children.push_back(it->second);
          }
        }
        else
        {
          // can use simple loop if not term-context-sensitive
          for (const Node& cn : cur)
          {
            it = visited.find(cn);
            Assert(it != visited.end());
            Assert(!it->second.isNull());
            childChanged = childChanged || cn != it->second;
            children.push_back(it->second);
          }
        }
        if (childChanged)
        {
          ret = nm->mkNode(ck, children);
          rewritten[curHash] = ret;
          // congruence to show (cur = ret)
          PfRule congRule = PfRule::CONG;
          std::vector<Node> pfChildren;
          std::vector<Node> pfArgs;
          pfArgs.push_back(ProofRuleChecker::mkKindNode(ck));
          if (ck == APPLY_UF && children[0] != cur.getOperator())
          {
            // use HO_CONG if the operator changed
            congRule = PfRule::HO_CONG;
            pfChildren.push_back(cur.getOperator().eqNode(children[0]));
          }
          else if (kind::metaKindOf(ck) == kind::metakind::PARAMETERIZED)
          {
            pfArgs.push_back(cur.getOperator());
          }
          for (size_t i = 0, size = cur.getNumChildren(); i < size; i++)
          {
            if (cur[i] == ret[i])
            {
              // ensure REFL proof for unchanged children
              pf.addStep(cur[i].eqNode(cur[i]), PfRule::REFL, {}, {cur[i]});
            }
            pfChildren.push_back(cur[i].eqNode(ret[i]));
          }
          Node result = cur.eqNode(ret);
          pf.addStep(result, congRule, pfChildren, pfArgs);
          // must update the hash
          retHash = ret;
          if (tctx != nullptr)
          {
            retHash = TCtxNode::computeNodeHash(ret, curCVal);
          }
        }
        else if (tctx != nullptr)
        {
          // now we need the hash
          retHash = TCtxNode::computeNodeHash(cur, curCVal);
        }
        // did we rewrite ret (at post-rewrite)?
        Node rret;
        // only if not ONCE policy, which only does pre-rewrite
        if (d_policy != TConvPolicy::ONCE)
        {
          rret = getRewriteStepInternal(retHash);
        }
        if (!rret.isNull())
        {
          Trace("tconv-pf-gen-rewrite")
              << "*** " << retHash << " postrewrites to " << rret << std::endl;
          // d_proof should have a proof of ret = rret, hence nothing to do
          // here, for the same reasons as above. It also may be the case that
          // rret rewrites, hence we must revisit ret.
          rewritten[retHash] = rret;
          if (tctx != nullptr)
          {
            if (cur != ret)
            {
              visitctx->push(cur, curCVal);
            }
            visitctx->push(ret, curCVal);
            visitctx->push(rret, curCVal);
          }
          else
          {
            if (cur != ret)
            {
              visit.push_back(cur);
            }
            visit.push_back(ret);
            visit.push_back(rret);
          }
        }
        else
        {
          Trace("tconv-pf-gen-rewrite")
              << "-> (postrewrite) " << curHash << " = " << ret << std::endl;
          // it is final
          Assert(!ret.isNull());
          visited[curHash] = ret;
          doCache(curHash, cur, ret, pf);
        }
      }
    }
    else
    {
      Trace("tconv-pf-gen-rewrite") << "- already visited" << std::endl;
    }
  } while (!(tctx != nullptr ? visitctx->empty() : visit.empty()));
  Assert(visited.find(tinitialHash) != visited.end());
  Assert(!visited.find(tinitialHash)->second.isNull());
  Trace("tconv-pf-gen-rewrite")
      << "...finished, return " << visited[tinitialHash] << std::endl;
  // return the conclusion of the overall proof
  return t.eqNode(visited[tinitialHash]);
}

void TConvProofGenerator::doCache(Node curHash,
                                  Node cur,
                                  Node r,
                                  LazyCDProof& pf)
{
  if (d_cpolicy != TConvCachePolicy::NEVER)
  {
    Node eq = cur.eqNode(r);
    d_cache[curHash] = pf.getProofFor(eq);
  }
}

Node TConvProofGenerator::getRewriteStepInternal(Node t) const
{
  NodeNodeMap::const_iterator it = d_rewriteMap.find(t);
  if (it == d_rewriteMap.end())
  {
    return Node::null();
  }
  return (*it).second;
}
std::string TConvProofGenerator::identify() const { return d_name; }

std::string TConvProofGenerator::toStringDebug() const
{
  std::stringstream ss;
  ss << identify() << " (policy=" << d_policy << ", cache policy=" << d_cpolicy
     << (d_tcontext != nullptr ? ", term-context-sensitive" : "") << ")";
  return ss.str();
}

}  // namespace CVC4

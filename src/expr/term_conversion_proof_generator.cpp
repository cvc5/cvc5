/*********************                                                        */
/*! \file term_conversion_proof_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term conversion proof generator utility
 **/

#include "expr/term_conversion_proof_generator.h"

using namespace CVC4::kind;

namespace CVC4 {

TermConversionProofGenerator::TermConversionProofGenerator(ProofNodeManager* pnm,
            context::Context* c) : d_proof(pnm, nullptr, c), d_rewriteMap(c ? c : &d_context)
{
}

TermConversionProofGenerator::~TermConversionProofGenerator()
{
}

void TermConversionProofGenerator::addRewriteStep(Node t, Node s, ProofGenerator * pg)
{
  Assert (getRewriteStep(t).isNull());
  Node eq = t.eqNode(s);
  d_proof.addLazyStep(eq,pg);
}

void TermConversionProofGenerator::addRewriteStep(Node t, Node s, ProofStep ps)
{
  Assert (getRewriteStep(t).isNull());
  Node eq = t.eqNode(s);
  d_proof.addStep(eq,ps);
}

std::shared_ptr<ProofNode> TermConversionProofGenerator::getProofFor(Node f)
{
  Trace("tconv-pf-gen") << "TermConversionProofGenerator::getProofFor: " << f << std::endl;
  if (f.getKind()!=EQUAL)
  {
    Trace("tconv-pf-gen") << "... fail, non-equality" << std::endl;
    Assert (false);
    return nullptr;
  }
  std::shared_ptr<ProofNode> pf = getProofForRewriting(f[0]);
  if (pf==nullptr)
  {
    // failed to generate proof
    Trace("tconv-pf-gen") << "...failed to get proof" << std::endl;
    Assert (false);
    return pf;
  }
  if (pf->getResult()!=f)
  {
    Trace("tconv-pf-gen") << "...failed, mismatch: returned proof concludes " << pf->getResult() << std::endl;
    Assert (false);
    return nullptr;
  }
  Trace("tconv-pf-gen") << "... success" << std::endl;
  return pf;
}

std::shared_ptr<ProofNode> TermConversionProofGenerator::getProofForRewriting(Node t)
{
  // we use the existing proofs
  PRefProofGenerator prg(&d_proof);
  LazyCDProof pf(d_proof.getManager(), &prg);
  NodeManager * nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction> rewritten;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
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
      // did we rewrite the current node (possibly at prerewrite)?
      Node rcur = getRewriteStep(cur);
      if (!rcur.isNull())
      {
        // TODO
        Node eq = cur.eqNode(rcur);
        rewritten[cur] = rcur;
        visit.push_back(cur);
        visit.push_back(rcur);
      }
      else
      {
        visit.push_back(cur);
        visit.insert(visit.end(),cur.begin(),cur.end());
      }
    } 
    else if (it->second.isNull()) 
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED) {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur )
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
        // congruence here
        std::vector<Node> pfChildren;
        for (size_t i = 0, size = cur.getNumChildren(); i < size; i++)
        {
          if (cur[i]==ret[i])
          {
            // ensure REFL proof for unchanged children
            pf.addStep(cur[i].eqNode(cur[i]),PfRule::REFL, {}, {cur[i]});
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
      // did we rewrite the current node?
      Node rret = getRewriteStep(ret);
      if (!rret.isNull())
      {
        rewritten[cur] = rret;
        visit.push_back(cur);
        visit.push_back(rret);
      }
      else
      {
        visited[cur] = ret;
      }
    }
  } while (!visit.empty());
  Assert(visited.find(t) != visited.end());
  Assert(!visited.find(t)->second.isNull());
  
  
  return nullptr;
}

Node TermConversionProofGenerator::getRewriteStep(Node t) const
{
   NodeNodeMap::const_iterator it = d_rewriteMap.find(t);
   if (it==d_rewriteMap.end())
   {
     return Node::null();
   }
   return (*it).second;
}

}  // namespace CVC4

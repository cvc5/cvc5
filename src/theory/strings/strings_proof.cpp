/*********************                                                        */
/*! \file strings_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of strings proof
 **/

#include "theory/strings/strings_proof.h"

#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

const char* toString(ProofStep id)
{
  switch (id)
  {
    case ProofStep::ASSUME: return "ASSUME";
    case ProofStep::SUBSTITUTE: return "SUBSTITUTE";
    case ProofStep::REWRITE: return "REWRITE";
    case ProofStep::REFL: return "REFL";
    case ProofStep::SYMM: return "SYMM";
    case ProofStep::TRANS: return "TRANS";
    case ProofStep::UNKNOWN: return "UNKNOWN";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, ProofStep id)
{
  out << toString(id);
  return out;
}

ProofNode::ProofNode(ProofStep id,
                     const std::vector<ProofNode*>& children,
                     const std::vector<Node>& args)
    : d_id(id), d_children(children), d_args(args)
{
  computeResult();
}

Node ProofNode::getResult() const
{
  return d_proven;
}

bool ProofNode::computeResult()
{
  if (d_id==ProofStep::ASSUME)
  {
    Assert(d_children.empty());
    Assert(d_args.size()==1);
    d_proven = d_args[0];
  }
  else if (d_id==ProofStep::SUBSTITUTE)
  {
    Assert (d_children.size()>0);
    std::vector<Node> vars;
    std::vector<Node> subs;
    for (unsigned i=0, nchild = d_children.size(); i<nchild; i++)
    {
      Node eqp = d_children[i]->getResult();
      if (eqp.isNull() || eqp.getKind()!=EQUAL)
      {
        return false;
      }
      vars.push_back(eqp[0]);
      subs.push_back(eqp[1]);
    }
    Assert(d_args.size()==1);
    Node res = d_args[0].substitute(vars.begin(),vars.end(),subs.begin(),subs.end());
    d_proven = d_args[0].eqNode(res);
  }
  else if (d_id==ProofStep::REWRITE)
  {
    Node res = Rewriter::rewrite(d_args[0]);
    d_proven = d_args[0].eqNode(res);
  }
  else if (d_id==ProofStep::REFL)
  {
    Assert(d_children.empty());
    Assert(d_args.size()==1);
    d_proven = d_args[0].eqNode(d_args[0]);
  }
  else if (d_id==ProofStep::SYMM)
  {
    Assert(d_children.size()==1);
    Assert(d_args.empty());
  }
  else if (d_id==ProofStep::TRANS)
  {
    Assert(d_children.size()>0);
    Assert(d_args.empty());
    Node first;
    Node curr;
    for (unsigned i=0, nchild = d_children.size(); i<nchild; i++)
    {
      Node eqp = d_children[i]->getResult();
      if (eqp.isNull() || eqp.getKind()!=EQUAL)
      {
        return false;
      }
      if (first.isNull())
      {
        first = eqp[0];
      }
      else if (eqp[0]!=curr)
      {
        return false;
      }
      curr = eqp[1];
    }
    d_proven = first.eqNode(curr);
  }
  return true;
}

void ProofNode::printDebug(std::ostream& os) const
{
  // TODO
}

bool ProofManager::registerStep(Node fact,
                                ProofStep id,
                                const std::vector<Node>& children,
                                const std::vector<Node>& args)
{
  std::map<Node, std::unique_ptr<ProofNode> >::iterator it = d_nodes.find(fact);
  if (it != d_nodes.end())
  {
    // already proven
    return true;
  }
  std::vector<ProofNode*> pchildren;
  for (const Node& c : children)
  {
    ProofNode* pc = getProof(c);
    if (pc == nullptr)
    {
      // failed to get a proof for child, fail
      return false;
    }
    pchildren.push_back(pc);
  }
  d_nodes[fact].reset(new ProofNode(id, pchildren, args));
  Node pfact = d_nodes[fact]->getResult();
  // must be equal to given fact
  return fact == pfact;
}

ProofNode* ProofManager::getProof(Node fact) const
{
  std::map<Node, std::unique_ptr<ProofNode> >::const_iterator it =
      d_nodes.find(fact);
  if (it == d_nodes.end())
  {
    return nullptr;
  }
  return it->second.get();
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

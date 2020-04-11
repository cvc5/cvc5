/*********************                                                        */
/*! \file proof.cpp
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

#include "theory/strings/proof.h"

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
    case ProofStep::N_UNIFY: return "N_UNIFY";
    case ProofStep::N_UNIFY_REV: return "N_UNIFY_REV";
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
{
  initialize(id,children,args);
}

ProofStep ProofNode::getId() const { return d_id; }
Node ProofNode::getResult() const { return d_proven; }

bool ProofNode::initialize(ProofStep id,
                     const std::vector<ProofNode*>& children,
                     const std::vector<Node>& args)
{
  d_id = id;
  d_children = children;
  d_args = args;
  d_proven = Node::null();
  // compute what was proven
  if (d_id == ProofStep::ASSUME)
  {
    Assert(d_children.empty());
    Assert(d_args.size() == 1);
    d_proven = d_args[0];
  }
  else if (d_id == ProofStep::SUBSTITUTE)
  {
    Assert(d_children.size() > 0);
    Assert(d_args.size() == 1);
    std::vector<Node> vars;
    std::vector<Node> subs;
    Node curr = d_args[0];
    for (unsigned i = 0, nchild = d_children.size(); i < nchild; i++)
    {
      Node eqp = d_children[i]->getResult();
      if (eqp.isNull() || eqp.getKind() != EQUAL)
      {
        return false;
      }
      TNode var = eqp[0];
      TNode subs = eqp[1];
      curr = curr.substitute(var,subs);
    }
    d_proven = d_args[0].eqNode(curr);
  }
  else if (d_id == ProofStep::REWRITE)
  {
    Assert(d_children.empty());
    Assert(d_args.size() == 1);
    Node res = Rewriter::rewrite(d_args[0]);
    d_proven = d_args[0].eqNode(res);
  }
  else if (d_id == ProofStep::REFL)
  {
    Assert(d_children.empty());
    Assert(d_args.size() == 1);
    d_proven = d_args[0].eqNode(d_args[0]);
  }
  else if (d_id == ProofStep::SYMM)
  {
    Assert(d_children.size() == 1);
    Assert(d_args.empty());
    Node eqp = d_children[0]->getResult();
    if (eqp.isNull() || eqp.getKind() != EQUAL)
    {
      return false;
    }
    d_proven = eqp[1].eqNode(eqp[0]);
  }
  else if (d_id == ProofStep::TRANS)
  {
    Assert(d_children.size() > 0);
    Assert(d_args.empty());
    Node first;
    Node curr;
    for (unsigned i = 0, nchild = d_children.size(); i < nchild; i++)
    {
      Node eqp = d_children[i]->getResult();
      if (eqp.isNull() || eqp.getKind() != EQUAL)
      {
        return false;
      }
      if (first.isNull())
      {
        first = eqp[0];
      }
      else if (eqp[0] != curr)
      {
        return false;
      }
      curr = eqp[1];
    }
    d_proven = first.eqNode(curr);
  }
  else if (d_id == ProofStep::N_UNIFY || d_id == ProofStep::N_UNIFY_REV)
  {
    
  }
  else
  {
    return false;
  }
  Assert(!d_proven.isNull());
  return true;
}

void ProofNode::printDebug(std::ostream& os) const
{
  // TODO
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

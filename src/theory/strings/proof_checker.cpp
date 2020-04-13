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

#include "theory/strings/proof_checker.h"

#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

Node StringProofChecker::applySubstitution(Node n, const std::vector<Node>& exp)
{
  Node curr = n;
  // apply substitution one at a time
  for (const Node& eqp : exp)
  {
    if (eqp.isNull() || eqp.getKind() != EQUAL)
    {
      return Node::null();
    }
    TNode var = eqp[0];
    TNode subs = eqp[1];
    curr = curr.substitute(var, subs);
  }
  return curr;
}
  
Node StringProofChecker::check(
    ProofStep id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args)
{
  if (id == ProofStep::CONCAT_ENDP_UNIFY)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    Node eqs = children[0]->getResult();
    if (eqs.isNull() || eqs.getKind() != EQUAL)
    {
      return Node::null();
    }
    Node s = eqs[0];
    Node t = eqs[1];
    if (s.getKind() != STRING_CONCAT || t.getKind() != STRING_CONCAT)
    {
      return Node::null();
    }
    bool isRev = args[0].getConst<bool>();
    size_t index = 0;
    size_t nchilds = s.getNumChildren();
    size_t nchildt = t.getNumChildren();
    while (s[isRev ? (nchilds - 1 - index) : index]
           == t[isRev ? (nchildt - 1 - index) : index])
    {
      index++;
      if (index >= s.getNumChildren() || index >= t.getNumChildren())
      {
        return Node::null();
      }
    }
    // TODO
  }
  else if (id == ProofStep::CONCAT_UNIFY)
  {
    Assert(children.size() == 2);
    Assert(args.size() == 1);
    bool isRev = args[0].getConst<bool>();
    Node eqs = children[0]->getResult();
    if (eqs.isNull() || eqs.getKind() != EQUAL)
    {
      return Node::null();
    }
    Node s = eqs[0];
    Node t = eqs[1];
    if (s.getKind() != STRING_CONCAT || t.getKind() != STRING_CONCAT)
    {
      return Node::null();
    }
    Node s0 = s[isRev ? s.getNumChildren() - 1 : 0];
    Node t0 = t[isRev ? s.getNumChildren() - 1 : 0];
    Node eql = children[1]->getResult();
    if (eql.isNull() || eql.getKind() != EQUAL)
    {
      return Node::null();
    }
    Node ls = eql[0];
    Node lt = eql[1];
    if (ls.getKind() != STRING_LENGTH || lt.getKind() != STRING_LENGTH
        || ls[0] != s0 || lt[0] != t0)
    {
      return Node::null();
    }
    return s0.eqNode(t0);
  }
  else if (id == ProofStep::CONCAT_LPROP)
  {
    // TODO
  }
  else if (id == ProofStep::CONCAT_CPROP)
  {
    // TODO
  }
  else if (id == ProofStep::CTN_NOT_EQUAL)
  {
    // TODO
  }
  else if (id == ProofStep::REDUCTION)
  {
  }
  else if (id == ProofStep::RE_INTER)
  {
  }
  else if (id == ProofStep::RE_UNFOLD)
  {
  }
  return Node::null();
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

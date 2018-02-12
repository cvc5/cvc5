/*********************                                                        */
/*! \file dynamic_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of dynamic_rewriter
 **/

#include "theory/quantifiers/dynamic_rewrite.h"

#include "theory/rewriter.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

DynamicRewriter::DynamicRewriter(const std::string& name, QuantifiersEngine* qe)
    : d_qe(qe),
      d_equalityEngine(qe->getUserContext(), "DynamicRewriter::" + name, true),
      d_rewrites(qe->getUserContext())
{
  d_equalityEngine.addFunctionKind(kind::APPLY_UF);
}

bool DynamicRewriter::addRewrite(Node a, Node b)
{
  Trace("dyn-rewrite") << "Dyn-Rewriter : " << a << " == " << b << std::endl;
  if (a == b)
  {
    Trace("dyn-rewrite") << "...fail, equal." << std::endl;
    return false;
  }

  // add to the equality engine
  Node ai = toInternal(a);
  Node bi = toInternal(b);
  Trace("dyn-rewrite-debug") << "Internal : " << ai << " " << bi << std::endl;
  d_equalityEngine.addTerm(ai);
  d_equalityEngine.addTerm(bi);

  Trace("dyn-rewrite-debug") << "get reps..." << std::endl;
  // may already be equal by congruence
  Node air = d_equalityEngine.getRepresentative(ai);
  Node bir = d_equalityEngine.getRepresentative(bi);
  Trace("dyn-rewrite-debug") << "Reps : " << air << " " << bir << std::endl;
  if (air == bir)
  {
    Trace("dyn-rewrite") << "...fail, congruent." << std::endl;
    return false;
  }

  Trace("dyn-rewrite-debug") << "assert eq..." << std::endl;
  Node eq = ai.eqNode(bi);
  d_rewrites.push_back(eq);
  d_equalityEngine.assertEquality(eq, true, eq);
  Trace("dyn-rewrite-debug") << "Finished" << std::endl;
  return true;
}

Node DynamicRewriter::toInternal(Node a)
{
  std::map<Node, Node>::iterator it = d_term_to_internal.find(a);
  if (it != d_term_to_internal.end())
  {
    return it->second;
  }
  Node ret = a;

  if (!a.isVar())
  {
    std::vector<Node> children;
    if (a.hasOperator())
    {
      Node op = a.getOperator();
      if (a.getKind() != APPLY_UF)
      {
        op = d_ois_trie[op].getSymbol(a);
      }
      children.push_back(op);
    }
    for (const Node& ca : a)
    {
      Node cai = toInternal(ca);
      children.push_back(cai);
    }
    if (!children.empty())
    {
      if (children.size() == 1)
      {
        ret = children[0];
      }
      else
      {
        ret = NodeManager::currentNM()->mkNode(APPLY_UF, children);
      }
    }
  }
  d_term_to_internal[a] = ret;
  return ret;
}

Node DynamicRewriter::OpInternalSymTrie::getSymbol(Node n)
{
  std::vector<TypeNode> ctypes;
  for (const Node& cn : n)
  {
    ctypes.push_back(cn.getType());
  }
  ctypes.push_back(n.getType());

  OpInternalSymTrie* curr = this;
  for (unsigned i = 0, size = ctypes.size(); i < size; i++)
  {
    curr = &(curr->d_children[ctypes[i]]);
  }
  if (!curr->d_sym.isNull())
  {
    return curr->d_sym;
  }
  // make UF operator
  TypeNode utype;
  if (ctypes.size() == 1)
  {
    utype = ctypes[0];
  }
  else
  {
    utype = NodeManager::currentNM()->mkFunctionType(ctypes);
  }
  Node f = NodeManager::currentNM()->mkSkolem(
      "ufd", utype, "internal op for dynamic_rewriter");
  curr->d_sym = f;
  return f;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

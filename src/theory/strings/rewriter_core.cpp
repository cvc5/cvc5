/*********************                                                        */
/*! \file rewriter_core.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of core functions for the rewriter of the theory of
 ** strings
 **/

#include "theory/strings/rewriter_core.h"

#include "theory/strings/theory_strings_rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

Node RewriterCore::returnRewrite(Node node, Node ret, const char* c)
{
  Trace("strings-rewrite") << "Rewrite " << node << " to " << ret << " by " << c
                           << "." << std::endl;

  NodeManager* nm = NodeManager::currentNM();

  // standard post-processing
  // We rewrite (string) equalities immediately here. This allows us to forego
  // the standard invariant on equality rewrites (that s=t must rewrite to one
  // of { s=t, t=s, true, false } ).
  Kind retk = ret.getKind();
  if (retk == OR || retk == AND)
  {
    std::vector<Node> children;
    bool childChanged = false;
    for (const Node& cret : ret)
    {
      bool pol = cret.getKind()!=NOT;
      Node cretm = pol ? cret : cret[0];
      if (cretm.getKind() == EQUAL)
      {
        cretm = TheoryStringsRewriter::rewriteEqualityExt(cretm);
        if (!pol)
        {
          cretm = cretm.notNode();
        }
      }
      else
      {
        cretm = cret;
      }
      childChanged = childChanged || cret != cretm;
      children.push_back(cretm);
    }
    if (childChanged)
    {
      ret = nm->mkNode(retk, children);
    }
  }
  else if (retk == NOT && ret[0].getKind() == EQUAL)
  {
    ret = nm->mkNode(NOT, TheoryStringsRewriter::rewriteEqualityExt(ret[0]));
  }
  else if (retk == EQUAL && node.getKind() != EQUAL)
  {
    Trace("strings-rewrite")
        << "Apply extended equality rewrite on " << ret << std::endl;
    ret = TheoryStringsRewriter::rewriteEqualityExt(ret);
  }
  return ret;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

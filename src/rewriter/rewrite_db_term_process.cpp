/*********************                                                        */
/*! \file rewrite_db_term_process.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of rewrite db term processor.
 **/

#include "rewriter/rewrite_db_term_process.h"

#include "expr/attribute.h"
#include "expr/nary_term_util.h"
#include "util/string.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace rewriter {

Node RewriteDbNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  TypeNode tn = n.getType();
  if (k == CONST_STRING)
  {
    NodeManager* nm = NodeManager::currentNM();
    // "ABC" is (str.++ "A" "B" "C")
    const std::vector<unsigned>& vec = n.getConst<String>().getVec();
    if (vec.size() <= 1)
    {
      return n;
    }
    std::vector<unsigned> v(vec.begin(), vec.end());
    std::vector<Node> children;
    for (unsigned i = 0, size = v.size(); i < size; i++)
    {
      std::vector<unsigned> tmp;
      tmp.push_back(v[i]);
      children.push_back(nm->mkConst(String(tmp)));
    }
    return nm->mkNode(STRING_CONCAT, children);
  }
  /*
  if (k == CONST_STRING)
  {
    NodeManager* nm = NodeManager::currentNM();
    // "ABC" is (str.++ "A" (str.++ "B" "C"))
    const std::vector<unsigned>& vec = n.getConst<String>().getVec();
    if (vec.size() <= 1)
    {
      return n;
    }
    std::vector<unsigned> v(vec.begin(), vec.end());
    std::reverse(v.begin(), v.end());
    Node ret = expr::getNullTerminator(STRING_CONCAT, tn);
    Assert(!ret.isNull());
    for (unsigned i = 0, size = v.size(); i < size; i++)
    {
      std::vector<unsigned> tmp;
      tmp.push_back(v[i]);
      ret = nm->mkNode(STRING_CONCAT, nm->mkConst(String(tmp)), ret);
    }
    return ret;
  }
  else if (NodeManager::isNAryKind(k) && n.getNumChildren() >= 2)
  {
    NodeManager* nm = NodeManager::currentNM();
    Assert(n.getMetaKind() != kind::metakind::PARAMETERIZED);
    // convert to binary + null terminator
    std::vector<Node> children(n.begin(), n.end());
    std::reverse(children.begin(), children.end());
    Node ret = expr::getNullTerminator(k, tn);
    if (ret.isNull())
    {
      if (k == DISTINCT)
      {
        // FIXME
      }
      return n;
    }
    for (unsigned i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      ret = nm->mkNode(k, children[i], ret);
    }
    return ret;
  }
  */
  return n;
}

}  // namespace rewriter
}  // namespace cvc5

/*********************                                                        */
/*! \file lfsc_term_process.cpp
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

#include "proof/lfsc/lfsc_term_process.h"


using namespace CVC4::kind;

namespace CVC4 {
namespace proof {

LfscTermProcessCallback::LfscTermProcessCallback() : TermProcessCallback()
{
  
}

Node LfscTermProcessCallback::convertInternal(Node n)
{
  Kind ck = n.getKind();
  if (ck == CONST_STRING)
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
    std::vector<unsigned> tmp;
    tmp.push_back(v[0]);
    Node ret = nm->mkConst(String(tmp));
    tmp.pop_back();
    for (unsigned i = 1, size = v.size(); i < size; i++)
    {
      tmp.push_back(v[i]);
      ret = nm->mkNode(STRING_CONCAT, nm->mkConst(String(tmp)), ret);
      tmp.pop_back();
    }
    return ret;
  }
  else if (ExprManager::isNAryKind(ck) && n.getNumChildren() >= 2)
  {
    NodeManager* nm = NodeManager::currentNM();
    Assert(n.getMetaKind() != kind::metakind::PARAMETERIZED);
    // convert to binary
    std::vector<Node> children(n.begin(), n.end());
    std::reverse(children.begin(), children.end());
    Node ret = children[0];
    for (unsigned i = 1, nchild = n.getNumChildren(); i < nchild; i++)
    {
      ret = nm->mkNode(ck, children[i], ret);
    }
    return ret;
  }
  return n;
}

TypeNode LfscTermProcessCallback::convertInternalType(TypeNode tn)
{
  // TODO
  return tn;
}


}  // namespace proof
}  // namespace CVC4

/*********************                                                        */
/*! \file theory_strings_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Util functions for theory strings.
 **
 ** Util functions for theory strings.
 **/

#include "theory/strings/theory_strings_utils.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {
namespace utils {

Node mkAnd(std::vector<Node>& a)
{
  std::vector<Node> au;
  for (const Node& ai : a)
  {
    if (std::find(au.begin(), au.end(), ai) == au.end())
    {
      au.push_back(ai);
    }
  }
  if (au.empty())
  {
    return NodeManager::currentNM()->mkConst(true);
  }
  else if (au.size() == 1)
  {
    return au[0];
  }
  return NodeManager::currentNM()->mkNode(AND, au);
}

Node getConstantComponent(Node t)
{
  Kind tk = t.getKind();
  if (tk == STRING_TO_REGEXP)
  {
    return t[0].isConst() ? t[0] : Node::null();
  }
  return tk == CONST_STRING ? t : Node::null();
}

Node getConstantPrefix(Node e, bool isPost)
{
  Kind ek = e.getKind();
  if (ek == STRING_IN_REGEXP)
  {
    return getConstantPrefix(e[1], isPost);
  }
  if (ek == STRING_CONCAT || ek == REGEXP_CONCAT)
  {
    return getConstantComponent(e[isPost ? e.getNumChildren() - 1 : 0]);
  }
  return getConstantComponent(e);
}

}  // namespace utils
}  // namespace strings
}  // namespace theory
}  // namespace CVC4

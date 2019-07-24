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

void getConcat(Node n, std::vector<Node>& c)
{
  Kind k = n.getKind();
  if (k == STRING_CONCAT || k == REGEXP_CONCAT)
  {
    for (const Node& nc : n)
    {
      c.push_back(nc);
    }
  }
  else
  {
    c.push_back(n);
  }
}

Node mkConcat(Kind k, std::vector<Node>& c)
{
  Assert(!c.empty() || k == STRING_CONCAT);
  NodeManager* nm = NodeManager::currentNM();
  return c.size() > 1 ? nm->mkNode(k, c)
                      : (c.size() == 1 ? c[0] : nm->mkConst(String("")));
}

}  // namespace utils
}  // namespace strings
}  // namespace theory
}  // namespace CVC4

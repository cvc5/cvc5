/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements a n-ary match trie
 */

#include "expr/nary_match_trie.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace expr {

bool NaryMatchTrie::getMatches(Node n, NotifyMatch* ntm)
{
  // TODO
  return true;
}

void NaryMatchTrie::addTerm(Node n)
{
  Assert(!n.isNull());
  std::vector<Node> visit;
  visit.push_back(n);
  NaryMatchTrie* curr = this;
  while (!visit.empty())
  {
    Node cn = visit.back();
    visit.pop_back();
    if (cn.isNull())
    {
      curr = &(curr->d_children[cn]);
    }
    else if (cn.hasOperator())
    {
      curr = &(curr->d_children[cn.getOperator()]);
      // add null terminator if an n-ary kind
      if (NodeManager::isNAryKind(cn.getKind()))
      {
        visit.push_back(Node::null());
      }
      // note children in reverse order
      for (const Node& cnc : cn)
      {
        visit.push_back(cnc);
      }
    }
    else
    {
      if (cn.isVar()
          && std::find(curr->d_vars.begin(), curr->d_vars.end(), cn)
                 == curr->d_vars.end())
      {
        curr->d_vars.push_back(cn);
      }
      curr = &(curr->d_children[cn]);
    }
  }
  curr->d_data = n;
}

void NaryMatchTrie::clear()
{
  d_children.clear();
  d_vars.clear();
  d_data = Node::null();
}

}  // namespace expr
}  // namespace cvc5

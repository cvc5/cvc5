/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sygus to builtin
 */

#include "theory/quantifiers/sygus/print_sygus_to_builtin.h"

#include <sstream>

#include "expr/dtype.h"
#include "theory/datatypes/sygus_datatype_utils.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

Node getPrintableSygusToBuiltin(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      // only recurse on constructors
      if (cur.getKind() == kind::APPLY_CONSTRUCTOR)
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
      else
      {
        visited[cur] = cur;
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      Assert(cur.getKind() == kind::APPLY_CONSTRUCTOR);
      const DType& dt = cur.getType().getDType();
      // only applies to sygus datatypes
      if (dt.isSygus())
      {
        std::vector<Node> children;
        for (const Node& cn : cur)
        {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          children.push_back(it->second);
        }
        size_t index = datatypes::utils::indexOf(cur.getOperator());
        // mkSygusTerm, beta-reduced and external version
        ret = datatypes::utils::mkSygusTerm(dt, index, children, true, true);
        // then, annotate with the name of the datatype
        std::stringstream ss;
        ss << "(! " << ret << " :gterm " << dt.getName() << ")";
        ret = nm->mkRawSymbol(ss.str(), ret.getType());
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

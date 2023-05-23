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
 * Oracle caller
 */

#include "expr/oracle_caller.h"

#include "theory/quantifiers/quantifiers_attributes.h"

namespace cvc5::internal {

OracleCaller::OracleCaller(const Node& n)
    : d_oracleNode(getOracleFor(n)),
      d_oracle(NodeManager::currentNM()->getOracleFor(d_oracleNode))
{
  Assert(!d_oracleNode.isNull());
}

bool OracleCaller::callOracle(const Node& fapp, std::vector<Node>& res)
{
  std::map<Node, std::vector<Node>>::iterator it = d_cachedResults.find(fapp);
  if (it != d_cachedResults.end())
  {
    Trace("oracle-calls") << "Using cached oracle result for " << fapp
                          << std::endl;
    res = it->second;
    // don't bother setting runResult
    return false;
  }
  Assert(fapp.getKind() == kind::APPLY_UF);
  Assert(getOracleFor(fapp.getOperator()) == d_oracleNode);

  Trace("oracle-calls") << "Call oracle " << fapp << std::endl;
  // get the input arguments from the application
  std::vector<Node> args(fapp.begin(), fapp.end());
  // run the oracle method
  std::vector<Node> response = d_oracle.run(args);
  Trace("oracle-calls") << "response node " << response << std::endl;
  // cache the response
  d_cachedResults[fapp] = response;
  res = response;
  return true;
}

bool OracleCaller::isOracleFunction(Node f)
{
  return f.hasAttribute(theory::OracleInterfaceAttribute());
}

bool OracleCaller::isOracleFunctionApp(Node n)
{
  if (n.getKind() == kind::APPLY_UF)
  {
    return isOracleFunction(n.getOperator());
  }
  // possibly 0-ary
  return isOracleFunction(n);
}

Node OracleCaller::getOracleFor(const Node& n)
{
  // oracle functions have no children
  if (n.isVar())
  {
    Assert(isOracleFunction(n));
    Node o = n.getAttribute(theory::OracleInterfaceAttribute());
    Assert(o.getKind() == kind::ORACLE);
    return o;
  }
  else if (n.getKind() == kind::FORALL)
  {
    // oracle interfaces have children, and the attribute is stored in 2nd child
    for (const Node& v : n[2][0])
    {
      if (v.getKind() == kind::ORACLE)
      {
        return v;
      }
    }
  }
  Assert(false) << "Unexpected node for oracle " << n;
  return Node::null();
}

const std::map<Node, std::vector<Node>>& OracleCaller::getCachedResults() const
{
  return d_cachedResults;
}

}  // namespace cvc5::internal

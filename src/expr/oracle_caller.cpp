/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Elizabeth Polgreen
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Oracle caller
 */

#include "expr/oracle_caller.h"

#include <sstream>

#include "options/base_options.h"
#include "theory/quantifiers/quantifiers_attributes.h"

namespace cvc5::internal {

OracleCaller::OracleCaller(const Node& oracleInterfaceNode)
    : d_binaryName(getBinaryNameFor(oracleInterfaceNode))
{
}

bool OracleCaller::callOracle(const Node& fapp, Node& res, int& runResult)
{
  std::map<Node, Node>::iterator it = d_cachedResults.find(fapp);
  if (it != d_cachedResults.end())
  {
    Trace("oracle-calls") << "Using cached oracle result for " << fapp
                          << std::endl;
    res = it->second;
    // don't bother setting runResult
    return false;
  }
  Assert(fapp.getKind() == kind::APPLY_UF);
  Assert(getBinaryNameFor(fapp.getOperator()) == d_binaryName);
  std::vector<std::string> sargs;
  sargs.push_back(d_binaryName);

  Trace("oracle-calls") << "Call oracle " << fapp << std::endl;
  for (const Node& arg : fapp)
  {
    std::ostringstream oss;
    oss << arg;
    sargs.push_back(oss.str());
  }

  // Run the oracle binary for `sargs`, which indicates a list of
  // smt2 terms as strings.

  // Parse response from the binary into a Node. The response from the binary
  // should be a string that can be parsed as a (tuple of) terms in the smt2
  // format.
  Node response = Node::null();
  Trace("oracle-calls") << "response node " << response << std::endl;
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

std::string OracleCaller::getBinaryName() const { return d_binaryName; }

std::string OracleCaller::getBinaryNameFor(const Node& n)
{
  // oracle functions have no children
  if (n.isVar())
  {
    Assert(isOracleFunction(n));
    return n.getAttribute(theory::OracleInterfaceAttribute());
  }
  else if (n.getKind() == kind::FORALL)
  {
    // oracle interfaces have children, and the attribute is stored in 2nd child
    for (const Node& v : n[2][0])
    {
      if (v.getAttribute(theory::OracleInterfaceAttribute()) != "")
      {
        return v.getAttribute(theory::OracleInterfaceAttribute());
      }
    }
  }
  Assert(false) << "Unexpected node for binary name " << n;
  return "";
}

const std::map<Node, Node>& OracleCaller::getCachedResults() const
{
  return d_cachedResults;
}

}  // namespace cvc5::internal

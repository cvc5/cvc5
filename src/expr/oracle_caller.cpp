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
#include "util/miniParser/miniParser.h"
#include "util/rational.h"
#include "util/run.h"

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
  std::vector<std::string> sargs;
  sargs.push_back(d_binaryName);

  Trace("oracle-calls") << "Call oracle " << fapp << std::endl;
  for (const Node& arg : fapp)
  {
    std::ostringstream oss;
    oss << arg;
    sargs.push_back(oss.str());
  }

  // run the oracle binary
  std::ostringstream stdout_stream;

  runResult = run(d_binaryName, sargs, "", stdout_stream, "");

  // we assume that the oracle returns the result in SMT-LIB format
  std::istringstream oracle_response_istream(stdout_stream.str());

  // // we assume that an oracle has a return code of 0 or 10.
  // if (run_result != 0 && run_result != 10)
  // {
  //   Trace("oracle-calls") << "oracle " << d_binaryName
  //                         << " has failed with exit code " << run_result
  //                         << std::endl;
  //   AlwaysAssert(run_result == 0 || run_result == 10);
  // }

  // parse response into a Node
  Node response = mini_parsert(oracle_response_istream).expression();
  Trace("oracle-calls") << "response node " << response << std::endl;
  d_cachedResults[fapp] = response;
  res = response;
  return true;
}

bool OracleCaller::isOracleFunction(Node f)
{
  return f.hasAttribute(theory::OracleInterfaceAttribute());
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

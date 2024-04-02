/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Oracle checker
 */

#include "theory/quantifiers/oracle_checker.h"

#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

OracleChecker::OracleChecker(Env& env)
    : EnvObj(env), NodeConverter(env.getNodeManager())
{
}

Node OracleChecker::checkConsistent(Node app, Node val)
{
  Node result = evaluateApp(app);
  Trace("oracle-calls") << "checkConsistent " << app << " == " << result
                        << " vs " << val << std::endl;
  if (result != val)
  {
    return result;
  }
  return Node::null();
}

Node OracleChecker::evaluateApp(Node app)
{
  Assert(app.getKind() == Kind::APPLY_UF);
  Node f = app.getOperator();
  Assert(OracleCaller::isOracleFunction(f));
  // get oracle caller
  if (d_callers.find(f) == d_callers.end())
  {
    d_callers.insert(std::pair<Node, OracleCaller>(f, OracleCaller(f)));
  }
  OracleCaller& caller = d_callers.at(f);

  // get oracle result
  std::vector<Node> retv;
  bool ranOracle = caller.callOracle(app, retv);
  if (retv.size() != 1)
  {
    Assert(false) << "Failed to evaluate " << app
                  << " to a single return value, got: " << retv << std::endl;
    return app;
  }
  Node ret = retv[0];
  ret = rewrite(ret);
  if (ranOracle)
  {
    // prints the result of the oracle, if it was computed in the call above.
    // this prints the original application, its result, and the exit code
    // of the binary.
    d_env.output(options::OutputTag::ORACLES)
        << "(oracle-call " << app << " " << ret << ")" << std::endl;
  }
  if (ret.getType() != app.getType())
  {
    std::stringstream ss;
    ss << "Evaluated an oracle call with an unexpected type: " << app << " = "
       << ret << " whose type is " << ret.getType() << ", expected "
       << app.getType();
    throw LogicException(ss.str());
  }
  Assert(!ret.isNull());
  return ret;
}

Node OracleChecker::evaluate(Node n)
{
  // same as convert
  return convert(n);
}

Node OracleChecker::postConvert(Node n)
{
  Trace("oracle-checker-debug") << "postConvert: " << n << std::endl;
  // if it is an oracle function applied to constant arguments
  if (n.getKind() == Kind::APPLY_UF
      && OracleCaller::isOracleFunction(n.getOperator()))
  {
    bool allConst = true;
    for (const Node& nc : n)
    {
      if (nc.isConst())
      {
        continue;
      }
      // special case: assume all closed lambdas are constants
      if (nc.getKind() == Kind::LAMBDA)
      {
        // if the lambda does not have a free variable (BOUND_VARIABLE)
        if (!expr::hasFreeVar(nc))
        {
          // it also cannot have any free symbol
          std::unordered_set<Node> syms;
          expr::getSymbols(nc, syms);
          if (syms.empty())
          {
            continue;
          }
        }
      }
      // non-constant argument, fail
      allConst = false;
      break;
    }
    if (allConst)
    {
      // evaluate the application
      return evaluateApp(n);
    }
  }
  // otherwise, always rewrite
  return rewrite(n);
}
bool OracleChecker::hasOracles() const { return !d_callers.empty(); }
bool OracleChecker::hasOracleCalls(Node f) const
{
  std::map<Node, OracleCaller>::const_iterator it = d_callers.find(f);
  return it != d_callers.end();
}
const std::map<Node, std::vector<Node>>& OracleChecker::getOracleCalls(
    Node f) const
{
  Assert(hasOracleCalls(f));
  std::map<Node, OracleCaller>::const_iterator it = d_callers.find(f);
  return it->second.getCachedResults();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

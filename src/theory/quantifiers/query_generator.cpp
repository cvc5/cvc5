/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of a class for mining interesting satisfiability
 * queries from a stream of generated expressions.
 */

#include "theory/quantifiers/query_generator.h"

#include <fstream>
#include <sstream>

#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "smt/print_benchmark.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QueryGenerator::QueryGenerator(Env& env) : ExprMiner(env), d_queryCount(0) {}
void QueryGenerator::initialize(const std::vector<Node>& vars, SygusSampler* ss)
{
  d_queryCount = 0;
  ExprMiner::initialize(vars, ss);
}

void QueryGenerator::dumpQuery(Node qy,
                               const Result& r,
                               std::vector<Node>& queries)
{
  d_queryCount++;
  bool isSolved =
      r.getStatus() == Result::SAT || r.getStatus() == Result::UNSAT;
  // add to queries if not filtered
  if (!isSolved || !options().quantifiers.sygusQueryFilterSolved)
  {
    queries.push_back(qy);
  }
  // return if we should not dump the query based on the options
  if (options().quantifiers.sygusQueryGenDumpFiles
      == options::SygusQueryDumpFilesMode::NONE)
  {
    return;
  }
  if (options().quantifiers.sygusQueryGenDumpFiles
      == options::SygusQueryDumpFilesMode::UNSOLVED)
  {
    if (isSolved)
    {
      return;
    }
  }

  Node kqy = convertToSkolem(qy);
  // Print the query to to queryN.smt2
  std::stringstream fname;
  fname << "query" << d_queryCount << ".smt2";
  std::ofstream fs(fname.str(), std::ofstream::out);
  smt::PrintBenchmark pb(Printer::getPrinter(fs));
  pb.printBenchmark(fs, d_env.getLogicInfo().getLogicString(), {}, {kqy});
  fs.close();
}

void QueryGenerator::ensureBoolean(const Node& n) const
{
  if (!n.getType().isBoolean())
  {
    std::stringstream ss;
    ss << "SyGuS query generation in the current mode requires the grammar to "
          "generate Boolean terms only";
    throw LogicException(ss.str());
  }
}

QueryGeneratorBasic::QueryGeneratorBasic(Env& env) : QueryGenerator(env) {}

bool QueryGeneratorBasic::addTerm(Node n, std::vector<Node>& queries)
{
  ensureBoolean(n);
  SubsolverSetupInfo ssi(d_env);
  Result r = doCheck(n, ssi);
  dumpQuery(n, r, queries);
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

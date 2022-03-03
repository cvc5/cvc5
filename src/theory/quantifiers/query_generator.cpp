/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "smt/env.h"
#include "smt/print_benchmark.h"
#include "util/random.h"

using namespace std;
using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {

QueryGenerator::QueryGenerator(Env& env) : ExprMiner(env), d_queryCount(0) {}
void QueryGenerator::initialize(const std::vector<Node>& vars, SygusSampler* ss)
{
  Assert(ss != nullptr);
  d_queryCount = 0;
  ExprMiner::initialize(vars, ss);
}

void QueryGenerator::dumpQuery(Node qy)
{
  Node kqy = convertToSkolem(qy);
  // Print the query to to queryN.smt2
  std::stringstream fname;
  fname << "query" << d_queryCount << ".smt2";
  std::ofstream fs(fname.str(), std::ofstream::out);
  smt::PrintBenchmark pb(&d_env.getPrinter());
  pb.printBenchmark(fs, d_env.getLogicInfo().getLogicString(), {}, {kqy});
  fs.close();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

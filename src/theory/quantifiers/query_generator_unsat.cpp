/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for mining interesting satisfiability queries from a stream
 * of generated expressions.
 */

#include "theory/quantifiers/query_generator_unsat.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {


QueryGeneratorUnsat::QueryGeneratorUnsat(Env& env) : EnvObj(env){}

void QueryGeneratorUnsat::initialize(const std::vector<Node>& vars,
                SygusSampler* ss) {}

bool QueryGeneratorUnsat::addTerm(Node n, std::ostream& out)
{
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5


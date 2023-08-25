/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of a finite model finding decision strategy for strings.
 */

#include "theory/strings/strings_fmf.h"

#include "theory/trust_substitutions.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

StringsFmf::StringsFmf(Env& env, Valuation valuation, TermRegistry& tr)
    : EnvObj(env), d_sslds(nullptr), d_valuation(valuation), d_termReg(tr)
{
}

StringsFmf::~StringsFmf() {}

void StringsFmf::presolve()
{
  d_sslds.reset(new StringSumLengthDecisionStrategy(d_env, d_valuation));
  Trace("strings-dstrat-reg")
      << "presolve: register decision strategy." << std::endl;
  const NodeSet& ivars = d_termReg.getInputVars();
  std::vector<Node> inputVars;
  SubstitutionMap& tls = d_env.getTopLevelSubstitutions().get();
  for (NodeSet::const_iterator itr = ivars.begin(); itr != ivars.end(); ++itr)
  {
    Node var = *itr;
    // ensure we haven't solved for it?
    if (var == tls.apply(var))
    {
      inputVars.push_back(var);
    }
  }
  d_sslds->initialize(inputVars);
}

DecisionStrategy* StringsFmf::getDecisionStrategy() const
{
  return d_sslds.get();
}

StringsFmf::StringSumLengthDecisionStrategy::StringSumLengthDecisionStrategy(
    Env& env, Valuation valuation)
    : DecisionStrategyFmf(env, valuation), d_inputVarLsum(userContext())
{
}

bool StringsFmf::StringSumLengthDecisionStrategy::isInitialized()
{
  return !d_inputVarLsum.get().isNull();
}

void StringsFmf::StringSumLengthDecisionStrategy::initialize(
    const std::vector<Node>& vars)
{
  if (d_inputVarLsum.get().isNull() && !vars.empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> sum;
    for (const Node& v : vars)
    {
      sum.push_back(nm->mkNode(STRING_LENGTH, v));
    }
    Node sumn = sum.size() == 1 ? sum[0] : nm->mkNode(ADD, sum);
    d_inputVarLsum.set(sumn);
  }
}

Node StringsFmf::StringSumLengthDecisionStrategy::mkLiteral(unsigned i)
{
  if (d_inputVarLsum.get().isNull())
  {
    return Node::null();
  }
  NodeManager* nm = NodeManager::currentNM();
  Node lit = nm->mkNode(LEQ, d_inputVarLsum.get(), nm->mkConstInt(Rational(i)));
  Trace("strings-fmf") << "StringsFMF::mkLiteral: " << lit << std::endl;
  return lit;
}
std::string StringsFmf::StringSumLengthDecisionStrategy::identify() const
{
  return std::string("string_sum_len");
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

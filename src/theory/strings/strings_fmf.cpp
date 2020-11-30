/*********************                                                        */
/*! \file strings_fmf.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a finite model finding decision strategy for
 ** strings.
 **/

#include "theory/strings/strings_fmf.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

StringsFmf::StringsFmf(context::Context* c,
                       context::UserContext* u,
                       Valuation valuation,
                       TermRegistry& tr)
    : d_sslds(nullptr),
      d_satContext(c),
      d_userContext(u),
      d_valuation(valuation),
      d_termReg(tr)
{
}

StringsFmf::~StringsFmf() {}

void StringsFmf::presolve()
{
  d_sslds.reset(new StringSumLengthDecisionStrategy(
      d_satContext, d_userContext, d_valuation));
  Trace("strings-dstrat-reg")
      << "presolve: register decision strategy." << std::endl;
  const NodeSet& ivars = d_termReg.getInputVars();
  std::vector<Node> inputVars;
  for (NodeSet::const_iterator itr = ivars.begin(); itr != ivars.end(); ++itr)
  {
    inputVars.push_back(*itr);
  }
  d_sslds->initialize(inputVars);
}

DecisionStrategy* StringsFmf::getDecisionStrategy() const
{
  return d_sslds.get();
}

StringsFmf::StringSumLengthDecisionStrategy::StringSumLengthDecisionStrategy(
    context::Context* c, context::UserContext* u, Valuation valuation)
    : DecisionStrategyFmf(c, valuation), d_inputVarLsum(u)
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
    Node sumn = sum.size() == 1 ? sum[0] : nm->mkNode(PLUS, sum);
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
  Node lit = nm->mkNode(LEQ, d_inputVarLsum.get(), nm->mkConst(Rational(i)));
  Trace("strings-fmf") << "StringsFMF::mkLiteral: " << lit << std::endl;
  return lit;
}
std::string StringsFmf::StringSumLengthDecisionStrategy::identify() const
{
  return std::string("string_sum_len");
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

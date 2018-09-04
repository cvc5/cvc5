/*********************                                                        */
/*! \file decision_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of decision_manager
 **/

#include "theory/decision_manager.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

DecisionStrategyFmf::DecisionStrategyFmf(context::Context* satContext,
                                         Valuation valuation)
    : d_valuation(valuation),
      d_has_curr_literal(false, satContext),
      d_curr_literal(0, satContext)
{
}

void DecisionStrategyFmf::initialize() { d_literals.clear(); }

Node DecisionStrategyFmf::getNextDecisionRequest()
{
  if (d_has_curr_literal.get())
  {
    return Node::null();
  }
  bool success;
  unsigned curr_lit = d_curr_literal.get();
  do
  {
    success = true;
    // get the current literal
    Node lit = getLiteral(curr_lit);
    // if out of literals, we are done
    if (!lit.isNull())
    {
      bool value;
      if (!d_valuation.hasSatValue(lit, value))
      {
        // if it has not been decided, return it
        return lit;
      }
      else if (!value)
      {
        // asserted false, the current literal is incremented
        curr_lit = d_curr_literal.get() + 1;
        d_curr_literal.set(curr_lit);
        Assert(curr_lit < d_literals.size());
        // repeat
        success = false;
      }
    }
  } while (!success);
  // the current literal has been decided with the right polarity, we are done
  d_has_curr_literal = true;
  return Node::null();
}

bool DecisionStrategyFmf::getAssertedLiteralIndex(unsigned& i)
{
  if (d_has_curr_literal.get())
  {
    i = d_curr_literal.get();
    return true;
  }
  return false;
}

Node DecisionStrategyFmf::getAssertedLiteral()
{
  if (d_has_curr_literal.get())
  {
    Assert(d_curr_literal.get() < d_literals.size());
    return getLiteral(d_curr_literal.get());
  }
  return Node::null();
}

Node DecisionStrategyFmf::getLiteral(unsigned n)
{
  // allocate until the index is valid
  while (n >= d_literals.size())
  {
    d_literals.push_back(mkLiteral(d_literals.size()));
  }
  return d_literals[n];
}

DecisionManager::DecisionManager(context::Context* satContext)
    : d_curr_strategy(0, satContext)
{
}

void DecisionManager::registerStrategy(StrategyId id, DecisionStrategy* ds)
{
  d_reg_strategy[id].push_back(ds);
}

void DecisionManager::initialize()
{
  for (unsigned i = 0; i < strat_last; i++)
  {
    StrategyId s = static_cast<StrategyId>(i);
    std::map<StrategyId, std::vector<DecisionStrategy*> >::iterator itrs =
        d_reg_strategy.find(s);
    if (itrs != d_reg_strategy.end())
    {
      for (unsigned j = 0, size = itrs->second.size(); j < size; j++)
      {
        d_strategy.push_back(itrs->second[j]);
      }
    }
  }
}

Node DecisionManager::getNextDecisionRequest(unsigned& priorty)
{
  unsigned sstart = d_curr_strategy.get();
  for (unsigned i = sstart, nstrat = d_strategy.size(); i < nstrat; i++)
  {
    Node lit = d_strategy[i]->getNextDecisionRequest();
    if (!lit.isNull())
    {
      return lit;
    }
    // update d_curr_strategy?
  }
  return Node::null();
}

}  // namespace theory
}  // namespace CVC4

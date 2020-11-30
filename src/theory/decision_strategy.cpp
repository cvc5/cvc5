/*********************                                                        */
/*! \file decision_strategy.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of base classes for decision strategies used by theory
 ** solvers for use in the DecisionManager of TheoryEngine.
 **/

#include "theory/decision_strategy.h"

#include "theory/rewriter.h"

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
  Trace("dec-strategy-debug")
      << "Get next decision request " << identify() << "..." << std::endl;
  if (d_has_curr_literal.get())
  {
    Trace("dec-strategy-debug") << "...already has decision" << std::endl;
    return Node::null();
  }
  bool success;
  unsigned curr_lit = d_curr_literal.get();
  do
  {
    success = true;
    // get the current literal
    Node lit = getLiteral(curr_lit);
    Trace("dec-strategy-debug")
        << "...check literal #" << curr_lit << " : " << lit << std::endl;
    // if out of literals, we are done in the current SAT context
    if (!lit.isNull())
    {
      bool value;
      if (!d_valuation.hasSatValue(lit, value))
      {
        Trace("dec-strategy-debug") << "...not assigned, return." << std::endl;
        // if it has not been decided, return it
        return lit;
      }
      else if (!value)
      {
        Trace("dec-strategy-debug")
            << "...assigned false, increment." << std::endl;
        // asserted false, the current literal is incremented
        curr_lit = d_curr_literal.get() + 1;
        d_curr_literal.set(curr_lit);
        // repeat
        success = false;
      }
      else
      {
        Trace("dec-strategy-debug") << "...already assigned true." << std::endl;
      }
    }
    else
    {
      Trace("dec-strategy-debug") << "...exhausted literals." << std::endl;
    }
  } while (!success);
  // the current literal has been decided with the right polarity, we are done
  d_has_curr_literal = true;
  return Node::null();
}

bool DecisionStrategyFmf::getAssertedLiteralIndex(unsigned& i) const
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
    Node lit = mkLiteral(d_literals.size());
    if (!lit.isNull())
    {
      lit = Rewriter::rewrite(lit);
    }
    d_literals.push_back(lit);
  }
  Node ret = d_literals[n];
  if (!ret.isNull())
  {
    // always ensure it is in the CNF stream
    ret = d_valuation.ensureLiteral(ret);
  }
  return ret;
}

DecisionStrategySingleton::DecisionStrategySingleton(
    const char* name,
    Node lit,
    context::Context* satContext,
    Valuation valuation)
    : DecisionStrategyFmf(satContext, valuation), d_name(name), d_literal(lit)
{
}

Node DecisionStrategySingleton::mkLiteral(unsigned n)
{
  if (n == 0)
  {
    return d_literal;
  }
  return Node::null();
}

Node DecisionStrategySingleton::getSingleLiteral() { return d_literal; }

}  // namespace theory
}  // namespace CVC4

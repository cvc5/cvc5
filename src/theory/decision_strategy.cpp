/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of base classes for decision strategies used by theory
 * solvers for use in the DecisionManager of TheoryEngine.
 */

#include "theory/decision_strategy.h"

#include "expr/plugin.h"
#include "options/parallel_options.h"
#include "smt/env.h"
#include "theory/output_channel.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

DecisionStrategyFFD::DecisionStrategyFFD(Env& env, Valuation valuation)
    : DecisionStrategy(env),
      d_valuation(valuation),
      d_name("decisionStrategyFFD"),
      d_forced_count(0),
      d_notifiedPlugin(false)
{
}

void DecisionStrategyFFD::initialize() {}

void DecisionStrategyFFD::addLiteral(Node n)
{
  Node lit = rewrite(n);
  d_literals.push_back(d_valuation.ensureLiteral(lit));
}

void DecisionStrategyFFD::setOutputChannel(TheoryEngine* te)
{
  d_out = new OutputChannel(statisticsRegistry(), te, "ffdoc", 42);
}

Node DecisionStrategyFFD::getNextDecisionRequest()
{
  Trace("dec-strategy-debug")
      << "Get next decision request " << identify() << "... " << std::endl;

  if (options().parallel.forceFirstDecisionsOnce)
  {
    if (d_forced_count < d_literals.size())
    {
      for (auto n : d_literals)
      {
        bool value;
        if (!d_valuation.hasSatValue(n, value))
        {
          d_forced_count += 1;
          return n;
        }
      }
    }
  }
  else if (!d_notifiedPlugin)
  {
    bool allFalse = true;
    bool anyFalse = false;
    // for (auto n : d_literals)
    for (int i = 0; i < d_literals.size(); ++i)
    {
      Node n = d_literals[i];
      bool value;
      if (!d_valuation.hasSatValue(n, value))
      {
        return n;
      }
      if (value)
      {
        allFalse = false;
      }
      else
      {
        anyFalse = true;
      }
    }
    if (anyFalse && options().parallel.ffdPartitionMode)
    {
      // std::cout << "all false, returning unsat node" << std::endl;
      auto unsatNode = nodeManager()->mkConst(false);
      // return unsatNode;
      // // d_out(statisticsRegistry(), engine, name, d_idCounter)
      // OutputChannel d_out(statisticsRegistry(), d_valuation.d_engine, "ffd",
      // 42);

      d_out->lemma(unsatNode, InferenceId::PARTITION_GENERATOR_PARTITION);
    }
    else if (anyFalse && options().parallel.ffdFastPartitionMode)
    {
      std::vector<Plugin*> plugins = d_env.getPlugins();
      for (auto p : plugins)
      {
        if (p->getName() == "LemmaTransceiver")
        {
          p->handlePartitionSolved();
          d_notifiedPlugin = true;
        }
      }
      // If not sharing, want to stop trying to solve
      if (!d_notifiedPlugin)
      {
        auto unsatNode = nodeManager()->mkConst(false);
        d_out->lemma(unsatNode, InferenceId::PARTITION_GENERATOR_PARTITION);
      }
    }
  }

  return Node::null();
}

DecisionStrategyFmf::DecisionStrategyFmf(Env& env, Valuation valuation)
    : DecisionStrategy(env),
      d_valuation(valuation),
      d_has_curr_literal(context(), false),
      d_curr_literal(context(), 0)
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
        // the current literal has been decided with the right polarity, we are
        // done
        d_has_curr_literal = true;
      }
    }
    else
    {
      Trace("dec-strategy-debug") << "...exhausted literals." << std::endl;
    }
  } while (!success);
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
    if (lit.isNull())
    {
      // literal is not ready yet, return null
      // note we assume that mkLiteral is dynamic here.
      return lit;
    }
    lit = rewrite(lit);
    d_literals.push_back(lit);
  }
  Node ret = d_literals[n];
  // always ensure it is in the CNF stream
  return d_valuation.ensureLiteral(ret);
}

DecisionStrategySingleton::DecisionStrategySingleton(Env& env,
                                                     const char* name,
                                                     Node lit,
                                                     Valuation valuation)
    : DecisionStrategyFmf(env, valuation), d_name(name), d_literal(lit)
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

DecisionStrategyVector::DecisionStrategyVector(Env& env,
                                               const char* name,
                                               Valuation valuation)
    : DecisionStrategyFmf(env, valuation), d_name(name)
{
}

Node DecisionStrategyVector::mkLiteral(unsigned n)
{
  if (n < d_literals.size())
  {
    return d_literals[n];
  }
  return Node::null();
}

void DecisionStrategyVector::addLiteral(const Node& n)
{
  d_literals.push_back(n);
}

}  // namespace theory
}  // namespace cvc5::internal

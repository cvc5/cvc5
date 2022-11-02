/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A field-specific theory
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/sub_theory.h"

#include <CoCoA/BigInt.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/ring.H>

#include <numeric>

#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "smt/env_obj.h"
#include "util/cocoa_globals.h"
#include "util/ff_val.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

SubTheory::SubTheory(Env& env, FfStatistics* stats, Integer modulus)
    : EnvObj(env),
      context::ContextNotifyObj(context()),
      d_facts(context()),
      d_vars(userContext()),
      d_atoms(userContext()),
      d_stats(stats),
      d_baseRing(CoCoA::NewZZmod(CoCoA::BigIntFromString(modulus.toString()))),
      d_modulus(modulus)
{
  AlwaysAssert(modulus.isProbablePrime()) << "non-prime fields are unsupported";
  // must be initialized before using CoCoA.
  initCocoaGlobalManager();
}

void SubTheory::preRegisterTerm(TNode n)
{
  if (n.isVar())
  {
    clearPolyRing();
    d_vars.push_back(n);
  }
  else if (n.getKind() == Kind::EQUAL)
  {
    d_atoms.push_back(n);
  }
}

// CoCoA symbols must start with a letter and contain only letters and
// underscores.
//
// Thus, our encoding is: v_ESCAPED where any underscore or invalid character
// in NAME is replace in ESCAPED with an underscore followed by a base-16
// encoding of its ASCII code using alphabet abcde fghij klmno p, followed by
// another _.
//
// Sorry. It sucks, but we don't have much to work with here...
std::string varNameToSymName(const std::string& varName)
{
  std::ostringstream o;
  o << "v_";
  for (const auto c : varName)
  {
    if (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z'))
    {
      o << c;
    }
    else
    {
      uint8_t code = c;
      o << "_"
        << "abcdefghijklmnop"[code & 0x0f]
        << "abcdefghijklmnop"[(code >> 4) & 0x0f] << "_";
    }
  }
  return o.str();
}

void SubTheory::ensureInitPolyRing()
{
  if (!d_polyRing.has_value())
  {
    std::vector<CoCoA::symbol> symbols;
    for (const auto& v : d_vars)
    {
      symbols.push_back(CoCoA::symbol(varNameToSymName(v.getName())));
    }
    for (size_t i = 0; i < d_atoms.size(); ++i)
    {
      symbols.push_back(CoCoA::symbol("i", i));
    }
    d_polyRing = CoCoA::NewPolyRing(d_baseRing, symbols);
    size_t i = 0;
    Assert(d_translationCache.empty());
    Assert(d_symbolIdxVars.empty());
    for (const auto& v : d_vars)
    {
      d_translationCache.insert({v, CoCoA::indet(d_polyRing.value(), i)});
      d_symbolIdxVars.insert({i, v});
      ++i;
    }
    Assert(d_atomInverses.empty());
    for (const auto& a : d_atoms)
    {
      d_atomInverses.insert({a, CoCoA::indet(d_polyRing.value(), i)});
      Trace("ff::trans") << "inverse for " << a << std::endl;
      ++i;
    }
    Assert(!d_incrementalIdeal.has_value());
    Assert(d_updateIndices.empty());
    d_incrementalIdeal.emplace(d_env, d_polyRing.value());
    d_updateIndices.push_back(0);
  }
}

void SubTheory::clearPolyRing()
{
  d_polyRing.reset();
  d_checkIndices.clear();
  d_atomInverses.clear();
  d_translationCache.clear();
  d_incrementalIdeal.reset();
  d_symbolIdxVars.clear();
  d_updateIndices.clear();
}

void SubTheory::notifyFact(TNode fact)
{
  ensureInitPolyRing();
  d_facts.emplace_back(fact);
  d_model.clear();
}

void SubTheory::postCheck(Theory::Effort e)
{
  d_checkIndices.push_back(d_facts.size());
  auto inc = options().ff.ffIncrementality;
  if (e == Theory::EFFORT_STANDARD)
  {
    if (inc == options::FfIncrementality::EAGER)
    {
      computeBasis(d_facts.size());
    }
  }
  else if (e == Theory::EFFORT_FULL)
  {
    if (inc == options::FfIncrementality::EAGER
        || inc == options::FfIncrementality::LAZY)
    {
      for (size_t i : d_checkIndices)
      {
        if (i > d_updateIndices.back())
        {
          computeBasis(i);
          if (inConflict()) return;
        }
      }
    }
    else
    {
      computeBasis(d_facts.size());
    }
    if (!inConflict())
    {
      extractModel();
    }
  }
}

bool SubTheory::inConflict() const { return !d_conflict.empty(); }

const std::vector<Node>& SubTheory::conflict() const { return d_conflict; }

const std::unordered_map<Node, Node>& SubTheory::model() const
{
  return d_model;
}

void SubTheory::contextNotifyPop()
{
  Trace("ff::context") << "Pop " << context()->getLevel() << std::endl;
  while (d_updateIndices.back() > d_facts.size())
  {
    d_updateIndices.pop_back();
    d_incrementalIdeal.value().pop();
    d_conflict.clear();
  }
  while (d_checkIndices.size() > 0 && d_checkIndices.back() > d_facts.size())
  {
    d_checkIndices.pop_back();
  }
}

void SubTheory::computeBasis(size_t factIndex)
{
  Assert(d_conflict.empty());
  Assert(d_updateIndices.size() > 0);
  Assert(factIndex > d_updateIndices.back());
  IncrementalIdeal& ideal = d_incrementalIdeal.value();
  std::vector<CoCoA::RingElem> newGens;
  for (size_t i = d_updateIndices.back(); i < factIndex; ++i)
  {
    TNode fact = d_facts[i];
    translate(fact);
    newGens.push_back(d_translationCache.at(fact));
  }
  {
    CodeTimer reductionTimer(d_stats->d_reductionTime);
    ideal.pushGenerators(std::move(newGens));
    d_stats->d_numReductions += 1;
  }
  d_updateIndices.push_back(factIndex);
  if (ideal.idealIsTrivial())
  {
    for (size_t i : ideal.trivialCoreIndices())
    {
      d_conflict.push_back(d_facts[i]);
    }
    Trace("ff::conflict") << "conflict " << ideal.trivialCoreIndices().size()
                          << "/" << d_facts.size() << " facts" << std::endl;
    if (TraceChannel.isOn("ff::conflict"))
    {
      Trace("ff::conflict::debug")
          << "conflict " << NodeManager::currentNM()->mkAnd(d_conflict)
          << std::endl;
    }
  }
}

void SubTheory::extractModel()
{
  CodeTimer modelTimer(d_stats->d_modelConstructionTime);
  IncrementalIdeal& ideal = d_incrementalIdeal.value();
  Trace("ff::model") << "constructing model" << std::endl;
  d_model.clear();
  if (ideal.hasSolution())
  {
    Trace("ff::model") << "found model" << std::endl;
    const auto& values = ideal.solution();
    NodeManager* nm = NodeManager::currentNM();
    for (size_t i = 0, numVars = d_vars.size(); i < numVars; ++i)
    {
      std::ostringstream symName;
      symName << CoCoA::indet(d_polyRing.value(), i);
      Node var = d_symbolIdxVars.at(i);
      std::ostringstream valStr;
      valStr << values[i];
      Integer integer(valStr.str(), 10);
      FfVal literal(integer, d_modulus);
      Node value = nm->mkConst(literal);

      Trace("ff::model") << var << ": " << value << std::endl;
      d_model.emplace(var, value);
    }
  }
  else
  {
    ++d_stats->d_numConstructionErrors;
    d_conflict.insert(d_conflict.begin(), d_facts.begin(), d_facts.end());
  }
}

void SubTheory::translate(TNode t)
{
  auto& cache = d_translationCache;
  // Build polynomials for terms
  for (const auto& node :
       NodeDfsIterable(t, VisitOrder::POSTORDER, [&cache](TNode nn) {
         return cache.count(nn) > 0;
       }))
  {
    if (node.getType().isFiniteField() || node.getKind() == Kind::EQUAL
        || node.getKind() == Kind::NOT)
    {
      CoCoA::RingElem poly;
      std::vector<CoCoA::RingElem> subPolys;
      std::transform(node.begin(),
                     node.end(),
                     std::back_inserter(subPolys),
                     [&cache](Node n) { return cache[n]; });
      switch (node.getKind())
      {
        // FF-term cases:
        case Kind::FINITE_FIELD_ADD:
          poly = std::accumulate(
              subPolys.begin(),
              subPolys.end(),
              CoCoA::RingElem(d_polyRing.value()->myZero()),
              [](CoCoA::RingElem a, CoCoA::RingElem b) { return a + b; });
          break;
        case Kind::FINITE_FIELD_NEG: poly = -subPolys[0]; break;
        case Kind::FINITE_FIELD_MULT:
          poly = std::accumulate(
              subPolys.begin(),
              subPolys.end(),
              CoCoA::RingElem(d_polyRing.value()->myOne()),
              [](CoCoA::RingElem a, CoCoA::RingElem b) { return a * b; });
          break;
        case Kind::CONST_FINITE_FIELD:
          poly = d_polyRing.value()->myOne()
                 * CoCoA::BigIntFromString(
                     node.getConst<FfVal>().getValue().toString());
          break;
        // fact cases:
        case Kind::EQUAL: poly = subPolys[0] - subPolys[1]; break;
        case Kind::NOT:
          Assert(node[0].getKind() == Kind::EQUAL);
          poly = subPolys[0] * d_atomInverses.at(node[0]) - 1;
          break;
        default:
          Unreachable() << "Invalid finite field kind: " << node.getKind();
      }
      Trace("ff::trans")
          << "Translated " << node << "\t-> " << poly << std::endl;
      cache.insert(std::make_pair(node, poly));
    }
  }
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */

/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/ring.H>

#include <numeric>

#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "smt/env_obj.h"
#include "theory/ff/core.h"
#include "theory/ff/multi_roots.h"
#include "util/cocoa_globals.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

SubTheory::SubTheory(Env& env, FfStatistics* stats, Integer modulus)
    : EnvObj(env),
      d_facts(context()),
      d_stats(stats),
      d_baseRing(CoCoA::NewZZmod(CoCoA::BigIntFromString(modulus.toString()))),
      d_modulus(modulus)
{
  AlwaysAssert(modulus.isProbablePrime()) << "non-prime fields are unsupported";
  // must be initialized before using CoCoA.
  initCocoaGlobalManager();
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

void SubTheory::notifyFact(TNode fact) { d_facts.emplace_back(fact); }

void SubTheory::postCheck(Theory::Effort e)
{
  d_conflict.clear();
  d_model.clear();
  if (e == Theory::EFFORT_FULL)
  {
    if (d_facts.empty()) return;
    // all theory leaves
    std::vector<Node> leaves{};
    {
      // get all descendents
      std::unordered_set<Node> descendents{};
      for (const Node& node : d_facts)
      {
        for (const auto& child : NodeDfsIterable(
                 node, VisitOrder::POSTORDER, [&descendents](TNode nn) {
                   return descendents.count(nn) > 0;
                 }))
        {
          descendents.insert(child);
        }
      }
      // save those that are leaves
      std::copy_if(descendents.begin(),
                   descendents.end(),
                   std::back_inserter(leaves),
                   [](const Node& n) {
                     return Theory::isLeafOf(n, TheoryId::THEORY_FF)
                            && n.getType().isFiniteField() && !n.isConst();
                   });
    }

    // symbols for all theory leaves, then one inverse for each !=
    std::vector<CoCoA::symbol> symbols;
    {
      // a symbol for each leaf
      size_t leafNum = 0;
      for (const auto& v : leaves)
      {
        std::string name;
        if (v.isVar())
        {
          name = v.getName();
        }
        else
        {
          name = "leaf" + std::to_string(leafNum);
          ++leafNum;
        }
        Trace("ff::trans") << "var " << name << ": " << v << std::endl;
        symbols.push_back(CoCoA::symbol(varNameToSymName(name)));
      }

      // a symbol for each diseq
      size_t numDisequalities =
          std::count_if(d_facts.begin(), d_facts.end(), [&](const Node& node) {
            return node.getKind() == Kind::NOT;
          });
      for (size_t i = 0; i < numDisequalities; ++i)
      {
        symbols.push_back(CoCoA::symbol("i", i));
      }
    }

    // our polynomial ring
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(d_baseRing, symbols);
    // map from nodes to the polynomials that represent them
    std::unordered_map<Node, CoCoA::RingElem> nodeToCocoa{};
    // map from the rings indeterminates (their indices) to the theory leaves
    std::unordered_map<size_t, Node> symbolIdxToLeaves{};

    {
      // map CoCoA indeterminate numbers to leaves
      size_t i = 0;
      for (const auto& v : leaves)
      {
        nodeToCocoa.insert({v, CoCoA::indet(polyRing, i)});
        symbolIdxToLeaves.insert({i, v});
        ++i;
      }
    }

    {
      // populate nodeToCocoa
      size_t disEqIdx = 0;
      for (const Node& fact : d_facts)
      {
        // do a postorder traversal for each fact; skip if already in
        // nodeToCocoa
        for (const auto& node : NodeDfsIterable(
                 fact, VisitOrder::POSTORDER, [&nodeToCocoa](TNode nn) {
                   return nodeToCocoa.count(nn) > 0;
                 }))
        {
          Trace("ff::trans") << "Translating " << node << std::endl;
          Trace("ff::trans") << "size " << nodeToCocoa.size() << std::endl;
          if (node.getType().isFiniteField() || node.getKind() == Kind::EQUAL
              || node.getKind() == Kind::NOT)
          {
            CoCoA::RingElem poly;
            std::vector<CoCoA::RingElem> subPolys;
            std::transform(node.begin(),
                           node.end(),
                           std::back_inserter(subPolys),
                           [&nodeToCocoa](Node n) { return nodeToCocoa[n]; });
            switch (node.getKind())
            {
              // FF-term cases:
              case Kind::FINITE_FIELD_ADD:
                poly = std::accumulate(
                    subPolys.begin(),
                    subPolys.end(),
                    CoCoA::RingElem(polyRing->myZero()),
                    [](CoCoA::RingElem a, CoCoA::RingElem b) { return a + b; });
                break;
              case Kind::FINITE_FIELD_NEG: poly = -subPolys[0]; break;
              case Kind::FINITE_FIELD_MULT:
                poly = std::accumulate(
                    subPolys.begin(),
                    subPolys.end(),
                    CoCoA::RingElem(polyRing->myOne()),
                    [](CoCoA::RingElem a, CoCoA::RingElem b) { return a * b; });
                break;
              case Kind::CONST_FINITE_FIELD:
                poly =
                    polyRing->myOne()
                    * CoCoA::BigIntFromString(node.getConst<FiniteFieldValue>()
                                                  .getValue()
                                                  .toString());
                break;
              // fact cases:
              case Kind::EQUAL:
                Assert(node[0].getType().isFiniteField());
                poly = subPolys[0] - subPolys[1];
                break;
              case Kind::NOT:
              {
                Assert(node[0].getKind() == Kind::EQUAL);
                Assert(node[0][0].getType().isFiniteField());
                CoCoA::RingElem inverse =
                    CoCoA::indet(polyRing, leaves.size() + disEqIdx);
                ++disEqIdx;
                poly = subPolys[0] * inverse - 1;
                break;
              }
              default:
                Unreachable()
                    << "Invalid finite field kind: " << node.getKind();
            }
            Trace("ff::trans")
                << "Translated " << node << "\t-> " << poly << std::endl;
            nodeToCocoa.emplace(node, poly);
          }
        }
      }
    }

    // compute a GB
    std::vector<CoCoA::RingElem> generators;
    std::transform(d_facts.begin(),
                   d_facts.end(),
                   std::back_inserter(generators),
                   [&nodeToCocoa](const Node& fact) {
                     const auto poly = nodeToCocoa.at(fact);
                     Trace("ff::trans") << "Fact: " << fact << std::endl;
                     Trace("ff::trans") << "Poly: " << poly << std::endl;
                     return poly;
                   });
    Tracer tracer(generators);
    if (options().ff.ffFieldPolys)
    {
      for (const auto& var : CoCoA::indets(polyRing))
      {
        CoCoA::BigInt characteristic =
            CoCoA::characteristic(polyRing->myBaseRing());
        long power = CoCoA::LogCardinality(polyRing->myBaseRing());
        CoCoA::BigInt size = CoCoA::power(characteristic, power);
        generators.push_back(CoCoA::power(var, size) - var);
      }
    }
    if (options().ff.ffTraceGb) tracer.setFunctionPointers();
    CoCoA::ideal ideal = CoCoA::ideal(generators);
    const auto basis = CoCoA::GBasis(ideal);
    if (options().ff.ffTraceGb) tracer.unsetFunctionPointers();

    // if it is trivial, create a conflict
    bool is_trivial = basis.size() == 1 && CoCoA::deg(basis.front()) == 0;
    if (is_trivial)
    {
      Trace("ff::gb") << "Trivial GB" << std::endl;
      if (options().ff.ffTraceGb)
      {
        std::vector<size_t> coreIndices = tracer.trace(basis.front());
        Assert(d_conflict.empty());
        for (size_t i : coreIndices)
        {
          Trace("ff::core") << "Core: " << d_facts[i] << std::endl;
          d_conflict.push_back(d_facts[i]);
        }
      }
      else
      {
        setTrivialConflict();
      }
    }
    else
    {
      Trace("ff::gb") << "Non-trivial GB" << std::endl;

      // common root (vec of CoCoA base ring elements)
      std::vector<CoCoA::RingElem> root = commonRoot(ideal);

      if (root.empty())
      {
        // UNSAT
        setTrivialConflict();
      }
      else
      {
        // SAT: populate d_model from the root
        Assert(d_model.empty());
        const auto nm = NodeManager::currentNM();
        for (const auto& idxAndLeaf : symbolIdxToLeaves)
        {
          std::ostringstream valStr;
          valStr << root[idxAndLeaf.first];
          Integer integer(valStr.str(), 10);
          FiniteFieldValue literal(integer, d_modulus);
          Node value = nm->mkConst(literal);
          Trace("ff::model")
              << "Model: " << idxAndLeaf.second << " = " << value << std::endl;
          d_model.emplace(idxAndLeaf.second, value);
        }
      }
    }
    Assert((!d_conflict.empty() ^ !d_model.empty()) || d_facts.empty());
  }
}

void SubTheory::setTrivialConflict()
{
  std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
}

bool SubTheory::inConflict() const { return !d_conflict.empty(); }

const std::vector<Node>& SubTheory::conflict() const { return d_conflict; }

const std::unordered_map<Node, Node>& SubTheory::model() const
{
  return d_model;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */

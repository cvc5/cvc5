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
 * Finite fields UNSAT core construction
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/core.h"

#include <CoCoA/TmpGPoly.H>

#include <sstream>

#include "smt/assertions.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

const std::string INPUT = "!!INPUT";

template <typename T>
std::string ostring(const T& t)
{
  std::ostringstream o;
  o << t;
  return o.str();
}

IncrementalTracer::IncrementalTracer()
{
  d_inputs.emplace_back();
  IncrementalTracer* t = this;
  d_sPoly =
      std::function([=](CoCoA::ConstRefRingElem p,
                        CoCoA::ConstRefRingElem q,
                        CoCoA::ConstRefRingElem s) { t->sPoly(p, q, s); });
  d_reductionStart =
      std::function([=](CoCoA::ConstRefRingElem p) { t->reductionStart(p); });
  d_reductionStep =
      std::function([=](CoCoA::ConstRefRingElem p) { t->reductionStep(p); });
  d_reductionEnd =
      std::function([=](CoCoA::ConstRefRingElem p) { t->reductionEnd(p); });
};

void IncrementalTracer::setFunctionPointers()
{
  CoCoA::handlersEnabled = true;
  CoCoA::sPolyHandler = d_sPoly;
  CoCoA::reductionStartHandler = d_reductionStart;
  CoCoA::reductionStepHandler = d_reductionStep;
  CoCoA::reductionEndHandler = d_reductionEnd;
}

void IncrementalTracer::addInput(const CoCoA::RingElem& i)
{
  Trace("ff::core") << "input: " << i << std::endl;
  std::string si = ostring(i);
  d_inputs.back().push_back(si);
  if (d_parents.count(ostring(i)) == 0)
  {
    Trace("ff::core") << " keep" << std::endl;
    d_inputNumbers[si] = d_nInputs;
    d_parents[si] = {};
  }
  else
  {
    Trace("ff::core") << " drop" << std::endl;
  }
  d_nInputs++;
}

std::vector<size_t> IncrementalTracer::trace(const CoCoA::RingElem& i) const
{
  std::vector<size_t> bs;
  std::vector<std::string> q{ostring(i)};
  std::unordered_set<std::string> visited{q.back()};
  while (q.size())
  {
    const std::string t = q.back();
    Trace("ff::core") << "traceback: " << t << std::endl;
    q.pop_back();
    if (d_inputNumbers.count(t))
    {
      Trace("ff::core") << " blame" << std::endl;
      bs.push_back(d_inputNumbers.at(t));
    }
    else
    {
      AlwaysAssert(d_parents.count(t) > 0);
      const auto& blames = d_parents.at(t);
      AlwaysAssert(blames.size() > 0);
      for (const auto& b : blames)
      {
        if (!visited.count(b))
        {
          visited.insert(b);
          q.push_back(b);
        }
      }
    }
  }
  std::sort(bs.begin(), bs.end());
  return bs;
}

void IncrementalTracer::push()
{
  Trace("ff::core") << "push" << std::endl;
  d_inputs.emplace_back();
}

void IncrementalTracer::pop()
{
  Trace("ff::core") << "pop" << std::endl;
  Assert(d_inputs.size() > 1);
  std::vector<std::string> q;
  for (auto& i : d_inputs.back())
  {
    --d_nInputs;
    if (d_parents[i].empty())
    {
      q.push_back(std::move(i));
    }
  }
  d_inputs.pop_back();
  for (const auto& input : q)
  {
    d_inputNumbers.erase(input);
  }
  while (q.size())
  {
    std::string node = std::move(q.back());
    q.pop_back();
    for (auto& child : d_children[node])
    {
      if (d_parents.count(child))
      {
        q.push_back(std::move(child));
      }
    }
    for (const auto& parent : d_parents[node])
    {
      const auto it = d_children.find(parent);
      if (it != d_children.end())
      {
        it->second.erase(node);
      }
    }
    d_children.erase(node);
    d_parents.erase(node);
  }
}

void IncrementalTracer::sPoly(CoCoA::ConstRefRingElem p,
                              CoCoA::ConstRefRingElem q,
                              CoCoA::ConstRefRingElem s)
{
  std::string ss = ostring(s);
  Trace("ff::core") << "s: " << p << ", " << q << " -> " << s << std::endl;
  if (d_parents.count(ss) == 0)
  {
    Trace("ff::core") << " keep" << std::endl;
    addDep(ostring(p), ss);
    addDep(ostring(q), ss);
  }
  else
  {
    Trace("ff::core") << " drop" << std::endl;
  }
}

void IncrementalTracer::reductionStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_reductionSeq.empty());
  Trace("ff::core") << "reduction start: " << p << std::endl;
  d_reductionSeq.push_back(ostring(p));
}

void IncrementalTracer::reductionStep(CoCoA::ConstRefRingElem q)
{
  Assert(!d_reductionSeq.empty());
  Trace("ff::core") << "reduction step: " << q << std::endl;
  d_reductionSeq.push_back(ostring(q));
}

void IncrementalTracer::reductionEnd(CoCoA::ConstRefRingElem r)
{
  Assert(!d_reductionSeq.empty());
  Trace("ff::core") << "reduction end: " << r << std::endl;
  std::string rr = ostring(r);
  if (d_parents.count(rr) == 0 && rr != d_reductionSeq.front())
  {
    Trace("ff::core") << " keep" << std::endl;
    for (auto& s : d_reductionSeq)
    {
      addDep(s, rr);
    }
  }
  else
  {
    Trace("ff::core") << " drop" << std::endl;
  }
  d_reductionSeq.clear();
}

void IncrementalTracer::addDep(const std::string& parent,
                               const std::string& child)
{
  d_parents[child].push_back(parent);
  d_children[parent].insert(child);
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */

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

Tracer::Tracer(const std::vector<CoCoA::RingElem>& inputs)
    : d_inputNumbers()
{
  for (size_t i = 0, end = inputs.size(); i < end; ++i)
  {
    const std::string s = ostring(inputs[i]);
    d_parents[s] = {};
    Trace("ff::trace") << "input: " << s << std::endl;
    d_inputNumbers.emplace(std::move(s), i);
  }
};

void Tracer::setFunctionPointers()
{
  Tracer* t = this;
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
  Assert(!CoCoA::handlersEnabled);
  CoCoA::handlersEnabled = true;
  CoCoA::sPolyHandler = d_sPoly;
  CoCoA::reductionStartHandler = d_reductionStart;
  CoCoA::reductionStepHandler = d_reductionStep;
  CoCoA::reductionEndHandler = d_reductionEnd;
}

void Tracer::unsetFunctionPointers()
{
  CoCoA::handlersEnabled = false;
}

std::vector<size_t> Tracer::trace(const CoCoA::RingElem& i) const
{
  std::vector<size_t> bs;
  std::vector<std::string> q{ostring(i)};
  std::unordered_set<std::string> visited{q.back()};
  while (q.size())
  {
    const std::string t = q.back();
    Trace("ff::trace") << "traceback: " << t << std::endl;
    q.pop_back();
    if (d_inputNumbers.count(t))
    {
      Trace("ff::trace") << " blame" << std::endl;
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

void Tracer::sPoly(CoCoA::ConstRefRingElem p,
                              CoCoA::ConstRefRingElem q,
                              CoCoA::ConstRefRingElem s)
{
  std::string ss = ostring(s);
  Trace("ff::trace") << "s: " << p << ", " << q << " -> " << s << std::endl;
  if (d_parents.count(ss) == 0)
  {
    Trace("ff::trace") << " keep" << std::endl;
    addDep(ostring(p), ss);
    addDep(ostring(q), ss);
  }
  else
  {
    Trace("ff::trace") << " drop" << std::endl;
  }
}

void Tracer::reductionStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_reductionSeq.empty());
  Trace("ff::trace") << "reduction start: " << p << std::endl;
  d_reductionSeq.push_back(ostring(p));
}

void Tracer::reductionStep(CoCoA::ConstRefRingElem q)
{
  Assert(!d_reductionSeq.empty());
  Trace("ff::trace") << "reduction step: " << q << std::endl;
  d_reductionSeq.push_back(ostring(q));
}

void Tracer::reductionEnd(CoCoA::ConstRefRingElem r)
{
  Assert(!d_reductionSeq.empty());
  Trace("ff::trace") << "reduction end: " << r << std::endl;
  std::string rr = ostring(r);
  if (d_parents.count(rr) == 0 && rr != d_reductionSeq.front())
  {
    Trace("ff::trace") << " keep" << std::endl;
    for (auto& s : d_reductionSeq)
    {
      addDep(s, rr);
    }
  }
  else
  {
    if (TraceIsOn("ff::trace"))
    {
      Trace("ff::trace") << " drop" << std::endl;
      if (d_parents.count(rr))
      {
        Trace("ff::trace") << " parents:";
        for (const auto& p : d_parents.at(rr))
        {
          Trace("ff::trace") << ", " << p;
        }
        Trace("ff::trace") << std::endl;
      }
    }
  }
  d_reductionSeq.clear();
}

void Tracer::addDep(const std::string& parent,
                               const std::string& child)
{
  d_parents[child].push_back(parent);
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */

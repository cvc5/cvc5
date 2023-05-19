/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of new non-linear solver.
 */

#include "theory/arith/nl/equality_substitution.h"

#include "smt/env.h"
#include "theory/arith/arith_utilities.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

namespace {
struct ShouldTraverse : public SubstitutionMap::ShouldTraverseCallback
{
  bool operator()(TNode n) const override
  {
    switch (theory::kindToTheoryId(n.getKind()))
    {
      case TheoryId::THEORY_BOOL:
      case TheoryId::THEORY_BUILTIN: return true;
      case TheoryId::THEORY_ARITH: return !isTranscendentalKind(n.getKind());
      default: return false;
    }
  }
};
}  // namespace

EqualitySubstitution::EqualitySubstitution(Env& env)
    : EnvObj(env), d_substitutions(std::make_unique<SubstitutionMap>())
{
}
void EqualitySubstitution::reset()
{
  d_substitutions = std::make_unique<SubstitutionMap>();
  d_conflict.clear();
  d_conflictMap.clear();
  d_trackOrigin.clear();
}

std::vector<Node> EqualitySubstitution::eliminateEqualities(
    const std::vector<Node>& assertions)
{
  if (TraceIsOn("nl-eqs"))
  {
    Trace("nl-eqs") << "Input:" << std::endl;
    for (const auto& a : assertions)
    {
      Trace("nl-eqs") << "\t" << a << std::endl;
    }
  }
  std::set<TNode> tracker;
  std::vector<Node> asserts = assertions;
  std::vector<Node> next;
  const ShouldTraverse stc;

  size_t last_size = 0;
  while (asserts.size() != last_size)
  {
    last_size = asserts.size();
    // collect all eliminations from original into d_substitutions
    for (const auto& orig : asserts)
    {
      if (orig.getKind() != Kind::EQUAL) continue;
      tracker.clear();
      d_substitutions->invalidateCache();
      Node o =
          d_substitutions->apply(orig, d_env.getRewriter(), &tracker, &stc);
      if (o.getKind() != Kind::EQUAL) continue;
      Assert(o.getNumChildren() == 2);
      for (size_t i = 0; i < 2; ++i)
      {
        const auto& l = (o[i].getKind() == Kind::TO_REAL ? o[i][0] : o[i]);
        const auto& r = (o[1-i].getKind() == Kind::TO_REAL ? o[1-i][0] : o[1-i]);
        // lhs can't be constant
        if (l.isConst()) continue;
        // types must match (otherwise we might have int/real issues)
        if (r.getType() != l.getType()) continue;
        // can't substitute stuff from other theories
        if (!Theory::isLeafOf(l, TheoryId::THEORY_ARITH)) continue;
        // can't substitute the same thing twice
        if (d_substitutions->hasSubstitution(l)) continue;
        // lhs can't be a subexpression of rhs, would leaf to recursion
        if (expr::hasSubterm(r, l)) continue;
        // the same, but after substitution
        d_substitutions->invalidateCache();
        if (expr::hasSubterm(d_substitutions->apply(r, nullptr, nullptr, &stc), l)) continue;
        Trace("nl-eqs") << "Found substitution " << l << " -> " << r
                        << std::endl
                        << " from " << o << " / " << orig << std::endl;
        d_substitutions->addSubstitution(l, r);
        d_trackOrigin.emplace(l, o);
        if (o != orig)
        {
          addToConflictMap(o, orig, tracker);
        }
        break;
      }
    }

    // simplify with subs from original into next
    next.clear();
    for (const auto& a : asserts)
    {
      tracker.clear();
      d_substitutions->invalidateCache();
      Node simp =
          d_substitutions->apply(a, d_env.getRewriter(), &tracker, &stc);
      if (simp.isConst())
      {
        if (simp.getConst<bool>())
        {
          continue;
        }
        Trace("nl-eqs") << "Simplified " << a << " to " << simp << std::endl;
        for (TNode t : tracker)
        {
          Trace("nl-eqs") << "Tracker has " << t << std::endl;
          auto toit = d_trackOrigin.find(t);
          Assert(toit != d_trackOrigin.end());
          d_conflict.emplace_back(toit->second);
        }
        d_conflict.emplace_back(a);
        postprocessConflict(d_conflict);
        Trace("nl-eqs") << "Direct conflict: " << d_conflict << std::endl;
        Trace("nl-eqs") << std::endl
                        << d_conflict.size() << " vs "
                        << std::distance(d_substitutions->begin(),
                                         d_substitutions->end())
                        << std::endl
                        << std::endl;
        return {};
      }
      if (simp != a)
      {
        Trace("nl-eqs") << "Simplified " << a << " to " << simp << std::endl;
        addToConflictMap(simp, a, tracker);
      }
      next.emplace_back(simp);
    }
    asserts = std::move(next);
  }
  d_conflict.clear();
  if (TraceIsOn("nl-eqs"))
  {
    Trace("nl-eqs") << "Output:" << std::endl;
    for (const auto& a : asserts)
    {
      Trace("nl-eqs") << "\t" << a << std::endl;
    }
    Trace("nl-eqs") << "Substitutions:" << std::endl;
    for (const auto& subs : d_substitutions->getSubstitutions())
    {
      Trace("nl-eqs") << "\t" << subs.first << " -> " << subs.second
                      << std::endl;
    }
  }
  return asserts;
}
void EqualitySubstitution::postprocessConflict(
    std::vector<Node>& conflict) const
{
  Trace("nl-eqs") << "Postprocessing " << conflict << std::endl;
  std::set<Node> result;
  for (const auto& c : conflict)
  {
    auto it = d_conflictMap.find(c);
    if (it == d_conflictMap.end())
    {
      result.insert(c);
    }
    else
    {
      Trace("nl-eqs") << "Origin of " << c << ": " << it->second << std::endl;
      result.insert(it->second.begin(), it->second.end());
    }
  }
  conflict.clear();
  conflict.insert(conflict.end(), result.begin(), result.end());
  Trace("nl-eqs") << "-> " << conflict << std::endl;
}
void EqualitySubstitution::insertOrigins(std::set<Node>& dest,
                                         const Node& n) const
{
  auto it = d_conflictMap.find(n);
  if (it == d_conflictMap.end())
  {
    dest.insert(n);
  }
  else
  {
    dest.insert(it->second.begin(), it->second.end());
  }
}
void EqualitySubstitution::addToConflictMap(const Node& n,
                                            const Node& orig,
                                            const std::set<TNode>& tracker)
{
  std::set<Node> origins;
  insertOrigins(origins, orig);
  for (const auto& t : tracker)
  {
    auto tit = d_trackOrigin.find(t);
    Assert(tit != d_trackOrigin.end());
    insertOrigins(origins, tit->second);
  }
  d_conflictMap.emplace(n, std::vector<Node>(origins.begin(), origins.end()));
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

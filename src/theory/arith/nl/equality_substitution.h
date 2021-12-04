/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * CAD-based solver based on https://arxiv.org/pdf/2003.05633.pdf.
 */

#ifndef CVC5__THEORY__ARITH__NL__EQUALITY_SUBSTITUTION_H
#define CVC5__THEORY__ARITH__NL__EQUALITY_SUBSTITUTION_H

#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "smt/env_obj.h"
#include "smt/env.h"
#include "theory/substitutions.h"
#include "theory/theory.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {

class EqualitySubstitution: protected EnvObj
{
    public:
        EqualitySubstitution(Env& env): EnvObj(env), d_substitutions(std::make_unique<SubstitutionMap>()) {
        }
        void reset() {
            d_substitutions = std::make_unique<SubstitutionMap>();
            d_conflict.clear();
            d_conflictMap.clear();
        }
        void addToConflictMap(const Node& n, const Node& orig, const std::set<TNode>& tracker)
        {
            std::set<Node> origins;
            auto it = d_conflictMap.find(orig);
            if (it == d_conflictMap.end())
            {
                origins.insert(orig);
            }
            else
            {
                origins.insert(it->second.begin(), it->second.end());
            }
            for (const auto& t : tracker)
            {
                auto tit = d_trackOrigin.find(t);
                Assert(tit != d_trackOrigin.end());
                Trace("nl-eqs") << "Track origin for " << t << ": " << tit->second << std::endl;
                origins.insert(tit->second);
            }
            Trace("nl-eqs") << "ConflictMap: " << n << " -> " << origins << std::endl;
            d_conflictMap.emplace(n, std::vector<Node>(origins.begin(), origins.end()));

        }

        std::vector<Node> eliminateEqualities(const std::vector<Node>& assertions)
        {
            std::set<TNode> tracker;
            std::vector<Node> asserts = assertions;
            std::vector<Node> next;

            size_t last_size = 0;
            while (asserts.size() != last_size)
            {
                last_size = asserts.size();
                // collect all eliminations from original into d_substitutions
                for (const auto& orig: asserts)
                {
                    if (orig.getKind() != Kind::EQUAL) continue;
                    tracker.clear();
                    d_substitutions->invalidateCache();
                    Node o = d_substitutions->apply(orig, true, &tracker);
                    if (o.getKind() != Kind::EQUAL) continue;
                    Assert(o.getNumChildren() == 2);
                    for (size_t i = 0; i < 2; ++i)
                    {
                        const auto& l = o[i];
                        const auto& r = o[1-i];
                        if (l.isConst()) continue;
                        if (!Theory::isLeafOf(l, TheoryId::THEORY_ARITH)) continue;
                        if (d_substitutions->hasSubstitution(l)) continue;
                        if (expr::hasSubterm(r, l, true)) continue;
                        Trace("nl-eqs") << "Found substitution " << l << " -> " << r << std::endl;
                        d_substitutions->addSubstitution(l, r);
                        d_trackOrigin.emplace(l, o);
                        if (o != orig) {
                            addToConflictMap(o, orig, tracker);
                        }
                        break;
                    }
                    // is o an elimination? Add to subs
                }

                // simplify with subs from original into next
                next.clear();
                for (const auto& a: asserts)
                {
                    tracker.clear();
                    d_substitutions->invalidateCache();
                    Node simp = d_substitutions->apply(a, true, &tracker);
                    Trace("nl-eqs") << "Simplifying " << a << " -> " << simp << std::endl;
                    if (simp.isConst())
                    {
                        if (simp.getConst<bool>())
                        {
                            continue;
                        }
                        Trace("nl-eqs") << "Simplified " << a << " to " << simp << std::endl;
                        for (TNode t: tracker) {
                            Trace("nl-eqs") << "Tracker has " << t << std::endl;
                            auto toit = d_trackOrigin.find(t);
                            Assert(toit != d_trackOrigin.end());
                            d_conflict.emplace_back(toit->second);
                        }
                        d_conflict.emplace_back(a);
                        Trace("nl-eqs") << std::endl << d_conflict.size() << " vs " << std::distance(d_substitutions->begin(), d_substitutions->end()) << std::endl << std::endl;
                        return {};
                    }
                    if (simp != a)
                    {
                        addToConflictMap(simp, a, tracker);
                    }
                    next.emplace_back(simp);
                }
                asserts = std::move(next);
            }
            d_conflict.clear();
            return asserts;
        }
        const SubstitutionMap& getSubstitutions() const {
            return *d_substitutions;
        }
        bool hasConflict() const {
            return !d_conflict.empty();
        }
        const std::vector<Node>& getConflict() const {
            return d_conflict;
        }
        void postprocessConflict(std::vector<Node>& conflict) const {
            Trace("nl-eqs") << "Postprocessing " << conflict << std::endl;
            std::set<Node> result;
            for (const auto& c: conflict)
            {
                auto it = d_conflictMap.find(c);
                if (it == d_conflictMap.end())
                {
                    result.insert(c);
                }
                else {
                    Trace("nl-eqs") << "Origin of " << c << ": " << it->second << std::endl;
                    result.insert(it->second.begin(), it->second.end());
                }
            }
            conflict.clear();
            conflict.insert(conflict.end(), result.begin(), result.end());
            Trace("nl-eqs") << "-> " << conflict << std::endl;
        }
    private:
        // The SubstitutionMap
        std::unique_ptr<SubstitutionMap> d_substitutions;
        // conflicting assertions, if a conflict was found
        std::vector<Node> d_conflict;
        // Maps a simplified assertion to the original assertion + set of original assertions used for substitutions
        std::map<Node, std::vector<Node>> d_conflictMap;
        // Maps substituted terms (what will end up in the tracker) to the equality from which the substitution was derived.
        std::map<Node,Node> d_trackOrigin;
}; 


}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__NL__EQUALITY_SUBSTITUTION_H */

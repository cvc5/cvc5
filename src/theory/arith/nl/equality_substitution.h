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
        }
        std::vector<Node> eliminateEqualities(const std::vector<Node>& assertions)
        {
            std::map<Node,Node> trackOrigin;
            std::set<TNode> tracker;
            std::map<Node,Node> asserts;
            for (const auto& a: assertions) {
                asserts.emplace(a, a);
            }

            size_t last_size = 0;
            while (asserts.size() != last_size)
            {
                last_size = asserts.size();
                // collect all eliminations from original into d_substitutions
                for (auto& orig: asserts)
                {
                    if (orig.second.getKind() != Kind::EQUAL) continue;
                    orig.second = d_substitutions->apply(orig.second, true);
                    if (orig.second.getKind() != Kind::EQUAL) continue;
                    Assert(orig.second.getNumChildren() == 2);
                    for (size_t i = 0; i < 2; ++i)
                    {
                        const auto& l = orig.second[i];
                        const auto& r = orig.second[1-i];
                        if (l.isConst()) continue;
                        if (!Theory::isLeafOf(l, TheoryId::THEORY_ARITH)) continue;
                        if (d_substitutions->hasSubstitution(l)) continue;
                        if (expr::hasSubterm(r, l, true)) continue;
                        d_substitutions->addSubstitution(l, r);
                        trackOrigin.emplace(l, orig.first);
                        break;
                    }
                    // is o an elimination? Add to subs
                }

                // simplify with subs from original into next
                for (auto it = asserts.begin(); it != asserts.end();)
                {
                    it->second = d_substitutions->apply(it->second, true, &tracker);
                    if (it->second.isConst())
                    {
                        if (it->second.getConst<bool>())
                        {
                            it = asserts.erase(it);
                            continue;
                        }
                        for (TNode t: tracker) {
                            auto toit = trackOrigin.find(t);
                            Assert(toit != trackOrigin.end());
                            d_conflict.emplace_back(toit->second);
                        }
                        d_conflict.emplace_back(it->first);
                        //std::cout << std::endl << d_conflict.size() << " vs " << std::distance(d_substitutions->begin(), d_substitutions->end()) << std::endl << std::endl;
                        return {};
                    }
                    ++it;

                }
            }
            std::vector<Node> result;
            for (const auto& a: asserts)
            {
                result.emplace_back(a.second);
            }
            d_conflict.clear();
            return result;
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
    private:
        std::unique_ptr<SubstitutionMap> d_substitutions;
        std::vector<Node> d_conflict;
}; 


}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__NL__EQUALITY_SUBSTITUTION_H */

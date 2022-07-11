/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A shared statistics class for sygus.
 */

#include "theory/quantifiers/sygus/sygus_stats.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusStatistics::SygusStatistics()
    : d_solutions(
        statisticsRegistry().registerInt("SynthConjecture::solutions")),
      d_filtered_solutions(statisticsRegistry().registerInt(
          "SynthConjecture::filtered_solutions")),
      d_candidate_rewrites_print(statisticsRegistry().registerInt(
          "SynthConjecture::candidate_rewrites_print")),
      d_enumTermsRewrite(statisticsRegistry().registerInt(
          "SygusEnumerator::enumTermsRewrite")),
      d_enumTermsExampleEval(statisticsRegistry().registerInt(
          "SygusEnumerator::enumTermsEvalExamples")),
      d_enumTerms(
          statisticsRegistry().registerInt("SygusEnumerator::enumTerms"))

{
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

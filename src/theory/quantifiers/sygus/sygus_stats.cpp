/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A shared statistics class for sygus.
 */

#include "theory/quantifiers/sygus/sygus_stats.h"

#include "smt/smt_statistics_registry.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

SygusStatistics::SygusStatistics()
    : d_solutions(
          smtStatisticsRegistry().registerInt("SynthConjecture::solutions")),
      d_filtered_solutions(smtStatisticsRegistry().registerInt(
          "SynthConjecture::filtered_solutions")),
      d_candidate_rewrites_print(smtStatisticsRegistry().registerInt(
          "SynthConjecture::candidate_rewrites_print")),
      d_enumTermsRewrite(smtStatisticsRegistry().registerInt(
          "SygusEnumerator::enumTermsRewrite")),
      d_enumTermsExampleEval(smtStatisticsRegistry().registerInt(
          "SygusEnumerator::enumTermsEvalExamples")),
      d_enumTerms(
          smtStatisticsRegistry().registerInt("SygusEnumerator::enumTerms"))

{
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

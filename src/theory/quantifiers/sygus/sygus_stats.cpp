/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

SygusStatistics::SygusStatistics(StatisticsRegistry& sr)
    : d_solutions(sr.registerInt("SynthConjecture::solutions")),
      d_filtered_solutions(
          sr.registerInt("SynthConjecture::filtered_solutions")),
      d_enumTermsRewrite(sr.registerInt("SygusEnumerator::enumTermsRewrite")),
      d_enumTermsExampleEval(
          sr.registerInt("SygusEnumerator::enumTermsEvalExamples")),
      d_enumTerms(sr.registerInt("SygusEnumerator::enumTerms"))

{
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

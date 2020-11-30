/*********************                                                        */
/*! \file sygus_stats.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A shared statistics class for sygus.
 **
 **/

#include "theory/quantifiers/sygus/sygus_stats.h"

#include "smt/smt_statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusStatistics::SygusStatistics()
    : d_cegqi_lemmas_ce("SynthEngine::cegqi_lemmas_ce", 0),
      d_cegqi_lemmas_refine("SynthEngine::cegqi_lemmas_refine", 0),
      d_cegqi_si_lemmas("SynthEngine::cegqi_lemmas_si", 0),
      d_solutions("SynthConjecture::solutions", 0),
      d_filtered_solutions("SynthConjecture::filtered_solutions", 0),
      d_candidate_rewrites_print("SynthConjecture::candidate_rewrites_print",
                                 0),
      d_enumTermsRewrite("SygusEnumerator::enumTermsRewrite", 0),
      d_enumTermsExampleEval("SygusEnumerator::enumTermsEvalExamples", 0),
      d_enumTerms("SygusEnumerator::enumTerms", 0)

{
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->registerStat(&d_cegqi_si_lemmas);
  smtStatisticsRegistry()->registerStat(&d_solutions);
  smtStatisticsRegistry()->registerStat(&d_filtered_solutions);
  smtStatisticsRegistry()->registerStat(&d_candidate_rewrites_print);
  smtStatisticsRegistry()->registerStat(&d_enumTermsRewrite);
  smtStatisticsRegistry()->registerStat(&d_enumTermsExampleEval);
  smtStatisticsRegistry()->registerStat(&d_enumTerms);
}

SygusStatistics::~SygusStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_si_lemmas);
  smtStatisticsRegistry()->unregisterStat(&d_solutions);
  smtStatisticsRegistry()->unregisterStat(&d_filtered_solutions);
  smtStatisticsRegistry()->unregisterStat(&d_candidate_rewrites_print);
  smtStatisticsRegistry()->unregisterStat(&d_enumTermsRewrite);
  smtStatisticsRegistry()->unregisterStat(&d_enumTermsExampleEval);
  smtStatisticsRegistry()->unregisterStat(&d_enumTerms);
}

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */

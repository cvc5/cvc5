/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * sygus_enumerator
 */

#include "theory/quantifiers/sygus/sygus_enumerator_callback.h"

#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/example_eval_cache.h"
#include "theory/quantifiers/sygus/sygus_stats.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

SygusEnumeratorCallback::SygusEnumeratorCallback(Node e) : d_enum(e)
{
  d_tn = e.getType();
}

SygusEnumeratorCallbackDefault::SygusEnumeratorCallbackDefault(
    Node e, ExampleEvalCache* eec, SygusStatistics* s, SygusSampler* ssrv)
    : SygusEnumeratorCallback(e), d_eec(eec), d_stats(s), d_samplerRrV(ssrv)
{
}
bool SygusEnumeratorCallbackDefault::addTerm(Node bn, Node bnr, bool isPre)
{
  if (isPre)
  {
    if (d_samplerRrV != nullptr)
    {
      d_samplerRrV->checkEquivalent(bn, bnr);
    }
  }
  else
  {
    // if we are doing PBE symmetry breaking
    if (d_eec != nullptr)
    {
      if (d_stats != nullptr)
      {
        ++(d_stats->d_enumTermsExampleEval);
      }
      // Is it equivalent under examples?
      Node bne = d_eec->addSearchVal(d_tn, bnr);
      if (!bne.isNull())
      {
        if (bnr != bne)
        {
          Trace("sygus-enum-exc")
              << "Exclude (by examples): " << bn << ", since we already have "
              << bne << std::endl;
          return false;
        }
      }
    }
    Trace("sygus-enum-terms") << "tc(" << d_tn << "): term " << bn << std::endl;
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

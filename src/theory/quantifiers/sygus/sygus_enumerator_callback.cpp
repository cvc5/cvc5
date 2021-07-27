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

SygusEnumeratorCallback::SygusEnumeratorCallback(Node e, SygusStatistics* s)
    : d_enum(e), d_stats(s)
{
  d_tn = e.getType();
}

bool SygusEnumeratorCallback::addTerm(Node n, std::unordered_set<Node>& bterms)
{
  Node bn = datatypes::utils::sygusToBuiltin(n);
  Node bnr = d_extr.extendedRewrite(bn);
  if (d_stats != nullptr)
  {
    ++(d_stats->d_enumTermsRewrite);
  }
  // call the solver-specific notify term
  notifyTermInternal(n, bn, bnr);
  // check whether we should keep the term, which is based on the callback,
  // and the builtin terms
  // First, must be unique up to rewriting
  if (bterms.find(bnr) != bterms.end())
  {
    Trace("sygus-enum-exc") << "Exclude: " << bn << std::endl;
    return false;
  }
  // insert to builtin term cache, regardless of whether it is redundant
  // based on the callback
  bterms.insert(bnr);
  // callback-specific add term
  if (!addTermInternal(n, bn, bnr))
  {
    Trace("sygus-enum-exc")
        << "Exclude: " << bn << " due to callback" << std::endl;
    return false;
  }
  Trace("sygus-enum-terms") << "tc(" << d_tn << "): term " << bn << std::endl;
  return true;
}

SygusEnumeratorCallbackDefault::SygusEnumeratorCallbackDefault(
    Node e, SygusStatistics* s, ExampleEvalCache* eec, SygusSampler* ssrv)
    : SygusEnumeratorCallback(e, s), d_eec(eec), d_samplerRrV(ssrv)
{
}
void SygusEnumeratorCallbackDefault::notifyTermInternal(Node n,
                                                        Node bn,
                                                        Node bnr)
{
  if (d_samplerRrV != nullptr)
  {
    d_samplerRrV->checkEquivalent(bn, bnr);
  }
}

bool SygusEnumeratorCallbackDefault::addTermInternal(Node n, Node bn, Node bnr)
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
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

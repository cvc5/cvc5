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
 * sygus_enumerator
 */

#include "theory/quantifiers/sygus/sygus_enumerator_callback.h"

#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/example_eval_cache.h"
#include "theory/quantifiers/sygus/sygus_stats.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/sygus_sampler.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusEnumeratorCallback::SygusEnumeratorCallback(Env& env,
                                                 TermDbSygus* tds,
                                                 SygusStatistics* s,
                                                 ExampleEvalCache* eec)
    : EnvObj(env), d_tds(tds), d_stats(s), d_eec(eec)
{
}

bool SygusEnumeratorCallback::addTerm(const Node& n,
                                      std::unordered_set<Node>& bterms)
{
  Node bn = datatypes::utils::sygusToBuiltin(n);
  if (d_stats != nullptr)
  {
    ++(d_stats->d_enumTermsRewrite);
  }

  // check whether we should keep the term, which is based on the callback,
  // and the builtin terms
  // First, must be unique up to rewriting
  Node cval = getCacheValue(n, bn);
  if (bterms.find(cval) != bterms.end())
  {
    Trace("sygus-enum-exc") << "Exclude (by rewriting): " << bn << std::endl;
    return false;
  }
  // insert to builtin term cache, regardless of whether it is redundant
  // based on the callback
  bterms.insert(cval);

  // callback-specific add term
  if (!addTermInternal(n, bn, cval))
  {
    return false;
  }
  return true;
}

Node SygusEnumeratorCallback::getCacheValue(const Node& n, const Node& bn)
{
  // By default, we cache based on the rewritten form.
  // Further criteria for uniqueness (e.g. weights) may go here.
  return d_tds == nullptr ? extendedRewrite(bn) : d_tds->rewriteNode(bn);
}

bool SygusEnumeratorCallback::addTermInternal(const Node& n,
                                              const Node& bn,
                                              const Node& cval)
{
  // if we are doing PBE symmetry breaking
  if (d_eec != nullptr)
  {
    if (d_stats != nullptr)
    {
      ++(d_stats->d_enumTermsExampleEval);
    }
    // Is it equivalent under examples?
    // NOTE: currently assumes the cache value is the rewritten form of bn
    Assert(cval.getType() == bn.getType());
    Node bne = d_eec->addSearchVal(n.getType(), cval);
    if (!bne.isNull())
    {
      if (cval != bne)
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
}  // namespace cvc5::internal

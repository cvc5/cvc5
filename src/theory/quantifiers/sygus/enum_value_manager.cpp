/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Management of current value for an enumerator
 */
#include "theory/quantifiers/sygus/enum_value_manager.h"

#include "options/base_options.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/sygus/enum_stream_substitution.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_random_enumerator.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_registry.h"

using namespace cvc5::internal::kind;
using namespace std;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EnumValueManager::EnumValueManager(Env& env,
                                   QuantifiersState& qs,
                                   QuantifiersInferenceManager& qim,
                                   TermRegistry& tr,
                                   SygusStatistics& s,
                                   Node e,
                                   bool hasExamples)
    : EnvObj(env),
      d_enum(e),
      d_qstate(qs),
      d_qim(qim),
      d_treg(tr),
      d_stats(s),
      d_tds(tr.getTermDatabaseSygus()),
      d_eec(hasExamples ? new ExampleEvalCache(d_tds, e) : nullptr)
{
}

EnumValueManager::~EnumValueManager() {}

Node EnumValueManager::getEnumeratedValue(bool& activeIncomplete)
{
  Trace("sygus-engine-debug2") << "get enumerated value " << d_enum << " "
                               << d_enum.getType() << std::endl;
  Node e = d_enum;
  bool isEnum = d_tds->isEnumerator(e);

  if (isEnum && !e.getAttribute(SygusSymBreakOkAttribute()))
  {
    // if the current model value of e was not registered by the datatypes
    // sygus solver, or was excluded by symmetry breaking, then it does not
    // have a proper model value that we should consider, thus we return null.
    Trace("sygus-engine-debug2")
        << "...does not have proper model value." << std::endl;
    return Node::null();
  }

  if (!isEnum || d_tds->isPassiveEnumerator(e))
  {
    Trace("sygus-engine-debug2") << "...take model value" << std::endl;
    return getModelValue(e);
  }

  // management of actively generated enumerators goes here

  // initialize the enumerated value generator for e
  if (d_evg == nullptr)
  {
    if (d_tds->isVariableAgnosticEnumerator(e))
    {
      d_evg = std::make_unique<EnumStreamConcrete>(d_env, d_tds);
    }
    else
    {
      // Actively-generated enumerators are currently either variable agnostic
      // or basic. The auto mode always prefers the optimized enumerator over
      // the basic one.
      Assert(d_tds->isBasicEnumerator(e));
      if (options().quantifiers.sygusEnumMode == options::SygusEnumMode::RANDOM)
      {
        d_evg = std::make_unique<SygusRandomEnumerator>(d_env, d_tds);
      }
      else
      {
        Assert(options().quantifiers.sygusEnumMode
                   == options::SygusEnumMode::FAST
               || options().quantifiers.sygusEnumMode
                      == options::SygusEnumMode::AUTO);
        // create the enumerator callback
        if (options().datatypes.sygusRewriter
            != options::SygusRewriterMode::NONE)
        {
          d_secd = std::make_unique<SygusEnumeratorCallback>(
              d_env, d_tds, &d_stats, d_eec.get());
        }
        // if sygus repair const is enabled, we enumerate terms with free
        // variables as arguments to any-constant constructors
        d_evg = std::make_unique<SygusEnumerator>(
            d_env,
            d_tds,
            d_secd.get(),
            &d_stats,
            false,
            options().quantifiers.sygusRepairConst,
            options().quantifiers.sygusEnumFastNumConsts);
      }
    }
    Trace("sygus-active-gen")
        << "Active-gen: initialize for " << e << std::endl;
    d_evg->initialize(e);
    d_ev_curr_active_gen = Node::null();
    Trace("sygus-active-gen-debug") << "...finish" << std::endl;
  }
  // if we have a waiting value, return it
  if (!d_evActiveGenWaiting.isNull())
  {
    Trace("sygus-engine-debug2")
        << "...return waiting " << d_evActiveGenWaiting << std::endl;
    return d_evActiveGenWaiting;
  }
  // Check if there is an (abstract) value absE we were actively generating
  // values based on.
  Node absE = d_ev_curr_active_gen;
  bool firstTime = false;
  if (absE.isNull())
  {
    // None currently exist. The next abstract value is the model value for e.
    absE = getModelValue(e);
    if (TraceIsOn("sygus-active-gen"))
    {
      Trace("sygus-active-gen") << "Active-gen: new abstract value : ";
      TermDbSygus::toStreamSygus("sygus-active-gen", e);
      Trace("sygus-active-gen") << " -> ";
      TermDbSygus::toStreamSygus("sygus-active-gen", absE);
      Trace("sygus-active-gen") << std::endl;
    }
    d_ev_curr_active_gen = absE;
    d_evg->addValue(absE);
    firstTime = true;
  }
  bool inc = true;
  if (!firstTime)
  {
    Trace("sygus-engine-debug2") << "Increment enum" << std::endl;
    inc = d_evg->increment();
    Trace("sygus-engine-debug2") << "...finish" << std::endl;
  }
  Node v;
  if (inc)
  {
    v = d_evg->getCurrent();
  }
  Trace("sygus-active-gen-debug")
      << "...generated " << v << ", with increment success : " << inc
      << std::endl;
  if (!inc)
  {
    // No more concrete values generated from absE.
    NodeManager* nm = NodeManager::currentNM();
    d_ev_curr_active_gen = Node::null();
    std::vector<Node> exp;
    // If we are a basic enumerator, a single abstract value maps to *all*
    // concrete values of its type, thus we don't depend on the current
    // solution.
    if (!d_tds->isBasicEnumerator(e))
    {
      // We must block e = absE
      d_tds->getExplain()->getExplanationForEquality(e, absE, exp);
      for (unsigned i = 0, size = exp.size(); i < size; i++)
      {
        exp[i] = exp[i].negate();
      }
    }
    Node g = d_tds->getActiveGuardForEnumerator(e);
    if (!g.isNull())
    {
      if (d_evActiveGenFirstVal.isNull())
      {
        exp.push_back(g.negate());
        d_evActiveGenFirstVal = absE;
      }
    }
    else
    {
      Assert(false);
    }
    Node lem = exp.size() == 1 ? exp[0] : nm->mkNode(OR, exp);
    Trace("cegqi-lemma") << "Cegqi::Lemma : actively-generated enumerator "
                            "exclude current solution : "
                         << lem << std::endl;
    if (TraceIsOn("sygus-active-gen-debug"))
    {
      Trace("sygus-active-gen-debug") << "Active-gen: block ";
      TermDbSygus::toStreamSygus("sygus-active-gen-debug", absE);
      Trace("sygus-active-gen-debug") << std::endl;
    }
    d_qim.lemma(lem, InferenceId::QUANTIFIERS_SYGUS_ACTIVE_GEN_EXCLUDE_CURRENT);
  }
  else
  {
    // We are waiting to send e -> v to the module that requested it.
    if (v.isNull())
    {
      activeIncomplete = true;
    }
    else
    {
      d_evActiveGenWaiting = v;
    }
    if (TraceIsOn("sygus-active-gen"))
    {
      Trace("sygus-active-gen") << "Active-gen : " << e << " : ";
      TermDbSygus::toStreamSygus("sygus-active-gen", absE);
      Trace("sygus-active-gen") << " -> ";
      TermDbSygus::toStreamSygus("sygus-active-gen", v);
      Trace("sygus-active-gen") << std::endl;
    }
  }

  return v;
}

void EnumValueManager::notifyCandidate(bool modelSuccess)
{
  d_evActiveGenWaiting = Node::null();
  // clear evaluation
  if (modelSuccess && d_eec != nullptr)
  {
    d_eec->clearEvaluationAll();
  }
}

ExampleEvalCache* EnumValueManager::getExampleEvalCache()
{
  return d_eec.get();
}

Node EnumValueManager::getModelValue(Node n)
{
  return d_treg.getModel()->getValue(n);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

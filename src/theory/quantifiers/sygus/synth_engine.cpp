/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the quantifiers module for managing all approaches
 * to synthesis, in particular, those described in Reynolds et al CAV 2015.
 */
#include "theory/quantifiers/sygus/synth_engine.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_registry.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {

SynthEngine::SynthEngine(Env& env,
                         QuantifiersState& qs,
                         QuantifiersInferenceManager& qim,
                         QuantifiersRegistry& qr,
                         TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr), d_conj(nullptr), d_sqp(env)
{
  d_conjs.push_back(std::unique_ptr<SynthConjecture>(
      new SynthConjecture(env, qs, qim, qr, tr, d_statistics)));
  d_conj = d_conjs.back().get();
}

SynthEngine::~SynthEngine() {}

void SynthEngine::presolve()
{
  Trace("sygus-engine") << "SynthEngine::presolve" << std::endl;
  for (unsigned i = 0, size = d_conjs.size(); i < size; i++)
  {
    d_conjs[i]->presolve();
  }
  Trace("sygus-engine") << "SynthEngine::presolve finished" << std::endl;
}

bool SynthEngine::needsCheck(Theory::Effort e)
{
  return e >= Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort SynthEngine::needsModel(Theory::Effort e)
{
  return QEFFORT_MODEL;
}

void SynthEngine::check(Theory::Effort e, QEffort quant_e)
{
  // are we at the proper effort level?
  if (quant_e != QEFFORT_MODEL)
  {
    return;
  }

  // if we are waiting to assign the conjecture, do it now
  bool assigned = !d_waiting_conj.empty();
  while (!d_waiting_conj.empty())
  {
    Node q = d_waiting_conj.back();
    d_waiting_conj.pop_back();
    Trace("sygus-engine") << "--- Conjecture waiting to assign: " << q
                          << std::endl;
    assignConjecture(q);
  }
  if (assigned)
  {
    // assign conjecture always uses the output channel, either by reducing a
    // quantified formula to another, or adding initial lemmas during
    // SynthConjecture::assign. Thus, we return here and re-check.
    return;
  }

  Trace("sygus-engine") << "---Counterexample Guided Instantiation Engine---"
                        << std::endl;
  Trace("sygus-engine-debug") << std::endl;
  Valuation& valuation = d_qstate.getValuation();
  std::vector<SynthConjecture*> activeCheckConj;
  for (unsigned i = 0, size = d_conjs.size(); i < size; i++)
  {
    SynthConjecture* sc = d_conjs[i].get();
    bool active = false;
    bool value;
    if (valuation.hasSatValue(sc->getConjecture(), value))
    {
      active = value;
    }
    else
    {
      Trace("sygus-engine-debug") << "...no value for quantified formula."
                                  << std::endl;
    }
    Trace("sygus-engine-debug")
        << "Current conjecture status : active : " << active << std::endl;
    if (active && sc->needsCheck())
    {
      activeCheckConj.push_back(sc);
    }
  }
  std::vector<SynthConjecture*> acnext;
  do
  {
    Trace("sygus-engine-debug") << "Checking " << activeCheckConj.size()
                                << " active conjectures..." << std::endl;
    for (unsigned i = 0, size = activeCheckConj.size(); i < size; i++)
    {
      SynthConjecture* sc = activeCheckConj[i];
      if (!checkConjecture(sc))
      {
        acnext.push_back(sc);
      }
    }
    activeCheckConj.clear();
    activeCheckConj = acnext;
    acnext.clear();
  } while (!activeCheckConj.empty() && !d_qstate.getValuation().needCheck());
  Trace("sygus-engine")
      << "Finished Counterexample Guided Instantiation engine." << std::endl;
}

void SynthEngine::assignConjecture(Node q)
{
  Trace("sygus-engine") << "SynthEngine::assignConjecture " << q << std::endl;
  if (options().quantifiers.sygusQePreproc)
  {
    Node lem = d_sqp.preprocess(q);
    if (!lem.isNull())
    {
      Trace("cegqi-lemma") << "Cegqi::Lemma : qe-preprocess : " << lem
                           << std::endl;
      d_qim.lemma(lem, InferenceId::QUANTIFIERS_SYGUS_QE_PREPROC);
      // we've reduced the original to a preprocessed version, return
      return;
    }
  }
  // allocate a new synthesis conjecture if not assigned
  if (d_conjs.back()->isAssigned())
  {
    d_conjs.push_back(std::unique_ptr<SynthConjecture>(new SynthConjecture(
        d_env, d_qstate, d_qim, d_qreg, d_treg, d_statistics)));
  }
  d_conjs.back()->assign(q);
}

void SynthEngine::checkOwnership(Node q)
{
  // take ownership of quantified formulas with sygus attribute, and function
  // definitions when the sygusRecFun option is true.
  QuantAttributes& qa = d_qreg.getQuantAttributes();
  if (qa.isSygus(q) || (qa.isFunDef(q) && options().quantifiers.sygusRecFun))
  {
    d_qreg.setOwner(q, this, 2);
  }
}

void SynthEngine::registerQuantifier(Node q)
{
  Trace("cegqi-debug") << "SynthEngine: Register quantifier : " << q
                       << std::endl;
  if (d_qreg.getOwner(q) != this)
  {
    return;
  }
  if (d_qreg.getQuantAttributes().isFunDef(q))
  {
    Assert(options().quantifiers.sygusRecFun);
    // If it is a recursive function definition, add it to the function
    // definition evaluator class.
    Trace("cegqi") << "Registering function definition : " << q << "\n";
    FunDefEvaluator* fde = d_treg.getTermDatabaseSygus()->getFunDefEvaluator();
    fde->assertDefinition(q);
    return;
  }
  Trace("cegqi") << "Register conjecture : " << q << std::endl;
  if (options().quantifiers.sygusQePreproc)
  {
    d_waiting_conj.push_back(q);
  }
  else
  {
    // assign it now
    assignConjecture(q);
  }
}

bool SynthEngine::checkConjecture(SynthConjecture* conj)
{
  if (Trace.isOn("sygus-engine-debug"))
  {
    conj->debugPrint("sygus-engine-debug");
    Trace("sygus-engine-debug") << std::endl;
  }
  Trace("sygus-engine-debug") << "Do conjecture check..." << std::endl;
  Trace("sygus-engine-debug") << "  *** Check candidate phase..." << std::endl;
  size_t prevPending = d_qim.numPendingLemmas();
  bool ret = conj->doCheck();
  // if we added a lemma, return true
  if (d_qim.numPendingLemmas() > prevPending)
  {
    Trace("sygus-engine-debug")
        << "  ...check for counterexample." << std::endl;
    return true;
  }
  return ret;
}

bool SynthEngine::getSynthSolutions(
    std::map<Node, std::map<Node, Node> >& sol_map)
{
  bool ret = true;
  for (unsigned i = 0, size = d_conjs.size(); i < size; i++)
  {
    if (d_conjs[i]->isAssigned())
    {
      if (!d_conjs[i]->getSynthSolutions(sol_map))
      {
        // if one conjecture fails, we fail overall
        ret = false;
        break;
      }
    }
  }
  return ret;
}

void SynthEngine::preregisterAssertion(Node n)
{
  // check if it sygus conjecture
  if (QuantAttributes::checkSygusConjecture(n))
  {
    // this is a sygus conjecture
    Trace("cegqi") << "Preregister sygus conjecture : " << n << std::endl;
    d_conj->preregisterConjecture(n);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

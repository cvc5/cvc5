/*********************                                                        */
/*! \file synth_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the quantifiers module for managing all approaches
 ** to synthesis, in particular, those described in Reynolds et al CAV 2015.
 **
 **/
#include "theory/quantifiers/sygus/synth_engine.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SynthEngine::SynthEngine(QuantifiersEngine* qe, context::Context* c)
    : QuantifiersModule(qe),
      d_tds(qe->getTermDatabaseSygus()),
      d_conj(nullptr),
      d_sqp(qe)
{
  d_conjs.push_back(std::unique_ptr<SynthConjecture>(
      new SynthConjecture(d_quantEngine, d_statistics)));
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
  Valuation& valuation = d_quantEngine->getValuation();
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
        if (!sc->needsRefinement())
        {
          acnext.push_back(sc);
        }
      }
    }
    activeCheckConj.clear();
    activeCheckConj = acnext;
    acnext.clear();
  } while (!activeCheckConj.empty()
           && !d_quantEngine->theoryEngineNeedsCheck());
  Trace("sygus-engine")
      << "Finished Counterexample Guided Instantiation engine." << std::endl;
}

void SynthEngine::assignConjecture(Node q)
{
  Trace("sygus-engine") << "SynthEngine::assignConjecture " << q << std::endl;
  if (options::sygusQePreproc())
  {
    Node lem = d_sqp.preprocess(q);
    if (!lem.isNull())
    {
      Trace("cegqi-lemma") << "Cegqi::Lemma : qe-preprocess : " << lem
                           << std::endl;
      d_quantEngine->getOutputChannel().lemma(lem);
      // we've reduced the original to a preprocessed version, return
      return;
    }
  }
  // allocate a new synthesis conjecture if not assigned
  if (d_conjs.back()->isAssigned())
  {
    d_conjs.push_back(std::unique_ptr<SynthConjecture>(
        new SynthConjecture(d_quantEngine, d_statistics)));
  }
  d_conjs.back()->assign(q);
}

void SynthEngine::registerQuantifier(Node q)
{
  Trace("cegqi-debug") << "SynthEngine: Register quantifier : " << q
                       << std::endl;
  if (d_quantEngine->getOwner(q) != this)
  {
    return;
  }
  if (d_quantEngine->getQuantAttributes()->isFunDef(q))
  {
    Assert(options::sygusRecFun());
    // If it is a recursive function definition, add it to the function
    // definition evaluator class.
    Trace("cegqi") << "Registering function definition : " << q << "\n";
    FunDefEvaluator* fde = d_tds->getFunDefEvaluator();
    fde->assertDefinition(q);
    return;
  }
  Trace("cegqi") << "Register conjecture : " << q << std::endl;
  if (options::sygusQePreproc())
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

  if (!conj->needsRefinement())
  {
    Trace("sygus-engine-debug") << "Do conjecture check..." << std::endl;
    Trace("sygus-engine-debug")
        << "  *** Check candidate phase..." << std::endl;
    std::vector<Node> cclems;
    bool ret = conj->doCheck(cclems);
    bool addedLemma = false;
    for (const Node& lem : cclems)
    {
      if (d_quantEngine->addLemma(lem))
      {
        ++(d_statistics.d_cegqi_lemmas_ce);
        addedLemma = true;
      }
      else
      {
        // this may happen if we eagerly unfold, simplify to true
        Trace("sygus-engine-debug")
            << "  ...FAILED to add candidate!" << std::endl;
      }
    }
    if (addedLemma)
    {
      Trace("sygus-engine-debug")
          << "  ...check for counterexample." << std::endl;
      return true;
    }
    if (!conj->needsRefinement())
    {
      return ret;
    }
    // otherwise, immediately go to refine candidate
  }
  Trace("sygus-engine-debug") << "  *** Refine candidate phase..." << std::endl;
  return conj->doRefine();
}

void SynthEngine::printSynthSolution(std::ostream& out)
{
  Assert(!d_conjs.empty());
  for (unsigned i = 0, size = d_conjs.size(); i < size; i++)
  {
    if (d_conjs[i]->isAssigned())
    {
      d_conjs[i]->printSynthSolution(out);
    }
  }
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
} /* namespace CVC4 */

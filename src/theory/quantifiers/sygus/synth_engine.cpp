/*********************                                                        */
/*! \file synth_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the quantifiers module for managing all approaches
 ** to synthesis, in particular, those described in Reynolds et al CAV 2015.
 **
 **/
#include "theory/quantifiers/sygus/synth_engine.h"

#include "options/quantifiers_options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
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
    : QuantifiersModule(qe)
{
  d_conjs.push_back(std::unique_ptr<SynthConjecture>(
      new SynthConjecture(d_quantEngine, this)));
  d_conj = d_conjs.back().get();
}

SynthEngine::~SynthEngine() {}
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
    Trace("cegqi-engine") << "--- Conjecture waiting to assign: " << q
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

  Trace("cegqi-engine") << "---Counterexample Guided Instantiation Engine---"
                        << std::endl;
  Trace("cegqi-engine-debug") << std::endl;
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
      Trace("cegqi-engine-debug") << "...no value for quantified formula."
                                  << std::endl;
    }
    Trace("cegqi-engine-debug")
        << "Current conjecture status : active : " << active << std::endl;
    if (active && sc->needsCheck())
    {
      activeCheckConj.push_back(sc);
    }
  }
  std::vector<SynthConjecture*> acnext;
  do
  {
    Trace("cegqi-engine-debug") << "Checking " << activeCheckConj.size()
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
           && !d_quantEngine->getTheoryEngine()->needCheck());
  Trace("cegqi-engine")
      << "Finished Counterexample Guided Instantiation engine." << std::endl;
}

void SynthEngine::assignConjecture(Node q)
{
  Trace("cegqi-engine") << "--- Assign conjecture " << q << std::endl;
  if (options::sygusQePreproc())
  {
    // the following does quantifier elimination as a preprocess step
    // for "non-ground single invocation synthesis conjectures":
    //   exists f. forall xy. P[ f(x), x, y ]
    // We run quantifier elimination:
    //   exists y. P[ z, x, y ] ----> Q[ z, x ]
    // Where we replace the original conjecture with:
    //   exists f. forall x. Q[ f(x), x ]
    // For more details, see Example 6 of Reynolds et al. SYNT 2017.
    Node body = q[1];
    if (body.getKind() == NOT && body[0].getKind() == FORALL)
    {
      body = body[0][1];
    }
    NodeManager* nm = NodeManager::currentNM();
    Trace("cegqi-qep") << "Compute single invocation for " << q << "..."
                       << std::endl;
    quantifiers::SingleInvocationPartition sip;
    std::vector<Node> funcs;
    funcs.insert(funcs.end(), q[0].begin(), q[0].end());
    sip.init(funcs, body);
    Trace("cegqi-qep") << "...finished, got:" << std::endl;
    sip.debugPrint("cegqi-qep");

    if (!sip.isPurelySingleInvocation() && sip.isNonGroundSingleInvocation())
    {
      // create new smt engine to do quantifier elimination
      SmtEngine smt_qe(nm->toExprManager());
      smt_qe.setIsInternalSubsolver();
      smt_qe.setLogic(smt::currentSmtEngine()->getLogicInfo());
      Trace("cegqi-qep") << "Property is non-ground single invocation, run "
                            "QE to obtain single invocation."
                         << std::endl;
      // partition variables
      std::vector<Node> all_vars;
      sip.getAllVariables(all_vars);
      std::vector<Node> si_vars;
      sip.getSingleInvocationVariables(si_vars);
      std::vector<Node> qe_vars;
      std::vector<Node> nqe_vars;
      for (unsigned i = 0, size = all_vars.size(); i < size; i++)
      {
        Node v = all_vars[i];
        if (std::find(si_vars.begin(), si_vars.end(), v) == si_vars.end())
        {
          qe_vars.push_back(v);
        }
        else
        {
          nqe_vars.push_back(v);
        }
      }
      std::vector<Node> orig;
      std::vector<Node> subs;
      // skolemize non-qe variables
      for (unsigned i = 0, size = nqe_vars.size(); i < size; i++)
      {
        Node k = nm->mkSkolem(
            "k", nqe_vars[i].getType(), "qe for non-ground single invocation");
        orig.push_back(nqe_vars[i]);
        subs.push_back(k);
        Trace("cegqi-qep") << "  subs : " << nqe_vars[i] << " -> " << k
                           << std::endl;
      }
      std::vector<Node> funcs;
      sip.getFunctions(funcs);
      for (unsigned i = 0, size = funcs.size(); i < size; i++)
      {
        Node f = funcs[i];
        Node fi = sip.getFunctionInvocationFor(f);
        Node fv = sip.getFirstOrderVariableForFunction(f);
        Assert(!fi.isNull());
        orig.push_back(fi);
        Node k =
            nm->mkSkolem("k",
                         fv.getType(),
                         "qe for function in non-ground single invocation");
        subs.push_back(k);
        Trace("cegqi-qep") << "  subs : " << fi << " -> " << k << std::endl;
      }
      Node conj_se_ngsi = sip.getFullSpecification();
      Trace("cegqi-qep") << "Full specification is " << conj_se_ngsi
                         << std::endl;
      Node conj_se_ngsi_subs = conj_se_ngsi.substitute(
          orig.begin(), orig.end(), subs.begin(), subs.end());
      Assert(!qe_vars.empty());
      conj_se_ngsi_subs = nm->mkNode(EXISTS,
                                     nm->mkNode(BOUND_VAR_LIST, qe_vars),
                                     conj_se_ngsi_subs.negate());

      Trace("cegqi-qep") << "Run quantifier elimination on "
                         << conj_se_ngsi_subs << std::endl;
      Expr qe_res = smt_qe.doQuantifierElimination(
          conj_se_ngsi_subs.toExpr(), true, false);
      Trace("cegqi-qep") << "Result : " << qe_res << std::endl;

      // create single invocation conjecture
      Node qe_res_n = Node::fromExpr(qe_res);
      qe_res_n = qe_res_n.substitute(
          subs.begin(), subs.end(), orig.begin(), orig.end());
      if (!nqe_vars.empty())
      {
        qe_res_n =
            nm->mkNode(EXISTS, nm->mkNode(BOUND_VAR_LIST, nqe_vars), qe_res_n);
      }
      Assert(q.getNumChildren() == 3);
      qe_res_n = nm->mkNode(FORALL, q[0], qe_res_n, q[2]);
      Trace("cegqi-qep") << "Converted conjecture after QE : " << qe_res_n
                         << std::endl;
      qe_res_n = Rewriter::rewrite(qe_res_n);
      Node nq = qe_res_n;
      // must assert it is equivalent to the original
      Node lem = q.eqNode(nq);
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
        new SynthConjecture(d_quantEngine, this)));
  }
  d_conjs.back()->assign(q);
}

void SynthEngine::registerQuantifier(Node q)
{
  if (d_quantEngine->getOwner(q) == this)
  {
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
  else
  {
    Trace("cegqi-debug") << "Register quantifier : " << q << std::endl;
  }
}

bool SynthEngine::checkConjecture(SynthConjecture* conj)
{
  Node q = conj->getEmbeddedConjecture();
  Node aq = conj->getConjecture();
  if (Trace.isOn("cegqi-engine-debug"))
  {
    conj->debugPrint("cegqi-engine-debug");
    Trace("cegqi-engine-debug") << std::endl;
  }

  if (!conj->needsRefinement())
  {
    Trace("cegqi-engine-debug") << "Do conjecture check..." << std::endl;
    Trace("cegqi-engine-debug")
        << "  *** Check candidate phase..." << std::endl;
    std::vector<Node> cclems;
    bool ret = conj->doCheck(cclems);
    bool addedLemma = false;
    for (const Node& lem : cclems)
    {
      Trace("cegqi-lemma") << "Cegqi::Lemma : counterexample : " << lem
                           << std::endl;
      if (d_quantEngine->addLemma(lem))
      {
        ++(d_statistics.d_cegqi_lemmas_ce);
        addedLemma = true;
      }
      else
      {
        // this may happen if we eagerly unfold, simplify to true
        Trace("cegqi-engine-debug")
            << "  ...FAILED to add candidate!" << std::endl;
      }
    }
    if (addedLemma)
    {
      Trace("cegqi-engine-debug")
          << "  ...check for counterexample." << std::endl;
      return true;
    }
    else
    {
      if (conj->needsRefinement())
      {
        // immediately go to refine candidate
        return checkConjecture(conj);
      }
    }
    return ret;
  }
  else
  {
    Trace("cegqi-engine-debug")
        << "  *** Refine candidate phase..." << std::endl;
    std::vector<Node> rlems;
    conj->doRefine(rlems);
    bool addedLemma = false;
    for (unsigned i = 0; i < rlems.size(); i++)
    {
      Node lem = rlems[i];
      Trace("cegqi-lemma") << "Cegqi::Lemma : candidate refinement : " << lem
                           << std::endl;
      bool res = d_quantEngine->addLemma(lem);
      if (res)
      {
        ++(d_statistics.d_cegqi_lemmas_refine);
        conj->incrementRefineCount();
        addedLemma = true;
      }
      else
      {
        Trace("cegqi-warn") << "  ...FAILED to add refinement!" << std::endl;
      }
    }
    if (addedLemma)
    {
      Trace("cegqi-engine-debug") << "  ...refine candidate." << std::endl;
    }
  }
  return true;
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

void SynthEngine::getSynthSolutions(std::map<Node, Node>& sol_map)
{
  for (unsigned i = 0, size = d_conjs.size(); i < size; i++)
  {
    if (d_conjs[i]->isAssigned())
    {
      d_conjs[i]->getSynthSolutions(sol_map);
    }
  }
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

SynthEngine::Statistics::Statistics()
    : d_cegqi_lemmas_ce("SynthEngine::cegqi_lemmas_ce", 0),
      d_cegqi_lemmas_refine("SynthEngine::cegqi_lemmas_refine", 0),
      d_cegqi_si_lemmas("SynthEngine::cegqi_lemmas_si", 0),
      d_solutions("SynthConjecture::solutions", 0),
      d_filtered_solutions("SynthConjecture::filtered_solutions", 0),
      d_candidate_rewrites_print("SynthConjecture::candidate_rewrites_print", 0)

{
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->registerStat(&d_cegqi_si_lemmas);
  smtStatisticsRegistry()->registerStat(&d_solutions);
  smtStatisticsRegistry()->registerStat(&d_filtered_solutions);
  smtStatisticsRegistry()->registerStat(&d_candidate_rewrites_print);
}

SynthEngine::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_si_lemmas);
  smtStatisticsRegistry()->unregisterStat(&d_solutions);
  smtStatisticsRegistry()->unregisterStat(&d_filtered_solutions);
  smtStatisticsRegistry()->unregisterStat(&d_candidate_rewrites_print);
}

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */

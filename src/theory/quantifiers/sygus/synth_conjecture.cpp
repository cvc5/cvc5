/*********************                                                        */
/*! \file synth_conjecture.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of class that encapsulates techniques for a single
 ** (SyGuS) synthesis conjecture.
 **/
#include "theory/quantifiers/sygus/synth_conjecture.h"

#include "expr/datatype.h"
#include "options/base_options.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "prop/prop_engine.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/enum_stream_substitution.h"
#include "theory/quantifiers/sygus/synth_engine.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/theory_engine.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SynthConjecture::SynthConjecture(QuantifiersEngine* qe)
    : d_qe(qe),
      d_tds(qe->getTermDatabaseSygus()),
      d_ceg_si(new CegSingleInv(qe, this)),
      d_ceg_proc(new SynthConjectureProcess(qe)),
      d_ceg_gc(new CegGrammarConstructor(qe, this)),
      d_sygus_rconst(new SygusRepairConst(qe)),
      d_ceg_pbe(new SygusPbe(qe, this)),
      d_ceg_cegis(new Cegis(qe, this)),
      d_ceg_cegisUnif(new CegisUnif(qe, this)),
      d_master(nullptr),
      d_set_ce_sk_vars(false),
      d_repair_index(0),
      d_refine_count(0)
{
  if (options::sygusSymBreakPbe() || options::sygusUnifPbe())
  {
    d_modules.push_back(d_ceg_pbe.get());
  }
  if (options::sygusUnif())
  {
    d_modules.push_back(d_ceg_cegisUnif.get());
  }
  d_modules.push_back(d_ceg_cegis.get());
}

SynthConjecture::~SynthConjecture() {}

void SynthConjecture::assign(Node q)
{
  Assert(d_embed_quant.isNull());
  Assert(q.getKind() == FORALL);
  Trace("cegqi") << "SynthConjecture : assign : " << q << std::endl;
  d_quant = q;
  NodeManager* nm = NodeManager::currentNM();

  // pre-simplify the quantified formula based on the process utility
  d_simp_quant = d_ceg_proc->preSimplify(d_quant);

  std::map<Node, Node> templates;
  std::map<Node, Node> templates_arg;
  // register with single invocation if applicable
  if (d_qe->getQuantAttributes()->isSygus(q))
  {
    d_ceg_si->initialize(d_simp_quant);
    d_simp_quant = d_ceg_si->getSimplifiedConjecture();
    // carry the templates
    for (unsigned i = 0; i < q[0].getNumChildren(); i++)
    {
      Node v = q[0][i];
      Node templ = d_ceg_si->getTemplate(v);
      if (!templ.isNull())
      {
        templates[v] = templ;
        templates_arg[v] = d_ceg_si->getTemplateArg(v);
      }
    }
  }

  // post-simplify the quantified formula based on the process utility
  d_simp_quant = d_ceg_proc->postSimplify(d_simp_quant);

  // finished simplifying the quantified formula at this point

  // convert to deep embedding and finalize single invocation here
  d_embed_quant = d_ceg_gc->process(d_simp_quant, templates, templates_arg);
  Trace("cegqi") << "SynthConjecture : converted to embedding : "
                 << d_embed_quant << std::endl;

  // we now finalize the single invocation module, based on the syntax
  // restrictions
  if (d_qe->getQuantAttributes()->isSygus(q))
  {
    d_ceg_si->finishInit(d_ceg_gc->isSyntaxRestricted());
  }

  Assert(d_candidates.empty());
  std::vector<Node> vars;
  for (unsigned i = 0; i < d_embed_quant[0].getNumChildren(); i++)
  {
    vars.push_back(d_embed_quant[0][i]);
    Node e =
        NodeManager::currentNM()->mkSkolem("e", d_embed_quant[0][i].getType());
    d_candidates.push_back(e);
  }
  Trace("cegqi") << "Base quantified formula is : " << d_embed_quant
                 << std::endl;
  // construct base instantiation
  d_base_inst = Rewriter::rewrite(d_qe->getInstantiate()->getInstantiation(
      d_embed_quant, vars, d_candidates));
  Trace("cegqi") << "Base instantiation is :      " << d_base_inst << std::endl;

  // initialize the sygus constant repair utility
  if (options::sygusRepairConst())
  {
    d_sygus_rconst->initialize(d_base_inst.negate(), d_candidates);
    if (options::sygusConstRepairAbort())
    {
      if (!d_sygus_rconst->isActive())
      {
        // no constant repair is possible: abort
        std::stringstream ss;
        ss << "Grammar does not allow repair constants." << std::endl;
        throw LogicException(ss.str());
      }
    }
  }

  // register this term with sygus database and other utilities that impact
  // the enumerative sygus search
  std::vector<Node> guarded_lemmas;
  if (!isSingleInvocation())
  {
    d_ceg_proc->initialize(d_base_inst, d_candidates);
    for (unsigned i = 0, size = d_modules.size(); i < size; i++)
    {
      if (d_modules[i]->initialize(d_base_inst, d_candidates, guarded_lemmas))
      {
        d_master = d_modules[i];
        break;
      }
    }
    Assert(d_master != nullptr);
  }

  Assert(d_qe->getQuantAttributes()->isSygus(q));
  // if the base instantiation is an existential, store its variables
  if (d_base_inst.getKind() == NOT && d_base_inst[0].getKind() == FORALL)
  {
    for (const Node& v : d_base_inst[0][0])
    {
      d_inner_vars.push_back(v);
    }
  }

  // initialize the guard
  d_feasible_guard = nm->mkSkolem("G", nm->booleanType());
  d_feasible_guard = Rewriter::rewrite(d_feasible_guard);
  d_feasible_guard = d_qe->getValuation().ensureLiteral(d_feasible_guard);
  AlwaysAssert(!d_feasible_guard.isNull());
  // register the strategy
  d_feasible_strategy.reset(
      new DecisionStrategySingleton("sygus_feasible",
                                    d_feasible_guard,
                                    d_qe->getSatContext(),
                                    d_qe->getValuation()));
  d_qe->getTheoryEngine()->getDecisionManager()->registerStrategy(
      DecisionManager::STRAT_QUANT_SYGUS_FEASIBLE, d_feasible_strategy.get());
  // this must be called, both to ensure that the feasible guard is
  // decided on with true polariy, but also to ensure that output channel
  // has been used on this call to check.
  d_qe->getOutputChannel().requirePhase(d_feasible_guard, true);

  if (isSingleInvocation())
  {
    std::vector<Node> lems;
    d_ceg_si->getInitialSingleInvLemma(d_feasible_guard, lems);
    for (unsigned i = 0; i < lems.size(); i++)
    {
      Trace("cegqi-lemma") << "Cegqi::Lemma : single invocation " << i << " : "
                           << lems[i] << std::endl;
      d_qe->getOutputChannel().lemma(lems[i]);
      if (Trace.isOn("cegqi-debug"))
      {
        Node rlem = Rewriter::rewrite(lems[i]);
        Trace("cegqi-debug") << "...rewritten : " << rlem << std::endl;
      }
    }
  }
  Node gneg = d_feasible_guard.negate();
  for (unsigned i = 0; i < guarded_lemmas.size(); i++)
  {
    Node lem = nm->mkNode(OR, gneg, guarded_lemmas[i]);
    Trace("cegqi-lemma") << "Cegqi::Lemma : initial (guarded) lemma : " << lem
                         << std::endl;
    d_qe->getOutputChannel().lemma(lem);
  }

  if (options::sygusStream())
  {
    d_stream_strategy.reset(new SygusStreamDecisionStrategy(
        d_qe->getSatContext(), d_qe->getValuation()));
    d_qe->getTheoryEngine()->getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_QUANT_SYGUS_STREAM_FEASIBLE,
        d_stream_strategy.get());
    d_current_stream_guard = d_stream_strategy->getLiteral(0);
  }
  Trace("cegqi") << "...finished, single invocation = " << isSingleInvocation()
                 << std::endl;
}

Node SynthConjecture::getGuard() const { return d_feasible_guard; }

bool SynthConjecture::isSingleInvocation() const
{
  return d_ceg_si->isSingleInvocation();
}

bool SynthConjecture::needsCheck()
{
  if (isSingleInvocation() && !d_ceg_si->needsCheck())
  {
    return false;
  }
  bool value;
  Assert(!d_feasible_guard.isNull());
  // non or fully single invocation : look at guard only
  if (d_qe->getValuation().hasSatValue(d_feasible_guard, value))
  {
    if (!value)
    {
      Trace("cegqi-engine-debug") << "Conjecture is infeasible." << std::endl;
      return false;
    }
  }
  else
  {
    Trace("cegqi-warn") << "WARNING: Guard " << d_feasible_guard
                        << " is not assigned!" << std::endl;
    Assert(false);
  }
  return true;
}

void SynthConjecture::doSingleInvCheck(std::vector<Node>& lems)
{
  if (d_ceg_si != NULL)
  {
    d_ceg_si->check(lems);
  }
}

bool SynthConjecture::needsRefinement() const { return d_set_ce_sk_vars; }
void SynthConjecture::doCheck(std::vector<Node>& lems)
{
  Assert(d_master != nullptr);

  // process the sygus streaming guard
  if (options::sygusStream())
  {
    Assert(!isSingleInvocation());
    // it may be the case that we have a new solution now
    Node currGuard = getCurrentStreamGuard();
    if (currGuard != d_current_stream_guard)
    {
      // we have a new guard, print and continue the stream
      printAndContinueStream();
      d_current_stream_guard = currGuard;
      return;
    }
  }
  bool checkSuccess = false;
  do
  {
    Trace("cegqi-check-debug") << "doCheckNext..." << std::endl;
    checkSuccess = doCheckNext(lems);
    Trace("cegqi-check-debug")
        << "...finished " << lems.empty() << " " << !needsRefinement() << " "
        << !d_qe->getTheoryEngine()->needCheck() << " " << checkSuccess
        << std::endl;
  } while (lems.empty() && !needsRefinement()
           && !d_qe->getTheoryEngine()->needCheck() && checkSuccess);
}

bool SynthConjecture::doCheckNext(std::vector<Node>& lems)
{
  // get the list of terms that the master strategy is interested in
  std::vector<Node> terms;
  d_master->getTermList(d_candidates, terms);

  Assert(!d_candidates.empty());

  Trace("cegqi-check") << "CegConjuncture : check, build candidates..."
                       << std::endl;
  std::vector<Node> candidate_values;
  bool constructed_cand = false;

  // If a module is not trying to repair constants in solutions and the option
  // sygusRepairConst  is true, we use a default scheme for trying to repair
  // constants here.
  if (options::sygusRepairConst() && !d_master->usingRepairConst())
  {
    // have we tried to repair the previous solution?
    // if not, call the repair constant utility
    unsigned ninst = d_cinfo[d_candidates[0]].d_inst.size();
    if (d_repair_index < ninst)
    {
      std::vector<Node> fail_cvs;
      for (const Node& cprog : d_candidates)
      {
        Assert(d_repair_index < d_cinfo[cprog].d_inst.size());
        fail_cvs.push_back(d_cinfo[cprog].d_inst[d_repair_index]);
      }
      if (Trace.isOn("cegqi-engine"))
      {
        Trace("cegqi-engine") << "CegConjuncture : repair previous solution ";
        for (const Node& fc : fail_cvs)
        {
          std::stringstream ss;
          Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, fc);
          Trace("cegqi-engine") << ss.str() << " ";
        }
        Trace("cegqi-engine") << std::endl;
      }
      d_repair_index++;
      if (d_sygus_rconst->repairSolution(
              d_candidates, fail_cvs, candidate_values, true))
      {
        constructed_cand = true;
      }
    }
  }

  if (!constructed_cand)
  {
    // get the model value of the relevant terms from the master module
    std::vector<Node> enum_values;
    bool fullModel = getEnumeratedValues(terms, enum_values);

    // if the master requires a full model and the model is partial, we fail
    if (!d_master->allowPartialModel() && !fullModel)
    {
      // we retain the values in d_ev_active_gen_waiting
      Trace("cegqi-engine") << "...partial model, fail." << std::endl;
      return false;
    }
    // the waiting values are passed to the module below, clear
    d_ev_active_gen_waiting.clear();

    // debug print
    Assert(terms.size() == enum_values.size());
    bool emptyModel = true;
    Trace("cegqi-engine") << "  * Value is : ";
    for (unsigned i = 0, size = terms.size(); i < size; i++)
    {
      Node nv = enum_values[i];
      if (!nv.isNull())
      {
        emptyModel = false;
      }
      if (Trace.isOn("cegqi-engine"))
      {
        Node onv = nv.isNull() ? d_qe->getModel()->getValue(terms[i]) : nv;
        TypeNode tn = onv.getType();
        std::stringstream ss;
        Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, onv);
        Trace("cegqi-engine") << terms[i] << " -> ";
        if (nv.isNull())
        {
          Trace("cegqi-engine") << "[EXC: " << ss.str() << "] ";
        }
        else
        {
          Trace("cegqi-engine") << ss.str() << " ";
          if (Trace.isOn("cegqi-engine-rr"))
          {
            Node bv = d_tds->sygusToBuiltin(nv, tn);
            bv = Rewriter::rewrite(bv);
            Trace("cegqi-engine-rr") << " -> " << bv << std::endl;
          }
        }
      }
    }
    Trace("cegqi-engine") << std::endl;
    if (emptyModel)
    {
      Trace("cegqi-engine") << "...empty model, fail." << std::endl;
      return false;
    }
    Assert(candidate_values.empty());
    constructed_cand = d_master->constructCandidates(
        terms, enum_values, d_candidates, candidate_values, lems);
  }

  NodeManager* nm = NodeManager::currentNM();

  // must get a counterexample to the value of the current candidate
  Node inst;
  if (constructed_cand)
  {
    if (Trace.isOn("cegqi-check"))
    {
      Trace("cegqi-check") << "CegConjuncture : check candidate : "
                           << std::endl;
      for (unsigned i = 0, size = candidate_values.size(); i < size; i++)
      {
        Trace("cegqi-check") << "  " << i << " : " << d_candidates[i] << " -> "
                             << candidate_values[i] << std::endl;
      }
    }
    Assert(candidate_values.size() == d_candidates.size());
    inst = d_base_inst.substitute(d_candidates.begin(),
                                  d_candidates.end(),
                                  candidate_values.begin(),
                                  candidate_values.end());
  }
  else
  {
    inst = d_base_inst;
  }

  // check whether we will run CEGIS on inner skolem variables
  bool sk_refine = (!isGround() || d_refine_count == 0) && constructed_cand;
  if (sk_refine)
  {
    if (options::cegisSample() == CEGIS_SAMPLE_TRUST)
    {
      // we have that the current candidate passed a sample test
      // since we trust sampling in this mode, we assert there is no
      // counterexample to the conjecture here.
      Node lem = nm->mkNode(OR, d_quant.negate(), nm->mkConst(false));
      lem = getStreamGuardedLemma(lem);
      lems.push_back(lem);
      recordInstantiation(candidate_values);
      return true;
    }
    Assert(!d_set_ce_sk_vars);
  }
  else
  {
    if (!constructed_cand)
    {
      return true;
    }
  }

  // immediately skolemize inner existentials
  Node lem;
  // introduce the skolem variables
  std::vector<Node> sks;
  if (constructed_cand)
  {
    if (inst.getKind() == NOT && inst[0].getKind() == FORALL)
    {
      std::vector<Node> vars;
      for (const Node& v : inst[0][0])
      {
        Node sk = nm->mkSkolem("rsk", v.getType());
        sks.push_back(sk);
        vars.push_back(v);
        Trace("cegqi-check-debug")
            << "  introduce skolem " << sk << " for " << v << "\n";
      }
      lem = inst[0][1].substitute(
          vars.begin(), vars.end(), sks.begin(), sks.end());
      lem = lem.negate();
    }
    else
    {
      // use the instance itself
      lem = inst;
    }
  }
  if (sk_refine)
  {
    d_ce_sk_vars.insert(d_ce_sk_vars.end(), sks.begin(), sks.end());
    d_set_ce_sk_vars = true;
  }

  if (lem.isNull())
  {
    // no lemma to check
    return true;
  }

  lem = Rewriter::rewrite(lem);
  // eagerly unfold applications of evaluation function
  Trace("cegqi-debug") << "pre-unfold counterexample : " << lem << std::endl;
  std::map<Node, Node> visited_n;
  lem = d_tds->getEagerUnfold(lem, visited_n);
  // record the instantiation
  // this is used for remembering the solution
  recordInstantiation(candidate_values);
  Node query = lem;
  bool success = false;
  if (query.isConst() && !query.getConst<bool>())
  {
    // short circuit the check
    lem = d_quant.negate();
    success = true;
  }
  else
  {
    // This is the "verification lemma", which states
    // either this conjecture does not have a solution, or candidate_values
    // is a solution for this conjecture.
    lem = nm->mkNode(OR, d_quant.negate(), query);
    if (options::sygusVerifySubcall())
    {
      Trace("cegqi-engine") << "  *** Verify with subcall..." << std::endl;
      SmtEngine verifySmt(nm->toExprManager());
      verifySmt.setLogic(smt::currentSmtEngine()->getLogicInfo());
      verifySmt.assertFormula(query.toExpr());
      Result r = verifySmt.checkSat();
      Trace("cegqi-engine") << "  ...got " << r << std::endl;
      if (r.asSatisfiabilityResult().isSat() == Result::SAT)
      {
        Trace("cegqi-engine") << "  * Verification lemma failed for:\n   ";
        // do not send out
        for (const Node& v : d_ce_sk_vars)
        {
          Node mv = Node::fromExpr(verifySmt.getValue(v.toExpr()));
          Trace("cegqi-engine") << v << " -> " << mv << " ";
          d_ce_sk_var_mvs.push_back(mv);
        }
        Trace("cegqi-engine") << std::endl;
#ifdef CVC4_ASSERTIONS
        // the values for the query should be a complete model
        Node squery = query.substitute(d_ce_sk_vars.begin(),
                                       d_ce_sk_vars.end(),
                                       d_ce_sk_var_mvs.begin(),
                                       d_ce_sk_var_mvs.end());
        Trace("cegqi-debug") << "...squery : " << squery << std::endl;
        squery = Rewriter::rewrite(squery);
        Trace("cegqi-debug") << "...rewrites to : " << squery << std::endl;
        Assert(squery.isConst() && squery.getConst<bool>());
#endif
        return true;
      }
      else if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
      {
        // if the result in the subcall was unsatisfiable, we avoid
        // rechecking, hence we drop "query" from the verification lemma
        lem = d_quant.negate();
        // we can short circuit adding the lemma (for sygus stream)
        success = true;
      }
      // In the rare case that the subcall is unknown, we add the verification
      // lemma in the main solver. This should only happen if the quantifier
      // free logic is undecidable.
    }
  }
  if (success && options::sygusStream())
  {
    // if we were successful, we immediately print the current solution.
    // this saves us from introducing a verification lemma and a new guard.
    printAndContinueStream();
    return true;
  }
  lem = getStreamGuardedLemma(lem);
  lems.push_back(lem);
  return true;
}

void SynthConjecture::doRefine(std::vector<Node>& lems)
{
  Assert(lems.empty());
  Assert(d_set_ce_sk_vars);

  // first, make skolem substitution
  Trace("cegqi-refine") << "doRefine : construct skolem substitution..."
                        << std::endl;
  std::vector<Node> sk_vars;
  std::vector<Node> sk_subs;
  // collect the substitution over all disjuncts
  if (!d_ce_sk_vars.empty())
  {
    Trace("cegqi-refine") << "Get model values for skolems..." << std::endl;
    Assert(d_inner_vars.size() == d_ce_sk_vars.size());
    if (d_ce_sk_var_mvs.empty())
    {
      std::vector<Node> model_values;
      for (const Node& v : d_ce_sk_vars)
      {
        Node mv = getModelValue(v);
        Trace("cegqi-refine") << "  " << v << " -> " << mv << std::endl;
        model_values.push_back(mv);
      }
      sk_subs.insert(sk_subs.end(), model_values.begin(), model_values.end());
    }
    else
    {
      Assert(d_ce_sk_var_mvs.size() == d_ce_sk_vars.size());
      sk_subs.insert(
          sk_subs.end(), d_ce_sk_var_mvs.begin(), d_ce_sk_var_mvs.end());
    }
    sk_vars.insert(sk_vars.end(), d_inner_vars.begin(), d_inner_vars.end());
  }
  else
  {
    Assert(d_inner_vars.empty());
  }

  std::vector<Node> lem_c;
  Trace("cegqi-refine") << "doRefine : Construct refinement lemma..."
                        << std::endl;
  Trace("cegqi-refine-debug")
      << "  For counterexample skolems : " << d_ce_sk_vars << std::endl;
  Node base_lem;
  if (d_base_inst.getKind() == NOT && d_base_inst[0].getKind() == FORALL)
  {
    base_lem = d_base_inst[0][1];
  }
  else
  {
    base_lem = d_base_inst.negate();
  }

  Assert(sk_vars.size() == sk_subs.size());

  Trace("cegqi-refine") << "doRefine : substitute..." << std::endl;
  base_lem = base_lem.substitute(
      sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end());
  Trace("cegqi-refine") << "doRefine : rewrite..." << std::endl;
  base_lem = Rewriter::rewrite(base_lem);
  Trace("cegqi-refine") << "doRefine : register refinement lemma " << base_lem
                        << "..." << std::endl;
  d_master->registerRefinementLemma(sk_vars, base_lem, lems);
  Trace("cegqi-refine") << "doRefine : finished" << std::endl;
  d_set_ce_sk_vars = false;
  d_ce_sk_vars.clear();
  d_ce_sk_var_mvs.clear();
}

void SynthConjecture::preregisterConjecture(Node q)
{
  d_ceg_si->preregisterConjecture(q);
}

bool SynthConjecture::getEnumeratedValues(std::vector<Node>& n,
                                          std::vector<Node>& v)
{
  bool ret = true;
  for (unsigned i = 0; i < n.size(); i++)
  {
    Node nv = getEnumeratedValue(n[i]);
    v.push_back(nv);
    ret = ret && !nv.isNull();
  }
  return ret;
}

Node SynthConjecture::getEnumeratedValue(Node e)
{
  if (e.getAttribute(SygusSymBreakExcAttribute()))
  {
    // if the current model value of e was excluded by symmetry breaking, then
    // it does not have a proper model value that we should consider, thus we
    // return null.
    return Node::null();
  }

  if (!d_tds->isEnumerator(e) || d_tds->isPassiveEnumerator(e))
  {
    return getModelValue(e);
  }
  // management of actively generated enumerators goes here

  // initialize the enumerated value generator for e
  std::map<Node, std::unique_ptr<EnumValGenerator> >::iterator iteg =
      d_evg.find(e);
  if (iteg == d_evg.end())
  {
    d_evg[e].reset(new EnumStreamConcrete(d_tds));
    Trace("sygus-active-gen")
        << "Active-gen: initialize for " << e << std::endl;
    d_evg[e]->initialize(e);
    d_ev_curr_active_gen[e] = Node::null();
    iteg = d_evg.find(e);
    Trace("sygus-active-gen-debug") << "...finish" << std::endl;
  }
  // if we have a waiting value, return it
  std::map<Node, Node>::iterator itw = d_ev_active_gen_waiting.find(e);
  if (itw != d_ev_active_gen_waiting.end())
  {
    Trace("sygus-active-gen-debug")
        << "Active-gen: return waiting " << itw->second << std::endl;
    return itw->second;
  }
  // Check if there is an (abstract) value absE we were actively generating
  // values based on.
  Node absE = d_ev_curr_active_gen[e];
  if (absE.isNull())
  {
    // None currently exist. The next abstract value is the model value for e.
    absE = getModelValue(e);
    if (Trace.isOn("sygus-active-gen"))
    {
      Trace("sygus-active-gen") << "Active-gen: new abstract value : ";
      TermDbSygus::toStreamSygus("sygus-active-gen", e);
      Trace("sygus-active-gen") << " -> ";
      TermDbSygus::toStreamSygus("sygus-active-gen", absE);
      Trace("sygus-active-gen") << std::endl;
    }
    d_ev_curr_active_gen[e] = absE;
    iteg->second->addValue(absE);
  }
  Node v = iteg->second->getNext();
  if (v.isNull())
  {
    // No more concrete values generated from absE.
    NodeManager* nm = NodeManager::currentNM();
    d_ev_curr_active_gen[e] = Node::null();
    // We must block e = absE.
    std::vector<Node> exp;
    d_tds->getExplain()->getExplanationForEquality(e, absE, exp);
    for (unsigned i = 0, size = exp.size(); i < size; i++)
    {
      exp[i] = exp[i].negate();
    }
    Node g = d_tds->getActiveGuardForEnumerator(e);
    if (!g.isNull())
    {
      if (d_ev_active_gen_first_val.find(e) == d_ev_active_gen_first_val.end())
      {
        exp.push_back(g.negate());
        d_ev_active_gen_first_val[e] = absE;
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
    if (Trace.isOn("sygus-active-gen-debug"))
    {
      Trace("sygus-active-gen-debug") << "Active-gen: block ";
      TermDbSygus::toStreamSygus("sygus-active-gen-debug", absE);
      Trace("sygus-active-gen-debug") << std::endl;
    }
    d_qe->getOutputChannel().lemma(lem);
  }
  else
  {
    // We are waiting to send e -> v to the module that requested it.
    d_ev_active_gen_waiting[e] = v;
    if (Trace.isOn("sygus-active-gen"))
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

Node SynthConjecture::getModelValue(Node n)
{
  Trace("cegqi-mv") << "getModelValue for : " << n << std::endl;
  return d_qe->getModel()->getValue(n);
}

void SynthConjecture::debugPrint(const char* c)
{
  Trace(c) << "Synthesis conjecture : " << d_embed_quant << std::endl;
  Trace(c) << "  * Candidate programs : " << d_candidates << std::endl;
  Trace(c) << "  * Counterexample skolems : " << d_ce_sk_vars << std::endl;
}

Node SynthConjecture::getCurrentStreamGuard() const
{
  if (d_stream_strategy != nullptr)
  {
    // the stream guard is the current asserted literal of the stream strategy
    Node lit = d_stream_strategy->getAssertedLiteral();
    if (lit.isNull())
    {
      // if none exist, get the first
      lit = d_stream_strategy->getLiteral(0);
    }
    return lit;
  }
  return Node::null();
}

Node SynthConjecture::getStreamGuardedLemma(Node n) const
{
  if (options::sygusStream())
  {
    // if we are in streaming mode, we guard with the current stream guard
    Node csg = getCurrentStreamGuard();
    Assert(!csg.isNull());
    return NodeManager::currentNM()->mkNode(kind::OR, csg.negate(), n);
  }
  return n;
}

SynthConjecture::SygusStreamDecisionStrategy::SygusStreamDecisionStrategy(
    context::Context* satContext, Valuation valuation)
    : DecisionStrategyFmf(satContext, valuation)
{
}

Node SynthConjecture::SygusStreamDecisionStrategy::mkLiteral(unsigned i)
{
  NodeManager* nm = NodeManager::currentNM();
  Node curr_stream_guard = nm->mkSkolem("G_Stream", nm->booleanType());
  return curr_stream_guard;
}

void SynthConjecture::printAndContinueStream()
{
  Assert(d_master != nullptr);
  // we have generated a solution, print it
  // get the current output stream
  // this output stream should coincide with wherever --dump-synth is output on
  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  printSynthSolution(*nodeManagerOptions.getOut(), false);

  // We will not refine the current candidate solution since it is a solution
  // thus, we clear information regarding the current refinement
  d_set_ce_sk_vars = false;
  d_ce_sk_vars.clear();
  d_ce_sk_var_mvs.clear();
  // However, we need to exclude the current solution using an explicit
  // blocking clause, so that we proceed to the next solution. We do this only
  // for passively-generated enumerators (TermDbSygus::isPassiveEnumerator).
  std::vector<Node> terms;
  d_master->getTermList(d_candidates, terms);
  std::vector<Node> exp;
  for (const Node& cprog : terms)
  {
    Assert(d_tds->isEnumerator(cprog));
    if (d_tds->isPassiveEnumerator(cprog))
    {
      Node sol = cprog;
      if (!d_cinfo[cprog].d_inst.empty())
      {
        sol = d_cinfo[cprog].d_inst.back();
        // add to explanation of exclusion
        d_tds->getExplain()->getExplanationForEquality(cprog, sol, exp);
      }
    }
  }
  if (!exp.empty())
  {
    Node exc_lem = exp.size() == 1
                       ? exp[0]
                       : NodeManager::currentNM()->mkNode(kind::AND, exp);
    exc_lem = exc_lem.negate();
    Trace("cegqi-lemma") << "Cegqi::Lemma : stream exclude current solution : "
                         << exc_lem << std::endl;
    d_qe->getOutputChannel().lemma(exc_lem);
  }
}

void SynthConjecture::printSynthSolution(std::ostream& out,
                                         bool singleInvocation)
{
  Trace("cegqi-debug") << "Printing synth solution..." << std::endl;
  Assert(d_quant[0].getNumChildren() == d_embed_quant[0].getNumChildren());
  std::vector<Node> sols;
  std::vector<int> statuses;
  if (!getSynthSolutionsInternal(sols, statuses, singleInvocation))
  {
    return;
  }
  for (unsigned i = 0, size = d_embed_quant[0].getNumChildren(); i < size; i++)
  {
    Node sol = sols[i];
    if (!sol.isNull())
    {
      Node prog = d_embed_quant[0][i];
      int status = statuses[i];
      TypeNode tn = prog.getType();
      const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
      std::stringstream ss;
      ss << prog;
      std::string f(ss.str());
      f.erase(f.begin());
      SynthEngine* cei = d_qe->getSynthEngine();
      ++(cei->d_statistics.d_solutions);

      bool is_unique_term = true;

      if (status != 0 && options::sygusRewSynth())
      {
        std::map<Node, ExpressionMinerManager>::iterator its =
            d_exprm.find(prog);
        if (its == d_exprm.end())
        {
          d_exprm[prog].initializeSygus(
              d_qe, d_candidates[i], options::sygusSamples(), true);
          if (options::sygusRewSynth())
          {
            d_exprm[prog].enableRewriteRuleSynth();
          }
          its = d_exprm.find(prog);
        }
        bool rew_print = false;
        is_unique_term = d_exprm[prog].addTerm(sol, out, rew_print);
        if (rew_print)
        {
          ++(cei->d_statistics.d_candidate_rewrites_print);
        }
        if (!is_unique_term)
        {
          ++(cei->d_statistics.d_candidate_rewrites);
        }
      }
      if (is_unique_term)
      {
        out << "(define-fun " << f << " ";
        if (dt.getSygusVarList().isNull())
        {
          out << "() ";
        }
        else
        {
          out << dt.getSygusVarList() << " ";
        }
        out << dt.getSygusType() << " ";
        if (status == 0)
        {
          out << sol;
        }
        else
        {
          Printer::getPrinter(options::outputLanguage())
              ->toStreamSygus(out, sol);
        }
        out << ")" << std::endl;
      }
    }
  }
}

void SynthConjecture::getSynthSolutions(std::map<Node, Node>& sol_map,
                                        bool singleInvocation)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> sols;
  std::vector<int> statuses;
  if (!getSynthSolutionsInternal(sols, statuses, singleInvocation))
  {
    return;
  }
  for (unsigned i = 0, size = d_embed_quant[0].getNumChildren(); i < size; i++)
  {
    Node sol = sols[i];
    int status = statuses[i];
    // get the builtin solution
    Node bsol = sol;
    if (status != 0)
    {
      // convert sygus to builtin here
      bsol = d_tds->sygusToBuiltin(sol, sol.getType());
    }
    // convert to lambda
    TypeNode tn = d_embed_quant[0][i].getType();
    const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
    Node bvl = Node::fromExpr(dt.getSygusVarList());
    if (!bvl.isNull())
    {
      bsol = nm->mkNode(LAMBDA, bvl, bsol);
    }
    // store in map
    Node fvar = d_quant[0][i];
    Assert(fvar.getType() == bsol.getType());
    sol_map[fvar] = bsol;
  }
}

bool SynthConjecture::getSynthSolutionsInternal(std::vector<Node>& sols,
                                                std::vector<int>& statuses,
                                                bool singleInvocation)
{
  for (unsigned i = 0, size = d_embed_quant[0].getNumChildren(); i < size; i++)
  {
    Node prog = d_embed_quant[0][i];
    Trace("cegqi-debug") << "  get solution for " << prog << std::endl;
    TypeNode tn = prog.getType();
    Assert(tn.isDatatype());
    // get the solution
    Node sol;
    int status = -1;
    if (singleInvocation)
    {
      Assert(d_ceg_si != NULL);
      sol = d_ceg_si->getSolution(i, tn, status, true);
      if (sol.isNull())
      {
        return false;
      }
      sol = sol.getKind() == LAMBDA ? sol[1] : sol;
    }
    else
    {
      Node cprog = getCandidate(i);
      if (!d_cinfo[cprog].d_inst.empty())
      {
        // the solution is just the last instantiated term
        sol = d_cinfo[cprog].d_inst.back();
        status = 1;

        // check if there was a template
        Node sf = d_quant[0][i];
        Node templ = d_ceg_si->getTemplate(sf);
        if (!templ.isNull())
        {
          Trace("cegqi-inv-debug")
              << sf << " used template : " << templ << std::endl;
          // if it was not embedded into the grammar
          if (!options::sygusTemplEmbedGrammar())
          {
            TNode templa = d_ceg_si->getTemplateArg(sf);
            // make the builtin version of the full solution
            sol = d_tds->sygusToBuiltin(sol, sol.getType());
            Trace("cegqi-inv") << "Builtin version of solution is : " << sol
                               << ", type : " << sol.getType() << std::endl;
            TNode tsol = sol;
            sol = templ.substitute(templa, tsol);
            Trace("cegqi-inv-debug") << "With template : " << sol << std::endl;
            sol = Rewriter::rewrite(sol);
            Trace("cegqi-inv-debug") << "Simplified : " << sol << std::endl;
            // now, reconstruct to the syntax
            sol = d_ceg_si->reconstructToSyntax(sol, tn, status, true);
            sol = sol.getKind() == LAMBDA ? sol[1] : sol;
            Trace("cegqi-inv-debug")
                << "Reconstructed to syntax : " << sol << std::endl;
          }
          else
          {
            Trace("cegqi-inv-debug")
                << "...was embedding into grammar." << std::endl;
          }
        }
        else
        {
          Trace("cegqi-inv-debug")
              << sf << " did not use template" << std::endl;
        }
      }
      else
      {
        Trace("cegqi-warn") << "WARNING : No recorded instantiations for "
                               "syntax-guided solution!"
                            << std::endl;
      }
    }
    sols.push_back(sol);
    statuses.push_back(status);
  }
  return true;
}

Node SynthConjecture::getSymmetryBreakingPredicate(
    Node x, Node e, TypeNode tn, unsigned tindex, unsigned depth)
{
  std::vector<Node> sb_lemmas;

  // based on simple preprocessing
  Node ppred =
      d_ceg_proc->getSymmetryBreakingPredicate(x, e, tn, tindex, depth);
  if (!ppred.isNull())
  {
    sb_lemmas.push_back(ppred);
  }

  // other static conjecture-dependent symmetry breaking goes here

  if (!sb_lemmas.empty())
  {
    return sb_lemmas.size() == 1
               ? sb_lemmas[0]
               : NodeManager::currentNM()->mkNode(kind::AND, sb_lemmas);
  }
  else
  {
    return Node::null();
  }
}

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */

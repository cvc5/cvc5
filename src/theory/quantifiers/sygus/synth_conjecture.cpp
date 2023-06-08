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
 * Implementation of class that encapsulates techniques for a single
 * (SyGuS) synthesis conjecture.
 */
#include "theory/quantifiers/sygus/synth_conjecture.h"

#include "base/configuration.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "smt/logic_exception.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/embedding_converter.h"
#include "theory/quantifiers/sygus/enum_value_manager.h"
#include "theory/quantifiers/sygus/print_sygus_to_builtin.h"
#include "theory/quantifiers/sygus/sygus_pbe.h"
#include "theory/quantifiers/sygus/synth_engine.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::internal::kind;
using namespace std;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SynthConjecture::SynthConjecture(Env& env,
                                 QuantifiersState& qs,
                                 QuantifiersInferenceManager& qim,
                                 QuantifiersRegistry& qr,
                                 TermRegistry& tr,
                                 SygusStatistics& s)
    : EnvObj(env),
      d_qstate(qs),
      d_qim(qim),
      d_qreg(qr),
      d_treg(tr),
      d_stats(s),
      d_tds(tr.getTermDatabaseSygus()),
      d_verify(env, d_tds),
      d_hasSolution(false),
      d_computedSolution(false),
      d_runExprMiner(options().quantifiers.sygusFilterSolMode
                     != options::SygusFilterSolMode::NONE),
      d_ceg_si(new CegSingleInv(env, tr, s)),
      d_templInfer(new SygusTemplateInfer(env)),
      d_ceg_proc(new SynthConjectureProcess(env)),
      d_embConv(new EmbeddingConverter(env, d_tds, this)),
      d_sygus_rconst(new SygusRepairConst(env, d_tds)),
      d_exampleInfer(new ExampleInfer(d_tds)),
      d_ceg_pbe(new SygusPbe(env, qs, qim, d_tds, this)),
      d_ceg_cegis(new Cegis(env, qs, qim, d_tds, this)),
      d_ceg_cegisUnif(new CegisUnif(env, qs, qim, d_tds, this)),
      d_sygus_ccore(new CegisCoreConnective(env, qs, qim, d_tds, this)),
      d_master(nullptr),
      d_repair_index(0)
{
  if (options().datatypes.sygusSymBreakPbe
      || options().quantifiers.sygusUnifPbe)
  {
    d_modules.push_back(d_ceg_pbe.get());
  }
  if (options().quantifiers.sygusUnifPi != options::SygusUnifPiMode::NONE)
  {
    d_modules.push_back(d_ceg_cegisUnif.get());
  }
  if (options().quantifiers.sygusCoreConnective)
  {
    d_modules.push_back(d_sygus_ccore.get());
  }
  d_modules.push_back(d_ceg_cegis.get());
}

SynthConjecture::~SynthConjecture() {}

void SynthConjecture::presolve()
{
  // If we previously had a solution, block it. Notice that
  // excludeCurrentSolution in the block below ensures we implement a
  // policy where a *new* solution is generated for check-synth if the set of
  // SyGuS constraints has not changed. This call will block solutions for
  // *smart* enumerators only. This behavior makes smart enumeration have
  // a consistent policy with *fast* enumerators, which will generate
  // a new, next solution in their enumeration.
  if (d_hasSolution)
  {
    excludeCurrentSolution(d_solutionValues.back(),
                           InferenceId::QUANTIFIERS_SYGUS_INC_EXCLUDE_CURRENT);
    // we don't have a solution yet
    d_hasSolution = false;
    d_computedSolution = false;
    d_sol.clear();
    d_solStatus.clear();
  }
}

void SynthConjecture::assign(Node q)
{
  Assert(d_embed_quant.isNull());
  Assert(q.getKind() == FORALL);
  Trace("cegqi") << "SynthConjecture : assign : " << q << std::endl;
  d_quant = q;
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();

  // pre-simplify the quantified formula based on the process utility
  d_simp_quant = d_ceg_proc->preSimplify(d_quant);

  // compute its attributes
  QAttributes qa;
  QuantAttributes::computeQuantAttributes(q, qa);

  Node sc = qa.d_sygusSideCondition;
  // we check whether the conjecture is single invocation if we are marked
  // with the sygus attribute and don't have a side condition
  bool checkSingleInvocation = qa.d_sygus && sc.isNull();

  std::map<Node, Node> templates;
  std::map<Node, Node> templates_arg;
  // register with single invocation if applicable
  if (checkSingleInvocation)
  {
    d_ceg_si->initialize(d_simp_quant);
    d_simp_quant = d_ceg_si->getSimplifiedConjecture();
    if (!d_ceg_si->isSingleInvocation())
    {
      d_templInfer->initialize(d_simp_quant);
    }
    // carry the templates
    for (const Node& v : q[0])
    {
      Node templ = d_templInfer->getTemplate(v);
      if (!templ.isNull())
      {
        templates[v] = templ;
        templates_arg[v] = d_templInfer->getTemplateArg(v);
      }
    }
  }

  // post-simplify the quantified formula based on the process utility
  d_simp_quant = d_ceg_proc->postSimplify(d_simp_quant);

  // finished simplifying the quantified formula at this point

  // convert to deep embedding and finalize single invocation here
  d_embed_quant = d_embConv->process(d_simp_quant, templates, templates_arg);
  Trace("cegqi") << "SynthConjecture : converted to embedding : "
                 << d_embed_quant << std::endl;

  if (!sc.isNull())
  {
    Trace("cegqi-debug") << "Side condition is: " << sc << std::endl;
    // Immediately check if unsat, use lambda returning true for functions
    // to synthesize.
    std::vector<Node> vars;
    std::vector<Node> subs;
    for (const Node& v : q[0])
    {
      vars.push_back(v);
      TypeNode vtype = v.getType();
      Assert(vtype.isBoolean()
             || (vtype.isFunction() && vtype.getRangeType().isBoolean()));
      Node s = nm->mkConst(true);
      if (vtype.isFunction())
      {
        std::vector<TypeNode> atypes = vtype.getArgTypes();
        std::vector<Node> lvars;
        for (const TypeNode& tn : atypes)
        {
          lvars.push_back(nm->mkBoundVar(tn));
        }
        s = nm->mkNode(LAMBDA, nm->mkNode(BOUND_VAR_LIST, lvars), s);
      }
      subs.push_back(s);
    }
    Node ksc =
        sc.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    Result r = d_verify.verify(ksc);
    // if infeasible, we are done
    if (r.getStatus() == Result::UNSAT)
    {
      d_qim.lemma(d_quant.negate(),
                  InferenceId::QUANTIFIERS_SYGUS_SC_INFEASIBLE);
      return;
    }
    // convert to deep embedding
    d_embedSideCondition = d_embConv->convertToEmbedding(sc);
    Trace("cegqi") << "SynthConjecture : side condition : "
                   << d_embedSideCondition << std::endl;
  }

  // we now finalize the single invocation module, based on the syntax
  // restrictions
  if (checkSingleInvocation)
  {
    d_ceg_si->finishInit(d_embConv->isSyntaxRestricted());
  }

  Assert(d_candidates.empty());
  std::vector<Node> vars;
  for (size_t i = 0, nvars = d_embed_quant[0].getNumChildren(); i < nvars; i++)
  {
    Node v = d_embed_quant[0][i];
    vars.push_back(v);
    Node e = sm->mkSkolemFunction(SkolemFunId::QUANTIFIERS_SYNTH_FUN_EMBED,
                                  v.getType(),
                                  d_simp_quant[0][i]);
    d_candidates.push_back(e);
  }
  Trace("cegqi") << "Base quantified formula is : " << d_embed_quant
                 << std::endl;
  // construct base instantiation
  Subs bsubs;
  bsubs.add(vars, d_candidates);
  d_base_inst = d_tds->rewriteNode(bsubs.apply(d_embed_quant[1]));
  d_checkBody = d_embed_quant[1];
  if (d_checkBody.getKind() == NOT && d_checkBody[0].getKind() == FORALL)
  {
    for (const Node& v : d_checkBody[0][0])
    {
      Node sk = sm->mkDummySkolem("rsk", v.getType());
      bsubs.add(v, sk);
      d_innerVars.push_back(v);
      d_innerSks.push_back(sk);
    }
    d_checkBody = d_checkBody[0][1].negate();
  }
  d_checkBody = bsubs.apply(d_checkBody);
  d_checkBody = d_tds->rewriteNode(d_checkBody);
  if (!d_embedSideCondition.isNull() && !vars.empty())
  {
    d_embedSideCondition = d_embedSideCondition.substitute(
        vars.begin(), vars.end(), d_candidates.begin(), d_candidates.end());
  }
  Trace("cegqi") << "Base instantiation is :      " << d_base_inst << std::endl;

  // initialize the sygus constant repair utility
  if (options().quantifiers.sygusRepairConst)
  {
    d_sygus_rconst->initialize(d_base_inst.negate(), d_candidates);
    if (options().quantifiers.sygusConstRepairAbort)
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
  // initialize the example inference utility
  // Notice that we must also consider the side condition when inferring
  // whether the conjecture is PBE. This ensures we do not prune solutions
  // that may satisfy the side condition based on equivalence-up-to-examples
  // with solutions that do not.
  Node conjForExamples = d_base_inst;
  if (!d_embedSideCondition.isNull())
  {
    conjForExamples = nm->mkNode(AND, d_embedSideCondition, d_base_inst);
  }
  if (d_exampleInfer!=nullptr && !d_exampleInfer->initialize(conjForExamples, d_candidates))
  {
    // there is a contradictory example pair, the conjecture is infeasible.
    Node infLem = d_quant.negate();
    d_qim.lemma(infLem, InferenceId::QUANTIFIERS_SYGUS_EXAMPLE_INFER_CONTRA);
    // we don't need to continue initialization in this case
    return;
  }

  // register this term with sygus database and other utilities that impact
  // the enumerative sygus search
  if (!isSingleInvocation())
  {
    d_ceg_proc->initialize(d_base_inst, d_candidates);
    for (unsigned i = 0, size = d_modules.size(); i < size; i++)
    {
      if (d_modules[i]->initialize(d_simp_quant, d_base_inst, d_candidates))
      {
        d_master = d_modules[i];
        break;
      }
    }
    Assert(d_master != nullptr);
  }

  Assert(d_qreg.getQuantAttributes().isSygus(q));

  Trace("cegqi") << "...finished, single invocation = " << isSingleInvocation()
                 << std::endl;
}


bool SynthConjecture::isSingleInvocation() const
{
  return d_ceg_si->isSingleInvocation();
}

bool SynthConjecture::needsCheck()
{
  return true;
}

bool SynthConjecture::doCheck()
{
  if (d_hasSolution)
  {
    return true;
  }
  if (isSingleInvocation())
  {
    // We now try to solve with the single invocation solver, which may or may
    // not succeed in solving the conjecture. In either case,  we are done and
    // return true.
    Result res = d_ceg_si->solve();
    if (res.getStatus() == Result::UNSAT)
    {
      d_hasSolution = true;
      // the conjecture has a solution, we set incomplete
      d_qim.setModelUnsound(IncompleteId::QUANTIFIERS_SYGUS_SOLVED);
    }
    else if (res.getStatus() == Result::SAT)
    {
      // the conjecture is definitely infeasible
      d_qim.lemma(d_quant.negate(),
                  InferenceId::QUANTIFIERS_SYGUS_SI_INFEASIBLE);
    }
    return true;
  }
  Assert(d_master != nullptr);

  // get the list of terms that the master strategy is interested in
  std::vector<Node> terms;
  d_master->getTermList(d_candidates, terms);

  Assert(!d_candidates.empty());

  Trace("sygus-engine-debug")
      << "CegConjuncture : check, build candidates..." << std::endl;
  std::vector<Node> candidate_values;
  bool constructed_cand = false;

  // If a module is not trying to repair constants in solutions and the option
  // sygusRepairConst  is true, we use a default scheme for trying to repair
  // constants here.
  bool doRepairConst =
      options().quantifiers.sygusRepairConst && !d_master->usingRepairConst();
  if (doRepairConst)
  {
    // have we tried to repair the previous solution?
    // if not, call the repair constant utility
    size_t ninst = d_solutionValues.size();
    if (d_repair_index < ninst)
    {
      std::vector<Node> fail_cvs = d_solutionValues[d_repair_index];
      if (TraceIsOn("sygus-engine"))
      {
        Trace("sygus-engine") << "CegConjuncture : repair previous solution ";
        for (const Node& fc : fail_cvs)
        {
          std::stringstream ss;
          TermDbSygus::toStreamSygus(ss, fc);
          Trace("sygus-engine") << ss.str() << " ";
        }
        Trace("sygus-engine") << std::endl;
      }
      d_repair_index++;
      if (d_sygus_rconst->repairSolution(
              d_candidates, fail_cvs, candidate_values, true))
      {
        constructed_cand = true;
      }
    }
  }

  bool printDebug = isOutputOn(OutputTag::SYGUS);
  if (!constructed_cand)
  {
    // get the model value of the relevant terms from the master module
    std::vector<Node> enum_values;
    bool activeIncomplete = false;
    bool fullModel = getEnumeratedValues(terms, enum_values, activeIncomplete);

    // if the master requires a full model and the model is partial, we fail
    if (!d_master->allowPartialModel() && !fullModel)
    {
      // we retain the values in d_ev_active_gen_waiting
      Trace("sygus-engine-debug") << "...partial model, fail." << std::endl;
      // if we are partial due to an active enumerator, we may still succeed
      // on the next call
      return !activeIncomplete;
    }
    // determine if we had at least one value for an enumerator
    Assert(terms.size() == enum_values.size());
    bool modelSuccess = false;
    for (unsigned i = 0, size = terms.size(); i < size; i++)
    {
      if (!enum_values[i].isNull())
      {
        modelSuccess = true;
      }
    }
    if (modelSuccess)
    {
      // Must separately compute whether trace is on due to compilation of
      // TraceIsOn.
      bool traceIsOn = TraceIsOn("sygus-engine");
      if (printDebug || traceIsOn)
      {
        Trace("sygus-engine") << "  * Value is : ";
        std::stringstream sygusEnumOut;
        FirstOrderModel* m = d_treg.getModel();
        for (unsigned i = 0, size = terms.size(); i < size; i++)
        {
          Node nv = enum_values[i];
          Node onv = nv.isNull() ? m->getValue(terms[i]) : nv;
          TypeNode tn = onv.getType();
          std::stringstream ss;
          TermDbSygus::toStreamSygus(ss, onv);
          if (printDebug)
          {
            sygusEnumOut << " " << ss.str();
          }
          Trace("sygus-engine") << terms[i] << " -> ";
          if (nv.isNull())
          {
            Trace("sygus-engine") << "[EXC: " << ss.str() << "] ";
          }
          else
          {
            Trace("sygus-engine") << ss.str() << " ";
            if (TraceIsOn("sygus-engine-rr"))
            {
              Node bv = d_tds->sygusToBuiltin(nv, tn);
              bv = d_tds->rewriteNode(bv);
              Trace("sygus-engine-rr") << " -> " << bv << std::endl;
            }
          }
        }
        Trace("sygus-engine") << std::endl;
        if (d_env.isOutputOn(OutputTag::SYGUS))
        {
          d_env.output(OutputTag::SYGUS)
              << "(sygus-enum" << sygusEnumOut.str() << ")" << std::endl;
        }
      }
      Assert(candidate_values.empty());
      constructed_cand = d_master->constructCandidates(
          terms, enum_values, d_candidates, candidate_values);
    }
    // notify the enumerator managers of the status of the candidate
    for (std::pair<const Node, std::unique_ptr<EnumValueManager>>& ecp :
         d_enumManager)
    {
      ecp.second->notifyCandidate(modelSuccess);
    }
    // if we did not generate a candidate, return now
    if (!modelSuccess)
    {
      Trace("sygus-engine-debug") << "...empty model, fail." << std::endl;
      return !activeIncomplete;
    }
  }

  if (constructed_cand)
  {
    // check the side condition if we constructed a candidate
    if (!checkSideCondition(candidate_values))
    {
      excludeCurrentSolution(candidate_values,
                             InferenceId::QUANTIFIERS_SYGUS_SC_EXCLUDE_CURRENT);
      Trace("sygus-engine") << "...failed side condition" << std::endl;
      return false;
    }
  }

  // must get a counterexample to the value of the current candidate
  Node query;
  if (constructed_cand)
  {
    if (TraceIsOn("sygus-engine-debug"))
    {
      Trace("sygus-engine-debug")
          << "CegConjuncture : check candidate : " << std::endl;
      for (unsigned i = 0, size = candidate_values.size(); i < size; i++)
      {
        Trace("sygus-engine-debug")
            << "  " << i << " : " << d_candidates[i] << " -> "
            << candidate_values[i] << std::endl;
      }
    }
    Assert(candidate_values.size() == d_candidates.size());
    query = d_checkBody.substitute(d_candidates.begin(),
                                   d_candidates.end(),
                                   candidate_values.begin(),
                                   candidate_values.end());
  }
  else
  {
    query = d_checkBody;
  }

  if (!constructed_cand)
  {
    return false;
  }

  // if we trust the sampling we ran, we terminate now
  if (options().quantifiers.cegisSample == options::CegisSampleMode::TRUST)
  {
    // we have that the current candidate passed a sample test
    // since we trust sampling in this mode, we assume there is a solution here
    // and set incomplete.
    d_hasSolution = true;
    d_qim.setModelUnsound(IncompleteId::QUANTIFIERS_SYGUS_SOLVED);
    recordSolution(candidate_values);
    return true;
  }

  // print the candidate solution for debugging
  if (constructed_cand && printDebug)
  {
    std::ostream& out = output(OutputTag::SYGUS);
    out << "(sygus-candidate ";
    Assert(d_quant[0].getNumChildren() == candidate_values.size());
    for (size_t i = 0, ncands = candidate_values.size(); i < ncands; i++)
    {
      Node v = candidate_values[i];
      out << "(" << d_quant[0][i] << " ";
      TermDbSygus::toStreamSygus(out, v);
      out << ")";
    }
    out << ")" << std::endl;
  }

  if (query.isNull())
  {
    // no lemma to check
    return false;
  }

  // Record the solution, which may be falsified below. We require recording
  // here since the result of the satisfiability test may be unknown.
  recordSolution(candidate_values);

  std::vector<Node> skModel;
  Result r = d_verify.verify(query, d_innerSks, skModel);

  if (r.getStatus() == Result::SAT)
  {
    // we have a counterexample
    return processCounterexample(skModel);
  }
  else if (r.getStatus() != Result::UNSAT)
  {
    // In the rare case that the subcall is unknown, we simply exclude the
    // solution, without adding a counterexample point. This should only
    // happen if the quantifier free logic is undecidable.
    excludeCurrentSolution(
        candidate_values,
        InferenceId::QUANTIFIERS_SYGUS_NO_VERIFY_EXCLUDE_CURRENT);
    // We should set refutation unsound, since an "unsat" answer should not be
    // interpreted as "infeasible", which would make a difference in the rare
    // case where e.g. we had a finite grammar and exhausted the grammar.
    // In other words, we are unsound by excluding the current candidate
    // which we could not verify whether or not it was a solution.
    d_qim.setRefutationUnsound(IncompleteId::QUANTIFIERS_SYGUS_NO_VERIFY);
    return false;
  }
  // otherwise we are unsat, and we will process the solution below

  // now mark that we have a solution
  d_hasSolution = true;
  ++(d_stats.d_solutions);
  // determine if we should filter this solution, e.g. based on expression
  // mining or sygus stream
  if (runExprMiner())
  {
    // excluded due to expression mining
    excludeCurrentSolution(
        candidate_values,
        InferenceId::QUANTIFIERS_SYGUS_STREAM_EXCLUDE_CURRENT);
    // streaming means now we immediately are looking for a new solution
    d_hasSolution = false;
    d_computedSolution = false;
    d_sol.clear();
    d_solStatus.clear();
    return false;
  }
  // We set incomplete and terminate with unknown.
  d_qim.setModelUnsound(IncompleteId::QUANTIFIERS_SYGUS_SOLVED);
  return true;
}

bool SynthConjecture::checkSideCondition(const std::vector<Node>& cvals)
{
  if (d_embedSideCondition.isNull())
  {
    return true;
  }
  Node sc = d_embedSideCondition;
  if (!cvals.empty())
  {
    sc = sc.substitute(
        d_candidates.begin(), d_candidates.end(), cvals.begin(), cvals.end());
  }
  Trace("sygus-engine") << "Check side condition..." << std::endl;
  Result r = d_verify.verify(sc);
  Trace("sygus-engine") << "...result of check side condition : " << r
                        << std::endl;
  if (r == Result::UNSAT)
  {
    return false;
  }
  Trace("sygus-engine") << "...passed side condition" << std::endl;
  return true;
}

bool SynthConjecture::processCounterexample(const std::vector<Node>& skModel)
{
  Trace("cegqi-refine") << "doRefine : Construct refinement lemma..."
                        << std::endl;
  Trace("cegqi-refine-debug")
      << "  For counterexample skolems : " << d_innerSks << std::endl;
  Node base_lem = d_checkBody.negate();

  Assert(d_innerSks.size() == skModel.size());

  Trace("cegqi-refine") << "doRefine : substitute..." << std::endl;
  base_lem = base_lem.substitute(
      d_innerSks.begin(), d_innerSks.end(), skModel.begin(), skModel.end());
  Trace("cegqi-refine") << "doRefine : rewrite..." << std::endl;
  base_lem = d_tds->rewriteNode(base_lem);
  Trace("cegqi-refine") << "doRefine : register refinement lemma " << base_lem
                        << "..." << std::endl;
  size_t prevPending = d_qim.numPendingLemmas();
  d_master->registerRefinementLemma(d_innerSks, base_lem);
  Trace("cegqi-refine") << "doRefine : finished" << std::endl;

  // check if we added a lemma
  bool addedLemma = d_qim.numPendingLemmas() > prevPending;
  if (addedLemma)
  {
    Trace("sygus-engine-debug") << "  ...refine candidate." << std::endl;
  }
  else
  {
    Trace("sygus-engine-debug") << "  ...(warning) failed to refine candidate, "
                                   "manually exclude candidate."
                                << std::endl;
    std::vector<Node> cvals = d_solutionValues.back();
    // something went wrong, exclude the current candidate
    excludeCurrentSolution(
        cvals, InferenceId::QUANTIFIERS_SYGUS_REPEAT_CEX_EXCLUDE_CURRENT);
    // Note this happens when evaluation is incapable of disproving a candidate
    // for counterexample point c, but satisfiability checking happened to find
    // the the same point c is indeed a true counterexample. It is sound
    // to exclude the candidate in this case.
  }
  return addedLemma;
}

void SynthConjecture::ppNotifyConjecture(Node q)
{
  d_ceg_si->ppNotifyConjecture(q);
}

bool SynthConjecture::getEnumeratedValues(std::vector<Node>& n,
                                          std::vector<Node>& v,
                                          bool& activeIncomplete)
{
  Trace("sygus-engine-debug") << "getEnumeratedValues" << std::endl;
  std::vector<Node> ncheck = n;
  n.clear();
  bool ret = true;
  for (unsigned i = 0, size = ncheck.size(); i < size; i++)
  {
    Node e = ncheck[i];
    // if it is not active, we return null
    Node g = d_tds->getActiveGuardForEnumerator(e);
    if (!g.isNull())
    {
      Node gstatus = d_qstate.getValuation().getSatValue(g);
      if (gstatus.isNull() || !gstatus.getConst<bool>())
      {
        Trace("sygus-engine-debug")
            << "Enumerator " << e << " is inactive." << std::endl;
        continue;
      }
    }
    EnumValueManager* eman = getEnumValueManagerFor(e);
    Trace("sygus-engine-debug2") << "- get value for " << e << std::endl;
    Node nv = eman->getEnumeratedValue(activeIncomplete);
    Trace("sygus-engine-debug2") << "  ...return " << nv << std::endl;
    n.push_back(e);
    v.push_back(nv);
    ret = ret && !nv.isNull();
  }
  return ret;
}

EnumValueManager* SynthConjecture::getEnumValueManagerFor(Node e)
{
  std::map<Node, std::unique_ptr<EnumValueManager>>::iterator it =
      d_enumManager.find(e);
  if (it != d_enumManager.end())
  {
    return it->second.get();
  }
  // otherwise, allocate it
  Node f = d_tds->getSynthFunForEnumerator(e);
  bool hasExamples = (d_exampleInfer != nullptr && d_exampleInfer->hasExamples(f)
                      && d_exampleInfer->getNumExamples(f) != 0);
  d_enumManager[e].reset(new EnumValueManager(
      d_env, d_qstate, d_qim, d_treg, d_stats, e, hasExamples));
  EnumValueManager* eman = d_enumManager[e].get();
  // set up the examples
  if (hasExamples)
  {
    ExampleEvalCache* eec = eman->getExampleEvalCache();
    Assert(eec != nullptr);
    for (unsigned i = 0, nex = d_exampleInfer->getNumExamples(f); i < nex; i++)
    {
      std::vector<Node> input;
      d_exampleInfer->getExample(f, i, input);
      eec->addExample(input);
    }
  }
  return eman;
}

ExpressionMinerManager* SynthConjecture::getExprMinerManagerFor(Node e)
{
  if (!d_runExprMiner)
  {
    return nullptr;
  }
  std::map<Node, std::unique_ptr<ExpressionMinerManager>>::iterator its =
      d_exprm.find(e);
  if (its != d_exprm.end())
  {
    return its->second.get();
  }
  d_exprm[e].reset(new ExpressionMinerManager(d_env));
  ExpressionMinerManager* emm = d_exprm[e].get();
  emm->initializeSygus(e.getType());
  return emm;
}

Node SynthConjecture::getModelValue(Node n)
{
  Trace("cegqi-mv") << "getModelValue for : " << n << std::endl;
  return d_treg.getModel()->getValue(n);
}

void SynthConjecture::debugPrint(const char* c)
{
  Trace(c) << "Synthesis conjecture : " << d_embed_quant << std::endl;
  Trace(c) << "  * Candidate programs : " << d_candidates << std::endl;
  Trace(c) << "  * Counterexample skolems : " << d_innerSks << std::endl;
}

void SynthConjecture::excludeCurrentSolution(const std::vector<Node>& values,
                                             InferenceId id)
{
  Assert(values.size() == d_candidates.size());
  Trace("cegqi-debug") << "Exclude current solution: " << values << std::endl;
  // However, we need to exclude the current solution using an explicit
  // blocking clause, so that we proceed to the next solution. We do this only
  // for passively-generated enumerators (TermDbSygus::isPassiveEnumerator).
  std::vector<Node> exp;
  for (size_t i = 0, tsize = d_candidates.size(); i < tsize; i++)
  {
    Node cprog = d_candidates[i];
    Assert(d_tds->isEnumerator(cprog));
    if (d_tds->isPassiveEnumerator(cprog))
    {
      Node cval = values[i];
      // add to explanation of exclusion
      d_tds->getExplain()->getExplanationForEquality(cprog, cval, exp);
    }
  }
  if (!exp.empty())
  {
    Node exc_lem = exp.size() == 1
                       ? exp[0]
                       : NodeManager::currentNM()->mkNode(kind::AND, exp);
    exc_lem = exc_lem.negate();
    Trace("cegqi-lemma") << "Cegqi::Lemma : exclude current solution : "
                         << exc_lem << " by " << id << std::endl;
    d_qim.lemma(exc_lem, id);
  }
}

bool SynthConjecture::runExprMiner()
{
  // if not using expression mining and sygus stream
  if (!d_runExprMiner && !options().quantifiers.sygusStream)
  {
    return false;
  }
  Trace("cegqi-sol-debug") << "Run expression mining..." << std::endl;
  Assert(d_quant[0].getNumChildren() == d_embed_quant[0].getNumChildren());
  std::vector<Node> sols;
  std::vector<int8_t> statuses;
  if (!getSynthSolutionsInternal(sols, statuses))
  {
    return false;
  }
  // always exclude if sygus stream is enabled
  bool doExclude = options().quantifiers.sygusStream;
  NodeManager* nm = NodeManager::currentNM();
  std::ostream& out = options().base.out;
  for (size_t i = 0, size = d_embed_quant[0].getNumChildren(); i < size; i++)
  {
    Node sol = sols[i];
    if (sol.isNull())
    {
      // failed to reconstruct to syntax, skip
      continue;
    }
    Node e = d_embed_quant[0][i];
    int8_t status = statuses[i];
    // run expression mining
    if (status != 0)
    {
      ExpressionMinerManager* emm = getExprMinerManagerFor(e);
      if (emm != nullptr)
      {
        bool ret = emm->addTerm(sol);
        if (!ret)
        {
          // count the number of filtered solutions
          ++(d_stats.d_filtered_solutions);
          // if any term is excluded due to mining, its output is excluded
          // from sygus stream, and the entire solution is excluded.
          doExclude = true;
          continue;
        }
      }
    }
    // print to stream
    if (options().quantifiers.sygusStream)
    {
      TypeNode tn = e.getType();
      const DType& dt = tn.getDType();
      std::stringstream ss;
      ss << e;
      std::string f(ss.str());
      f.erase(f.begin());
      out << "(define-fun " << f << " ";
      // Only include variables that are truly bound variables of the
      // function-to-synthesize. This means we exclude variables that encode
      // external terms. This ensures that --sygus-stream prints
      // solutions with no arguments on the predicate for responses to
      // the get-abduct command.
      // pvs stores the variables that will be printed in the argument list
      // below.
      std::vector<Node> pvs;
      Node vl = dt.getSygusVarList();
      if (!vl.isNull())
      {
        Assert(vl.getKind() == BOUND_VAR_LIST);
        SygusVarToTermAttribute sta;
        for (const Node& v : vl)
        {
          if (!v.hasAttribute(sta))
          {
            pvs.push_back(v);
          }
        }
      }
      if (pvs.empty())
      {
        out << "() ";
      }
      else
      {
        vl = nm->mkNode(BOUND_VAR_LIST, pvs);
        out << vl << " ";
      }
      out << dt.getSygusType() << " ";
      if (status == 0)
      {
        out << sol;
      }
      else
      {
        Node bsol = datatypes::utils::sygusToBuiltin(sol, true);
        out << bsol;
      }
      out << ")" << std::endl;
    }
  }
  return doExclude;
}

bool SynthConjecture::getSynthSolutions(
    std::map<Node, std::map<Node, Node> >& sol_map)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> sols;
  std::vector<int8_t> statuses;
  Trace("cegqi-debug") << "getSynthSolutions..." << std::endl;
  if (!getSynthSolutionsInternal(sols, statuses))
  {
    Trace("cegqi-debug") << "...failed internal" << std::endl;
    return false;
  }
  // we add it to the solution map, indexed by this conjecture
  std::map<Node, Node>& smc = sol_map[d_quant];
  for (unsigned i = 0, size = d_embed_quant[0].getNumChildren(); i < size; i++)
  {
    Node sol = sols[i];
    int8_t status = statuses[i];
    Trace("cegqi-debug") << "...got " << i << ": " << sol
                         << ", status=" << status << std::endl;
    // get the builtin solution
    Node bsol = sol;
    if (status != 0)
    {
      // Convert sygus to builtin here.
      // We must use the external representation to ensure bsol matches the
      // grammar.
      bsol = datatypes::utils::sygusToBuiltin(sol, true);
    }
    // convert to lambda
    TypeNode tn = d_embed_quant[0][i].getType();
    const DType& dt = tn.getDType();
    Node fvar = d_quant[0][i];
    Node bvl = dt.getSygusVarList();
    if (!bvl.isNull())
    {
      // since we don't have function subtyping, this assertion should only
      // check the return type
      Assert(fvar.getType().isFunction());
      Assert(fvar.getType().getRangeType() == bsol.getType());
      bsol = nm->mkNode(LAMBDA, bvl, bsol);
    }
    else
    {
      Assert(fvar.getType() == bsol.getType());
    }
    // store in map
    smc[fvar] = bsol;
    Trace("cegqi-debug") << "...return " << bsol << std::endl;
  }
  return true;
}

void SynthConjecture::recordSolution(const std::vector<Node>& vs)
{
  Assert(vs.size() == d_candidates.size());
  d_solutionValues.clear();
  d_solutionValues.push_back(vs);
}

bool SynthConjecture::getSynthSolutionsInternal(std::vector<Node>& sols,
                                                std::vector<int8_t>& statuses)
{
  if (!d_hasSolution)
  {
    return false;
  }
  if (d_computedSolution)
  {
    sols.insert(sols.end(), d_sol.begin(), d_sol.end());
    statuses.insert(statuses.end(), d_solStatus.begin(), d_solStatus.end());
    return true;
  }
  d_computedSolution = true;
  // get the (SyGuS datatype) values of the solutions, if they exist
  std::vector<Node> svals;
  if (!d_solutionValues.empty())
  {
    svals = d_solutionValues.back();
  }
  for (size_t i = 0, size = d_embed_quant[0].getNumChildren(); i < size; i++)
  {
    Node prog = d_embed_quant[0][i];
    Trace("cegqi-debug") << "  get solution for " << prog << std::endl;
    TypeNode tn = prog.getType();
    Assert(tn.isDatatype());
    // get the solution
    Node sol;
    int8_t status = -1;
    if (isSingleInvocation())
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
      Node cprog = d_candidates[i];
      if (!svals.empty())
      {
        // the solution is the value of the last term
        sol = svals[i];
        status = 1;

        // check if there was a template
        Node sf = d_quant[0][i];
        Node templ = d_templInfer->getTemplate(sf);
        if (!templ.isNull())
        {
          Trace("cegqi-inv-debug")
              << sf << " used template : " << templ << std::endl;
          TNode templa = d_templInfer->getTemplateArg(sf);
          // make the builtin version of the full solution
          sol = d_tds->sygusToBuiltin(sol, sol.getType());
          Trace("cegqi-inv") << "Builtin version of solution is : " << sol
                             << ", type : " << sol.getType() << std::endl;
          TNode tsol = sol;
          sol = templ.substitute(templa, tsol);
          Trace("cegqi-inv-debug") << "With template : " << sol << std::endl;
          sol = rewrite(sol);
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
    d_sol.push_back(sol);
    d_solStatus.push_back(status);
    // Note that this assumes that the name of the resulting datatype matches
    // the original name from the user. This is usually the case, although
    // if grammar normalization is used, it is not. If it is not, the names
    // in the annotation will not match, but no failures will occur.
    // Also note that we do not print annotations if the solution was not
    // reconstructed to the grammar (status != 1), which is the case if the
    // grammar is ignored by single invocation above. On the other hand,
    // annotations will be printed correctly if the solution was successfully
    // reconstructed by single invocation (status == 1).
    if (isOutputOn(OutputTag::SYGUS_SOL_GTERM) && status == 1)
    {
      Node psol = getPrintableSygusToBuiltin(sol);
      d_env.output(OutputTag::SYGUS_SOL_GTERM)
          << "(sygus-sol-gterm (" << d_quant[0][i] << " " << psol << "))"
          << std::endl;
    }
  }
  sols.insert(sols.end(), d_sol.begin(), d_sol.end());
  statuses.insert(statuses.end(), d_solStatus.begin(), d_solStatus.end());
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

ExampleEvalCache* SynthConjecture::getExampleEvalCache(Node e)
{
  EnumValueManager* eman = getEnumValueManagerFor(e);
  return eman->getExampleEvalCache();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

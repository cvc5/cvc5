/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of cegis.
 */

#include "theory/quantifiers/sygus/cegis.h"

#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/quantifiers/sygus/example_min_eval.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/rewriter.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

Cegis::Cegis(Env& env,
             QuantifiersState& qs,
             QuantifiersInferenceManager& qim,
             TermDbSygus* tds,
             SynthConjecture* p)
    : SygusModule(env, qs, qim, tds, p),
      d_eval_unfold(tds->getEvalUnfold()),
      d_cexClosedEnum(false),
      d_cegis_sampler(env),
      d_usingSymCons(false)
{
}

bool Cegis::initialize(Node conj, Node n, const std::vector<Node>& candidates)
{
  d_base_body = n;
  d_cexClosedEnum = true;
  if (d_base_body.getKind() == NOT && d_base_body[0].getKind() == FORALL)
  {
    for (const Node& v : d_base_body[0][0])
    {
      d_base_vars.push_back(v);
      if (!v.getType().isClosedEnumerable())
      {
        // not closed enumerable, refinement lemmas cannot be sent to the
        // quantifier-free datatype solver
        d_cexClosedEnum = false;
      }
    }
    d_base_body = d_base_body[0][1];
  }

  // assign the cegis sampler if applicable
  if (options().quantifiers.cegisSample != options::CegisSampleMode::NONE)
  {
    Trace("cegis-sample") << "Initialize sampler for " << d_base_body << "..."
                          << std::endl;
    TypeNode bt = d_base_body.getType();
    d_cegis_sampler.initialize(
        bt, d_base_vars, options().quantifiers.sygusSamples);
  }
  return processInitialize(conj, n, candidates);
}

bool Cegis::processInitialize(Node conj,
                              Node n,
                              const std::vector<Node>& candidates)
{
  Trace("cegis") << "Initialize cegis..." << std::endl;
  size_t csize = candidates.size();
  // The role of enumerators is to be either the single solution or part of
  // a solution involving multiple enumerators.
  EnumeratorRole erole =
      csize == 1 ? ROLE_ENUM_SINGLE_SOLUTION : ROLE_ENUM_MULTI_SOLUTION;
  // initialize an enumerator for each candidate
  std::vector<Node> activeGuards;
  for (size_t i = 0; i < csize; i++)
  {
    Trace("cegis") << "...register enumerator " << candidates[i];
    // We use symbolic constants if we are doing repair constants or if the
    // grammar construction was not simple.
    if (options().quantifiers.sygusRepairConst
        || options().quantifiers.sygusGrammarConsMode
               != options::SygusGrammarConsMode::SIMPLE)
    {
      TypeNode ctn = candidates[i].getType();
      d_tds->registerSygusType(ctn);
      SygusTypeInfo& cti = d_tds->getTypeInfo(ctn);
      if (cti.hasSubtermSymbolicCons())
      {
        // remember that we are using symbolic constructors
        d_usingSymCons = true;
        Trace("cegis") << " (using symbolic constructors)";
      }
    }
    Trace("cegis") << std::endl;
    Node e = candidates[i];
    d_tds->registerEnumerator(e, e, d_parent, erole);
    Node g = d_tds->getActiveGuardForEnumerator(e);
    if (!g.isNull())
    {
      activeGuards.push_back(g);
    }
  }
  if (!activeGuards.empty())
  {
    // This lemma has the semantics "if the conjecture holds, then there must
    // be another value to enumerate for each function to synthesize". Note
    // that active guards are only assigned for "actively generated"
    // enumerators, e.g. when using sygus-enum=fast. Thus, this lemma is
    // typically only added for single function conjectures.
    // This lemma allows us to answer infeasible when we run out of values (for
    // finite grammars).
    NodeManager* nm = NodeManager::currentNM();
    Node enumLem = nm->mkNode(IMPLIES, conj, nm->mkAnd(activeGuards));
    d_qim.lemma(enumLem, InferenceId::QUANTIFIERS_SYGUS_COMPLETE_ENUM);
  }
  return true;
}

void Cegis::getTermList(const std::vector<Node>& candidates,
                        std::vector<Node>& enums)
{
  enums.insert(enums.end(), candidates.begin(), candidates.end());
}

bool Cegis::addEvalLemmas(const std::vector<Node>& candidates,
                          const std::vector<Node>& candidate_values)
{
  // First, decide if this call will apply "conjecture-specific refinement".
  // In other words, in some settings, the following method will identify and
  // block a class of solutions {candidates -> S} that generalizes the current
  // one (given by {candidates -> candidate_values}), such that for each
  // candidate_values' in S, we have that {candidates -> candidate_values'} is
  // also not a solution for the given conjecture. We may not
  // apply this form of refinement if any (relevant) enumerator in candidates is
  // "actively generated" (see TermDbSygs::isPassiveEnumerator), since its
  // model values are themselves interpreted as classes of solutions.
  bool doGen = true;
  for (const Node& v : candidates)
  {
    // if it is relevant to refinement
    if (d_refinement_lemma_vars.find(v) != d_refinement_lemma_vars.end())
    {
      if (!d_tds->isPassiveEnumerator(v))
      {
        doGen = false;
        break;
      }
    }
  }
  NodeManager* nm = NodeManager::currentNM();
  bool addedEvalLemmas = false;
  // Refinement evaluation should not be done for grammars with symbolic
  // constructors.
  if (!d_usingSymCons)
  {
    Trace("sygus-engine") << "  *** Do refinement lemma evaluation"
                          << (doGen ? " with conjecture-specific refinement"
                                    : "")
                          << "..." << std::endl;
    // see if any refinement lemma is refuted by evaluation
    if (doGen)
    {
      std::vector<Node> cre_lems;
      getRefinementEvalLemmas(candidates, candidate_values, cre_lems);
      if (!cre_lems.empty())
      {
        for (const Node& cl : cre_lems)
        {
          d_qim.addPendingLemma(cl, InferenceId::QUANTIFIERS_SYGUS_REFINE_EVAL);
        }
        addedEvalLemmas = true;
        /* we could, but do not return here. experimentally, it is better to
          add the lemmas below as well, in parallel. */
      }
    }
    else
    {
      // just check whether the refinement lemmas are satisfied, fail if not
      if (checkRefinementEvalLemmas(candidates, candidate_values))
      {
        Trace("sygus-engine") << "...(actively enumerated) candidate failed "
                                 "refinement lemma evaluation."
                              << std::endl;
        return true;
      }
    }
  }
  // we only do evaluation unfolding for passive enumerators
  bool doEvalUnfold = (doGen
                       && options().quantifiers.sygusEvalUnfoldMode
                              != options::SygusEvalUnfoldMode::NONE)
                      || d_usingSymCons;
  if (doEvalUnfold)
  {
    Trace("sygus-engine") << "  *** Do evaluation unfolding..." << std::endl;
    std::vector<Node> eager_terms, eager_vals, eager_exps;
    for (unsigned i = 0, size = candidates.size(); i < size; ++i)
    {
      Trace("cegqi-debug") << "  register " << candidates[i] << " -> "
                           << candidate_values[i] << std::endl;
      d_eval_unfold->registerModelValue(candidates[i],
                                        candidate_values[i],
                                        eager_terms,
                                        eager_vals,
                                        eager_exps);
    }
    Trace("cegqi-debug") << "...produced " << eager_terms.size()
                         << " evaluation unfold lemmas.\n";
    for (unsigned i = 0, size = eager_terms.size(); i < size; ++i)
    {
      Node lem = nm->mkNode(
          OR, eager_exps[i].negate(), eager_terms[i].eqNode(eager_vals[i]));
      d_qim.addPendingLemma(lem, InferenceId::QUANTIFIERS_SYGUS_EVAL_UNFOLD);
      addedEvalLemmas = true;
      Trace("cegqi-lemma") << "Cegqi::Lemma : evaluation unfold : " << lem
                           << std::endl;
    }
  }
  return addedEvalLemmas;
}

Node Cegis::getRefinementLemmaFormula()
{
  std::vector<Node> conj;
  conj.insert(
      conj.end(), d_refinement_lemmas.begin(), d_refinement_lemmas.end());
  // get the propagated values
  for (unsigned i = 0, nprops = d_rl_eval_hds.size(); i < nprops; i++)
  {
    conj.push_back(d_rl_eval_hds[i].eqNode(d_rl_vals[i]));
  }
  // make the formula
  NodeManager* nm = NodeManager::currentNM();
  Node ret;
  if (conj.empty())
  {
    ret = nm->mkConst(true);
  }
  else
  {
    ret = conj.size() == 1 ? conj[0] : nm->mkNode(AND, conj);
  }
  return ret;
}

bool Cegis::constructCandidates(const std::vector<Node>& enums,
                                const std::vector<Node>& enum_values,
                                const std::vector<Node>& candidates,
                                std::vector<Node>& candidate_values)
{
  if (TraceIsOn("cegis"))
  {
    Trace("cegis") << "  Enumerators :\n";
    for (unsigned i = 0, size = enums.size(); i < size; ++i)
    {
      Trace("cegis") << "    " << enums[i] << " -> ";
      TermDbSygus::toStreamSygus("cegis", enum_values[i]);
      Trace("cegis") << "\n";
    }
  }
  // if we are using grammar-based repair
  if (d_usingSymCons && options().quantifiers.sygusRepairConst)
  {
    SygusRepairConst* src = d_parent->getRepairConst();
    Assert(src != nullptr);
    // check if any enum_values have symbolic terms that must be repaired
    bool mustRepair = false;
    for (const Node& c : enum_values)
    {
      if (SygusRepairConst::mustRepair(c))
      {
        mustRepair = true;
        break;
      }
    }
    Trace("cegis") << "...must repair is: " << mustRepair << std::endl;
    // if the solution contains a subterm that must be repaired
    if (mustRepair)
    {
      std::vector<Node> fail_cvs = enum_values;
      Assert(candidates.size() == fail_cvs.size());
      // try to solve entire problem?
      if (src->repairSolution(candidates, fail_cvs, candidate_values))
      {
        return true;
      }
      Node rl = getRefinementLemmaFormula();
      // try to solve for the refinement lemmas only
      bool ret =
          src->repairSolution(rl, candidates, fail_cvs, candidate_values);
      // Even if ret is true, we will exclude the skeleton as well; this means
      // that we have one chance to repair each skeleton. It is possible however
      // that we might want to repair the same skeleton multiple times.
      std::vector<Node> exp;
      for (unsigned i = 0, size = enums.size(); i < size; i++)
      {
        d_tds->getExplain()->getExplanationForEquality(
            enums[i], enum_values[i], exp);
      }
      Assert(!exp.empty());
      NodeManager* nm = NodeManager::currentNM();
      Node expn = exp.size() == 1 ? exp[0] : nm->mkNode(AND, exp);
      // must guard it
      expn = nm->mkNode(OR, d_parent->getConjecture().negate(), expn.negate());
      d_qim.addPendingLemma(
          expn, InferenceId::QUANTIFIERS_SYGUS_REPAIR_CONST_EXCLUDE);
      return ret;
    }
  }

  // evaluate on refinement lemmas
  bool addedEvalLemmas = addEvalLemmas(enums, enum_values);

  // try to construct candidates
  if (!processConstructCandidates(
          enums, enum_values, candidates, candidate_values, !addedEvalLemmas))
  {
    return false;
  }

  if (options().quantifiers.cegisSample != options::CegisSampleMode::NONE
      && !addedEvalLemmas)
  {
    // if we didn't add a lemma, trying sampling to add a refinement lemma
    // that immediately refutes the candidate we just constructed
    if (sampleAddRefinementLemma(candidates, candidate_values))
    {
      candidate_values.clear();
      // restart (should be guaranteed to add evaluation lemmas on this call)
      return constructCandidates(
          enums, enum_values, candidates, candidate_values);
    }
  }
  return true;
}

bool Cegis::processConstructCandidates(const std::vector<Node>& enums,
                                       const std::vector<Node>& enum_values,
                                       const std::vector<Node>& candidates,
                                       std::vector<Node>& candidate_values,
                                       bool satisfiedRl)
{
  if (satisfiedRl)
  {
    candidate_values.insert(
        candidate_values.end(), enum_values.begin(), enum_values.end());
    return true;
  }
  return false;
}

void Cegis::addRefinementLemma(Node lem)
{
  Trace("cegis-rl") << "Cegis::addRefinementLemma: " << lem << std::endl;
  d_refinement_lemmas.push_back(lem);
  // apply existing substitution
  Node slem = lem;
  if (!d_rl_eval_hds.empty())
  {
    slem = lem.substitute(d_rl_eval_hds.begin(),
                          d_rl_eval_hds.end(),
                          d_rl_vals.begin(),
                          d_rl_vals.end());
  }
  // rewrite with extended rewriter
  slem = d_tds->rewriteNode(slem);
  // collect all variables in slem
  expr::getSymbols(slem, d_refinement_lemma_vars);
  std::vector<Node> waiting;
  waiting.push_back(lem);
  unsigned wcounter = 0;
  // while we are not done adding lemmas
  while (wcounter < waiting.size())
  {
    // add the conjunct, possibly propagating
    addRefinementLemmaConjunct(wcounter, waiting);
    wcounter++;
  }
}

void Cegis::addRefinementLemmaConjunct(unsigned wcounter,
                                       std::vector<Node>& waiting)
{
  Node lem = waiting[wcounter];
  lem = rewrite(lem);
  // apply substitution and rewrite if applicable
  if (lem.isConst())
  {
    if (!lem.getConst<bool>())
    {
      // conjecture is infeasible
    }
    else
    {
      return;
    }
  }
  // break into conjunctions
  if (lem.getKind() == AND)
  {
    for (const Node& lc : lem)
    {
      waiting.push_back(lc);
    }
    return;
  }
  // does this correspond to a substitution?
  NodeManager* nm = NodeManager::currentNM();
  TNode term;
  TNode val;
  if (lem.getKind() == EQUAL)
  {
    for (unsigned i = 0; i < 2; i++)
    {
      if (lem[i].isConst() && d_tds->isEvaluationPoint(lem[1 - i]))
      {
        term = lem[1 - i];
        val = lem[i];
        break;
      }
    }
  }
  else
  {
    term = lem.getKind() == NOT ? lem[0] : lem;
    // predicate case: the conjunct is a (negated) evaluation point
    if (d_tds->isEvaluationPoint(term))
    {
      val = nm->mkConst(lem.getKind() != NOT);
    }
  }
  if (!val.isNull())
  {
    if (d_refinement_lemma_unit.find(lem) != d_refinement_lemma_unit.end())
    {
      // already added
      return;
    }
    Trace("cegis-rl") << "* cegis-rl: propagate: " << term << " -> " << val
                      << std::endl;
    d_rl_eval_hds.push_back(term);
    d_rl_vals.push_back(val);
    d_refinement_lemma_unit.insert(lem);

    // apply to waiting lemmas beyond this one
    for (unsigned i = wcounter + 1, size = waiting.size(); i < size; i++)
    {
      waiting[i] = waiting[i].substitute(term, val);
    }
    // apply to all existing refinement lemmas
    std::vector<Node> to_rem;
    for (const Node& rl : d_refinement_lemma_conj)
    {
      Node srl = rl.substitute(term, val);
      if (srl != rl)
      {
        Trace("cegis-rl") << "* cegis-rl: replace: " << rl << " -> " << srl
                          << std::endl;
        waiting.push_back(srl);
        to_rem.push_back(rl);
      }
    }
    for (const Node& tr : to_rem)
    {
      d_refinement_lemma_conj.erase(tr);
    }
  }
  else
  {
    if (TraceIsOn("cegis-rl"))
    {
      if (d_refinement_lemma_conj.find(lem) == d_refinement_lemma_conj.end())
      {
        Trace("cegis-rl") << "cegis-rl: add: " << lem << std::endl;
      }
    }
    d_refinement_lemma_conj.insert(lem);
  }
}

void Cegis::registerRefinementLemma(const std::vector<Node>& vars, Node lem)
{
  addRefinementLemma(lem);
  // must be closed enumerable
  if (d_cexClosedEnum
      && options().quantifiers.sygusEvalUnfoldMode
             != options::SygusEvalUnfoldMode::NONE)
  {
    // Make the refinement lemma and add it to lems.
    // This lemma is guarded by the parent's conjecture, which has the semantics
    // "this conjecture has a solution", hence this lemma states:
    // if the parent conjecture has a solution, it satisfies the specification
    // for the given concrete point.
    Node rlem = NodeManager::currentNM()->mkNode(
        OR, d_parent->getConjecture().negate(), lem);
    d_qim.addPendingLemma(rlem, InferenceId::QUANTIFIERS_SYGUS_CEGIS_REFINE);
  }
}

bool Cegis::usingRepairConst() { return true; }
bool Cegis::getRefinementEvalLemmas(const std::vector<Node>& vs,
                                    const std::vector<Node>& ms,
                                    std::vector<Node>& lems)
{
  Trace("sygus-cref-eval") << "Cref eval : conjecture has "
                           << d_refinement_lemma_unit.size() << " unit and "
                           << d_refinement_lemma_conj.size()
                           << " non-unit refinement lemma conjunctions."
                           << std::endl;
  Assert(vs.size() == ms.size());

  NodeManager* nm = NodeManager::currentNM();

  Node nfalse = nm->mkConst(false);
  Node neg_guard = d_parent->getConjecture().negate();
  bool ret = false;

  for (unsigned r = 0; r < 2; r++)
  {
    std::unordered_set<Node>& rlemmas =
        r == 0 ? d_refinement_lemma_unit : d_refinement_lemma_conj;
    for (const Node& lem : rlemmas)
    {
      Assert(!lem.isNull());
      std::map<Node, Node> visited;
      std::map<Node, std::vector<Node> > exp;
      EvalSygusInvarianceTest vsit(d_env.getRewriter());
      Trace("sygus-cref-eval") << "Check refinement lemma conjunct " << lem
                               << " against current model." << std::endl;
      Trace("sygus-cref-eval2") << "Check refinement lemma conjunct " << lem
                                << " against current model." << std::endl;
      Node cre_lem;
      Node lemcs = lem.substitute(vs.begin(), vs.end(), ms.begin(), ms.end());
      Trace("sygus-cref-eval2")
          << "...under substitution it is : " << lemcs << std::endl;
      Node lemcsu = d_tds->rewriteNode(lemcs);
      Trace("sygus-cref-eval2")
          << "...after unfolding is : " << lemcsu << std::endl;
      if (lemcsu.isConst() && !lemcsu.getConst<bool>())
      {
        ret = true;
        std::vector<Node> msu;
        std::vector<Node> mexp;
        msu.insert(msu.end(), ms.begin(), ms.end());
        std::map<TypeNode, int> var_count;
        for (unsigned k = 0; k < vs.size(); k++)
        {
          vsit.setUpdatedTerm(msu[k]);
          msu[k] = vs[k];
          // substitute for everything except this
          Node sconj =
              lem.substitute(vs.begin(), vs.end(), msu.begin(), msu.end());
          vsit.init(sconj, vs[k], nfalse);
          // get minimal explanation for this
          Node ut = vsit.getUpdatedTerm();
          Trace("sygus-cref-eval2-debug")
              << "  compute min explain of : " << vs[k] << " = " << ut
              << std::endl;
          d_tds->getExplain()->getExplanationFor(
              vs[k], ut, mexp, vsit, var_count, false);
          Trace("sygus-cref-eval2-debug") << "exp now: " << mexp << std::endl;
          msu[k] = vsit.getUpdatedTerm();
          Trace("sygus-cref-eval2-debug")
              << "updated term : " << msu[k] << std::endl;
        }
        if (!mexp.empty())
        {
          Node en = mexp.size() == 1 ? mexp[0] : nm->mkNode(kind::AND, mexp);
          cre_lem = nm->mkNode(kind::OR, en.negate(), neg_guard);
        }
        else
        {
          cre_lem = neg_guard;
        }
        if (std::find(lems.begin(), lems.end(), cre_lem) == lems.end())
        {
          Trace("sygus-cref-eval") << "...produced lemma : " << cre_lem
                                   << std::endl;
          lems.push_back(cre_lem);
        }
      }
    }
    if (!lems.empty())
    {
      break;
    }
  }
  return ret;
}

bool Cegis::checkRefinementEvalLemmas(const std::vector<Node>& vs,
                                      const std::vector<Node>& ms)
{
  // Maybe we already evaluated some terms in refinement lemmas.
  // In particular, the example eval cache for f may have some evaluations
  // cached, which we add to evalVisited and pass to the evaluator below.
  std::unordered_map<Node, Node> evalVisited;
  ExampleInfer* ei = d_parent->getExampleInfer();
  for (unsigned i = 0, vsize = vs.size(); i < vsize; i++)
  {
    Node f = vs[i];
    ExampleEvalCache* eec = d_parent->getExampleEvalCache(f);
    if (eec != nullptr)
    {
      // get the results we obtained through the example evaluation utility
      std::vector<Node> vsProc;
      std::vector<Node> msProc;
      Node bmsi = d_tds->sygusToBuiltin(ms[i]);
      ei->getExampleTerms(f, vsProc);
      eec->evaluateVec(bmsi, msProc);
      Assert(vsProc.size() == msProc.size());
      for (unsigned j = 0, psize = vsProc.size(); j < psize; j++)
      {
        evalVisited[vsProc[j]] = msProc[j];
        Assert(vsProc[j].getType() == msProc[j].getType());
      }
    }
  }

  for (unsigned r = 0; r < 2; r++)
  {
    std::unordered_set<Node>& rlemmas =
        r == 0 ? d_refinement_lemma_unit : d_refinement_lemma_conj;
    for (const Node& lem : rlemmas)
    {
      // We may have computed the evaluation of some function applications
      // via example-based symmetry breaking, stored in evalVisited.
      Node lemcsu = evaluate(lem, vs, ms, evalVisited);
      if (lemcsu.isConst() && !lemcsu.getConst<bool>())
      {
        return true;
      }
    }
  }
  return false;
}

bool Cegis::sampleAddRefinementLemma(const std::vector<Node>& candidates,
                                     const std::vector<Node>& vals)
{
  Trace("sygus-engine") << "  *** Do sample add refinement..." << std::endl;
  if (TraceIsOn("cegis-sample"))
  {
    Trace("cegis-sample") << "Check sampling for candidate solution"
                          << std::endl;
    for (unsigned i = 0, size = vals.size(); i < size; i++)
    {
      Trace("cegis-sample") << "  " << candidates[i] << " -> " << vals[i]
                            << std::endl;
    }
  }
  Assert(vals.size() == candidates.size());
  Node sbody = d_base_body.substitute(
      candidates.begin(), candidates.end(), vals.begin(), vals.end());
  Trace("cegis-sample-debug2") << "Sample " << sbody << std::endl;
  // do eager rewriting
  sbody = rewrite(sbody);
  Trace("cegis-sample") << "Sample (after rewriting): " << sbody << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  for (size_t i = 0, size = d_cegis_sampler.getNumSamplePoints(); i < size; i++)
  {
    if (d_cegis_sample_refine.find(i) == d_cegis_sample_refine.end())
    {
      Node ev = d_cegis_sampler.evaluate(sbody, i);
      Trace("cegis-sample-debug") << "...evaluate point #" << i << " to " << ev
                                  << std::endl;
      Assert(ev.getType().isBoolean());
      // if it evaluates to false
      if (ev.isConst() && !ev.getConst<bool>())
      {
        Trace("cegis-sample-debug") << "...false for point #" << i << std::endl;
        // mark this as a CEGIS point (no longer sampled)
        d_cegis_sample_refine.insert(i);
        const std::vector<Node>& pt = d_cegis_sampler.getSamplePoint(i);
        Assert(d_base_vars.size() == pt.size());
        Node rlem = d_base_body.substitute(
            d_base_vars.begin(), d_base_vars.end(), pt.begin(), pt.end());
        rlem = rewrite(rlem);
        if (std::find(
                d_refinement_lemmas.begin(), d_refinement_lemmas.end(), rlem)
            == d_refinement_lemmas.end())
        {
          if (TraceIsOn("cegis-sample"))
          {
            Trace("cegis-sample") << "   false for point #" << i << " : ";
            for (const Node& cn : pt)
            {
              Trace("cegis-sample") << cn << " ";
            }
            Trace("cegis-sample") << std::endl;
          }
          Trace("sygus-engine") << "  *** Refine by sampling" << std::endl;
          addRefinementLemma(rlem);
          // if trust, we are not interested in sending out refinement lemmas
          if (options().quantifiers.cegisSample
              != options::CegisSampleMode::TRUST)
          {
            Node lem = nm->mkNode(OR, d_parent->getConjecture().negate(), rlem);
            d_qim.addPendingLemma(
                lem, InferenceId::QUANTIFIERS_SYGUS_CEGIS_REFINE_SAMPLE);
          }
          return true;
        }
        else
        {
          Trace("cegis-sample-debug") << "...duplicate." << std::endl;
        }
      }
    }
  }
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

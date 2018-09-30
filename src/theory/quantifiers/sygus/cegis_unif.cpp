/*********************                                                        */
/*! \file cegis_unif.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief implementation of class for cegis with unification techniques
 **/

#include "theory/quantifiers/sygus/cegis_unif.h"

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/quantifiers/sygus/sygus_unif_rl.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/theory_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegisUnif::CegisUnif(QuantifiersEngine* qe, SynthConjecture* p)
    : Cegis(qe, p), d_sygus_unif(p), d_u_enum_manager(qe, p)
{
}

CegisUnif::~CegisUnif() {}
bool CegisUnif::processInitialize(Node n,
                                  const std::vector<Node>& candidates,
                                  std::vector<Node>& lemmas)
{
  // list of strategy points for unification candidates
  std::vector<Node> unif_candidate_pts;
  // map from strategy points to their conditions
  std::map<Node, Node> pt_to_cond;
  // strategy lemmas for each strategy point
  std::map<Node, std::vector<Node>> strategy_lemmas;
  // Initialize strategies for all functions-to-synhesize
  for (const Node& f : candidates)
  {
    // Init UNIF util for this candidate
    d_sygus_unif.initializeCandidate(
        d_qe, f, d_cand_to_strat_pt[f], strategy_lemmas);
    if (!d_sygus_unif.usingUnif(f))
    {
      Trace("cegis-unif") << "* non-unification candidate : " << f << std::endl;
      d_tds->registerEnumerator(f, f, d_parent);
      d_non_unif_candidates.push_back(f);
    }
    else
    {
      d_unif_candidates.push_back(f);
      Trace("cegis-unif") << "* unification candidate : " << f
                          << " with strategy points:" << std::endl;
      std::vector<Node>& enums = d_cand_to_strat_pt[f];
      unif_candidate_pts.insert(
          unif_candidate_pts.end(), enums.begin(), enums.end());
      // map strategy point to its condition in pt_to_cond
      for (const Node& e : enums)
      {
        Node cond = d_sygus_unif.getConditionForEvaluationPoint(e);
        Assert(!cond.isNull());
        Trace("cegis-unif")
            << "  " << e << " with condition : " << cond << std::endl;
        pt_to_cond[e] = cond;
      }
    }
  }
  // initialize the enumeration manager
  d_u_enum_manager.initialize(unif_candidate_pts, pt_to_cond, strategy_lemmas);
  return true;
}

void CegisUnif::getTermList(const std::vector<Node>& candidates,
                            std::vector<Node>& enums)
{
  // Non-unif candidate are themselves the enumerators
  enums.insert(
      enums.end(), d_non_unif_candidates.begin(), d_non_unif_candidates.end());
  Valuation& valuation = d_qe->getValuation();
  for (const Node& c : d_unif_candidates)
  {
    // Collect heads of candidates
    for (const Node& hd : d_sygus_unif.getEvalPointHeads(c))
    {
      Trace("cegis-unif-enum-debug")
          << "......cand " << c << " with enum hd " << hd << "\n";
      enums.push_back(hd);
    }
    // get unification enumerators
    for (const Node& e : d_cand_to_strat_pt[c])
    {
      for (unsigned index = 0; index < 2; index++)
      {
        std::vector<Node> uenums;
        // get the current unification enumerators
        d_u_enum_manager.getEnumeratorsForStrategyPt(e, uenums, index);
        if (index == 1 && options::sygusUnifCondIndependent())
        {
          Assert(uenums.size() == 1);
          Node eu = uenums[0];
          Node g = d_u_enum_manager.getActiveGuardForEnumerator(eu);
          // If active guard for this enumerator is not true, there are no more
          // values for it, and hence we ignore it
          Node gstatus = valuation.getSatValue(g);
          if (gstatus.isNull() || !gstatus.getConst<bool>())
          {
            continue;
          }
        }
        // get the model value of each enumerator
        enums.insert(enums.end(), uenums.begin(), uenums.end());
      }
    }
  }
}

bool CegisUnif::processConstructCandidates(const std::vector<Node>& enums,
                                           const std::vector<Node>& enum_values,
                                           const std::vector<Node>& candidates,
                                           std::vector<Node>& candidate_values,
                                           bool satisfiedRl,
                                           std::vector<Node>& lems)
{
  if (d_unif_candidates.empty())
  {
    Assert(d_non_unif_candidates.size() == candidates.size());
    return Cegis::processConstructCandidates(
        enums, enum_values, candidates, candidate_values, satisfiedRl, lems);
  }
  if (!satisfiedRl)
  {
    Trace("cegis-unif")
        << "..added refinement lemmas\n---CegisUnif Engine---\n";
    // if we didn't satisfy the specification, there is no way to repair
    return false;
  }
  // build model value map
  std::map<Node, Node> mvMap;
  for (unsigned i = 0, size = enums.size(); i < size; i++)
  {
    mvMap[enums[i]] = enum_values[i];
  }
  // the unification enumerators (return values, conditions) and their model
  // values
  NodeManager* nm = NodeManager::currentNM();
  bool addedUnifEnumSymBreakLemma = false;
  Node cost_lit = d_u_enum_manager.getAssertedLiteral();
  std::map<Node, std::vector<Node>> unif_enums[2];
  std::map<Node, std::vector<Node>> unif_values[2];
  for (const Node& c : d_unif_candidates)
  {
    // for each decision tree strategy allocated for c (these are referenced
    // by strategy points in d_cand_to_strat_pt[c])
    for (const Node& e : d_cand_to_strat_pt[c])
    {
      for (unsigned index = 0; index < 2; index++)
      {
        Trace("cegis") << "  " << (index == 0 ? "Return values" : "Conditions")
                       << " for " << e << ":\n";
        // get the current unification enumerators
        d_u_enum_manager.getEnumeratorsForStrategyPt(
            e, unif_enums[index][e], index);
        if (index == 1 && options::sygusUnifCondIndependent())
        {
          Assert(unif_enums[index][e].size() == 1);
          Node eu = unif_enums[index][e][0];
          if (mvMap.find(eu) == mvMap.end())
          {
            Trace("cegis") << "    " << eu << " -> N/A\n";
            unif_enums[index][e].clear();
            continue;
          }
        }
        // get the model value of each enumerator
        for (const Node& eu : unif_enums[index][e])
        {
          Assert(mvMap.find(eu) != mvMap.end());
          Node m_eu = mvMap[eu];
          if (Trace.isOn("cegis"))
          {
            Trace("cegis") << "    " << eu << " -> ";
            std::stringstream ss;
            Printer::getPrinter(options::outputLanguage())
                ->toStreamSygus(ss, m_eu);
            Trace("cegis") << ss.str() << std::endl;
          }
          unif_values[index][e].push_back(m_eu);
        }
        // inter-enumerator symmetry breaking for return values
        if (index == 0)
        {
          // given a pool of unification enumerators eu_1, ..., eu_n,
          // CegisUnifEnumDecisionStrategy insists that size(eu_1) <= ... <= size(eu_n).
          // We additionally insist that M(eu_i) < M(eu_{i+1}) when
          // size(eu_i) = size(eu_{i+1}), where < is pointer comparison.
          // We enforce this below by adding symmetry breaking lemmas of the
          // form ~( eu_i = M(eu_i) ^ eu_{i+1} = M(eu_{i+1} ) )
          // when applicable.
          // we only do this for return value enumerators, since condition
          // enumerators cannot be ordered (their order is based on the
          // seperation resolution scheme during model construction).
          for (unsigned j = 1, nenum = unif_values[index][e].size(); j < nenum;
               j++)
          {
            Node prev_val = unif_values[index][e][j - 1];
            Node curr_val = unif_values[index][e][j];
            // compare the node values
            if (curr_val < prev_val)
            {
              // must have the same size
              unsigned prev_size = d_tds->getSygusTermSize(prev_val);
              unsigned curr_size = d_tds->getSygusTermSize(curr_val);
              Assert(prev_size <= curr_size);
              if (curr_size == prev_size)
              {
                Node slem = nm->mkNode(AND,
                                       unif_enums[index][e][j - 1].eqNode(
                                           unif_values[index][e][j - 1]),
                                       unif_enums[index][e][j].eqNode(
                                           unif_values[index][e][j]))
                                .negate();
                Trace("cegis-unif")
                    << "CegisUnif::lemma, inter-unif-enumerator "
                       "symmetry breaking lemma : "
                    << slem << "\n";
                d_qe->getOutputChannel().lemma(slem);
                addedUnifEnumSymBreakLemma = true;
                break;
              }
            }
          }
        }
      }
    }
  }
  if (addedUnifEnumSymBreakLemma)
  {
    Trace("cegis-unif") << "..added unif enum symmetry breaking "
                           "lemma\n---CegisUnif Engine---\n";
    return false;
  }
  // set the conditions
  for (const Node& c : d_unif_candidates)
  {
    for (const Node& e : d_cand_to_strat_pt[c])
    {
      d_sygus_unif.setConditions(
          e, cost_lit, unif_enums[1][e], unif_values[1][e]);
      // if condition enumerator had value, exclude this value
      if (options::sygusUnifCondIndependent() && !unif_enums[1][e].empty())
      {
        Node eu = unif_enums[1][e][0];
        Assert(d_tds->isEnumerator(eu));
        if (d_tds->isPassiveEnumerator(eu))
        {
          Node g = d_u_enum_manager.getActiveGuardForEnumerator(eu);
          Node exp_exc =
              d_tds->getExplain()
                  ->getExplanationForEquality(eu, unif_values[1][e][0])
                  .negate();
          lems.push_back(nm->mkNode(OR, g.negate(), exp_exc));
        }
      }
    }
  }
  // build solutions (for unif candidates a divide-and-conquer approach is used)
  std::vector<Node> sols;
  std::vector<Node> lemmas;
  if (d_sygus_unif.constructSolution(sols, lemmas))
  {
    candidate_values.insert(candidate_values.end(), sols.begin(), sols.end());
    if (Trace.isOn("cegis-unif"))
    {
      Trace("cegis-unif") << "* Candidate solutions are:\n";
      for (const Node& sol : sols)
      {
        Trace("cegis-unif")
            << "... " << d_tds->sygusToBuiltin(sol, sol.getType()) << "\n";
      }
      Trace("cegis-unif") << "---CegisUnif Engine---\n";
    }
    return true;
  }

  // TODO tie this to the lemma for getting a new condition value
  Assert(options::sygusUnifCondIndependent() || !lemmas.empty());
  for (const Node& lem : lemmas)
  {
    Trace("cegis-unif-lemma")
        << "CegisUnif::lemma, separation lemma : " << lem << "\n";
    d_qe->getOutputChannel().lemma(lem);
  }
  Trace("cegis-unif") << "..failed to separate heads\n---CegisUnif Engine---\n";
  return false;
}

void CegisUnif::registerRefinementLemma(const std::vector<Node>& vars,
                                        Node lem,
                                        std::vector<Node>& lems)
{
  // Notify lemma to unification utility and get its purified form
  std::map<Node, std::vector<Node>> eval_pts;
  Node plem = d_sygus_unif.addRefLemma(lem, eval_pts);
  addRefinementLemma(plem);
  Trace("cegis-unif-lemma")
      << "CegisUnif::lemma, refinement lemma : " << plem << "\n";
  // Notify the enumeration manager if there are new evaluation points
  for (const std::pair<const Node, std::vector<Node>>& ep : eval_pts)
  {
    Assert(d_cand_to_strat_pt.find(ep.first) != d_cand_to_strat_pt.end());
    // Notify each strategy point of the respective candidate
    for (const Node& n : d_cand_to_strat_pt[ep.first])
    {
      d_u_enum_manager.registerEvalPts(ep.second, n);
    }
  }
  // Make the refinement lemma and add it to lems. This lemma is guarded by the
  // parent's guard, which has the semantics "this conjecture has a solution",
  // hence this lemma states: if the parent conjecture has a solution, it
  // satisfies the specification for the given concrete point.
  lems.push_back(NodeManager::currentNM()->mkNode(
      OR, d_parent->getGuard().negate(), plem));
}

CegisUnifEnumDecisionStrategy::CegisUnifEnumDecisionStrategy(
    QuantifiersEngine* qe, SynthConjecture* parent)
    : DecisionStrategyFmf(qe->getSatContext(), qe->getValuation()),
      d_qe(qe),
      d_parent(parent)
{
  d_initialized = false;
  d_tds = d_qe->getTermDatabaseSygus();
}

Node CegisUnifEnumDecisionStrategy::mkLiteral(unsigned n)
{
  NodeManager* nm = NodeManager::currentNM();
  Node new_lit = nm->mkSkolem("G_cost", nm->booleanType());
  unsigned new_size = n + 1;

  // allocate an enumerator for each candidate
  for (std::pair<const Node, StrategyPtInfo>& ci : d_ce_info)
  {
    Node c = ci.first;
    TypeNode ct = c.getType();
    Node eu = nm->mkSkolem("eu", ct);
    Node ceu;
    if (!options::sygusUnifCondIndependent() && !ci.second.d_enums[0].empty())
    {
      // make a new conditional enumerator as well, starting the
      // second type around
      ceu = nm->mkSkolem("cu", ci.second.d_ce_type);
    }
    // register the new enumerators
    for (unsigned index = 0; index < 2; index++)
    {
      Node e = index == 0 ? eu : ceu;
      if (e.isNull())
      {
        continue;
      }
      setUpEnumerator(e, ci.second, index);
    }
  }
  // register the evaluation points at the new value
  for (std::pair<const Node, StrategyPtInfo>& ci : d_ce_info)
  {
    Node c = ci.first;
    for (const Node& ei : ci.second.d_eval_points)
    {
      Trace("cegis-unif-enum") << "...increasing enum number for hd " << ei
                               << " to new size " << new_size << "\n";
      registerEvalPtAtSize(c, ei, new_lit, new_size);
    }
  }
  // enforce fairness between number of enumerators and enumerator size
  if (new_size > 1)
  {
    // construct the "virtual enumerator"
    if (d_virtual_enum.isNull())
    {
      // we construct the default integer grammar with no variables, e.g.:
      //   A -> 0 | 1 | A+A
      TypeNode intTn = nm->integerType();
      // use a null variable list
      Node bvl;
      std::stringstream ss;
      ss << "_virtual_enum_grammar";
      std::string virtualEnumName(ss.str());
      std::map<TypeNode, std::vector<Node>> extra_cons;
      std::map<TypeNode, std::vector<Node>> exclude_cons;
      // do not include "-", which is included by default for integers
      exclude_cons[intTn].push_back(nm->operatorOf(MINUS));
      std::unordered_set<Node, NodeHashFunction> term_irrelevant;
      TypeNode vtn = CegGrammarConstructor::mkSygusDefaultType(intTn,
                                                               bvl,
                                                               virtualEnumName,
                                                               extra_cons,
                                                               exclude_cons,
                                                               term_irrelevant);
      d_virtual_enum = nm->mkSkolem("_ve", vtn);
      d_tds->registerEnumerator(d_virtual_enum, Node::null(), d_parent);
    }
    // if new_size is a power of two, then isPow2 returns log2(new_size)+1
    // otherwise, this returns 0. In the case it returns 0, we don't care
    // since the floor( log2( i ) ) = floor( log2( i - 1 ) ) and we do not
    // increase our size bound.
    unsigned pow_two = Integer(new_size).isPow2();
    if (pow_two > 0)
    {
      Node size_ve = nm->mkNode(DT_SIZE, d_virtual_enum);
      Node fair_lemma =
          nm->mkNode(GEQ, size_ve, nm->mkConst(Rational(pow_two - 1)));
      fair_lemma = nm->mkNode(OR, new_lit, fair_lemma);
      Trace("cegis-unif-enum-lemma")
          << "CegisUnifEnum::lemma, fairness size:" << fair_lemma << "\n";
      // this lemma relates the number of conditions we enumerate and the
      // maximum size of a term that is part of our solution. It is of the
      // form:
      //   G_uq_i => size(ve) >= log_2( i-1 )
      // In other words, if we use i conditions, then we allow terms in our
      // solution whose size is at most log_2(i-1).
      d_qe->getOutputChannel().lemma(fair_lemma);
    }
  }

  return new_lit;
}

void CegisUnifEnumDecisionStrategy::initialize(
    const std::vector<Node>& es,
    const std::map<Node, Node>& e_to_cond,
    const std::map<Node, std::vector<Node>>& strategy_lemmas)
{
  Assert(!d_initialized);
  d_initialized = true;
  if (es.empty())
  {
    return;
  }
  // initialize type information for candidates
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& e : es)
  {
    Trace("cegis-unif-enum-debug") << "...adding strategy point " << e << "\n";
    // currently, we allocate the same enumerators for candidates of the same
    // type
    d_ce_info[e].d_pt = e;
    std::map<Node, Node>::const_iterator itcc = e_to_cond.find(e);
    Assert(itcc != e_to_cond.end());
    Node cond = itcc->second;
    Trace("cegis-unif-enum-debug")
        << "...its condition strategy point is " << cond << "\n";
    d_ce_info[e].d_ce_type = cond.getType();
    // initialize the symmetry breaking lemma templates
    for (unsigned index = 0; index < 2; index++)
    {
      Assert(d_ce_info[e].d_sbt_lemma_tmpl[index].first.isNull());
      Node sp = index == 0 ? e : cond;
      std::map<Node, std::vector<Node>>::const_iterator it =
          strategy_lemmas.find(sp);
      if (it == strategy_lemmas.end())
      {
        continue;
      }
      // collect lemmas for removing redundant ops for this candidate's type
      Node d_sbt_lemma =
          it->second.size() == 1 ? it->second[0] : nm->mkNode(AND, it->second);
      Trace("cegis-unif-enum-debug")
          << "...adding lemma template to remove redundant operators for " << sp
          << " --> lambda " << sp << ". " << d_sbt_lemma << "\n";
      d_ce_info[e].d_sbt_lemma_tmpl[index] =
          std::pair<Node, Node>(d_sbt_lemma, sp);
    }
  }

  // register this strategy
  d_qe->getTheoryEngine()->getDecisionManager()->registerStrategy(
      DecisionManager::STRAT_QUANT_CEGIS_UNIF_NUM_ENUMS, this);

  // create single condition enumerator for each decision tree strategy
  if (options::sygusUnifCondIndependent())
  {
    // allocate a condition enumerator for each candidate
    for (std::pair<const Node, StrategyPtInfo>& ci : d_ce_info)
    {
      Node ceu = nm->mkSkolem("cu", ci.second.d_ce_type);
      setUpEnumerator(ceu, ci.second, 1);
      d_enum_to_active_guard[ceu] = d_tds->getActiveGuardForEnumerator(ceu);
    }
  }
}

void CegisUnifEnumDecisionStrategy::getEnumeratorsForStrategyPt(Node e,
                                                       std::vector<Node>& es,
                                                       unsigned index) const
{
  // the number of active enumerators is related to the current cost value
  unsigned num_enums = 0;
  bool has_num_enums = getAssertedLiteralIndex(num_enums);
  AlwaysAssert(has_num_enums);
  num_enums = num_enums + 1;
  if (index == 1)
  {
    // we always use (cost-1) conditions, or 1 if in the indepedent case
    num_enums = !options::sygusUnifCondIndependent() ? num_enums - 1 : 1;
  }
  if (num_enums > 0)
  {
    std::map<Node, StrategyPtInfo>::const_iterator itc = d_ce_info.find(e);
    Assert(itc != d_ce_info.end());
    Assert(num_enums <= itc->second.d_enums[index].size());
    es.insert(es.end(),
              itc->second.d_enums[index].begin(),
              itc->second.d_enums[index].begin() + num_enums);
  }
}

Node CegisUnifEnumDecisionStrategy::getActiveGuardForEnumerator(Node e)
{
  Assert(d_enum_to_active_guard.find(e) != d_enum_to_active_guard.end());
  return d_enum_to_active_guard[e];
}

void CegisUnifEnumDecisionStrategy::setUpEnumerator(Node e,
                                           StrategyPtInfo& si,
                                           unsigned index)
{
  NodeManager* nm = NodeManager::currentNM();
  // instantiate template for removing redundant operators
  if (!si.d_sbt_lemma_tmpl[index].first.isNull())
  {
    Node templ = si.d_sbt_lemma_tmpl[index].first;
    TNode templ_var = si.d_sbt_lemma_tmpl[index].second;
    Node sym_break_red_ops = templ.substitute(templ_var, e);
    Trace("cegis-unif-enum-lemma")
        << "CegisUnifEnum::lemma, remove redundant ops of " << e << " : "
        << sym_break_red_ops << "\n";
    d_qe->getOutputChannel().lemma(sym_break_red_ops);
  }
  // symmetry breaking between enumerators
  if (!si.d_enums[index].empty() && index == 0)
  {
    Node e_prev = si.d_enums[index].back();
    Node size_e = nm->mkNode(DT_SIZE, e);
    Node size_e_prev = nm->mkNode(DT_SIZE, e_prev);
    Node sym_break = nm->mkNode(GEQ, size_e, size_e_prev);
    Trace("cegis-unif-enum-lemma")
        << "CegisUnifEnum::lemma, enum sym break:" << sym_break << "\n";
    d_qe->getOutputChannel().lemma(sym_break);
  }
  // register the enumerator
  si.d_enums[index].push_back(e);
  Trace("cegis-unif-enum") << "* Registering new enumerator " << e
                           << " to strategy point " << si.d_pt << "\n";
  d_tds->registerEnumerator(
      e, si.d_pt, d_parent, options::sygusUnifCondIndependent() && index == 1);
}

void CegisUnifEnumDecisionStrategy::registerEvalPts(const std::vector<Node>& eis, Node e)
{
  // candidates of the same type are managed
  std::map<Node, StrategyPtInfo>::iterator it = d_ce_info.find(e);
  Assert(it != d_ce_info.end());
  it->second.d_eval_points.insert(
      it->second.d_eval_points.end(), eis.begin(), eis.end());
  // register at all already allocated sizes
  for (const Node& ei : eis)
  {
    Assert(ei.getType() == e.getType());
    for (unsigned j = 0, size = d_literals.size(); j < size; j++)
    {
      Trace("cegis-unif-enum") << "...for cand " << e << " adding hd " << ei
                               << " at size " << j << "\n";
      registerEvalPtAtSize(e, ei, d_literals[j], j + 1);
    }
  }
}


void CegisUnifEnumDecisionStrategy::registerEvalPtAtSize(Node e,
                                                Node ei,
                                                Node guq_lit,
                                                unsigned n)
{
  // must be equal to one of the first n enums
  std::map<Node, StrategyPtInfo>::iterator itc = d_ce_info.find(e);
  Assert(itc != d_ce_info.end());
  Assert(itc->second.d_enums[0].size() >= n);
  std::vector<Node> disj;
  disj.push_back(guq_lit.negate());
  for (unsigned i = 0; i < n; i++)
  {
    disj.push_back(ei.eqNode(itc->second.d_enums[0][i]));
  }
  Node lem = NodeManager::currentNM()->mkNode(OR, disj);
  Trace("cegis-unif-enum-lemma")
      << "CegisUnifEnum::lemma, domain:" << lem << "\n";
  d_qe->getOutputChannel().lemma(lem);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

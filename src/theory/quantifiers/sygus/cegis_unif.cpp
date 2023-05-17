/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of class for cegis with unification techniques.
 */

#include "theory/quantifiers/sygus/cegis_unif.h"

#include "expr/skolem_manager.h"
#include "expr/sygus_datatype.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/sygus_unif_rl.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

CegisUnif::CegisUnif(Env& env,
                     QuantifiersState& qs,
                     QuantifiersInferenceManager& qim,
                     TermDbSygus* tds,
                     SynthConjecture* p)
    : Cegis(env, qs, qim, tds, p),
      d_sygus_unif(env, p),
      d_u_enum_manager(env, qs, qim, tds, p)
{
}

CegisUnif::~CegisUnif() {}
bool CegisUnif::processInitialize(Node conj,
                                  Node n,
                                  const std::vector<Node>& candidates)
{
  // list of strategy points for unification candidates
  std::vector<Node> unif_candidate_pts;
  // map from strategy points to their conditions
  std::map<Node, Node> pt_to_cond;
  // strategy lemmas for each strategy point
  std::map<Node, std::vector<Node>> strategy_lemmas;
  // Initialize strategies for all functions-to-synthesize
  // The role of non-unification enumerators is to be either the single solution
  // or part of a solution involving multiple enumerators.
  EnumeratorRole eroleNonUnif = candidates.size() == 1
                                    ? ROLE_ENUM_SINGLE_SOLUTION
                                    : ROLE_ENUM_MULTI_SOLUTION;
  for (const Node& f : candidates)
  {
    // Init UNIF util for this candidate
    d_sygus_unif.initializeCandidate(
        d_tds, f, d_cand_to_strat_pt[f], strategy_lemmas);
    if (!d_sygus_unif.usingUnif(f))
    {
      Trace("cegis-unif") << "* non-unification candidate : " << f << std::endl;
      d_tds->registerEnumerator(f, f, d_parent, eroleNonUnif);
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
        // get the model value of each enumerator
        enums.insert(enums.end(), uenums.begin(), uenums.end());
      }
    }
  }
}

bool CegisUnif::getEnumValues(const std::vector<Node>& enums,
                              const std::vector<Node>& enum_values,
                              std::map<Node, std::vector<Node>>& unif_cenums,
                              std::map<Node, std::vector<Node>>& unif_cvalues)
{
  NodeManager* nm = NodeManager::currentNM();
  Node cost_lit = d_u_enum_manager.getAssertedLiteral();
  std::map<Node, std::vector<Node>> unif_renums, unif_rvalues;
  // build model value map
  std::map<Node, Node> mvMap;
  for (unsigned i = 0, size = enums.size(); i < size; i++)
  {
    mvMap[enums[i]] = enum_values[i];
  }
  bool addedUnifEnumSymBreakLemma = false;
  // populate maps between unification enumerators and their model values
  for (const Node& c : d_unif_candidates)
  {
    // for each decision tree strategy allocated for c (these are referenced
    // by strategy points in d_cand_to_strat_pt[c])
    for (const Node& e : d_cand_to_strat_pt[c])
    {
      for (unsigned index = 0; index < 2; index++)
      {
        std::vector<Node> es, vs;
        Trace("cegis-unif")
            << "  " << (index == 0 ? "Return values" : "Conditions") << " for "
            << e << ":\n";
        // get the current unification enumerators
        d_u_enum_manager.getEnumeratorsForStrategyPt(e, es, index);
        // set enums for condition enumerators
        if (index == 1)
        {
          if (usingConditionPool())
          {
            Assert(es.size() == 1);
            // whether valueus exhausted
            if (mvMap.find(es[0]) == mvMap.end())
            {
              Trace("cegis-unif") << "    " << es[0] << " -> N/A\n";
              es.clear();
            }
          }
          unif_cenums[e] = es;
        }
        // get the model value of each enumerator
        for (const Node& eu : es)
        {
          Assert(mvMap.find(eu) != mvMap.end());
          Node m_eu = mvMap[eu];
          if (TraceIsOn("cegis-unif"))
          {
            Trace("cegis-unif") << "    " << eu << " -> ";
            TermDbSygus::toStreamSygus("cegis-unif", m_eu);
            Trace("cegis-unif") << "\n";
          }
          vs.push_back(m_eu);
        }
        // set values for condition enumerators of e
        if (index == 1)
        {
          unif_cvalues[e] = vs;
        }
        // inter-enumerator symmetry breaking for return values
        else
        {
          // given a pool of unification enumerators eu_1, ..., eu_n,
          // CegisUnifEnumDecisionStrategy insists that size(eu_1) <= ... <=
          // size(eu_n). We additionally insist that M(eu_i) < M(eu_{i+1}) when
          // size(eu_i) = size(eu_{i+1}), where < is pointer comparison.
          // We enforce this below by adding symmetry breaking lemmas of the
          // form ~( eu_i = M(eu_i) ^ eu_{i+1} = M(eu_{i+1} ) )
          // when applicable.
          // we only do this for return value enumerators, since condition
          // enumerators cannot be ordered (their order is based on the
          // seperation resolution scheme during model construction).
          for (unsigned j = 1, nenum = vs.size(); j < nenum; j++)
          {
            Node prev_val = vs[j - 1];
            Node curr_val = vs[j];
            // compare the node values
            if (curr_val < prev_val)
            {
              // must have the same size
              unsigned prev_size = datatypes::utils::getSygusTermSize(prev_val);
              unsigned curr_size = datatypes::utils::getSygusTermSize(curr_val);
              Assert(prev_size <= curr_size);
              if (curr_size == prev_size)
              {
                Node slem =
                    nm->mkNode(
                          AND, es[j - 1].eqNode(vs[j - 1]), es[j].eqNode(vs[j]))
                        .negate();
                Trace("cegis-unif")
                    << "CegisUnif::lemma, inter-unif-enumerator "
                       "symmetry breaking lemma : "
                    << slem << "\n";
                d_qim.lemma(
                    slem, InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_INTER_ENUM_SB);
                addedUnifEnumSymBreakLemma = true;
                break;
              }
            }
          }
        }
      }
    }
  }
  return !addedUnifEnumSymBreakLemma;
}

bool CegisUnif::usingConditionPool() const
{
  return d_sygus_unif.usingConditionPool();
}

void CegisUnif::setConditions(
    const std::map<Node, std::vector<Node>>& unif_cenums,
    const std::map<Node, std::vector<Node>>& unif_cvalues)
{
  Node cost_lit = d_u_enum_manager.getAssertedLiteral();
  NodeManager* nm = NodeManager::currentNM();
  // set the conditions
  for (const Node& c : d_unif_candidates)
  {
    for (const Node& e : d_cand_to_strat_pt[c])
    {
      Assert(unif_cenums.find(e) != unif_cenums.end());
      Assert(unif_cvalues.find(e) != unif_cvalues.end());
      std::map<Node, std::vector<Node>>::const_iterator itc =
          unif_cenums.find(e);
      std::map<Node, std::vector<Node>>::const_iterator itv =
          unif_cvalues.find(e);
      d_sygus_unif.setConditions(e, cost_lit, itc->second, itv->second);
      // d_sygus_unif.setConditions(e, cost_lit, unif_cenums[e],
      // unif_cvalues[e]); if condition enumerator had value and it is being
      // passively generated, exclude this value
      if (usingConditionPool() && !itc->second.empty())
      {
        Node eu = itc->second[0];
        Assert(d_tds->isEnumerator(eu));
        Assert(!itv->second.empty());
        if (d_tds->isPassiveEnumerator(eu))
        {
          Node g = d_tds->getActiveGuardForEnumerator(eu);
          Node exp_exc = d_tds->getExplain()
                             ->getExplanationForEquality(eu, itv->second[0])
                             .negate();
          Node lem = nm->mkNode(OR, g.negate(), exp_exc);
          d_qim.addPendingLemma(
              lem, InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_COND_EXCLUDE);
        }
      }
    }
  }
}

bool CegisUnif::processConstructCandidates(const std::vector<Node>& enums,
                                           const std::vector<Node>& enum_values,
                                           const std::vector<Node>& candidates,
                                           std::vector<Node>& candidate_values,
                                           bool satisfiedRl)
{
  if (d_unif_candidates.empty())
  {
    Assert(d_non_unif_candidates.size() == candidates.size());
    return Cegis::processConstructCandidates(
        enums, enum_values, candidates, candidate_values, satisfiedRl);
  }
  if (TraceIsOn("cegis-unif"))
  {
    for (const Node& c : d_unif_candidates)
    {
      // Collect heads of candidates
      Trace("cegis-unif") << "  Evaluation heads for " << c << " :\n";
      for (const Node& hd : d_sygus_unif.getEvalPointHeads(c))
      {
        bool isUnit = false;
        // d_rl_eval_hds accumulates eval apps, so need to look at operators
        for (const Node& hd_unit : d_rl_eval_hds)
        {
          if (hd == hd_unit[0])
          {
            isUnit = true;
            break;
          }
        }
        Trace("cegis-unif") << "    " << hd << (isUnit ? "*" : "") << " -> ";
        Assert(std::find(enums.begin(), enums.end(), hd) != enums.end());
        unsigned i = std::distance(enums.begin(),
                                   std::find(enums.begin(), enums.end(), hd));
        Assert(i >= 0 && i < enum_values.size());
        TermDbSygus::toStreamSygus("cegis-unif", enum_values[i]);
        Trace("cegis-unif") << "\n";
      }
    }
  }
  // the unification enumerators for conditions and their model values
  std::map<Node, std::vector<Node>> unif_cenums;
  std::map<Node, std::vector<Node>> unif_cvalues;
  // we only proceed to solution building if we are not introducing symmetry
  // breaking lemmas between return values and if we have not previously
  // introduced return values refinement lemmas
  if (!getEnumValues(enums, enum_values, unif_cenums, unif_cvalues)
      || !satisfiedRl)
  {
    // if condition values are being indepedently enumerated, they should be
    // communicated to the decision tree strategies indepedently of we
    // proceeding to attempt solution building
    if (usingConditionPool())
    {
      setConditions(unif_cenums, unif_cvalues);
    }
    Trace("cegis-unif") << (!satisfiedRl
                                ? "..added refinement lemmas"
                                : "..added unif enum symmetry breaking")
                        << "\n---CegisUnif Engine---\n";
    // if we didn't satisfy the specification, there is no way to repair
    return false;
  }
  setConditions(unif_cenums, unif_cvalues);
  // build solutions (for unif candidates a divide-and-conquer approach is used)
  std::vector<Node> sols;
  std::vector<Node> lemmas;
  if (d_sygus_unif.constructSolution(sols, lemmas))
  {
    candidate_values.insert(candidate_values.end(), sols.begin(), sols.end());
    if (TraceIsOn("cegis-unif"))
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
  Assert(usingConditionPool() || !lemmas.empty());
  for (const Node& lem : lemmas)
  {
    Trace("cegis-unif-lemma")
        << "CegisUnif::lemma, separation lemma : " << lem << "\n";
    d_qim.lemma(lem, InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_SEPARATION);
  }
  Trace("cegis-unif") << "..failed to separate heads\n---CegisUnif Engine---\n";
  return false;
}

void CegisUnif::registerRefinementLemma(const std::vector<Node>& vars, Node lem)
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
  // parent's conjecture, hence this lemma states: if the parent conjecture has
  // a solution, it satisfies the specification for the given concrete point.
  Node rlem =
      NodeManager::currentNM()->mkNode(OR, d_parent->getConjecture().negate(), plem);
  d_qim.addPendingLemma(rlem,
                        InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_REFINEMENT);
}

CegisUnifEnumDecisionStrategy::CegisUnifEnumDecisionStrategy(
    Env& env,
    QuantifiersState& qs,
    QuantifiersInferenceManager& qim,
    TermDbSygus* tds,
    SynthConjecture* parent)
    : DecisionStrategyFmf(env, qs.getValuation()),
      d_qim(qim),
      d_tds(tds),
      d_parent(parent)
{
  d_initialized = false;
  options::SygusUnifPiMode mode = options().quantifiers.sygusUnifPi;
  d_useCondPool = mode == options::SygusUnifPiMode::CENUM
                  || mode == options::SygusUnifPiMode::CENUM_IGAIN;
}

Node CegisUnifEnumDecisionStrategy::mkLiteral(unsigned n)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node newLit = sm->mkDummySkolem("G_cost", nm->booleanType());
  unsigned new_size = n + 1;

  // allocate an enumerator for each candidate
  for (std::pair<const Node, StrategyPtInfo>& ci : d_ce_info)
  {
    Node c = ci.first;
    TypeNode ct = c.getType();
    Node eu = sm->mkDummySkolem("eu", ct);
    Node ceu;
    if (!d_useCondPool && !ci.second.d_enums[0].empty())
    {
      // make a new conditional enumerator as well, starting the
      // second type around
      ceu = sm->mkDummySkolem("cu", ci.second.d_ce_type);
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
      registerEvalPtAtSize(c, ei, newLit, new_size);
    }
  }
  // enforce fairness between number of enumerators and enumerator size
  if (new_size > 1)
  {
    // construct the "virtual enumerator"
    if (d_virtual_enum.isNull())
    {
      // we construct the default integer grammar with no variables, e.g.:
      //   A -> 1 | A+A
      TypeNode intTn = nm->integerType();
      // use a null variable list
      Node bvl;
      std::string veName("_virtual_enum_grammar");
      SygusDatatype sdt(veName);
      TypeNode u = nm->mkUnresolvedDatatypeSort(veName);
      std::vector<TypeNode> cargsEmpty;
      Node cr = nm->mkConstInt(Rational(1));
      sdt.addConstructor(cr, "1", cargsEmpty);
      std::vector<TypeNode> cargsPlus;
      cargsPlus.push_back(u);
      cargsPlus.push_back(u);
      sdt.addConstructor(ADD, cargsPlus);
      sdt.initializeDatatype(nm->integerType(), bvl, false, false);
      std::vector<DType> datatypes;
      datatypes.push_back(sdt.getDatatype());
      std::vector<TypeNode> dtypes = nm->mkMutualDatatypeTypes(datatypes);
      d_virtual_enum = sm->mkDummySkolem("_ve", dtypes[0]);
      d_tds->registerEnumerator(
          d_virtual_enum, Node::null(), d_parent, ROLE_ENUM_CONSTRAINED);
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
          nm->mkNode(GEQ, size_ve, nm->mkConstInt(Rational(pow_two - 1)));
      fair_lemma = nm->mkNode(OR, newLit, fair_lemma);
      Trace("cegis-unif-enum-lemma")
          << "CegisUnifEnum::lemma, fairness size:" << fair_lemma << "\n";
      // this lemma relates the number of conditions we enumerate and the
      // maximum size of a term that is part of our solution. It is of the
      // form:
      //   G_uq_i => size(ve) >= log_2( i-1 )
      // In other words, if we use i conditions, then we allow terms in our
      // solution whose size is at most log_2(i-1).
      d_qim.lemma(fair_lemma, InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_FAIR_SIZE);
    }
  }

  return newLit;
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
  SkolemManager* sm = nm->getSkolemManager();
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
  d_qim.getDecisionManager()->registerStrategy(
      DecisionManager::STRAT_QUANT_CEGIS_UNIF_NUM_ENUMS, this);

  // create single condition enumerator for each decision tree strategy
  if (d_useCondPool)
  {
    // allocate a condition enumerator for each candidate
    for (std::pair<const Node, StrategyPtInfo>& ci : d_ce_info)
    {
      Node ceu = sm->mkDummySkolem("cu", ci.second.d_ce_type);
      setUpEnumerator(ceu, ci.second, 1);
    }
  }
}

void CegisUnifEnumDecisionStrategy::getEnumeratorsForStrategyPt(
    Node e, std::vector<Node>& es, unsigned index) const
{
  // the number of active enumerators is related to the current cost value
  unsigned num_enums = 0;
  bool has_num_enums = getAssertedLiteralIndex(num_enums);
  AlwaysAssert(has_num_enums);
  num_enums = num_enums + 1;
  if (index == 1)
  {
    // we always use (cost-1) conditions, or 1 if in the indepedent case
    num_enums = !d_useCondPool ? num_enums - 1 : 1;
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
    d_qim.lemma(sym_break_red_ops,
                InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_REM_OPS);
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
    d_qim.lemma(sym_break, InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_ENUM_SB);
  }
  // register the enumerator
  si.d_enums[index].push_back(e);
  EnumeratorRole erole = ROLE_ENUM_CONSTRAINED;
  // if we are using a single independent enumerator for conditions, then we
  // allocate an active guard, and are eligible to use variable-agnostic
  // enumeration.
  if (d_useCondPool && index == 1)
  {
    erole = ROLE_ENUM_POOL;
  }
  Trace("cegis-unif-enum") << "* Registering new enumerator " << e
                           << " to strategy point " << si.d_pt << "\n";
  d_tds->registerEnumerator(e, si.d_pt, d_parent, erole);
}

void CegisUnifEnumDecisionStrategy::registerEvalPts(
    const std::vector<Node>& eis, Node e)
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
  d_qim.lemma(lem, InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_DOMAIN);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

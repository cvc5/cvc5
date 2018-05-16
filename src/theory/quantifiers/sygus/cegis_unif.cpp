/*********************                                                        */
/*! \file cegis_unif.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Andrew Reynolds
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
#include "theory/quantifiers/sygus/ce_guided_conjecture.h"
#include "theory/quantifiers/sygus/sygus_unif_rl.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegisUnif::CegisUnif(QuantifiersEngine* qe, CegConjecture* p)
    : Cegis(qe, p), d_sygus_unif(p), d_u_enum_manager(qe, p)
{
  d_tds = d_qe->getTermDatabaseSygus();
}

CegisUnif::~CegisUnif() {}
bool CegisUnif::initialize(Node n,
                           const std::vector<Node>& candidates,
                           std::vector<Node>& lemmas)
{
  Trace("cegis-unif") << "Initialize CegisUnif : " << n << std::endl;
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
    }
    else
    {
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
        Trace("cegis-unif") << "  " << e << " with condition : " << cond
                            << std::endl;
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
  for (const Node& c : candidates)
  {
    // Non-unif candidate are themselves the enumerators
    if (!d_sygus_unif.usingUnif(c))
    {
      enums.push_back(c);
      continue;
    }
    // Collect heads of candidates
    for (const Node& hd : d_sygus_unif.getEvalPointHeads(c))
    {
      Trace("cegis-unif-enum-debug") << "......cand " << c << " with enum hd "
                                     << hd << "\n";
      enums.push_back(hd);
    }
  }
}

bool CegisUnif::constructCandidates(const std::vector<Node>& enums,
                                    const std::vector<Node>& enum_values,
                                    const std::vector<Node>& candidates,
                                    std::vector<Node>& candidate_values,
                                    std::vector<Node>& lems)
{
  if (Trace.isOn("cegis-unif-enum"))
  {
    Trace("cegis-unif-enum") << "  Evaluation heads :\n";
    for (unsigned i = 0, size = enums.size(); i < size; ++i)
    {
      Trace("cegis-unif-enum") << "    " << enums[i] << " -> ";
      std::stringstream ss;
      Printer::getPrinter(options::outputLanguage())
          ->toStreamSygus(ss, enum_values[i]);
      Trace("cegis-unif-enum") << ss.str() << std::endl;
    }
  }
  // evaluate on refinement lemmas
  if (addEvalLemmas(enums, enum_values))
  {
    return false;
  }
  // the unification enumerators (return values, conditions) and their model
  // values
  NodeManager* nm = NodeManager::currentNM();
  bool addedUnifEnumSymBreakLemma = false;
  std::map<Node, std::vector<Node>> unif_enums[2];
  std::map<Node, std::vector<Node>> unif_values[2];
  for (const Node& c : candidates)
  {
    // for each decision tree strategy allocated for c (these are referenced
    // by strategy points in d_cand_to_strat_pt[c])
    for (const Node& e : d_cand_to_strat_pt[c])
    {
      for (unsigned index = 0; index < 2; index++)
      {
        Trace("cegis-unif-enum")
            << "  " << (index == 0 ? "Return values" : "Conditions") << " for "
            << e << ":\n";
        // get the current unification enumerators
        d_u_enum_manager.getEnumeratorsForStrategyPt(
            e, unif_enums[index][e], index);
        // get the model value of each enumerator
        for (const Node& eu : unif_enums[index][e])
        {
          Node m_eu = d_parent->getModelValue(eu);
          if (Trace.isOn("cegis-unif-enum"))
          {
            Trace("cegis-unif-enum") << "    " << eu << " -> ";
            std::stringstream ss;
            Printer::getPrinter(options::outputLanguage())
                ->toStreamSygus(ss, m_eu);
            Trace("cegis-unif-enum") << ss.str() << std::endl;
          }
          unif_values[index][e].push_back(m_eu);
        }
        if (index == 0)
        {
          // inter-enumerator symmetry breaking
          // given a pool of unification enumerators eu_1, ..., eu_n,
          // CegisUnifEnumManager insists that size(eu_1) <= ... <= size(eu_n).
          // We additionally insist that M(eu_i) < M(eu_{i+1}) when
          // size(eu_i) = size(eu_{i+1}), where < is pointer comparison.
          // We enforce this below by adding symmetry breaking lemmas of the
          // form ~( eu_i = M(eu_i) ^ eu_{i+1} = M(eu_{i+1} ) )
          // when applicable.
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
    return false;
  }
  // set the conditions
  for (const Node& c : candidates)
  {
    for (const Node& e : d_cand_to_strat_pt[c])
    {
      d_sygus_unif.setConditions(e, unif_values[0][e], unif_values[1][e]);
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
  else
  {
    Assert(!lemmas.empty());
    for (const Node& lem : lemmas)
    {
      Trace("cegis-unif") << "CegisUnif::lemma, separation lemma : " << lem
                          << "\n";
      d_qe->getOutputChannel().lemma(lem);
    }
  }
  /*
  std::map<Node, std::vector<Node>> sepPairs;
  if (d_sygus_unif.getSeparationPairs(sepPairs))
  {
    // Build separation lemma based on current size, and for each heads that
    // could not be separated, the condition values currently enumerated for its
    // decision tree
    Node neg_cost_lit = d_u_enum_manager.getCurrentLiteral().negate();
    std::vector<Node> cenums, cond_eqs;
    for (std::pair<const Node, std::vector<Node>>& np : sepPairs)
    {
      Node e = np.first;
      // Build equalities between condition enumerators associated with the
      // strategy point whose decision tree could not separate the given heads
      std::vector<Node> cond_eqs;
      std::map<Node, std::vector<Node>>::iterator itue = unif_enums[1].find(e);
      Assert(itue != unif_enums[1].end());
      std::map<Node, std::vector<Node>>::iterator ituv = unif_values[1].find(e);
      Assert(ituv != unif_values[1].end());
      Assert(itue->second.size() == ituv->second.size());
      for (unsigned i = 0, size = itue->second.size(); i < size; i++)
      {
        cond_eqs.push_back(itue->second[i].eqNode(ituv->second[i]));
      }
      Assert(!cond_eqs.empty());
      Node neg_conds_lit =
          cond_eqs.size() > 1 ? nm->mkNode(AND, cond_eqs) : cond_eqs[0];
      neg_conds_lit = neg_conds_lit.negate();
      for (const Node& eq : np.second)
      {
        // A separation lemma is of the shape
        //   (cost_n+1 ^ (c_1 = M(c_1) ^ ... ^ M(c_n))) => e_i = e_j
        // in which cost_n+1 is the cost function for the size n+1, each c_k is
        // a conditional enumerator associated with the respective decision
        // tree, each M(c_k) its current model value, and e_i, e_j are two
        // distinct heads that could not be separated by these condition values
        //
        // Such a lemma will force the ground solver, within the restrictions of
        // the respective cost function, to make e_i and e_j equal or to come up
        // with new values for the conditional enumerators such that we can try
        Node sep_lemma = nm->mkNode(OR, neg_cost_lit, neg_conds_lit, eq);
        Trace("cegis-unif")
            << "CegisUnif::lemma, separation lemma : " << sep_lemma << "\n";
        d_qe->getOutputChannel().lemma(sep_lemma);
      }
    }
  }
  */
  return false;
}

void CegisUnif::registerRefinementLemma(const std::vector<Node>& vars,
                                        Node lem,
                                        std::vector<Node>& lems)
{
  // Notify lemma to unification utility and get its purified form
  std::map<Node, std::vector<Node>> eval_pts;
  Node plem = d_sygus_unif.addRefLemma(lem, eval_pts);
  d_refinement_lemmas.push_back(plem);
  Trace("cegis-unif-lemma") << "* Refinement lemma:\n" << plem << "\n";
  // Notify the enumeration manager if there are new evaluation points
  for (const std::pair<const Node, std::vector<Node>>& ep : eval_pts)
  {
    Assert(d_cand_to_strat_pt.find(ep.first) != d_cand_to_strat_pt.end());
    // Notify each startegy point of the respective candidate
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

Node CegisUnif::getNextDecisionRequest(unsigned& priority)
{
  return d_u_enum_manager.getNextDecisionRequest(priority);
}

CegisUnifEnumManager::CegisUnifEnumManager(QuantifiersEngine* qe,
                                           CegConjecture* parent)
    : d_qe(qe),
      d_parent(parent),
      d_ret_dec(qe->getSatContext(), false),
      d_curr_guq_val(qe->getSatContext(), 0)
{
  d_initialized = false;
  d_tds = d_qe->getTermDatabaseSygus();
}

void CegisUnifEnumManager::initialize(
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
    Trace("cegis-unif-enum-debug") << "...its condition strategy point is "
                                   << cond << "\n";
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
  // initialize the current literal
  incrementNumEnumerators();
}

void CegisUnifEnumManager::getEnumeratorsForStrategyPt(Node e,
                                                       std::vector<Node>& es,
                                                       unsigned index) const
{
  std::map<Node, StrategyPtInfo>::const_iterator itc = d_ce_info.find(e);
  Assert(itc != d_ce_info.end());
  es.insert(es.end(),
            itc->second.d_enums[index].begin(),
            itc->second.d_enums[index].end());
}

void CegisUnifEnumManager::registerEvalPts(const std::vector<Node>& eis, Node e)
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
    for (const std::pair<const unsigned, Node>& p : d_guq_lit)
    {
      Trace("cegis-unif-enum") << "...for cand " << e << " adding hd " << ei
                               << " at size " << p.first << "\n";
      registerEvalPtAtSize(e, ei, p.second, p.first);
    }
  }
}

Node CegisUnifEnumManager::getNextDecisionRequest(unsigned& priority)
{
  // are we not initialized or have we returned our decision in the current SAT
  // context?
  if (!d_initialized || d_ret_dec.get())
  {
    return Node::null();
  }
  if (d_ce_info.empty())
  {
    // if no enumerators, the decision is null
    d_ret_dec = true;
    return Node::null();
  }
  Node lit = getCurrentLiteral();
  bool value;
  if (!d_qe->getValuation().hasSatValue(lit, value))
  {
    priority = 1;
    return lit;
  }
  else if (!value)
  {
    // propagated false, increment
    incrementNumEnumerators();
    return getNextDecisionRequest(priority);
  }
  d_ret_dec = true;
  return Node::null();
}

void CegisUnifEnumManager::incrementNumEnumerators()
{
  unsigned new_size = d_curr_guq_val.get() + 1;
  d_curr_guq_val.set(new_size);
  // ensure that the literal has been allocated
  std::map<unsigned, Node>::iterator itc = d_guq_lit.find(new_size);
  if (itc == d_guq_lit.end())
  {
    // allocate the new literal
    NodeManager* nm = NodeManager::currentNM();
    Node new_lit = Rewriter::rewrite(nm->mkSkolem("G_cost", nm->booleanType()));
    new_lit = d_qe->getValuation().ensureLiteral(new_lit);
    AlwaysAssert(!new_lit.isNull());
    d_qe->getOutputChannel().requirePhase(new_lit, true);
    d_guq_lit[new_size] = new_lit;
    // allocate an enumerator for each candidate
    for (std::pair<const Node, StrategyPtInfo>& ci : d_ce_info)
    {
      Node c = ci.first;
      TypeNode ct = c.getType();
      Node eu = nm->mkSkolem("eu", ct);
      Node ceu;
      if (!ci.second.d_enums[0].empty())
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
        // instantiate template for removing redundant operators
        if (!ci.second.d_sbt_lemma_tmpl[index].first.isNull())
        {
          Node templ = ci.second.d_sbt_lemma_tmpl[index].first;
          TNode templ_var = ci.second.d_sbt_lemma_tmpl[index].second;
          Node sym_break_red_ops = templ.substitute(templ_var, e);
          Trace("cegis-unif-enum-lemma")
              << "CegisUnifEnum::lemma, remove redundant ops of " << e << " : "
              << sym_break_red_ops << "\n";
          d_qe->getOutputChannel().lemma(sym_break_red_ops);
        }
        // symmetry breaking between enumerators
        if (!ci.second.d_enums[index].empty() && index == 0)
        {
          Node e_prev = ci.second.d_enums[index].back();
          Node size_e = nm->mkNode(DT_SIZE, e);
          Node size_e_prev = nm->mkNode(DT_SIZE, e_prev);
          Node sym_break = nm->mkNode(GEQ, size_e, size_e_prev);
          Trace("cegis-unif-enum-lemma")
              << "CegisUnifEnum::lemma, enum sym break:" << sym_break << "\n";
          d_qe->getOutputChannel().lemma(sym_break);
        }
        // register the enumerator
        ci.second.d_enums[index].push_back(e);
        Trace("cegis-unif-enum") << "* Registering new enumerator " << e
                                 << " to strategy point " << ci.second.d_pt
                                 << "\n";
        d_tds->registerEnumerator(e, ci.second.d_pt, d_parent);
        // if the sygus datatype is interpreted as an infinite type
        // (this should be the case for almost all examples)
        TypeNode et = e.getType();
        if (!et.isInterpretedFinite())
        {
          // it is disequal from all previous ones
          for (const Node& ei : ci.second.d_enums[index])
          {
            if (ei == e)
            {
              continue;
            }
            Node deq = e.eqNode(ei).negate();
            Trace("cegis-unif-enum-lemma")
                << "CegisUnifEnum::lemma, enum deq:" << deq << "\n";
            d_qe->getOutputChannel().lemma(deq);
          }
        }
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
  }
}

Node CegisUnifEnumManager::getCurrentLiteral() const
{
  return getLiteral(d_curr_guq_val.get());
}

Node CegisUnifEnumManager::getLiteral(unsigned n) const
{
  std::map<unsigned, Node>::const_iterator itc = d_guq_lit.find(n);
  Assert(itc != d_guq_lit.end());
  return itc->second;
}

void CegisUnifEnumManager::registerEvalPtAtSize(Node e,
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
  Trace("cegis-unif-enum-lemma") << "CegisUnifEnum::lemma, domain:" << lem
                                 << "\n";
  d_qe->getOutputChannel().lemma(lem);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

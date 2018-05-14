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
  // Init UNIF util
  std::map<Node, std::vector<Node>> strategy_lemmas;
  d_sygus_unif.initialize(d_qe, candidates, d_cond_enums, strategy_lemmas);
  Trace("cegis-unif") << "Initializing enums for pure Cegis case\n";
  std::vector<Node> unif_candidates;
  // Initialize enumerators for non-unif functions-to-synhesize
  for (const Node& c : candidates)
  {
    if (!d_sygus_unif.usingUnif(c))
    {
      Trace("cegis-unif") << "* non-unification candidate : " << c << std::endl;
      d_tds->registerEnumerator(c, c, d_parent);
    }
    else
    {
      Trace("cegis-unif") << "* unification candidate : " << c << std::endl;
      unif_candidates.push_back(c);
    }
  }
  for (const Node& e : d_cond_enums)
  {
    Node g = d_tds->getActiveGuardForEnumerator(e);
    Assert(!g.isNull());
    d_enum_to_active_guard[e] = g;
  }
  // initialize the enumeration manager
  // TODO : map strategy points to their conditions
  //d_u_enum_manager.initialize(unif_candidates, strategy_lemmas);
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
    // Collect heads of candidate
    for (const Node& hd : d_sygus_unif.getEvalPointHeads(c))
    {
      Trace("cegis-unif-enum-debug") << "......cand " << c << " with enum hd "
                                     << hd << "\n";
      enums.push_back(hd);
    }
  }
  // Collect condition enumerators
  Valuation& valuation = d_qe->getValuation();
  for (const Node& e : d_cond_enums)
  {
    Assert(d_enum_to_active_guard.find(e) != d_enum_to_active_guard.end());
    Node g = d_enum_to_active_guard[e];
    // Get whether the active guard for this enumerator is set. If so, then
    // there may exist more values for it, and hence we add it to enums.
    Node gstatus = valuation.getSatValue(g);
    if (!gstatus.isNull() && gstatus.getConst<bool>())
    {
      enums.push_back(e);
    }
  }
}

bool CegisUnif::constructCandidates(const std::vector<Node>& enums,
                                    const std::vector<Node>& enum_values,
                                    const std::vector<Node>& candidates,
                                    std::vector<Node>& candidate_values,
                                    std::vector<Node>& lems)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("cegis-unif-enum") << "Register new enumerated values :\n";
  for (unsigned i = 0, size = enums.size(); i < size; ++i)
  {
    // Non-unif enums (which are the very candidates) should not be notified
    if (enums[i] == candidates[i] && !d_sygus_unif.usingUnif(enums[i]))
    {
      Trace("cegis-unif-enum") << "  Ignoring non-unif candidate " << enums[i]
                               << std::endl;
      continue;
    }
    if (Trace.isOn("cegis-unif-enum"))
    {
      Trace("cegis-unif-enum") << "  " << enums[i] << " -> ";
      std::stringstream ss;
      Printer::getPrinter(options::outputLanguage())
          ->toStreamSygus(ss, enum_values[i]);
      Trace("cegis-unif-enum") << ss.str() << std::endl;
    }
    Node e = enums[i], v = enum_values[i];
    std::vector<Node> enum_lems;
    d_sygus_unif.notifyEnumeration(e, v, enum_lems);
    // introduce lemmas to exclude this value of a condition enumerator from
    // future consideration
    std::map<Node, Node>::iterator it = d_enum_to_active_guard.find(e);
    if (it == d_enum_to_active_guard.end())
    {
      continue;
    }
    for (unsigned j = 0, size = enum_lems.size(); j < size; ++j)
    {
      enum_lems[j] = nm->mkNode(OR, it->second.negate(), enum_lems[j]);
    }
    lems.insert(lems.end(), enum_lems.begin(), enum_lems.end());
  }
  // evaluate on refinement lemmas
  if (addEvalLemmas(enums, enum_values))
  {
    Trace("cegis-unif-lemma") << "Added eval lemmas\n";
    return false;
  }
  // build solutions (for unif candidates a divide-and-conquer approach is used)
  std::vector<Node> sols;
  if (d_sygus_unif.constructSolution(sols))
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
  Trace("cegis-unif") << "* Refinement lemma:\n" << plem << "\n";
  // Notify the enumeration manager if there are new evaluation points
  for (const std::pair<const Node, std::vector<Node>>& ep : eval_pts)
  {
    Trace("cegis-unif") << "** Registering new point:\n" << plem << "\n";
    d_u_enum_manager.registerEvalPts(ep.second, ep.first);
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
    const std::vector<Node>& cs,
    const std::map<Node,Node>& c_to_cond,
    const std::map<Node, std::vector<Node>>& strategy_lemmas)
{
  Assert(!d_initialized);
  d_initialized = true;
  if (cs.empty())
  {
    return;
  }
  // initialize type information for candidates
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& c : cs)
  {
    Trace("cegis-unif-enum-debug") << "...adding candidate " << c << "\n";
    // currently, we allocate the same enumerators for candidates of the same
    // type
    d_ce_info[c].d_candidate = c;
    std::map<Node,Node>::const_iterator itcc = c_to_cond.find(c);
    Assert( itcc!=c_to_cond.end() );
    Node cond = itcc->second;
    Trace("cegis-unif-enum-debug") << "...its condition strategy point is " << cond << "\n";
    d_ce_info[c].d_ce_type = cond.getType();
    // initialize the symmetry breaking lemma templates
    for( unsigned index=0; index<2; index++ )
    {
      Assert(d_ce_info[c].d_sbt_lemma_tmpl[index].first.isNull());
      Node sp = index==0 ? c : cond;
      std::map<Node, std::vector<Node>>::const_iterator it = strategy_lemmas.find(sp);
      if (it == strategy_lemmas.end())
      {
        continue;
      }
      // collect lemmas for removing redundant ops for this candidate's type
      Node d_sbt_lemma = it->second.size()==1 ?  it->second[0] : nm->mkNode(AND, it->second);
      Trace("cegis-unif-enum-debug")
          << "...adding lemma template to remove redundant operators for " << sp
          << " --> lambda " << sp << ". " << d_sbt_lemma << "\n";
      d_ce_info[c].d_sbt_lemma_tmpl[index] = std::pair<Node,Node>(d_sbt_lemma,sp);
    }
  }
  // initialize the current literal
  incrementNumEnumerators();
}

void CegisUnifEnumManager::getCondEnumeratorsForCandidate(Node c, std::vector< Node >& ces ) const
{
  std::map<Node, CandidateInfo>::const_iterator itc = d_ce_info.find(c);
  Assert( itc!=d_ce_info.end() );
  ces.insert( ces.end(), itc->second.d_enums[1].begin(), itc->second.d_enums[1].end() );
}

void CegisUnifEnumManager::registerEvalPts(const std::vector<Node>& eis, Node c)
{
  // candidates of the same type are managed
  std::map<Node, CandidateInfo>::iterator it = d_ce_info.find(c);
  Assert(it != d_ce_info.end());
  it->second.d_eval_points.insert(
      it->second.d_eval_points.end(), eis.begin(), eis.end());
  // register at all already allocated sizes
  for (const Node& ei : eis)
  {
    Assert(ei.getType() == c.getType());
    for (const std::pair<const unsigned, Node>& p : d_guq_lit)
    {
      Trace("cegis-unif-enum") << "...for cand " << c << " adding hd " << ei
                               << " at size " << p.first << "\n";
      registerEvalPtAtSize(c, ei, p.second, p.first);
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
    for (std::pair<const Node, CandidateInfo>& ci : d_ce_info)
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
      for( unsigned index=0; index<2; index++ )
      {
        Node e = index==0 ? eu : ceu;
        if( e.isNull() )
        {
          continue;
        }
        // register the enumerator
        ci.second.d_enums[index].push_back(e);
        d_tds->registerEnumerator(e, ci.second.d_candidate, d_parent);
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
        Node e_prev = ci.second.d_enums[index].back();
        Node size_e = nm->mkNode(DT_SIZE, e);
        Node size_e_prev = nm->mkNode(DT_SIZE, e_prev);
        Node sym_break = nm->mkNode(GEQ, size_e, size_e_prev);
        Trace("cegis-unif-enum-lemma")
            << "CegisUnifEnum::lemma, enum sym break:" << sym_break << "\n";
        d_qe->getOutputChannel().lemma(sym_break);
        // if the sygus datatype is interpreted as an infinite type
        // (this should be the case for almost all examples)
        TypeNode et = e.getType();
        if (!et.isInterpretedFinite())
        {
          // it is disequal from all previous ones
          for (const Node ei : ci.second.d_enums[index])
          {
            Node deq = e.eqNode(ei).negate();
            Trace("cegis-unif-enum-lemma")
                << "CegisUnifEnum::lemma, enum deq:" << deq << "\n";
            d_qe->getOutputChannel().lemma(deq);
          }
        }
      }
    }
    // register the evaluation points at the new value
    for (std::pair<const Node, CandidateInfo>& ci : d_ce_info)
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

void CegisUnifEnumManager::registerEvalPtAtSize(Node c,
                                                Node ei,
                                                Node guq_lit,
                                                unsigned n)
{
  // must be equal to one of the first n enums
  std::map<Node, CandidateInfo>::iterator itc = d_ce_info.find(c);
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

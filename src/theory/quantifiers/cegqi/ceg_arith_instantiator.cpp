/*********************                                                        */
/*! \file ceg_arith_instantiator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of ceg_arith_instantiator
 **/

#include "theory/quantifiers/cegqi/ceg_arith_instantiator.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/theory_arith_private.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "util/random.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

ArithInstantiator::ArithInstantiator(TypeNode tn, VtsTermCache* vtc)
    : Instantiator(tn), d_vtc(vtc)
{
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
}

void ArithInstantiator::reset(CegInstantiator* ci,
                              SolvedForm& sf,
                              Node pv,
                              CegInstEffort effort)
{
  d_vts_sym[0] = d_vtc->getVtsInfinity(d_type, false, false);
  d_vts_sym[1] = d_vtc->getVtsDelta(false, false);
  for (unsigned i = 0; i < 2; i++)
  {
    d_mbp_bounds[i].clear();
    d_mbp_coeff[i].clear();
    for (unsigned j = 0; j < 2; j++)
    {
      d_mbp_vts_coeff[i][j].clear();
    }
    d_mbp_lit[i].clear();
  }
}

bool ArithInstantiator::hasProcessEquality(CegInstantiator* ci,
                                           SolvedForm& sf,
                                           Node pv,
                                           CegInstEffort effort)
{
  return true;
}

bool ArithInstantiator::processEquality(CegInstantiator* ci,
                                        SolvedForm& sf,
                                        Node pv,
                                        std::vector<TermProperties>& term_props,
                                        std::vector<Node>& terms,
                                        CegInstEffort effort)
{
  NodeManager* nm = NodeManager::currentNM();
  Node eq_lhs = terms[0];
  Node eq_rhs = terms[1];
  Node lhs_coeff = term_props[0].d_coeff;
  Node rhs_coeff = term_props[1].d_coeff;
  // make the same coefficient
  if (rhs_coeff != lhs_coeff)
  {
    if (!rhs_coeff.isNull())
    {
      Trace("cegqi-arith-debug") << "...mult lhs by " << rhs_coeff << std::endl;
      eq_lhs = nm->mkNode(MULT, rhs_coeff, eq_lhs);
      eq_lhs = Rewriter::rewrite(eq_lhs);
    }
    if (!lhs_coeff.isNull())
    {
      Trace("cegqi-arith-debug") << "...mult rhs by " << lhs_coeff << std::endl;
      eq_rhs = nm->mkNode(MULT, lhs_coeff, eq_rhs);
      eq_rhs = Rewriter::rewrite(eq_rhs);
    }
  }
  Node eq = eq_lhs.eqNode(eq_rhs);
  eq = Rewriter::rewrite(eq);
  Node val;
  TermProperties pv_prop;
  Node vts_coeff_inf;
  Node vts_coeff_delta;
  // isolate pv in the equality
  CegTermType ires = solve_arith(
      ci, pv, eq, pv_prop.d_coeff, val, vts_coeff_inf, vts_coeff_delta);
  if (ires != CEG_TT_INVALID)
  {
    pv_prop.d_type = CEG_TT_EQUAL;
    if (ci->constructInstantiationInc(pv, val, pv_prop, sf))
    {
      return true;
    }
  }
  return false;
}

bool ArithInstantiator::hasProcessAssertion(CegInstantiator* ci,
                                            SolvedForm& sf,
                                            Node pv,
                                            CegInstEffort effort)
{
  return effort != CEG_INST_EFFORT_FULL;
}

Node ArithInstantiator::hasProcessAssertion(CegInstantiator* ci,
                                            SolvedForm& sf,
                                            Node pv,
                                            Node lit,
                                            CegInstEffort effort)
{
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  // arithmetic inequalities and disequalities
  if (atom.getKind() == GEQ
      || (atom.getKind() == EQUAL && atom[0].getType().isReal()))
  {
    return lit;
  }
  return Node::null();
}

bool ArithInstantiator::processAssertion(CegInstantiator* ci,
                                         SolvedForm& sf,
                                         Node pv,
                                         Node lit,
                                         Node alit,
                                         CegInstEffort effort)
{
  NodeManager* nm = NodeManager::currentNM();
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool pol = lit.getKind() != NOT;
  // arithmetic inequalities and disequalities
  Assert(atom.getKind() == GEQ
         || (atom.getKind() == EQUAL && atom[0].getType().isReal()));
  // get model value for pv
  Node pv_value = ci->getModelValue(pv);
  // cannot contain infinity?
  Node vts_coeff_inf;
  Node vts_coeff_delta;
  Node val;
  TermProperties pv_prop;
  // isolate pv in the inequality
  CegTermType ires = solve_arith(
      ci, pv, atom, pv_prop.d_coeff, val, vts_coeff_inf, vts_coeff_delta);
  if (ires == CEG_TT_INVALID)
  {
    return false;
  }
  // compute how many bounds we will consider
  unsigned rmax = 1;
  if (atom.getKind() == EQUAL && (pol || !options::cegqiModel()))
  {
    rmax = 2;
  }
  for (unsigned r = 0; r < rmax; r++)
  {
    CegTermType uires = ires;
    Node uval = val;
    if (atom.getKind() == GEQ)
    {
      // push negation downwards
      if (!pol)
      {
        uires = mkNegateCTT(ires);
        if (d_type.isInteger())
        {
          uval = nm->mkNode(
              PLUS,
              val,
              nm->mkConst(Rational(isUpperBoundCTT(uires) ? 1 : -1)));
          uval = Rewriter::rewrite(uval);
        }
        else
        {
          Assert(d_type.isReal());
          // now is strict inequality
          uires = mkStrictCTT(uires);
        }
      }
    }
    else if (pol)
    {
      // equalities are both non-strict upper and lower bounds
      uires = r == 0 ? CEG_TT_UPPER : CEG_TT_LOWER;
    }
    else
    {
      // disequalities are either strict upper or lower bounds
      bool is_upper;
      if (options::cegqiModel())
      {
        // disequality is a disjunction : only consider the bound in the
        // direction of the model
        // first check if there is an infinity...
        if (!vts_coeff_inf.isNull())
        {
          // coefficient or val won't make a difference, just compare with zero
          Trace("cegqi-arith-debug") << "Disequality : check infinity polarity "
                                     << vts_coeff_inf << std::endl;
          Assert(vts_coeff_inf.isConst());
          is_upper = (vts_coeff_inf.getConst<Rational>().sgn() == 1);
        }
        else
        {
          Node rhs_value = ci->getModelValue(val);
          Node lhs_value = pv_prop.getModifiedTerm(pv_value);
          if (!pv_prop.isBasic())
          {
            lhs_value = pv_prop.getModifiedTerm(pv_value);
            lhs_value = Rewriter::rewrite(lhs_value);
          }
          Trace("cegqi-arith-debug")
              << "Disequality : check model values " << lhs_value << " "
              << rhs_value << std::endl;
          // it generally should be the case that lhs_value!=rhs_value
          // however, this assertion is violated e.g. if non-linear is enabled
          // since the quantifier-free arithmetic solver may pass full
          // effort with no lemmas even when we are not guaranteed to have a
          // model. By convention, we use GEQ to compare the values here.
          // It also may be the case that cmp is non-constant, in the case
          // where lhs or rhs contains a transcendental function. We consider
          // the bound to be an upper bound in this case.
          Node cmp = nm->mkNode(GEQ, lhs_value, rhs_value);
          cmp = Rewriter::rewrite(cmp);
          is_upper = !cmp.isConst() || !cmp.getConst<bool>();
        }
      }
      else
      {
        // since we are not using the model, we try both.
        is_upper = (r == 0);
      }
      Assert(atom.getKind() == EQUAL && !pol);
      if (d_type.isInteger())
      {
        uires = is_upper ? CEG_TT_LOWER : CEG_TT_UPPER;
        uval = nm->mkNode(
            PLUS, val, nm->mkConst(Rational(isUpperBoundCTT(uires) ? 1 : -1)));
        uval = Rewriter::rewrite(uval);
      }
      else
      {
        Assert(d_type.isReal());
        uires = is_upper ? CEG_TT_LOWER_STRICT : CEG_TT_UPPER_STRICT;
      }
    }
    if (Trace.isOn("cegqi-arith-bound-inf"))
    {
      Node pvmod = pv_prop.getModifiedTerm(pv);
      Trace("cegqi-arith-bound-inf") << "From " << lit << ", got : ";
      Trace("cegqi-arith-bound-inf")
          << pvmod << " -> " << uval << ", styp = " << uires << std::endl;
    }
    // take into account delta
    if (uires == CEG_TT_UPPER_STRICT || uires == CEG_TT_LOWER_STRICT)
    {
      if (options::cegqiModel())
      {
        Node delta_coeff =
            nm->mkConst(Rational(isUpperBoundCTT(uires) ? 1 : -1));
        if (vts_coeff_delta.isNull())
        {
          vts_coeff_delta = delta_coeff;
        }
        else
        {
          vts_coeff_delta = nm->mkNode(PLUS, vts_coeff_delta, delta_coeff);
          vts_coeff_delta = Rewriter::rewrite(vts_coeff_delta);
        }
      }
      else
      {
        Node delta = d_vtc->getVtsDelta();
        uval = nm->mkNode(
            uires == CEG_TT_UPPER_STRICT ? PLUS : MINUS, uval, delta);
        uval = Rewriter::rewrite(uval);
      }
    }
    if (options::cegqiModel())
    {
      // just store bounds, will choose based on tighest bound
      unsigned index = isUpperBoundCTT(uires) ? 0 : 1;
      d_mbp_bounds[index].push_back(uval);
      d_mbp_coeff[index].push_back(pv_prop.d_coeff);
      Trace("cegqi-arith-debug")
          << "Store bound " << index << " " << uval << " " << pv_prop.d_coeff
          << " " << vts_coeff_inf << " " << vts_coeff_delta << " " << lit
          << std::endl;
      for (unsigned t = 0; t < 2; t++)
      {
        d_mbp_vts_coeff[index][t].push_back(t == 0 ? vts_coeff_inf
                                                   : vts_coeff_delta);
      }
      d_mbp_lit[index].push_back(lit);
    }
    else
    {
      // try this bound
      pv_prop.d_type = isUpperBoundCTT(uires) ? CEG_TT_UPPER : CEG_TT_LOWER;
      if (ci->constructInstantiationInc(pv, uval, pv_prop, sf))
      {
        return true;
      }
    }
  }
  return false;
}

bool ArithInstantiator::processAssertions(CegInstantiator* ci,
                                          SolvedForm& sf,
                                          Node pv,
                                          CegInstEffort effort)
{
  if (!options::cegqiModel())
  {
    return false;
  }
  NodeManager* nm = NodeManager::currentNM();
  bool use_inf =
      d_type.isInteger() ? options::cegqiUseInfInt() : options::cegqiUseInfReal();
  bool upper_first = Random::getRandom().pickWithProb(0.5);
  if (options::cegqiMinBounds())
  {
    upper_first = d_mbp_bounds[1].size() < d_mbp_bounds[0].size();
  }
  int best_used[2];
  std::vector<Node> t_values[3];
  Node pv_value = ci->getModelValue(pv);
  // try optimal bounds
  for (unsigned r = 0; r < 2; r++)
  {
    int rr = upper_first ? (1 - r) : r;
    best_used[rr] = -1;
    if (d_mbp_bounds[rr].empty())
    {
      if (use_inf)
      {
        Trace("cegqi-arith-bound")
            << "No " << (rr == 0 ? "lower" : "upper") << " bounds for " << pv
            << " (type=" << d_type << ")" << std::endl;
        // no bounds, we do +- infinity
        Node val = d_vtc->getVtsInfinity(d_type);
        // could get rho value for infinity here
        if (rr == 0)
        {
          val = nm->mkNode(UMINUS, val);
          val = Rewriter::rewrite(val);
        }
        TermProperties pv_prop_no_bound;
        if (ci->constructInstantiationInc(pv, val, pv_prop_no_bound, sf))
        {
          return true;
        }
        else if (!options::cegqiMultiInst())
        {
          return false;
        }
      }
    }
    else
    {
      Trace("cegqi-arith-bound")
          << (rr == 0 ? "Lower" : "Upper") << " bounds for " << pv
          << " (type=" << d_type << ") : " << std::endl;
      int best = -1;
      Node best_bound_value[3];
      for (unsigned j = 0, nbounds = d_mbp_bounds[rr].size(); j < nbounds; j++)
      {
        Node value[3];
        if (Trace.isOn("cegqi-arith-bound"))
        {
          Assert(!d_mbp_bounds[rr][j].isNull());
          Trace("cegqi-arith-bound")
              << "  " << j << ": " << d_mbp_bounds[rr][j];
          if (!d_mbp_vts_coeff[rr][0][j].isNull())
          {
            Trace("cegqi-arith-bound")
                << " (+ " << d_mbp_vts_coeff[rr][0][j] << " * INF)";
          }
          if (!d_mbp_vts_coeff[rr][1][j].isNull())
          {
            Trace("cegqi-arith-bound")
                << " (+ " << d_mbp_vts_coeff[rr][1][j] << " * DELTA)";
          }
          if (!d_mbp_coeff[rr][j].isNull())
          {
            Trace("cegqi-arith-bound") << " (div " << d_mbp_coeff[rr][j] << ")";
          }
          Trace("cegqi-arith-bound") << ", value = ";
        }
        t_values[rr].push_back(Node::null());
        // check if it is better than the current best bound : lexicographic
        // order infinite/finite/infinitesimal parts
        bool new_best_set = false;
        bool new_best = true;
        for (unsigned t = 0; t < 3; t++)
        {
          // get the value
          if (t == 0)
          {
            value[0] = d_mbp_vts_coeff[rr][0][j];
            if (!value[0].isNull())
            {
              Trace("cegqi-arith-bound") << "( " << value[0] << " * INF ) + ";
            }
            else
            {
              value[0] = d_zero;
            }
          }
          else if (t == 1)
          {
            Node t_value = ci->getModelValue(d_mbp_bounds[rr][j]);
            t_values[rr][j] = t_value;
            value[1] = t_value;
            Trace("cegqi-arith-bound") << value[1];
          }
          else
          {
            value[2] = d_mbp_vts_coeff[rr][1][j];
            if (!value[2].isNull())
            {
              Trace("cegqi-arith-bound") << " + ( " << value[2] << " * DELTA )";
            }
            else
            {
              value[2] = d_zero;
            }
          }
          // multiply by coefficient
          if (value[t] != d_zero && !d_mbp_coeff[rr][j].isNull())
          {
            Assert(d_mbp_coeff[rr][j].isConst());
            value[t] = nm->mkNode(
                MULT,
                nm->mkConst(Rational(1)
                            / d_mbp_coeff[rr][j].getConst<Rational>()),
                value[t]);
            value[t] = Rewriter::rewrite(value[t]);
          }
          // check if new best, if we have not already set it.
          if (best != -1 && !new_best_set)
          {
            Assert(!value[t].isNull() && !best_bound_value[t].isNull());
            if (value[t] != best_bound_value[t])
            {
              Kind k = rr == 0 ? GEQ : LEQ;
              Node cmp_bound = nm->mkNode(k, value[t], best_bound_value[t]);
              cmp_bound = Rewriter::rewrite(cmp_bound);
              // Should be comparing two constant values which should rewrite
              // to a constant. If a step failed, we assume that this is not
              // the new best bound. We might not be comparing constant
              // values (for instance if transcendental functions are
              // involved), in which case we do update the best bound value.
              if (!cmp_bound.isConst() || !cmp_bound.getConst<bool>())
              {
                new_best = false;
                break;
              }
              // indicate that the value of new_best is now established.
              new_best_set = true;
            }
          }
        }
        Trace("cegqi-arith-bound") << std::endl;
        if (new_best)
        {
          for (unsigned t = 0; t < 3; t++)
          {
            best_bound_value[t] = value[t];
          }
          best = j;
        }
      }
      if (best != -1)
      {
        Trace("cegqi-arith-bound") << "...best bound is " << best << " : ";
        if (best_bound_value[0] != d_zero)
        {
          Trace("cegqi-arith-bound")
              << "( " << best_bound_value[0] << " * INF ) + ";
        }
        Trace("cegqi-arith-bound") << best_bound_value[1];
        if (best_bound_value[2] != d_zero)
        {
          Trace("cegqi-arith-bound")
              << " + ( " << best_bound_value[2] << " * DELTA )";
        }
        Trace("cegqi-arith-bound") << std::endl;
        best_used[rr] = best;
        // if using cbqiMidpoint, only add the instance based on one bound if
        // the bound is non-strict
        if (!options::cegqiMidpoint() || d_type.isInteger()
            || d_mbp_vts_coeff[rr][1][best].isNull())
        {
          Node val = d_mbp_bounds[rr][best];
          val = getModelBasedProjectionValue(ci,
                                             pv,
                                             val,
                                             rr == 0,
                                             d_mbp_coeff[rr][best],
                                             pv_value,
                                             t_values[rr][best],
                                             sf.getTheta(),
                                             d_mbp_vts_coeff[rr][0][best],
                                             d_mbp_vts_coeff[rr][1][best]);
          if (!val.isNull())
          {
            TermProperties pv_prop_bound;
            pv_prop_bound.d_coeff = d_mbp_coeff[rr][best];
            pv_prop_bound.d_type = rr == 0 ? CEG_TT_UPPER : CEG_TT_LOWER;
            if (ci->constructInstantiationInc(pv, val, pv_prop_bound, sf))
            {
              return true;
            }
            else if (!options::cegqiMultiInst())
            {
              return false;
            }
          }
        }
      }
    }
  }
  // if not using infinity, use model value of zero
  if (!use_inf && d_mbp_bounds[0].empty() && d_mbp_bounds[1].empty())
  {
    Node val = d_zero;
    TermProperties pv_prop_zero;
    Node theta = sf.getTheta();
    val = getModelBasedProjectionValue(ci,
                                       pv,
                                       val,
                                       true,
                                       pv_prop_zero.d_coeff,
                                       pv_value,
                                       d_zero,
                                       sf.getTheta(),
                                       Node::null(),
                                       Node::null());
    if (!val.isNull())
    {
      if (ci->constructInstantiationInc(pv, val, pv_prop_zero, sf))
      {
        return true;
      }
      else if (!options::cegqiMultiInst())
      {
        return false;
      }
    }
  }
  if (options::cegqiMidpoint() && !d_type.isInteger())
  {
    Node vals[2];
    bool bothBounds = true;
    Trace("cegqi-arith-bound") << "Try midpoint of bounds..." << std::endl;
    for (unsigned rr = 0; rr < 2; rr++)
    {
      int best = best_used[rr];
      if (best == -1)
      {
        bothBounds = false;
      }
      else
      {
        vals[rr] = d_mbp_bounds[rr][best];
        vals[rr] = getModelBasedProjectionValue(ci,
                                                pv,
                                                vals[rr],
                                                rr == 0,
                                                Node::null(),
                                                pv_value,
                                                t_values[rr][best],
                                                sf.getTheta(),
                                                d_mbp_vts_coeff[rr][0][best],
                                                Node::null());
      }
      Trace("cegqi-arith-bound") << "Bound : " << vals[rr] << std::endl;
    }
    Node val;
    if (bothBounds)
    {
      Assert(!vals[0].isNull() && !vals[1].isNull());
      if (vals[0] == vals[1])
      {
        val = vals[0];
      }
      else
      {
        val = nm->mkNode(MULT,
                         nm->mkNode(PLUS, vals[0], vals[1]),
                         nm->mkConst(Rational(1) / Rational(2)));
        val = Rewriter::rewrite(val);
      }
    }
    else
    {
      if (!vals[0].isNull())
      {
        val = nm->mkNode(PLUS, vals[0], d_one);
        val = Rewriter::rewrite(val);
      }
      else if (!vals[1].isNull())
      {
        val = nm->mkNode(MINUS, vals[1], d_one);
        val = Rewriter::rewrite(val);
      }
    }
    Trace("cegqi-arith-bound") << "Midpoint value : " << val << std::endl;
    if (!val.isNull())
    {
      TermProperties pv_prop_midpoint;
      if (ci->constructInstantiationInc(pv, val, pv_prop_midpoint, sf))
      {
        return true;
      }
      else if (!options::cegqiMultiInst())
      {
        return false;
      }
    }
  }
  // generally should not make it to this point, unless we are using a
  // non-monotonic selection function

  if (!options::cegqiNopt())
  {
    // if not trying non-optimal bounds, return
    return false;
  }
  // try non-optimal bounds (heuristic, may help when nested quantification) ?
  Trace("cegqi-arith-bound") << "Try non-optimal bounds..." << std::endl;
  for (unsigned r = 0; r < 2; r++)
  {
    int rr = upper_first ? (1 - r) : r;
    for (unsigned j = 0, nbounds = d_mbp_bounds[rr].size(); j < nbounds; j++)
    {
      if ((int)j != best_used[rr]
          && (!options::cegqiMidpoint() || d_mbp_vts_coeff[rr][1][j].isNull()))
      {
        Node val = getModelBasedProjectionValue(ci,
                                                pv,
                                                d_mbp_bounds[rr][j],
                                                rr == 0,
                                                d_mbp_coeff[rr][j],
                                                pv_value,
                                                t_values[rr][j],
                                                sf.getTheta(),
                                                d_mbp_vts_coeff[rr][0][j],
                                                d_mbp_vts_coeff[rr][1][j]);
        if (!val.isNull())
        {
          TermProperties pv_prop_nopt_bound;
          pv_prop_nopt_bound.d_coeff = d_mbp_coeff[rr][j];
          pv_prop_nopt_bound.d_type = rr == 0 ? CEG_TT_UPPER : CEG_TT_LOWER;
          if (ci->constructInstantiationInc(pv, val, pv_prop_nopt_bound, sf))
          {
            return true;
          }
          else if (!options::cegqiMultiInst())
          {
            return false;
          }
        }
      }
    }
  }
  return false;
}

bool ArithInstantiator::needsPostProcessInstantiationForVariable(
    CegInstantiator* ci, SolvedForm& sf, Node pv, CegInstEffort effort)
{
  return std::find(sf.d_non_basic.begin(), sf.d_non_basic.end(), pv)
         != sf.d_non_basic.end();
}

bool ArithInstantiator::postProcessInstantiationForVariable(
    CegInstantiator* ci,
    SolvedForm& sf,
    Node pv,
    CegInstEffort effort,
    std::vector<Node>& lemmas)
{
  Assert(std::find(sf.d_non_basic.begin(), sf.d_non_basic.end(), pv)
         != sf.d_non_basic.end());
  Assert(std::find(sf.d_vars.begin(), sf.d_vars.end(), pv) != sf.d_vars.end());
  unsigned index =
      std::find(sf.d_vars.begin(), sf.d_vars.end(), pv) - sf.d_vars.begin();
  Assert(!sf.d_props[index].isBasic());
  Node eq_lhs = sf.d_props[index].getModifiedTerm(sf.d_vars[index]);
  if (Trace.isOn("cegqi-arith-debug"))
  {
    Trace("cegqi-arith-debug") << "Normalize substitution for ";
    Trace("cegqi-arith-debug")
        << eq_lhs << " = " << sf.d_subs[index] << std::endl;
  }
  Assert(sf.d_vars[index].getType().isInteger());
  // must ensure that divisibility constraints are met
  // solve updated rewritten equality for vars[index], if coefficient is one,
  // then we are successful
  Node eq_rhs = sf.d_subs[index];
  Node eq = eq_lhs.eqNode(eq_rhs);
  eq = Rewriter::rewrite(eq);
  Trace("cegqi-arith-debug") << "...equality is " << eq << std::endl;
  std::map<Node, Node> msum;
  if (!ArithMSum::getMonomialSumLit(eq, msum))
  {
    Trace("cegqi-arith-debug") << "...failed to get monomial sum." << std::endl;
    return false;
  }
  Node veq;
  if (ArithMSum::isolate(sf.d_vars[index], msum, veq, EQUAL, true) == 0)
  {
    Trace("cegqi-arith-debug") << "...failed to isolate." << std::endl;
    return false;
  }
  Node veq_c;
  if (veq[0] != sf.d_vars[index])
  {
    Node veq_v;
    if (ArithMSum::getMonomial(veq[0], veq_c, veq_v))
    {
      Assert(veq_v == sf.d_vars[index]);
    }
  }
  sf.d_subs[index] = veq[1];
  if (!veq_c.isNull())
  {
    NodeManager* nm = NodeManager::currentNM();
    sf.d_subs[index] = nm->mkNode(INTS_DIVISION_TOTAL, veq[1], veq_c);
    Trace("cegqi-arith-debug")
        << "...bound type is : " << sf.d_props[index].d_type << std::endl;
    // intger division rounding up if from a lower bound
    if (sf.d_props[index].d_type == CEG_TT_UPPER
        && options::cegqiRoundUpLowerLia())
    {
      sf.d_subs[index] = nm->mkNode(
          PLUS,
          sf.d_subs[index],
          nm->mkNode(
              ITE,
              nm->mkNode(
                  EQUAL, nm->mkNode(INTS_MODULUS_TOTAL, veq[1], veq_c), d_zero),
              d_zero,
              d_one));
    }
  }
  Trace("cegqi-arith-debug") << "...normalize integers : " << sf.d_vars[index]
                             << " -> " << sf.d_subs[index] << std::endl;
  return true;
}

CegTermType ArithInstantiator::solve_arith(CegInstantiator* ci,
                                           Node pv,
                                           Node atom,
                                           Node& veq_c,
                                           Node& val,
                                           Node& vts_coeff_inf,
                                           Node& vts_coeff_delta)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("cegqi-arith-debug")
      << "isolate for " << pv << " in " << atom << std::endl;
  std::map<Node, Node> msum;
  if (!ArithMSum::getMonomialSumLit(atom, msum))
  {
    Trace("cegqi-arith-debug")
        << "fail : could not get monomial sum" << std::endl;
    return CEG_TT_INVALID;
  }
  Trace("cegqi-arith-debug") << "got monomial sum: " << std::endl;
  if (Trace.isOn("cegqi-arith-debug"))
  {
    ArithMSum::debugPrintMonomialSum(msum, "cegqi-arith-debug");
  }
  TypeNode pvtn = pv.getType();
  // remove vts symbols from polynomial
  Node vts_coeff[2];
  for (unsigned t = 0; t < 2; t++)
  {
    if (!d_vts_sym[t].isNull())
    {
      std::map<Node, Node>::iterator itminf = msum.find(d_vts_sym[t]);
      if (itminf != msum.end())
      {
        vts_coeff[t] = itminf->second;
        if (vts_coeff[t].isNull())
        {
          vts_coeff[t] = nm->mkConst(Rational(1));
        }
        // negate if coefficient on variable is positive
        std::map<Node, Node>::iterator itv = msum.find(pv);
        if (itv != msum.end())
        {
          // multiply by the coefficient we will isolate for
          if (itv->second.isNull())
          {
            vts_coeff[t] = ArithMSum::negate(vts_coeff[t]);
          }
          else
          {
            if (!pvtn.isInteger())
            {
              vts_coeff[t] = nm->mkNode(
                  MULT,
                  nm->mkConst(Rational(-1) / itv->second.getConst<Rational>()),
                  vts_coeff[t]);
              vts_coeff[t] = Rewriter::rewrite(vts_coeff[t]);
            }
            else if (itv->second.getConst<Rational>().sgn() == 1)
            {
              vts_coeff[t] = ArithMSum::negate(vts_coeff[t]);
            }
          }
        }
        Trace("cegqi-arith-debug")
            << "vts[" << t << "] coefficient is " << vts_coeff[t] << std::endl;
        msum.erase(d_vts_sym[t]);
      }
    }
  }

  int ires = ArithMSum::isolate(pv, msum, veq_c, val, atom.getKind());
  if (ires == 0)
  {
    Trace("cegqi-arith-debug") << "fail : isolate" << std::endl;
    return CEG_TT_INVALID;
  }
  if (Trace.isOn("cegqi-arith-debug"))
  {
    Trace("cegqi-arith-debug") << "Isolate : ";
    if (!veq_c.isNull())
    {
      Trace("cegqi-arith-debug") << veq_c << " * ";
    }
    Trace("cegqi-arith-debug")
        << pv << " " << atom.getKind() << " " << val << std::endl;
  }
  // when not pure LIA/LRA, we must check whether the lhs contains pv
  if (expr::hasSubterm(val, pv))
  {
    Trace("cegqi-arith-debug") << "fail : contains bad term" << std::endl;
    return CEG_TT_INVALID;
  }
  // if its type is integer but the substitution is not integer
  if (pvtn.isInteger()
      && ((!veq_c.isNull() && !veq_c.getType().isInteger())
          || !val.getType().isInteger()))
  {
    // redo, split integer/non-integer parts
    bool useCoeff = false;
    Integer coeff = ci->getQuantifiersEngine()
                        ->getTermUtil()
                        ->d_one.getConst<Rational>()
                        .getNumerator();
    for (std::map<Node, Node>::iterator it = msum.begin(); it != msum.end();
         ++it)
    {
      if (it->first.isNull() || it->first.getType().isInteger())
      {
        if (!it->second.isNull())
        {
          coeff = coeff.lcm(it->second.getConst<Rational>().getDenominator());
          useCoeff = true;
        }
      }
    }
    // multiply everything by this coefficient
    Node rcoeff = nm->mkConst(Rational(coeff));
    std::vector<Node> real_part;
    for (std::map<Node, Node>::iterator it = msum.begin(); it != msum.end();
         ++it)
    {
      if (useCoeff)
      {
        if (it->second.isNull())
        {
          msum[it->first] = rcoeff;
        }
        else
        {
          msum[it->first] =
              Rewriter::rewrite(nm->mkNode(MULT, it->second, rcoeff));
        }
      }
      if (!it->first.isNull() && !it->first.getType().isInteger())
      {
        real_part.push_back(msum[it->first].isNull()
                                ? it->first
                                : nm->mkNode(MULT, msum[it->first], it->first));
      }
    }
    // remove delta
    vts_coeff[1] = Node::null();
    // multiply inf
    if (!vts_coeff[0].isNull())
    {
      vts_coeff[0] = Rewriter::rewrite(nm->mkNode(MULT, rcoeff, vts_coeff[0]));
    }
    Node realPart = real_part.empty()
                        ? d_zero
                        : (real_part.size() == 1 ? real_part[0]
                                                 : nm->mkNode(PLUS, real_part));
    Assert(ci->isEligibleForInstantiation(realPart));
    // re-isolate
    Trace("cegqi-arith-debug") << "Re-isolate..." << std::endl;
    veq_c = Node::null();
    ires = ArithMSum::isolate(pv, msum, veq_c, val, atom.getKind());
    Trace("cegqi-arith-debug")
        << "Isolate for mixed Int/Real : " << veq_c << " * " << pv << " "
        << atom.getKind() << " " << val << std::endl;
    Trace("cegqi-arith-debug")
        << "                 real part : " << realPart << std::endl;
    if (ires != 0)
    {
      int ires_use =
          (msum[pv].isNull() || msum[pv].getConst<Rational>().sgn() == 1) ? 1
                                                                          : -1;
      val = Rewriter::rewrite(
          nm->mkNode(ires_use == -1 ? PLUS : MINUS,
                     nm->mkNode(ires_use == -1 ? MINUS : PLUS, val, realPart),
                     nm->mkNode(TO_INTEGER, realPart)));
      // could round up for upper bounds here
      Trace("cegqi-arith-debug") << "result : " << val << std::endl;
      Assert(val.getType().isInteger());
    }
    else
    {
      return CEG_TT_INVALID;
    }
  }
  vts_coeff_inf = vts_coeff[0];
  vts_coeff_delta = vts_coeff[1];
  Trace("cegqi-arith-debug")
      << "Return " << veq_c << " * " << pv << " " << atom.getKind() << " "
      << val << ", vts = (" << vts_coeff_inf << ", " << vts_coeff_delta << ")"
      << std::endl;
  Assert(ires != 0);
  if (atom.getKind() == EQUAL)
  {
    return CEG_TT_EQUAL;
  }
  return ires == 1 ? CEG_TT_UPPER : CEG_TT_LOWER;
}

Node ArithInstantiator::getModelBasedProjectionValue(CegInstantiator* ci,
                                                     Node e,
                                                     Node t,
                                                     bool isLower,
                                                     Node c,
                                                     Node me,
                                                     Node mt,
                                                     Node theta,
                                                     Node inf_coeff,
                                                     Node delta_coeff)
{
  NodeManager* nm = NodeManager::currentNM();
  Node val = t;
  Trace("cegqi-arith-bound2") << "Value : " << val << std::endl;
  Assert(!e.getType().isInteger() || t.getType().isInteger());
  Assert(!e.getType().isInteger() || mt.getType().isInteger());
  // add rho value
  // get the value of c*e
  Node ceValue = me;
  Node new_theta = theta;
  if (!c.isNull())
  {
    Assert(c.getType().isInteger());
    ceValue = nm->mkNode(MULT, ceValue, c);
    ceValue = Rewriter::rewrite(ceValue);
    if (new_theta.isNull())
    {
      new_theta = c;
    }
    else
    {
      new_theta = nm->mkNode(MULT, new_theta, c);
      new_theta = Rewriter::rewrite(new_theta);
    }
    Trace("cegqi-arith-bound2") << "...c*e = " << ceValue << std::endl;
    Trace("cegqi-arith-bound2") << "...theta = " << new_theta << std::endl;
  }
  if (!new_theta.isNull() && e.getType().isInteger())
  {
    Node rho;
    if (isLower)
    {
      rho = nm->mkNode(MINUS, ceValue, mt);
    }
    else
    {
      rho = nm->mkNode(MINUS, mt, ceValue);
    }
    rho = Rewriter::rewrite(rho);
    Trace("cegqi-arith-bound2")
        << "...rho = " << me << " - " << mt << " = " << rho << std::endl;
    Trace("cegqi-arith-bound2")
        << "..." << rho << " mod " << new_theta << " = ";
    rho = nm->mkNode(INTS_MODULUS_TOTAL, rho, new_theta);
    rho = Rewriter::rewrite(rho);
    Trace("cegqi-arith-bound2") << rho << std::endl;
    Kind rk = isLower ? PLUS : MINUS;
    val = nm->mkNode(rk, val, rho);
    val = Rewriter::rewrite(val);
    Trace("cegqi-arith-bound2") << "(after rho) : " << val << std::endl;
  }
  if (!inf_coeff.isNull())
  {
    Assert(!d_vts_sym[0].isNull());
    val = nm->mkNode(PLUS, val, nm->mkNode(MULT, inf_coeff, d_vts_sym[0]));
    val = Rewriter::rewrite(val);
  }
  if (!delta_coeff.isNull())
  {
    // create delta here if necessary
    val = nm->mkNode(
        PLUS, val, nm->mkNode(MULT, delta_coeff, d_vtc->getVtsDelta()));
    val = Rewriter::rewrite(val);
  }
  return val;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

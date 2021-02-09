/*********************                                                        */
/*! \file ceg_instantiator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Piotr Trojanek, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of counterexample-guided quantifier instantiation
 **/

#include "theory/quantifiers/cegqi/ceg_instantiator.h"

#include "theory/quantifiers/cegqi/ceg_arith_instantiator.h"
#include "theory/quantifiers/cegqi/ceg_bv_instantiator.h"
#include "theory/quantifiers/cegqi/ceg_dt_instantiator.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/cegqi/inst_strategy_cegqi.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegTermType mkStrictCTT(CegTermType c)
{
  Assert(!isStrictCTT(c));
  if (c == CEG_TT_LOWER)
  {
    return CEG_TT_LOWER_STRICT;
  }
  else if (c == CEG_TT_UPPER)
  {
    return CEG_TT_UPPER_STRICT;
  }
  return c;
}

CegTermType mkNegateCTT(CegTermType c)
{
  if (c == CEG_TT_LOWER)
  {
    return CEG_TT_UPPER;
  }
  else if (c == CEG_TT_UPPER)
  {
    return CEG_TT_LOWER;
  }
  else if (c == CEG_TT_LOWER_STRICT)
  {
    return CEG_TT_UPPER_STRICT;
  }
  else if (c == CEG_TT_UPPER_STRICT)
  {
    return CEG_TT_LOWER_STRICT;
  }
  return c;
}
bool isStrictCTT(CegTermType c)
{
  return c == CEG_TT_LOWER_STRICT || c == CEG_TT_UPPER_STRICT;
}
bool isLowerBoundCTT(CegTermType c)
{
  return c == CEG_TT_LOWER || c == CEG_TT_LOWER_STRICT;
}
bool isUpperBoundCTT(CegTermType c)
{
  return c == CEG_TT_UPPER || c == CEG_TT_UPPER_STRICT;
}

std::ostream& operator<<(std::ostream& os, CegInstEffort e)
{
  switch (e)
  {
    case CEG_INST_EFFORT_NONE: os << "?"; break;
    case CEG_INST_EFFORT_STANDARD: os << "STANDARD"; break;
    case CEG_INST_EFFORT_STANDARD_MV: os << "STANDARD_MV"; break;
    case CEG_INST_EFFORT_FULL: os << "FULL"; break;
    default: Unreachable();
  }
  return os;
}

std::ostream& operator<<(std::ostream& os, CegInstPhase phase)
{
  switch (phase)
  {
    case CEG_INST_PHASE_NONE: os << "?"; break;
    case CEG_INST_PHASE_EQC: os << "eqc"; break;
    case CEG_INST_PHASE_EQUAL: os << "eq"; break;
    case CEG_INST_PHASE_ASSERTION: os << "as"; break;
    case CEG_INST_PHASE_MVALUE: os << "mv"; break;
    default: Unreachable();
  }
  return os;
}
std::ostream& operator<<(std::ostream& os, CegHandledStatus status)
{
  switch (status)
  {
    case CEG_UNHANDLED: os << "unhandled"; break;
    case CEG_PARTIALLY_HANDLED: os << "partially_handled"; break;
    case CEG_HANDLED: os << "handled"; break;
    case CEG_HANDLED_UNCONDITIONAL: os << "handled_unc"; break;
    default: Unreachable();
  }
  return os;
}

void TermProperties::composeProperty(TermProperties& p)
{
  if (p.d_coeff.isNull())
  {
    return;
  }
  if (d_coeff.isNull())
  {
    d_coeff = p.d_coeff;
  }
  else
  {
    d_coeff = NodeManager::currentNM()->mkNode(MULT, d_coeff, p.d_coeff);
    d_coeff = Rewriter::rewrite(d_coeff);
  }
}

// push the substitution pv_prop.getModifiedTerm(pv) -> n
void SolvedForm::push_back(Node pv, Node n, TermProperties& pv_prop)
{
  d_vars.push_back(pv);
  d_subs.push_back(n);
  d_props.push_back(pv_prop);
  if (pv_prop.isBasic())
  {
    return;
  }
  d_non_basic.push_back(pv);
  // update theta value
  Node new_theta = getTheta();
  if (new_theta.isNull())
  {
    new_theta = pv_prop.d_coeff;
  }
  else
  {
    new_theta =
        NodeManager::currentNM()->mkNode(MULT, new_theta, pv_prop.d_coeff);
    new_theta = Rewriter::rewrite(new_theta);
  }
  d_theta.push_back(new_theta);
}
// pop the substitution pv_prop.getModifiedTerm(pv) -> n
void SolvedForm::pop_back(Node pv, Node n, TermProperties& pv_prop)
{
  d_vars.pop_back();
  d_subs.pop_back();
  d_props.pop_back();
  if (pv_prop.isBasic())
  {
    return;
  }
  d_non_basic.pop_back();
  // update theta value
  d_theta.pop_back();
}

CegInstantiator::CegInstantiator(Node q, InstStrategyCegqi* parent)
    : d_quant(q),
      d_parent(parent),
      d_qe(parent->getQuantifiersEngine()),
      d_is_nested_quant(false),
      d_effort(CEG_INST_EFFORT_NONE)
{
}

CegInstantiator::~CegInstantiator() {
  for (std::pair<Node, Instantiator*> inst : d_instantiator)
  {
    delete inst.second;
  }
  for (std::pair<TheoryId, InstantiatorPreprocess*> instp : d_tipp)
  {
    delete instp.second;
  }
}

void CegInstantiator::computeProgVars( Node n ){
  if( d_prog_var.find( n )==d_prog_var.end() ){
    d_prog_var[n].clear();
    if (n.getKind() == kind::WITNESS)
    {
      Assert(d_prog_var.find(n[0][0]) == d_prog_var.end());
      d_prog_var[n[0][0]].clear();
    }
    if (d_vars_set.find(n) != d_vars_set.end())
    {
      d_prog_var[n].insert(n);
    }
    else if (!isEligibleForInstantiation(n))
    {
      d_inelig.insert(n);
      return;
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      computeProgVars( n[i] );
      if( d_inelig.find( n[i] )!=d_inelig.end() ){
        d_inelig.insert(n);
      }
      // all variables in child are contained in this
      d_prog_var[n].insert(d_prog_var[n[i]].begin(), d_prog_var[n[i]].end());
    }
    // selectors applied to program variables are also variables
    if (n.getKind() == APPLY_SELECTOR_TOTAL
        && d_prog_var[n].find(n[0]) != d_prog_var[n].end())
    {
      d_prog_var[n].insert(n);
    }
    if (n.getKind() == kind::WITNESS)
    {
      d_prog_var.erase(n[0][0]);
    }
  }
}

bool CegInstantiator::isEligible( Node n ) {
  //compute d_subs_fv, which program variables are contained in n, and determines if eligible
  computeProgVars( n );
  return d_inelig.find( n )==d_inelig.end();
}

CegHandledStatus CegInstantiator::isCbqiKind(Kind k)
{
  if (quantifiers::TermUtil::isBoolConnective(k) || k == PLUS || k == GEQ
      || k == EQUAL || k == MULT || k == NONLINEAR_MULT || k == DIVISION
      || k == DIVISION_TOTAL || k == INTS_DIVISION || k == INTS_DIVISION_TOTAL
      || k == INTS_MODULUS || k == INTS_MODULUS_TOTAL || k == TO_INTEGER
      || k == IS_INTEGER)
  {
    return CEG_HANDLED;
  }

  // CBQI typically works for satisfaction-complete theories
  TheoryId t = kindToTheoryId(k);
  if (t == THEORY_BV || t == THEORY_FP || t == THEORY_DATATYPES
      || t == THEORY_BOOL)
  {
    return CEG_HANDLED;
  }
  return CEG_UNHANDLED;
}

CegHandledStatus CegInstantiator::isCbqiTerm(Node n)
{
  CegHandledStatus ret = CEG_HANDLED;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.getKind() != BOUND_VARIABLE && TermUtil::hasBoundVarAttr(cur))
      {
        if (cur.getKind() == FORALL || cur.getKind() == WITNESS)
        {
          visit.push_back(cur[1]);
        }
        else
        {
          CegHandledStatus curr = isCbqiKind(cur.getKind());
          if (curr < ret)
          {
            ret = curr;
            Trace("cegqi-debug2") << "Non-cbqi kind : " << cur.getKind()
                                 << " in " << n << std::endl;
            if (curr == CEG_UNHANDLED)
            {
              return CEG_UNHANDLED;
            }
          }
          for (const Node& nc : cur)
          {
            visit.push_back(nc);
          }
        }
      }
    }
  } while (!visit.empty());
  return ret;
}

CegHandledStatus CegInstantiator::isCbqiSort(TypeNode tn, QuantifiersEngine* qe)
{
  std::map<TypeNode, CegHandledStatus> visited;
  return isCbqiSort(tn, visited, qe);
}

CegHandledStatus CegInstantiator::isCbqiSort(
    TypeNode tn,
    std::map<TypeNode, CegHandledStatus>& visited,
    QuantifiersEngine* qe)
{
  std::map<TypeNode, CegHandledStatus>::iterator itv = visited.find(tn);
  if (itv != visited.end())
  {
    return itv->second;
  }
  CegHandledStatus ret = CEG_UNHANDLED;
  if (tn.isInteger() || tn.isReal() || tn.isBoolean() || tn.isBitVector()
      || tn.isFloatingPoint())
  {
    ret = CEG_HANDLED;
  }
  else if (tn.isDatatype())
  {
    // recursive calls to this datatype are handlable
    visited[tn] = CEG_HANDLED;
    // we initialize to handled, we remain handled as long as all subfields
    // of this datatype are not unhandled.
    ret = CEG_HANDLED;
    const DType& dt = tn.getDType();
    for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      // get the constructor type
      TypeNode consType;
      if (dt.isParametric())
      {
        // if parametric, must instantiate the argument types
        consType = dt[i].getSpecializedConstructorType(tn);
      }
      else
      {
        consType = dt[i].getConstructor().getType();
      }
      for (const TypeNode& crange : consType)
      {
        CegHandledStatus cret = isCbqiSort(crange, visited, qe);
        if (cret == CEG_UNHANDLED)
        {
          Trace("cegqi-debug2")
              << "Non-cbqi sort : " << tn << " due to " << crange << std::endl;
          visited[tn] = CEG_UNHANDLED;
          return CEG_UNHANDLED;
        }
        else if (cret < ret)
        {
          ret = cret;
        }
      }
    }
  }
  // sets, arrays, functions and others are not supported
  visited[tn] = ret;
  return ret;
}

CegHandledStatus CegInstantiator::isCbqiQuantPrefix(Node q,
                                                    QuantifiersEngine* qe)
{
  CegHandledStatus hmin = CEG_HANDLED_UNCONDITIONAL;
  for (const Node& v : q[0])
  {
    TypeNode tn = v.getType();
    CegHandledStatus handled = isCbqiSort(tn, qe);
    if (handled == CEG_UNHANDLED)
    {
      return CEG_UNHANDLED;
    }
    else if (handled < hmin)
    {
      hmin = handled;
    }
  }
  return hmin;
}

CegHandledStatus CegInstantiator::isCbqiQuant(Node q, QuantifiersEngine* qe)
{
  Assert(q.getKind() == FORALL);
  // compute attributes
  QAttributes qa;
  QuantAttributes::computeQuantAttributes(q, qa);
  if (qa.d_quant_elim)
  {
    return CEG_HANDLED;
  }
  if (qa.d_sygus)
  {
    return CEG_UNHANDLED;
  }
  Assert(!qa.d_quant_elim_partial);
  // if has an instantiation pattern, don't do it
  if (q.getNumChildren() == 3)
  {
    for (const Node& pat : q[2])
    {
      if (pat.getKind() == INST_PATTERN)
      {
        return CEG_UNHANDLED;
      }
    }
  }
  CegHandledStatus ret = CEG_HANDLED;
  // if quantifier has a non-handled variable, then do not use cbqi
  // if quantifier has an APPLY_UF term, then do not use cbqi unless EPR
  CegHandledStatus ncbqiv = CegInstantiator::isCbqiQuantPrefix(q, qe);
  Trace("cegqi-quant-debug") << "isCbqiQuantPrefix returned " << ncbqiv
                            << std::endl;
  if (ncbqiv == CEG_UNHANDLED)
  {
    // unhandled variable type
    ret = CEG_UNHANDLED;
  }
  else
  {
    CegHandledStatus cbqit = CegInstantiator::isCbqiTerm(q);
    Trace("cegqi-quant-debug") << "isCbqiTerm returned " << cbqit << std::endl;
    if (cbqit == CEG_UNHANDLED)
    {
      if (ncbqiv == CEG_HANDLED_UNCONDITIONAL)
      {
        // all variables are fully handled, this implies this will be handlable
        // regardless of body (e.g. for EPR)
        //  so, try but not exclusively
        ret = CEG_PARTIALLY_HANDLED;
      }
      else
      {
        // cannot be handled
        ret = CEG_UNHANDLED;
      }
    }
    else if (cbqit == CEG_PARTIALLY_HANDLED)
    {
      ret = CEG_PARTIALLY_HANDLED;
    }
  }
  if (ret == CEG_UNHANDLED && options::cegqiAll())
  {
    // try but not exclusively
    ret = CEG_PARTIALLY_HANDLED;
  }
  return ret;
}

bool CegInstantiator::hasVariable( Node n, Node pv ) {
  computeProgVars( n );
  return d_prog_var[n].find( pv )!=d_prog_var[n].end();
}

void CegInstantiator::activateInstantiationVariable(Node v, unsigned index)
{
  if( d_instantiator.find( v )==d_instantiator.end() ){
    TypeNode tn = v.getType();
    Instantiator * vinst;
    if( tn.isReal() ){
      vinst = new ArithInstantiator(tn, d_parent->getVtsTermCache());
    }else if( tn.isDatatype() ){
      vinst = new DtInstantiator(tn);
    }else if( tn.isBitVector() ){
      vinst = new BvInstantiator(tn, d_parent->getBvInverter());
    }else if( tn.isBoolean() ){
      vinst = new ModelValueInstantiator(tn);
    }else{
      //default
      vinst = new Instantiator(tn);
    }
    d_instantiator[v] = vinst;
  }
  d_curr_subs_proc[v].clear();
  d_curr_index[v] = index;
  d_curr_iphase[v] = CEG_INST_PHASE_NONE;
}

void CegInstantiator::deactivateInstantiationVariable(Node v)
{
  d_curr_subs_proc.erase(v);
  d_curr_index.erase(v);
  d_curr_iphase.erase(v);
}

bool CegInstantiator::hasTriedInstantiation(Node v)
{
  return !d_curr_subs_proc[v].empty();
}

void CegInstantiator::registerTheoryIds(TypeNode tn,
                                        std::map<TypeNode, bool>& visited)
{
  if (visited.find(tn) == visited.end())
  {
    visited[tn] = true;
    TheoryId tid = Theory::theoryOf(tn);
    registerTheoryId(tid);
    if (tn.isDatatype())
    {
      const DType& dt = tn.getDType();
      for (unsigned i = 0; i < dt.getNumConstructors(); i++)
      {
        for (unsigned j = 0; j < dt[i].getNumArgs(); j++)
        {
          registerTheoryIds(dt[i].getArgType(j), visited);
        }
      }
    }
  }
}

void CegInstantiator::registerTheoryId(TheoryId tid)
{
  if (std::find(d_tids.begin(), d_tids.end(), tid) == d_tids.end())
  {
    // setup any theory-specific preprocessors here
    if (tid == THEORY_BV)
    {
      d_tipp[tid] = new BvInstantiatorPreprocess;
    }
    d_tids.push_back(tid);
  }
}

void CegInstantiator::registerVariable(Node v)
{
  Assert(std::find(d_vars.begin(), d_vars.end(), v) == d_vars.end());
  d_vars.push_back(v);
  d_vars_set.insert(v);
  TypeNode vtn = v.getType();
  Trace("cegqi-proc-debug") << "Collect theory ids from type " << vtn << " of "
                           << v << std::endl;
  // collect relevant theories for this variable
  std::map<TypeNode, bool> visited;
  registerTheoryIds(vtn, visited);
}

bool CegInstantiator::constructInstantiation(SolvedForm& sf, unsigned i)
{
  if( i==d_vars.size() ){
    //solved for all variables, now construct instantiation
    bool needsPostprocess =
        sf.d_vars.size() > d_input_vars.size() || !d_var_order_index.empty();
    std::vector< Instantiator * > pp_inst;
    std::map< Instantiator *, Node > pp_inst_to_var;
    std::vector< Node > lemmas;
    for( std::map< Node, Instantiator * >::iterator ita = d_active_instantiators.begin(); ita != d_active_instantiators.end(); ++ita ){
      if (ita->second->needsPostProcessInstantiationForVariable(
              this, sf, ita->first, d_effort))
      {
        needsPostprocess = true;
        pp_inst_to_var[ ita->second ] = ita->first;
      }
    }
    if( needsPostprocess ){
      //must make copy so that backtracking reverts sf
      SolvedForm sf_tmp = sf;
      bool postProcessSuccess = true;
      for( std::map< Instantiator *, Node >::iterator itp = pp_inst_to_var.begin(); itp != pp_inst_to_var.end(); ++itp ){
        if (!itp->first->postProcessInstantiationForVariable(
                this, sf_tmp, itp->second, d_effort, lemmas))
        {
          postProcessSuccess = false;
          break;
        }
      }
      if( postProcessSuccess ){
        return doAddInstantiation( sf_tmp.d_vars, sf_tmp.d_subs, lemmas );
      }else{
        return false;
      }
    }else{
      return doAddInstantiation( sf.d_vars, sf.d_subs, lemmas );
    }
  }else{
    bool is_sv = false;
    Node pv;
    if( d_stack_vars.empty() ){
      pv = d_vars[i];
    }else{
      pv = d_stack_vars.back();
      is_sv = true;
      d_stack_vars.pop_back();
    }
    activateInstantiationVariable(pv, i);

    //get the instantiator object
    Assert(d_instantiator.find(pv) != d_instantiator.end());
    Instantiator* vinst = d_instantiator[pv];
    Assert(vinst != NULL);
    d_active_instantiators[pv] = vinst;
    vinst->reset(this, sf, pv, d_effort);
    // if d_effort is full, we must choose at least one model value
    if ((i + 1) < d_vars.size() || d_effort != CEG_INST_EFFORT_FULL)
    {
      // First, try to construct an instantiation term for pv based on
      // equality and theory-specific instantiation techniques.
      if (constructInstantiation(sf, vinst, pv))
      {
        return true;
      }
    }
    // If the above call fails, resort to using value in model. We do so if:
    // - we have yet to try an instantiation this round (or we are trying
    //   multiple instantiations, indicated by options::cegqiMultiInst),
    // - the instantiator uses model values at this effort or
    //   if we are solving for a subfield of a datatype (is_sv), and
    // - the instantiator allows model values.
    if ((options::cegqiMultiInst() || !hasTriedInstantiation(pv))
        && (vinst->useModelValue(this, sf, pv, d_effort) || is_sv)
        && vinst->allowModelValue(this, sf, pv, d_effort))
    {
      Node mv = getModelValue( pv );
      TermProperties pv_prop_m;
      Trace("cegqi-inst-debug") << "[4] " << i << "...try model value " << mv << std::endl;
      d_curr_iphase[pv] = CEG_INST_PHASE_MVALUE;
      CegInstEffort prev = d_effort;
      if (d_effort < CEG_INST_EFFORT_STANDARD_MV)
      {
        // update the effort level to indicate we have used a model value
        d_effort = CEG_INST_EFFORT_STANDARD_MV;
      }
      if (constructInstantiationInc(pv, mv, pv_prop_m, sf))
      {
        return true;
      }
      d_effort = prev;
    }

    Trace("cegqi-inst-debug") << "[No instantiation found for " << pv << "]" << std::endl;
    if (is_sv)
    {
      d_stack_vars.push_back( pv );
    }
    d_active_instantiators.erase( pv );
    deactivateInstantiationVariable(pv);
    return false;
  }
}

bool CegInstantiator::constructInstantiation(SolvedForm& sf,
                                             Instantiator* vinst,
                                             Node pv)
{
  TypeNode pvtn = pv.getType();
  TypeNode pvtnb = pvtn.getBaseType();
  Node pvr = pv;
  eq::EqualityEngine* ee = d_qe->getState().getEqualityEngine();
  if (ee->hasTerm(pv))
  {
    pvr = ee->getRepresentative(pv);
  }
  Trace("cegqi-inst-debug") << "[Find instantiation for " << pv
                           << "], rep=" << pvr << ", instantiator is "
                           << vinst->identify() << std::endl;
  Node pv_value;
  if (options::cegqiModel())
  {
    pv_value = getModelValue(pv);
    Trace("cegqi-bound2") << "...M( " << pv << " ) = " << pv_value << std::endl;
  }

  //[1] easy case : pv is in the equivalence class as another term not
  // containing pv
  if (vinst->hasProcessEqualTerm(this, sf, pv, d_effort))
  {
    Trace("cegqi-inst-debug")
        << "[1] try based on equivalence class." << std::endl;
    d_curr_iphase[pv] = CEG_INST_PHASE_EQC;
    std::map<Node, std::vector<Node> >::iterator it_eqc = d_curr_eqc.find(pvr);
    if (it_eqc != d_curr_eqc.end())
    {
      // std::vector< Node > eq_candidates;
      Trace("cegqi-inst-debug2")
          << "...eqc has size " << it_eqc->second.size() << std::endl;
      for (const Node& n : it_eqc->second)
      {
        if (n != pv)
        {
          Trace("cegqi-inst-debug")
              << "...try based on equal term " << n << std::endl;
          // must be an eligible term
          if (isEligible(n))
          {
            Node ns;
            // coefficient of pv in the equality we solve (null is 1)
            TermProperties pv_prop;
            bool proc = false;
            if (!d_prog_var[n].empty())
            {
              ns = applySubstitution(pvtn, n, sf, pv_prop, false);
              if (!ns.isNull())
              {
                computeProgVars(ns);
                // substituted version must be new and cannot contain pv
                proc = d_prog_var[ns].find(pv) == d_prog_var[ns].end();
              }
            }
            else
            {
              ns = n;
              proc = true;
            }
            if (proc)
            {
              if (vinst->processEqualTerm(this, sf, pv, pv_prop, ns, d_effort))
              {
                return true;
              }
              else if (!options::cegqiMultiInst() && hasTriedInstantiation(pv))
              {
                return false;
              }
              // Do not consider more than one equal term,
              // this helps non-monotonic strategies that may encounter
              // duplicate instantiations.
              break;
            }
          }
        }
      }
      if (vinst->processEqualTerms(this, sf, pv, it_eqc->second, d_effort))
      {
        return true;
      }
      else if (!options::cegqiMultiInst() && hasTriedInstantiation(pv))
      {
        return false;
      }
    }
    else
    {
      Trace("cegqi-inst-debug2") << "...eqc not found." << std::endl;
    }
  }

  //[2] : we can solve an equality for pv
  /// iterate over equivalence classes to find cases where we can solve for
  /// the variable
  if (vinst->hasProcessEquality(this, sf, pv, d_effort))
  {
    Trace("cegqi-inst-debug")
        << "[2] try based on solving equalities." << std::endl;
    d_curr_iphase[pv] = CEG_INST_PHASE_EQUAL;
    std::vector<Node>& cteqc = d_curr_type_eqc[pvtnb];

    for (const Node& r : cteqc)
    {
      std::map<Node, std::vector<Node> >::iterator it_reqc = d_curr_eqc.find(r);
      std::vector<Node> lhs;
      std::vector<bool> lhs_v;
      std::vector<TermProperties> lhs_prop;
      Assert(it_reqc != d_curr_eqc.end());
      for (const Node& n : it_reqc->second)
      {
        Trace("cegqi-inst-debug2") << "...look at term " << n << std::endl;
        // must be an eligible term
        if (isEligible(n))
        {
          Node ns;
          TermProperties pv_prop;
          if (!d_prog_var[n].empty())
          {
            ns = applySubstitution(pvtn, n, sf, pv_prop);
            if (!ns.isNull())
            {
              computeProgVars(ns);
            }
          }
          else
          {
            ns = n;
          }
          if (!ns.isNull())
          {
            bool hasVar = d_prog_var[ns].find(pv) != d_prog_var[ns].end();
            Trace("cegqi-inst-debug2") << "... " << ns << " has var " << pv
                                      << " : " << hasVar << std::endl;
            std::vector<TermProperties> term_props;
            std::vector<Node> terms;
            term_props.push_back(pv_prop);
            terms.push_back(ns);
            for (unsigned j = 0, size = lhs.size(); j < size; j++)
            {
              // if this term or the another has pv in it, try to solve for it
              if (hasVar || lhs_v[j])
              {
                Trace("cegqi-inst-debug") << "......try based on equality "
                                         << lhs[j] << " = " << ns << std::endl;
                term_props.push_back(lhs_prop[j]);
                terms.push_back(lhs[j]);
                if (vinst->processEquality(
                        this, sf, pv, term_props, terms, d_effort))
                {
                  return true;
                }
                else if (!options::cegqiMultiInst() && hasTriedInstantiation(pv))
                {
                  return false;
                }
                term_props.pop_back();
                terms.pop_back();
              }
            }
            lhs.push_back(ns);
            lhs_v.push_back(hasVar);
            lhs_prop.push_back(pv_prop);
          }
          else
          {
            Trace("cegqi-inst-debug2")
                << "... term " << n << " is ineligible after substitution."
                << std::endl;
          }
        }
        else
        {
          Trace("cegqi-inst-debug2")
              << "... term " << n << " is ineligible." << std::endl;
        }
      }
    }
  }
  //[3] directly look at assertions
  if (!vinst->hasProcessAssertion(this, sf, pv, d_effort))
  {
    return false;
  }
  Trace("cegqi-inst-debug") << "[3] try based on assertions." << std::endl;
  d_curr_iphase[pv] = CEG_INST_PHASE_ASSERTION;
  std::unordered_set<Node, NodeHashFunction> lits;
  for (unsigned r = 0; r < 2; r++)
  {
    TheoryId tid = r == 0 ? Theory::theoryOf(pvtn) : THEORY_UF;
    Trace("cegqi-inst-debug2") << "  look at assertions of " << tid << std::endl;
    std::map<TheoryId, std::vector<Node> >::iterator ita =
        d_curr_asserts.find(tid);
    if (ita != d_curr_asserts.end())
    {
      for (const Node& lit : ita->second)
      {
        if (lits.find(lit) == lits.end())
        {
          lits.insert(lit);
          Node plit;
          if (options::cegqiRepeatLit() || !isSolvedAssertion(lit))
          {
            plit = vinst->hasProcessAssertion(this, sf, pv, lit, d_effort);
          }
          if (!plit.isNull())
          {
            Trace("cegqi-inst-debug2") << "  look at " << lit;
            if (plit != lit)
            {
              Trace("cegqi-inst-debug2") << "...processed to : " << plit;
            }
            Trace("cegqi-inst-debug2") << std::endl;
            // apply substitutions
            Node slit = applySubstitutionToLiteral(plit, sf);
            if (!slit.isNull())
            {
              // check if contains pv
              if (hasVariable(slit, pv))
              {
                Trace("cegqi-inst-debug")
                    << "...try based on literal " << slit << "," << std::endl;
                Trace("cegqi-inst-debug") << "...from " << lit << std::endl;
                if (vinst->processAssertion(this, sf, pv, slit, lit, d_effort))
                {
                  return true;
                }
                else if (!options::cegqiMultiInst() && hasTriedInstantiation(pv))
                {
                  return false;
                }
              }
            }
          }
        }
      }
    }
  }
  if (vinst->processAssertions(this, sf, pv, d_effort))
  {
    return true;
  }
  return false;
}

void CegInstantiator::pushStackVariable( Node v ) {
  d_stack_vars.push_back( v );
}

void CegInstantiator::popStackVariable() {
  Assert(!d_stack_vars.empty());
  d_stack_vars.pop_back();
}

bool CegInstantiator::constructInstantiationInc(Node pv,
                                                Node n,
                                                TermProperties& pv_prop,
                                                SolvedForm& sf,
                                                bool revertOnSuccess)
{
  Node cnode = pv_prop.getCacheNode();
  if( d_curr_subs_proc[pv][n].find( cnode )==d_curr_subs_proc[pv][n].end() ){
    d_curr_subs_proc[pv][n][cnode] = true;
    if( Trace.isOn("cegqi-inst-debug") ){
      for( unsigned j=0; j<sf.d_subs.size(); j++ ){
        Trace("cegqi-inst-debug") << " ";
      }
      Trace("cegqi-inst-debug") << sf.d_subs.size() << ": (" << d_curr_iphase[pv]
                         << ") ";
      Node mod_pv = pv_prop.getModifiedTerm( pv );
      Trace("cegqi-inst-debug") << mod_pv << " -> " << n << std::endl;
      Assert(n.getType().isSubtypeOf(pv.getType()));
    }
    //must ensure variables have been computed for n
    computeProgVars( n );
    Assert(d_inelig.find(n) == d_inelig.end());

    //substitute into previous substitutions, when applicable
    std::vector< Node > a_var;
    a_var.push_back( pv );
    std::vector< Node > a_subs;
    a_subs.push_back( n );
    std::vector< TermProperties > a_prop;
    a_prop.push_back( pv_prop );
    std::vector< Node > a_non_basic;
    if( !pv_prop.isBasic() ){
      a_non_basic.push_back( pv );
    }
    bool success = true;
    std::map< int, Node > prev_subs;
    std::map< int, TermProperties > prev_prop;
    std::map< int, Node > prev_sym_subs;
    std::vector< Node > new_non_basic;
    Trace("cegqi-inst-debug2") << "Applying substitutions to previous substitution terms..." << std::endl;
    for( unsigned j=0; j<sf.d_subs.size(); j++ ){
      Trace("cegqi-inst-debug2") << "  Apply for " << sf.d_subs[j]  << std::endl;
      Assert(d_prog_var.find(sf.d_subs[j]) != d_prog_var.end());
      if( d_prog_var[sf.d_subs[j]].find( pv )!=d_prog_var[sf.d_subs[j]].end() ){
        prev_subs[j] = sf.d_subs[j];
        TNode tv = pv;
        TNode ts = n;
        TermProperties a_pv_prop;
        Node new_subs = applySubstitution( sf.d_vars[j].getType(), sf.d_subs[j], a_var, a_subs, a_prop, a_non_basic, a_pv_prop, true );
        if( !new_subs.isNull() ){
          sf.d_subs[j] = new_subs;
          // the substitution apply to this term resulted in a non-basic substitution relationship
          if( !a_pv_prop.isBasic() ){
            // we are processing:
            //    sf.d_props[j].getModifiedTerm( sf.d_vars[j] ) = sf.d_subs[j] { pv_prop.getModifiedTerm( pv ) -> n } 
          
            // based on the above substitution, we have:
            //   x = sf.d_subs[j] { pv_prop.getModifiedTerm( pv ) -> n } 
            // is equivalent to
            //   a_pv_prop.getModifiedTerm( x ) = new_subs
            
            // thus we must compose substitutions:
            //   a_pv_prop.getModifiedTerm( sf.d_props[j].getModifiedTerm( sf.d_vars[j] ) ) = new_subs
            
            prev_prop[j] = sf.d_props[j];
            bool prev_basic = sf.d_props[j].isBasic();
            
            // now compose the property
            sf.d_props[j].composeProperty( a_pv_prop );
            
            // if previously was basic, becomes non-basic
            if( prev_basic && !sf.d_props[j].isBasic() ){
              Assert(std::find(sf.d_non_basic.begin(),
                               sf.d_non_basic.end(),
                               sf.d_vars[j])
                     == sf.d_non_basic.end());
              new_non_basic.push_back( sf.d_vars[j] );
              sf.d_non_basic.push_back( sf.d_vars[j] );
            }
          }
          if( sf.d_subs[j]!=prev_subs[j] ){
            computeProgVars( sf.d_subs[j] );
            Assert(d_inelig.find(sf.d_subs[j]) == d_inelig.end());
          }
          Trace("cegqi-inst-debug2") << "Subs " << j << " " << sf.d_subs[j] << std::endl;
        }else{
          Trace("cegqi-inst-debug2") << "...failed to apply substitution to " << sf.d_subs[j] << std::endl;
          success = false;
          break;
        }
      }else{
        Trace("cegqi-inst-debug2") << "Skip " << j << " " << sf.d_subs[j] << std::endl;
      }
    }
    if( success ){
      Trace("cegqi-inst-debug2") << "Adding to vectors..." << std::endl;
      sf.push_back( pv, n, pv_prop );
      Trace("cegqi-inst-debug2") << "Recurse..." << std::endl;
      unsigned i = d_curr_index[pv];
      success = constructInstantiation(sf, d_stack_vars.empty() ? i + 1 : i);
      if (!success || revertOnSuccess)
      {
        Trace("cegqi-inst-debug2") << "Removing from vectors..." << std::endl;
        sf.pop_back( pv, n, pv_prop );
      }
    }
    if (success && !revertOnSuccess)
    {
      return true;
    }else{
      Trace("cegqi-inst-debug2") << "Revert substitutions..." << std::endl;
      //revert substitution information
      for (std::map<int, Node>::iterator it = prev_subs.begin();
           it != prev_subs.end();
           ++it)
      {
        sf.d_subs[it->first] = it->second;
      }
      for (std::map<int, TermProperties>::iterator it = prev_prop.begin();
           it != prev_prop.end();
           ++it)
      {
        sf.d_props[it->first] = it->second;
      }
      for( unsigned i=0; i<new_non_basic.size(); i++ ){
        sf.d_non_basic.pop_back();
      }
      return success;
    }
  }else{
    //already tried this substitution
    return false;
  }
}

bool CegInstantiator::doAddInstantiation( std::vector< Node >& vars, std::vector< Node >& subs, std::vector< Node >& lemmas ) {
  if (vars.size() > d_input_vars.size() || !d_var_order_index.empty())
  {
    Trace("cegqi-inst-debug") << "Reconstructing instantiations...." << std::endl;
    std::map< Node, Node > subs_map;
    for( unsigned i=0; i<subs.size(); i++ ){
      subs_map[vars[i]] = subs[i];
    }
    subs.clear();
    for (unsigned i = 0, size = d_input_vars.size(); i < size; ++i)
    {
      std::map<Node, Node>::iterator it = subs_map.find(d_input_vars[i]);
      Assert(it != subs_map.end());
      Node n = it->second;
      Trace("cegqi-inst-debug") << "  " << d_input_vars[i] << " -> " << n
                               << std::endl;
      Assert(n.getType().isSubtypeOf(d_input_vars[i].getType()));
      subs.push_back( n );
    }
  }
  if (Trace.isOn("cegqi-inst"))
  {
    Trace("cegqi-inst") << "Ceg Instantiator produced : " << std::endl;
    for (unsigned i = 0, size = d_input_vars.size(); i < size; ++i)
    {
      Node v = d_input_vars[i];
      Trace("cegqi-inst") << i << " (" << d_curr_iphase[v] << ") : " 
                         << v << " -> " << subs[i] << std::endl;
      Assert(subs[i].getType().isSubtypeOf(v.getType()));
    }
  }
  Trace("cegqi-inst-debug") << "Do the instantiation...." << std::endl;
  bool ret = d_parent->doAddInstantiation(subs);
  for (const Node& l : lemmas)
  {
    d_parent->addPendingLemma(l);
  }
  return ret;
}

bool CegInstantiator::isEligibleForInstantiation(Node n) const
{
  if (n.getKind() != INST_CONSTANT && n.getKind() != SKOLEM)
  {
    return true;
  }
  if (n.getAttribute(VirtualTermSkolemAttribute()))
  {
    // virtual terms are allowed
    return true;
  }
  // only legal if current quantified formula contains n
  return expr::hasSubterm(d_quant, n);
}

bool CegInstantiator::canApplyBasicSubstitution( Node n, std::vector< Node >& non_basic ){
  Assert(d_prog_var.find(n) != d_prog_var.end());
  if( !non_basic.empty() ){
    for (std::unordered_set<Node, NodeHashFunction>::iterator it =
             d_prog_var[n].begin();
         it != d_prog_var[n].end();
         ++it)
    {
      if (std::find(non_basic.begin(), non_basic.end(), *it) != non_basic.end())
      {
        return false;
      }
    }
  }
  return true;
}

Node CegInstantiator::applySubstitution( TypeNode tn, Node n, std::vector< Node >& vars, std::vector< Node >& subs, std::vector< TermProperties >& prop, 
                                         std::vector< Node >& non_basic, TermProperties& pv_prop, bool try_coeff ) {
  n = Rewriter::rewrite(n);
  computeProgVars( n );
  bool is_basic = canApplyBasicSubstitution( n, non_basic );
  if( Trace.isOn("sygus-si-apply-subs-debug") ){
    Trace("sygus-si-apply-subs-debug") << "is_basic = " << is_basic << "  " << tn << std::endl;
    for( unsigned i=0; i<subs.size(); i++ ){
      Trace("sygus-si-apply-subs-debug") << "  " << vars[i] << " -> " << subs[i] << "   types : " << vars[i].getType() << " -> " << subs[i].getType() << std::endl;
      Assert(subs[i].getType().isSubtypeOf(vars[i].getType()));
    }
  }
  Node nret;
  if( is_basic ){
    nret = n.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
  }else{
    if( !tn.isInteger() ){
      //can do basic substitution instead with divisions
      std::vector< Node > nvars;
      std::vector< Node > nsubs;
      for( unsigned i=0; i<vars.size(); i++ ){
        if( !prop[i].d_coeff.isNull() ){
          Assert(vars[i].getType().isInteger());
          Assert(prop[i].d_coeff.isConst());
          Node nn = NodeManager::currentNM()->mkNode( MULT, subs[i], NodeManager::currentNM()->mkConst( Rational(1)/prop[i].d_coeff.getConst<Rational>() ) );
          nn = NodeManager::currentNM()->mkNode( kind::TO_INTEGER, nn );
          nn =  Rewriter::rewrite( nn );
          nsubs.push_back( nn );
        }else{
          nsubs.push_back( subs[i] );
        }
      }
      nret = n.substitute( vars.begin(), vars.end(), nsubs.begin(), nsubs.end() );
    }else if( try_coeff ){
      //must convert to monomial representation
      std::map< Node, Node > msum;
      if (ArithMSum::getMonomialSum(n, msum))
      {
        std::map< Node, Node > msum_coeff;
        std::map< Node, Node > msum_term;
        for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
          //check if in substitution
          std::vector< Node >::iterator its = std::find( vars.begin(), vars.end(), it->first );
          if( its!=vars.end() ){
            int index = its-vars.begin();
            if( prop[index].d_coeff.isNull() ){
              //apply substitution
              msum_term[it->first] = subs[index];
            }else{
              //apply substitution, multiply to ensure no divisibility conflict
              msum_term[it->first] = subs[index];
              //relative coefficient
              msum_coeff[it->first] = prop[index].d_coeff;
              if( pv_prop.d_coeff.isNull() ){
                pv_prop.d_coeff = prop[index].d_coeff;
              }else{
                pv_prop.d_coeff = NodeManager::currentNM()->mkNode( MULT, pv_prop.d_coeff, prop[index].d_coeff );
              }
            }
          }else{
            msum_term[it->first] = it->first;
          }
        }
        //make sum with normalized coefficient
        if( !pv_prop.d_coeff.isNull() ){
          pv_prop.d_coeff = Rewriter::rewrite( pv_prop.d_coeff );
          Trace("sygus-si-apply-subs-debug") << "Combined coeff : " << pv_prop.d_coeff << std::endl;
          std::vector< Node > children;
          for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
            Node c_coeff;
            if( !msum_coeff[it->first].isNull() ){
              c_coeff = Rewriter::rewrite( NodeManager::currentNM()->mkConst( pv_prop.d_coeff.getConst<Rational>() / msum_coeff[it->first].getConst<Rational>() ) );
            }else{
              c_coeff = pv_prop.d_coeff;
            }
            if( !it->second.isNull() ){
              c_coeff = NodeManager::currentNM()->mkNode( MULT, c_coeff, it->second );
            }
            Assert(!c_coeff.isNull());
            Node c;
            if( msum_term[it->first].isNull() ){
              c = c_coeff;
            }else{
              c = NodeManager::currentNM()->mkNode( MULT, c_coeff, msum_term[it->first] );
            }
            children.push_back( c );
            Trace("sygus-si-apply-subs-debug") << "Add child : " << c << std::endl;
          }
          Node nretc = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( PLUS, children );
          nretc = Rewriter::rewrite( nretc );
          //ensure that nret does not contain vars
          if (!expr::hasSubterm(nretc, vars))
          {
            //result is ( nret / pv_prop.d_coeff )
            nret = nretc;
          }else{
            Trace("sygus-si-apply-subs-debug") << "Failed, since result " << nretc << " contains free variable." << std::endl;
          }
        }else{
          //implies that we have a monomial that has a free variable
          Trace("sygus-si-apply-subs-debug") << "Failed to find coefficient during substitution, implies monomial with free variable." << std::endl;
        }
      }else{
        Trace("sygus-si-apply-subs-debug") << "Failed to find monomial sum " << n << std::endl;
      }
    }
  }
  if( n!=nret && !nret.isNull() ){
    nret = Rewriter::rewrite( nret );
  }
  return nret;
}

Node CegInstantiator::applySubstitutionToLiteral( Node lit, std::vector< Node >& vars, std::vector< Node >& subs, 
                                                  std::vector< TermProperties >& prop, std::vector< Node >& non_basic ) {
  computeProgVars( lit );
  bool is_basic = canApplyBasicSubstitution( lit, non_basic );
  Node lret;
  if( is_basic ){
   lret = lit.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
  }else{
    Node atom = lit.getKind()==NOT ? lit[0] : lit;
    bool pol = lit.getKind()!=NOT;
    //arithmetic inequalities and disequalities
    if( atom.getKind()==GEQ || ( atom.getKind()==EQUAL && !pol && atom[0].getType().isReal() ) ){
      Assert(atom.getKind() != GEQ || atom[1].isConst());
      Node atom_lhs;
      Node atom_rhs;
      if( atom.getKind()==GEQ ){
        atom_lhs = atom[0];
        atom_rhs = atom[1];
      }else{
        atom_lhs = NodeManager::currentNM()->mkNode( MINUS, atom[0], atom[1] );
        atom_lhs = Rewriter::rewrite( atom_lhs );
        atom_rhs = getQuantifiersEngine()->getTermUtil()->d_zero;
      }
      //must be an eligible term
      if( isEligible( atom_lhs ) ){
        //apply substitution to LHS of atom
        TermProperties atom_lhs_prop;
        atom_lhs = applySubstitution( NodeManager::currentNM()->realType(), atom_lhs, vars, subs, prop, non_basic, atom_lhs_prop );
        if( !atom_lhs.isNull() ){
          if( !atom_lhs_prop.d_coeff.isNull() ){
            atom_rhs = Rewriter::rewrite( NodeManager::currentNM()->mkNode( MULT, atom_lhs_prop.d_coeff, atom_rhs ) );
          }
          lret = NodeManager::currentNM()->mkNode( atom.getKind(), atom_lhs, atom_rhs );
          if( !pol ){
            lret = lret.negate();
          }
        }
      }
    }else{
      // don't know how to apply substitution to literal
    }
  }
  if( lit!=lret && !lret.isNull() ){
    lret = Rewriter::rewrite( lret );
  }
  return lret;
}
  
bool CegInstantiator::check() {
  processAssertions();
  for( unsigned r=0; r<2; r++ ){
    d_effort = r == 0 ? CEG_INST_EFFORT_STANDARD : CEG_INST_EFFORT_FULL;
    SolvedForm sf;
    d_stack_vars.clear();
    d_bound_var_index.clear();
    d_solved_asserts.clear();
    //try to add an instantiation
    if (constructInstantiation(sf, 0))
    {
      return true;
    }
  }
  Trace("cegqi-engine") << "  WARNING : unable to find CEGQI single invocation instantiation." << std::endl;
  return false;
}

void CegInstantiator::processAssertions() {
  Trace("cegqi-proc") << "--- Process assertions, #var = " << d_vars.size()
                     << std::endl;
  d_curr_asserts.clear();
  d_curr_eqc.clear();
  d_curr_type_eqc.clear();

  // must use master equality engine to avoid value instantiations
  eq::EqualityEngine* ee = d_qe->getState().getEqualityEngine();

  //for each variable
  for( unsigned i=0; i<d_vars.size(); i++ ){
    Node pv = d_vars[i];
    TypeNode pvtn = pv.getType();
    Trace("cegqi-proc-debug") << "Collect theory ids from type " << pvtn << " of " << pv << std::endl;
    //collect information about eqc
    if( ee->hasTerm( pv ) ){
      Node pvr = ee->getRepresentative( pv );
      if( d_curr_eqc.find( pvr )==d_curr_eqc.end() ){
        Trace("cegqi-proc") << "Collect equivalence class " << pvr << std::endl;
        eq::EqClassIterator eqc_i = eq::EqClassIterator( pvr, ee );
        while( !eqc_i.isFinished() ){
          d_curr_eqc[pvr].push_back( *eqc_i );
          ++eqc_i;
        }
      }
    }
  }
  //collect assertions for relevant theories
  for( unsigned i=0; i<d_tids.size(); i++ ){
    TheoryId tid = d_tids[i];
    Theory* theory = d_qe->getTheoryEngine()->theoryOf( tid );
    if( theory && d_qe->getTheoryEngine()->isTheoryEnabled(tid) ){
      Trace("cegqi-proc") << "Collect assertions from theory " << tid << std::endl;
      d_curr_asserts[tid].clear();
      //collect all assertions from theory
      for( context::CDList<Assertion>::const_iterator it = theory->facts_begin(); it != theory->facts_end(); ++ it) {
        Node lit = (*it).d_assertion;
        Node atom = lit.getKind()==NOT ? lit[0] : lit;
        if( d_is_nested_quant || std::find( d_ce_atoms.begin(), d_ce_atoms.end(), atom )!=d_ce_atoms.end() ){
          d_curr_asserts[tid].push_back( lit );
          Trace("cegqi-proc-debug") << "...add : " << lit << std::endl;
        }else{
          Trace("cegqi-proc") << "...do not consider literal " << tid << " : " << lit << " since it is not part of CE body." << std::endl;
        }
      }
    }
  }
  //collect equivalence classes that correspond to relevant theories
  Trace("cegqi-proc-debug") << "...collect typed equivalence classes" << std::endl;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  while( !eqcs_i.isFinished() ){
    Node r = *eqcs_i;
    TypeNode rtn = r.getType();
    TheoryId tid = Theory::theoryOf( rtn );
    //if we care about the theory of this eqc
    if( std::find( d_tids.begin(), d_tids.end(), tid )!=d_tids.end() ){
      if( rtn.isInteger() || rtn.isReal() ){
        rtn = rtn.getBaseType();
      }
      Trace("cegqi-proc-debug") << "...type eqc: " << r << std::endl;
      d_curr_type_eqc[rtn].push_back( r );
      if( d_curr_eqc.find( r )==d_curr_eqc.end() ){
        Trace("cegqi-proc") << "Collect equivalence class " << r << std::endl;
        Trace("cegqi-proc-debug") << "  ";
        eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
        while( !eqc_i.isFinished() ){
          Trace("cegqi-proc-debug") << *eqc_i << " ";
          d_curr_eqc[r].push_back( *eqc_i );
          ++eqc_i;
        }
        Trace("cegqi-proc-debug") << std::endl;
      }
    }
    ++eqcs_i;
  }

  //remove unecessary assertions
  for( std::map< TheoryId, std::vector< Node > >::iterator it = d_curr_asserts.begin(); it != d_curr_asserts.end(); ++it ){
    std::vector< Node > akeep;
    for( unsigned i=0; i<it->second.size(); i++ ){
      Node n = it->second[i];
      //must be an eligible term
      if( isEligible( n ) ){
        //must contain at least one variable
        if( !d_prog_var[n].empty() ){
          Trace("cegqi-proc") << "...literal[" << it->first << "] : " << n << std::endl;
          akeep.push_back( n );
        }else{
          Trace("cegqi-proc") << "...remove literal from " << it->first << " : " << n << " since it contains no relevant variables." << std::endl;
        }
      }else{
        Trace("cegqi-proc") << "...remove literal from " << it->first << " : " << n << " since it contains ineligible terms." << std::endl;
      }
    }
    it->second.clear();
    it->second.insert( it->second.end(), akeep.begin(), akeep.end() );
  }

  //remove duplicate terms from eqc
  for( std::map< Node, std::vector< Node > >::iterator it = d_curr_eqc.begin(); it != d_curr_eqc.end(); ++it ){
    std::vector< Node > new_eqc;
    for( unsigned i=0; i<it->second.size(); i++ ){
      if( std::find( new_eqc.begin(), new_eqc.end(), it->second[i] )==new_eqc.end() ){
        new_eqc.push_back( it->second[i] );
      }
    }
    it->second.clear();
    it->second.insert( it->second.end(), new_eqc.begin(), new_eqc.end() );
  }
}

Node CegInstantiator::getModelValue( Node n ) {
  return d_qe->getModel()->getValue( n );
}

Node CegInstantiator::getBoundVariable(TypeNode tn)
{
  unsigned index = 0;
  std::unordered_map<TypeNode, unsigned, TypeNodeHashFunction>::iterator itb =
      d_bound_var_index.find(tn);
  if (itb != d_bound_var_index.end())
  {
    index = itb->second;
  }
  d_bound_var_index[tn] = index + 1;
  while (index >= d_bound_var[tn].size())
  {
    std::stringstream ss;
    ss << "x" << index;
    Node x = NodeManager::currentNM()->mkBoundVar(ss.str(), tn);
    d_bound_var[tn].push_back(x);
  }
  return d_bound_var[tn][index];
}

bool CegInstantiator::isSolvedAssertion(Node n) const
{
  return d_solved_asserts.find(n) != d_solved_asserts.end();
}

void CegInstantiator::markSolved(Node n, bool solved)
{
  if (solved)
  {
    d_solved_asserts.insert(n);
  }
  else if (isSolvedAssertion(n))
  {
    d_solved_asserts.erase(n);
  }
}

void CegInstantiator::collectCeAtoms( Node n, std::map< Node, bool >& visited ) {
  if( n.getKind()==FORALL ){
    d_is_nested_quant = true;
  }else if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( TermUtil::isBoolConnectiveTerm( n ) ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        collectCeAtoms( n[i], visited );
      }
    }else{
      if( std::find( d_ce_atoms.begin(), d_ce_atoms.end(), n )==d_ce_atoms.end() ){
        Trace("cegqi-ce-atoms") << "CE atoms : " << n << std::endl;
        d_ce_atoms.push_back( n );
      }
    }
  }
}

void CegInstantiator::registerCounterexampleLemma(Node lem,
                                                  std::vector<Node>& ceVars,
                                                  std::vector<Node>& auxLems)
{
  Trace("cegqi-reg") << "Register counterexample lemma..." << std::endl;
  d_input_vars.clear();
  d_input_vars.insert(d_input_vars.end(), ceVars.begin(), ceVars.end());

  //Assert( d_vars.empty() );
  d_vars.clear();
  registerTheoryId(THEORY_UF);
  for (const Node& cv : ceVars)
  {
    Trace("cegqi-reg") << "  register input variable : " << cv << std::endl;
    registerVariable(cv);
  }

  // preprocess with all relevant instantiator preprocessors
  Trace("cegqi-debug") << "Preprocess based on theory-specific methods..."
                      << std::endl;
  std::vector<Node> pvars;
  pvars.insert(pvars.end(), d_vars.begin(), d_vars.end());
  for (std::pair<const TheoryId, InstantiatorPreprocess*>& p : d_tipp)
  {
    p.second->registerCounterexampleLemma(lem, pvars, auxLems);
  }
  // must register variables generated by preprocessors
  Trace("cegqi-debug") << "Register variables from theory-specific methods "
                      << d_input_vars.size() << " " << pvars.size() << " ..."
                      << std::endl;
  for (unsigned i = d_input_vars.size(), size = pvars.size(); i < size; ++i)
  {
    Trace("cegqi-reg") << "  register inst preprocess variable : " << pvars[i]
                       << std::endl;
    registerVariable(pvars[i]);
  }

  // register variables that were introduced during TheoryEngine preprocessing
  std::unordered_set<Node, NodeHashFunction> ceSyms;
  expr::getSymbols(lem, ceSyms);
  std::unordered_set<Node, NodeHashFunction> qSyms;
  expr::getSymbols(d_quant, qSyms);
  // all variables that are in counterexample lemma but not in quantified
  // formula
  for (const Node& ces : ceSyms)
  {
    if (qSyms.find(ces) != qSyms.end())
    {
      // a free symbol of the quantified formula.
      continue;
    }
    if (std::find(d_vars.begin(), d_vars.end(), ces) != d_vars.end())
    {
      // already processed variable
      continue;
    }
    // must avoid selector symbols, and function skolems introduced by
    // theory preprocessing
    TypeNode ct = ces.getType();
    if (ct.isBoolean() || ct.isFunctionLike())
    {
      // Boolean variables, including the counterexample literal, don't matter
      // since they are always assigned a model value.
      continue;
    }
    Trace("cegqi-reg") << "  register theory preprocess variable : " << ces
                       << std::endl;
    // register the variable, which was introduced by TheoryEngine's preprocess
    // method, e.g. an ITE skolem.
    registerVariable(ces);
  }

  // determine variable order: must do Reals before Ints
  Trace("cegqi-debug") << "Determine variable order..." << std::endl;
  if (!d_vars.empty())
  {
    std::map<Node, unsigned> voo;
    bool doSort = false;
    std::vector<Node> vars;
    std::map<TypeNode, std::vector<Node> > tvars;
    for (unsigned i = 0, size = d_vars.size(); i < size; i++)
    {
      voo[d_vars[i]] = i;
      d_var_order_index.push_back(0);
      TypeNode tn = d_vars[i].getType();
      if (tn.isInteger())
      {
        doSort = true;
        tvars[tn].push_back(d_vars[i]);
      }
      else
      {
        vars.push_back(d_vars[i]);
      }
    }
    if (doSort)
    {
      Trace("cegqi-debug") << "Sort variables based on ordering." << std::endl;
      for (std::pair<const TypeNode, std::vector<Node> >& vs : tvars)
      {
        vars.insert(vars.end(), vs.second.begin(), vs.second.end());
      }

      Trace("cegqi-debug") << "Consider variables in this order : " << std::endl;
      for (unsigned i = 0; i < vars.size(); i++)
      {
        d_var_order_index[voo[vars[i]]] = i;
        Trace("cegqi-debug") << "  " << vars[i] << " : " << vars[i].getType()
                            << ", index was : " << voo[vars[i]] << std::endl;
        d_vars[i] = vars[i];
      }
      Trace("cegqi-debug") << std::endl;
    }
    else
    {
      d_var_order_index.clear();
    }
  }

  // collect atoms from all lemmas: we will only solve for literals coming from
  // the original body
  d_is_nested_quant = false;
  std::map< Node, bool > visited;
  collectCeAtoms(lem, visited);
  for (const Node& alem : auxLems)
  {
    collectCeAtoms(alem, visited);
  }
}

Instantiator::Instantiator(TypeNode tn) : d_type(tn)
{
  d_closed_enum_type = tn.isClosedEnumerable();
}

bool Instantiator::processEqualTerm(CegInstantiator* ci,
                                    SolvedForm& sf,
                                    Node pv,
                                    TermProperties& pv_prop,
                                    Node n,
                                    CegInstEffort effort)
{
  pv_prop.d_type = CEG_TT_EQUAL;
  return ci->constructInstantiationInc(pv, n, pv_prop, sf);
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

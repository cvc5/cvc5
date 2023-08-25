/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements conflict-based instantiation (Reynolds et al FMCAD 2014).
 */

#include "theory/quantifiers/quant_conflict_find.h"

#include "base/configuration.h"
#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "theory/quantifiers/ematching/trigger_term_info.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace std;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QuantInfo::QuantInfo(Env& env,
                     QuantifiersState& qs,
                     TermRegistry& tr,
                     QuantConflictFind* p,
                     Node q)
    : EnvObj(env),
      d_qs(qs),
      d_parent(p),
      d_instMatch(env, qs, tr, q),
      d_mg(nullptr),
      d_q(q),
      d_unassigned_nvar(0),
      d_una_index(0)
{
  Node qn = d_q[1];
  d_extra_var.clear();

  //register the variables
  for (size_t i = 0, nvars = d_q[0].getNumChildren(); i < nvars; i++)
  {
    Node v = d_q[0][i];
    d_match.push_back(TNode::null());
    d_match_term.push_back(TNode::null());
    d_var_num[v] = i;
    d_vars.push_back(v);
    d_var_types.push_back(v.getType());
  }

  registerNode( qn, true, true );

  Trace("qcf-qregister") << "- Make match gen structure..." << std::endl;
  d_mg = std::make_unique<MatchGen>(d_env, p, this, qn);

  if( d_mg->isValid() ){
    for (size_t j = q[0].getNumChildren(), nvars = d_vars.size(); j < nvars;
         j++)
    {
      if( d_vars[j].getKind()!=BOUND_VARIABLE ){
        d_var_mg[j] = nullptr;
        bool is_tsym = false;
        if( !MatchGen::isHandledUfTerm( d_vars[j] ) && d_vars[j].getKind()!=ITE ){
          is_tsym = true;
          d_tsym_vars.push_back( j );
        }
        if (!is_tsym || options().quantifiers.cbqiTConstraint)
        {
          d_var_mg[j] = std::make_unique<MatchGen>(d_env, p, this, d_vars[j], true);
        }
        if( !d_var_mg[j] || !d_var_mg[j]->isValid() ){
          Trace("qcf-invalid")
              << "QCF invalid : cannot match for " << d_vars[j] << std::endl;
          d_mg->setInvalid();
          break;
        }else{
          std::vector<size_t> bvars;
          d_var_mg[j]->determineVariableOrder(bvars);
        }
      }
    }
    if( d_mg->isValid() ){
      std::vector<size_t> bvars;
      d_mg->determineVariableOrder(bvars);
    }
  }else{
    Trace("qcf-invalid") << "QCF invalid : body of formula cannot be processed."
                         << std::endl;
  }
  Trace("qcf-qregister-summary")
      << "QCF register : " << (d_mg->isValid() ? "VALID " : "INVALID") << " : "
      << q << std::endl;

  if (d_mg->isValid() && options().quantifiers.cbqiEagerCheckRd)
  {
    //optimization : record variable argument positions for terms that must be matched
    std::vector< TNode > vars;
    //TODO: revisit this, makes QCF faster, but misses conflicts due to caring about paths that may not be relevant (starExec jobs 14136/14137)
    if (options().quantifiers.cbqiSkipRd)
    {
      for( unsigned j=q[0].getNumChildren(); j<d_vars.size(); j++ ){
        vars.push_back( d_vars[j] );
      }
    }
    else
    {
      //get all variables that are always relevant
      std::map< TNode, bool > visited;
      getPropagateVars(vars, q[1], false, visited);
    }
    for (TNode v : vars)
    {
      TNode f = p->getTermDatabase()->getMatchOperator( v );
      if( !f.isNull() ){
        Trace("qcf-opt") << "Record variable argument positions in " << v
                         << ", op=" << f << "..." << std::endl;
        for (size_t k = 0, vnchild = v.getNumChildren(); k < vnchild; k++)
        {
          Node n = v[k];
          std::map<TNode, size_t>::iterator itv = d_var_num.find(n);
          if( itv!=d_var_num.end() ){
            std::vector<size_t>& vrd = d_var_rel_dom[itv->second][f];
            Trace("qcf-opt")
                << "  arg " << k << " is var #" << itv->second << std::endl;
            if (std::find(vrd.begin(), vrd.end(), k) == vrd.end())
            {
              vrd.push_back(k);
            }
          }
        }
      }
    }
  }
}

QuantInfo::~QuantInfo() {}

Node QuantInfo::getQuantifiedFormula() const { return d_q; }

QuantifiersInferenceManager& QuantInfo::getInferenceManager()
{
  Assert(d_parent != nullptr);
  return d_parent->getInferenceManager();
}

void QuantInfo::getPropagateVars(std::vector<TNode>& vars,
                                 TNode n,
                                 bool pol,
                                 std::map<TNode, bool>& visited)
{
  std::map< TNode, bool >::iterator itv = visited.find( n );
  if( itv==visited.end() ){
    visited[n] = true;
    bool rec = true;
    bool newPol = pol;
    if( d_var_num.find( n )!=d_var_num.end() ){
      Assert(std::find(vars.begin(), vars.end(), n) == vars.end());
      vars.push_back( n );
      TNode f = d_parent->getTermDatabase()->getMatchOperator(n);
      if( !f.isNull() ){
        std::vector<Node>& rd = d_parent->d_func_rel_dom[f];
        if (std::find(rd.begin(), rd.end(), d_q) == rd.end())
        {
          rd.push_back(d_q);
        }
      } 
    }else if( MatchGen::isHandledBoolConnective( n ) ){
      Assert(n.getKind() != IMPLIES);
      QuantPhaseReq::getEntailPolarity( n, 0, true, pol, rec, newPol );
    }
    Trace("qcf-opt-debug") << "getPropagateVars " << n << ", pol = " << pol
                           << ", rec = " << rec << std::endl;
    if( rec ){
      for (const Node& nc : n)
      {
        getPropagateVars(vars, nc, pol, visited);
      }
    }
  }
}

bool QuantInfo::isBaseMatchComplete() {
  return d_vars_set.size()==(d_q[0].getNumChildren()+d_extra_var.size());
}

void QuantInfo::registerNode( Node n, bool hasPol, bool pol, bool beneathQuant ) {
  Trace("qcf-qregister-debug2") << "Register : " << n << std::endl;
  if( n.getKind()==FORALL ){
    registerNode( n[1], hasPol, pol, true );
  }else{
    if( !MatchGen::isHandledBoolConnective( n ) ){
      if (expr::hasBoundVar(n))
      {
        // literals
        if (n.getKind() == EQUAL)
        {
          for (unsigned i = 0; i < n.getNumChildren(); i++)
          {
            flatten(n[i], beneathQuant);
          }
        }
        else if (MatchGen::isHandledUfTerm(n))
        {
          flatten(n, beneathQuant);
        }
        else if (n.getKind() == ITE)
        {
          for (unsigned i = 1; i <= 2; i++)
          {
            flatten(n[i], beneathQuant);
          }
          registerNode(n[0], false, pol, beneathQuant);
        }
        else if (options().quantifiers.cbqiTConstraint)
        {
          // a theory-specific predicate
          for (unsigned i = 0; i < n.getNumChildren(); i++)
          {
            flatten(n[i], beneathQuant);
          }
        }
      }
    }else{
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        bool newHasPol;
        bool newPol;
        QuantPhaseReq::getPolarity( n, i, hasPol, pol, newHasPol, newPol );
        registerNode( n[i], newHasPol, newPol, beneathQuant );
      }
    }
  }
}

void QuantInfo::flatten( Node n, bool beneathQuant ) {
  Trace("qcf-qregister-debug2") << "Flatten : " << n << std::endl;
  if (expr::hasBoundVar(n))
  {
    if( d_var_num.find( n )==d_var_num.end() ){
      Trace("qcf-qregister-debug2") << "Add FLATTEN VAR : " << n << std::endl;
      d_var_num[n] = d_vars.size();
      d_vars.push_back( n );
      d_var_types.push_back( n.getType() );
      d_match.push_back( TNode::null() );
      d_match_term.push_back( TNode::null() );
      if( n.getKind()==ITE ){
        registerNode( n, false, false );
      }else if( n.getKind()==BOUND_VARIABLE ){
        d_extra_var.push_back( n );
      }else{
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          flatten( n[i], beneathQuant );
        }
      }
    }else{
      Trace("qcf-qregister-debug2") << "...already processed" << std::endl;
    }
  }else{
    Trace("qcf-qregister-debug2") << "...is ground." << std::endl;
  }
}

int QuantInfo::getVarNum(TNode v) const
{
  std::map<TNode, size_t>::const_iterator it = d_var_num.find(v);
  return it != d_var_num.end() ? static_cast<int>(it->second) : -1;
}

bool QuantInfo::reset_round()
{
  for (size_t i = 0, nmatch = d_match.size(); i < nmatch; i++)
  {
    d_match[i] = TNode::null();
    d_match_term[i] = TNode::null();
  }
  d_instMatch.resetAll();
  ieval::TermEvaluatorMode tev = d_parent->atConflictEffort()
                                     ? ieval::TermEvaluatorMode::CONFLICT
                                     : ieval::TermEvaluatorMode::PROP;
  d_instMatch.setEvaluatorMode(tev);
  d_vars_set.clear();
  d_curr_var_deq.clear();
  d_tconstraints.clear();

  d_mg->reset_round();
  for (const std::pair<const size_t, std::unique_ptr<MatchGen>>& vg : d_var_mg)
  {
    if (!vg.second->reset_round())
    {
      return false;
    }
  }
  //now, reset for matching
  d_mg->reset(false);
  return true;
}

size_t QuantInfo::getCurrentRepVar(size_t v)
{
  Assert(v < d_match.size());
  TNode m = d_match[v];
  if (!m.isNull())
  {
    std::map<TNode, size_t>::const_iterator it = d_var_num.find(m);
    if (it != d_var_num.end())
    {
      return getCurrentRepVar(it->second);
    }
  }
  return v;
}

TNode QuantInfo::getCurrentValue( TNode n ) {
  std::map<TNode, size_t>::const_iterator it = d_var_num.find(n);
  if (it == d_var_num.end())
  {
    return n;
  }
  Node m = d_match[it->second];
  if (m.isNull())
  {
    return n;
  }
  return getCurrentValue(m);
}

TNode QuantInfo::getCurrentExpValue( TNode n ) {
  std::map<TNode, size_t>::const_iterator it = d_var_num.find(n);
  if (it == d_var_num.end())
  {
    return n;
  }
  Node m = d_match[it->second];
  if (m.isNull())
  {
    return n;
  }
  Assert(m != n);
  Node mt = d_match_term[it->second];
  if (mt.isNull())
  {
    return getCurrentValue(m);
  }
  return mt;
}

bool QuantInfo::getCurrentCanBeEqual(size_t v, TNode n, bool chDiseq)
{
  //check disequalities
  std::map<size_t, std::map<TNode, size_t> >::iterator itd =
      d_curr_var_deq.find(v);
  if (itd == d_curr_var_deq.end())
  {
    return true;
  }
  for (std::pair<const TNode, size_t>& dd : itd->second)
  {
    Node cv = getCurrentValue(dd.first);
    Trace("qcf-ccbe") << "compare " << cv << " " << n << std::endl;
    if (cv == n)
    {
      return false;
    }
    else if (chDiseq && !isVar(n) && !isVar(cv))
    {
      // they must actually be disequal if we are looking for conflicts
      if (!d_qs.areDisequal(n, cv))
      {
        // TODO : check for entailed disequal
        return false;
      }
    }
  }

  return true;
}

int QuantInfo::addConstraint(size_t v, TNode n, bool polarity)
{
  v = getCurrentRepVar( v );
  int vn = getVarNum( n );
  if (vn != -1)
  {
    vn = static_cast<int>(getCurrentRepVar(static_cast<size_t>(vn)));
  }
  n = getCurrentValue( n );
  return addConstraint(v, n, vn, polarity, false);
}

int QuantInfo::addConstraint(
    size_t v, TNode n, int vn, bool polarity, bool doRemove)
{
  Assert(v < d_match.size());
  //for handling equalities between variables, and disequalities involving variables
  Trace("qcf-match-debug") << "- " << (doRemove ? "un" : "" ) << "constrain : " << v << " -> " << n << " (cv=" << getCurrentValue( n ) << ")";
  Trace("qcf-match-debug") << ", (vn=" << vn << "), polarity = " << polarity << std::endl;
  Assert(doRemove || n == getCurrentValue(n));
  Assert(doRemove || v == getCurrentRepVar(v));
  Assert(doRemove || (vn == -1 && getVarNum(n) == -1)
         || (vn >= 0
             && static_cast<size_t>(vn)
                    == getCurrentRepVar(static_cast<size_t>(getVarNum(n)))));
  if( polarity ){
    if (vn != static_cast<int>(v))
    {
      if( doRemove ){
        if( vn!=-1 ){
          //if set to this in the opposite direction, clean up opposite instead
          //          std::map< int, TNode >::iterator itmn = d_match.find( vn );
          if( d_match[vn]==d_vars[v] ){
            return addConstraint(vn, d_vars[v], v, true, true);
          }else{
            //unsetting variables equal
            std::map<size_t, std::map<TNode, size_t> >::iterator itd =
                d_curr_var_deq.find(vn);
            if( itd!=d_curr_var_deq.end() ){
              //remove disequalities owned by this
              std::vector< TNode > remDeq;
              for (const std::pair<const TNode, size_t>& dd : itd->second)
              {
                if (dd.second == v)
                {
                  remDeq.push_back(dd.first);
                }
              }
              for (TNode rd : remDeq)
              {
                itd->second.erase(rd);
              }
            }
          }
        }
        unsetMatch(v);
        return 1;
      }else{
        bool isGroundRep = false;
        bool isGround = false;
        if( vn!=-1 ){
          Trace("qcf-match-debug") << "  ...Variable bound to variable" << std::endl;
          if( d_match[v].isNull() ){
            //setting variables equal
            bool alreadySet = false;
            if( !d_match[vn].isNull() ){
              alreadySet = true;
              Assert(!isVar(d_match[vn]));
            }

            //copy or check disequalities
            std::map<size_t, std::map<TNode, size_t> >::iterator itd =
                d_curr_var_deq.find(v);
            if( itd!=d_curr_var_deq.end() ){
              std::map<TNode, size_t>& cvd = d_curr_var_deq[vn];
              for (const std::pair<const TNode, size_t>& dd : itd->second)
              {
                Node dv = getCurrentValue(dd.first);
                if( !alreadySet ){
                  if (cvd.find(dv) == cvd.end())
                  {
                    cvd[dv] = v;
                  }
                }
                else if (d_match[vn] == dv)
                {
                  Trace("qcf-match-debug")
                      << "  -> fail, conflicting disequality" << std::endl;
                  return -1;
                }
              }
            }
            if( alreadySet ){
              n = getCurrentValue( n );
            }
          }else{
            if( d_match[vn].isNull() ){
              Trace("qcf-match-debug") << " ...Reverse direction" << std::endl;
              //set the opposite direction
              return addConstraint(vn, d_vars[v], v, true, false);
            }else{
              Trace("qcf-match-debug") << "  -> Both variables bound, compare" << std::endl;
              //are they currently equal
              return d_match[v] == d_match[vn] ? 0 : -1;
            }
          }
        }else{
          Trace("qcf-match-debug") << "  ...Variable bound to ground" << std::endl;
          if( d_match[v].isNull() ){
            //isGroundRep = true;   ??
            isGround = true;
          }else{
            //compare ground values
            Trace("qcf-match-debug") << "  -> Ground value, compare " << d_match[v] << " "<< n << std::endl;
            return d_match[v] == n ? 0 : -1;
          }
        }
        if (setMatch(v, n, isGroundRep, isGround))
        {
          Trace("qcf-match-debug") << "  -> success" << std::endl;
          return 1;
        }
        else
        {
          Trace("qcf-match-debug") << "  -> fail, conflicting disequality" << std::endl;
          return -1;
        }
      }
    }
    else
    {
      Trace("qcf-match-debug") << "  -> redundant, variable identity" << std::endl;
      return 0;
    }
  }else{
    if (vn == static_cast<int>(v))
    {
      Trace("qcf-match-debug") << "  -> fail, variable identity" << std::endl;
      return -1;
    }
    else
    {
      if( doRemove ){
        Assert(d_curr_var_deq[v].find(n) != d_curr_var_deq[v].end());
        d_curr_var_deq[v].erase( n );
        return 1;
      }else{
        if( d_curr_var_deq[v].find( n )==d_curr_var_deq[v].end() ){
          //check if it respects equality
          if( !d_match[v].isNull() ){
            TNode nv = getCurrentValue( n );
            if (nv == d_match[v])
            {
              Trace("qcf-match-debug") << "  -> fail, conflicting disequality" << std::endl;
              return -1;
            }
          }
          d_curr_var_deq[v][n] = v;
          Trace("qcf-match-debug") << "  -> success" << std::endl;
          return 1;
        }else{
          Trace("qcf-match-debug") << "  -> redundant disequality" << std::endl;
          return 0;
        }
      }
    }
  }
}

bool QuantInfo::isConstrainedVar(size_t v)
{
  std::map<size_t, std::map<TNode, size_t> >::const_iterator it =
      d_curr_var_deq.find(v);
  if (it != d_curr_var_deq.end() && !it->second.empty())
  {
    return true;
  }
  TNode vv = getVar(v);
  if (std::find(d_match.begin(), d_match.end(), vv) != d_match.end())
  {
    return true;
  }
  for (const std::pair<const size_t, std::map<TNode, size_t> >& d :
       d_curr_var_deq)
  {
    for (const std::pair<const TNode, size_t>& dd : d.second)
    {
      if (dd.first == vv)
      {
        return true;
      }
    }
  }
  return false;
}

bool QuantInfo::setMatch(size_t v, TNode n, bool isGroundRep, bool isGround)
{
  if (!getCurrentCanBeEqual(v, n))
  {
    return false;
  }
  if (isGroundRep)
  {
    // fail if n does not exist in the relevant domain of each of the argument
    // positions
    std::map<size_t, std::map<TNode, std::vector<size_t> > >::iterator it =
        d_var_rel_dom.find(v);
    if (it != d_var_rel_dom.end())
    {
      TermDb* tdb = d_parent->getTermDatabase();
      for (std::pair<const TNode, std::vector<size_t> >& rd : it->second)
      {
        for (size_t index : rd.second)
        {
          Trace("qcf-match-debug2") << n << " in relevant domain " << rd.first
                                    << "." << index << "?" << std::endl;
          if (!tdb->inRelevantDomain(rd.first, index, n))
          {
            Trace("qcf-match-debug")
                << "  -> fail, since " << n << " is not in relevant domain of "
                << rd.first << "." << index << std::endl;
            return false;
          }
        }
      }
    }
  }
  Trace("qcf-match-debug") << "-- bind : " << v << " -> " << n << ", checked "
                           << d_curr_var_deq[v].size() << " disequalities"
                           << std::endl;
  if (isGround && d_vars[v].getKind() == BOUND_VARIABLE)
  {
    // Set the inst match object if this corresponds to an original variable
    if (v < d_q[0].getNumChildren())
    {
      // we overwrite, so we must reset/set here
      if (!d_instMatch.get(v).isNull())
      {
        d_instMatch.reset(v);
      }
      if (!d_instMatch.set(v, n))
      {
        return false;
      }
    }
    d_vars_set.insert(v);
    Trace("qcf-match-debug")
        << "---- now bound " << d_vars_set.size() << " / "
        << d_q[0].getNumChildren() << " base variables." << std::endl;
  }
  // Note that assigning to a variable that an original variable is equal to
  // should trigger the match object. For example, if we have auxiliary
  // variable k and original variable x where x <-> k currently, and we set
  // k -> t, then we should notify the match object that x -> t. However,
  // this is not done, as it would require more complex bookkeeping. Overall,
  // this means that we may fail in some rare cases to eagerly recognize when a
  // substitution is entailed.
  d_match[v] = n;
  return true;
}

void QuantInfo::unsetMatch(size_t v)
{
  Trace("qcf-match-debug") << "-- unbind : " << v << std::endl;
  if (d_vars[v].getKind() == BOUND_VARIABLE
      && d_vars_set.find(v) != d_vars_set.end())
  {
    d_vars_set.erase( v );
    // Reset the inst match object if this corresponds to an original variable
    if (v < d_q[0].getNumChildren())
    {
      if (!d_instMatch.get(v).isNull())
      {
        d_instMatch.reset(v);
      }
    }
  }
  d_match[v] = TNode::null();
}

bool QuantInfo::isMatchSpurious()
{
  for (size_t i = 0, nvars = getNumVars(); i < nvars; i++)
  {
    if( !d_match[i].isNull() ){
      if (!getCurrentCanBeEqual(i, d_match[i], d_parent->atConflictEffort()))
      {
        return true;
      }
    }
  }
  return false;
}

bool QuantInfo::isTConstraintSpurious(const std::vector<Node>& terms)
{
  if (options().quantifiers.ievalMode != options::IevalMode::OFF)
  {
    // We rely on the instantiation evaluator. When the instantiation evaluator
    // is enabled, this method (almost) always returns false. The code may
    // return true based on minor differences in the entailment tests, which
    // would allow us in very rare cases to recognize when an instantiation
    // is spurious.
    return false;
  }
  if (options().quantifiers.cbqiEagerTest)
  {
    EntailmentCheck* echeck = d_parent->getTermRegistry().getEntailmentCheck();
    //check whether the instantiation evaluates as expected
    std::map<TNode, TNode> subs;
    for (size_t i = 0, tsize = terms.size(); i < tsize; i++)
    {
      Trace("qcf-instance-check") << "  " << terms[i] << std::endl;
      subs[d_q[0][i]] = terms[i];
    }
    for (size_t i = 0, evsize = d_extra_var.size(); i < evsize; i++)
    {
      Node n = getCurrentExpValue(d_extra_var[i]);
      Trace("qcf-instance-check")
          << "  " << d_extra_var[i] << " -> " << n << std::endl;
      subs[d_extra_var[i]] = n;
    }
    if (d_parent->atConflictEffort()) {
      Trace("qcf-instance-check")
          << "Possible conflict instance for " << d_q << " : " << std::endl;
      if (!echeck->isEntailed(d_q[1], subs, false, false))
      {
        Trace("qcf-instance-check")
            << "...not entailed to be false." << std::endl;
        return true;
      }
    }else{
      // see if the body of the quantified formula evaluates to a Boolean
      // combination of known terms under the current substitution. We use
      // the helper method evaluateTerm from the entailment check utility.
      Node inst_eval = echeck->evaluateTerm(
          d_q[1], subs, false, options().quantifiers.cbqiTConstraint, true);
      if( TraceIsOn("qcf-instance-check") ){
        Trace("qcf-instance-check") << "Possible propagating instance for " << d_q << " : " << std::endl;
        Trace("qcf-instance-check") << "  " << terms << std::endl;
        Trace("qcf-instance-check")
            << "...evaluates to " << inst_eval << std::endl;
      }
      // If it is the case that instantiation can be rewritten to a Boolean
      // combination of terms that exist in the current context, then inst_eval
      // is non-null. Moreover, we insist that inst_eval is not true, or else
      // the instantiation is trivially entailed and hence is spurious.
      if (inst_eval.isNull()
          || (inst_eval.isConst() && inst_eval.getConst<bool>()))
      {
        Trace("qcf-instance-check") << "...spurious." << std::endl;
        return true;
      }else{
        if (Configuration::isDebugBuild())
        {
          if (!d_parent->isPropagatingInstance(inst_eval))
          {
            // Notice that this can happen in cases where:
            // (1) x = -1*y is rewritten to y = -1*x, and
            // (2) -1*y is a term in the master equality engine but -1*x is not.
            // In other words, we determined that x = -1*y is a relevant
            // equality to propagate since it involves two known terms, but
            // after rewriting, the equality y = -1*x involves an unknown term
            // -1*x. In this case, the equality is still relevant to propagate,
            // despite the above function not being precise enough to realize
            // it. We output a warning in debug for this. See #2993.
            Trace("qcf-instance-check")
                << "WARNING: not propagating." << std::endl;
          }
        }
        Trace("qcf-instance-check") << "...not spurious." << std::endl;
      }
    }
  }
  if( !d_tconstraints.empty() ){
    //check constraints
    QuantifiersRegistry& qr = d_parent->getQuantifiersRegistry();
    for( std::map< Node, bool >::iterator it = d_tconstraints.begin(); it != d_tconstraints.end(); ++it ){
      //apply substitution to the tconstraint
      Node cons = qr.substituteBoundVariables(it->first, d_q, terms);
      cons = it->second ? cons : cons.negate();
      if (!entailmentTest(cons, d_parent->atConflictEffort()))
      {
        return true;
      }
    }
  }
  // spurious if quantifiers engine is in conflict
  return d_parent->d_qstate.isInConflict();
}

bool QuantInfo::entailmentTest(Node lit, bool chEnt)
{
  Trace("qcf-tconstraint-debug") << "Check : " << lit << std::endl;
  Node rew = rewrite(lit);
  if (rew.isConst())
  {
    Trace("qcf-tconstraint-debug") << "...constraint " << lit << " rewrites to "
                                   << rew << "." << std::endl;
    return rew.getConst<bool>();
  }
  // if checking for conflicts, we must be sure that the (negation of)
  // constraint is (not) entailed
  if (!chEnt)
  {
    rew = rewrite(rew.negate());
  }
  // check if it is entailed
  Trace("qcf-tconstraint-debug")
      << "Check entailment of " << rew << "..." << std::endl;
  std::pair<bool, Node> et =
      d_parent->getState().getValuation().entailmentCheck(
          options::TheoryOfMode::THEORY_OF_TYPE_BASED, rew);
  ++(d_parent->d_statistics.d_entailment_checks);
  Trace("qcf-tconstraint-debug")
      << "ET result : " << et.first << " " << et.second << std::endl;
  if (!et.first)
  {
    Trace("qcf-tconstraint-debug")
        << "...cannot show entailment of " << rew << "." << std::endl;
    return !chEnt;
  }
  return chEnt;
}

bool QuantInfo::completeMatch(std::vector<size_t>& assigned, bool doContinue)
{
  //assign values for variables that were unassigned (usually not necessary, but handles corner cases)
  bool doFail = false;
  bool success = true;
  if( doContinue ){
    doFail = true;
    success = false;
  }else{
    if (isBaseMatchComplete() && options().quantifiers.cbqiEagerTest)
    {
      return true;
    }
    //solve for interpreted symbol matches
    //   this breaks the invariant that all introduced constraints are over existing terms
    for( int i=(int)(d_tsym_vars.size()-1); i>=0; i-- ){
      int index = d_tsym_vars[i];
      TNode v = getCurrentValue( d_vars[index] );
      int slv_v = -1;
      if( v==d_vars[index] ){
        slv_v = index;
      }
      Trace("qcf-tconstraint-debug")
          << "Solve " << d_vars[index] << " = " << v << " "
          << d_vars[index].getKind() << std::endl;
      if (d_vars[index].getKind() == ADD || d_vars[index].getKind() == MULT)
      {
        Kind k = d_vars[index].getKind();
        std::vector< TNode > children;
        for (const Node& vi : d_vars[index]){
          int vn = getVarNum( vi );
          if( vn!=-1 ){
            TNode vv = getCurrentValue( vi );
            if( vv==vi ){
              //we will assign this
              if( slv_v==-1 ){
                Trace("qcf-tconstraint-debug")
                    << "...will solve for var #" << vn << std::endl;
                slv_v = vn;
                if (!d_parent->atConflictEffort())
                {
                  break;
                }
              }else{
                Node z = d_parent->getZero(d_vars[index].getType(), k);
                if( !z.isNull() ){
                  size_t vni = static_cast<size_t>(vn);
                  Trace("qcf-tconstraint-debug")
                      << "...set " << d_vars[vn] << " = " << z << std::endl;
                  assigned.push_back(vni);
                  if (!setMatch(vni, z, false, true))
                  {
                    success = false;
                    break;
                  }
                }
              }
            }else{
              Trace("qcf-tconstraint-debug")
                  << "...sum value " << vv << std::endl;
              children.push_back( vv );
            }
          }else{
            Trace("qcf-tconstraint-debug") << "...sum " << vi << std::endl;
            children.push_back( vi );
          }
        }
        if( success ){
          if( slv_v!=-1 ){
            Node lhs;
            if( children.empty() ){
              lhs = d_parent->getZero(d_vars[index].getType(), k);
            }else if( children.size()==1 ){
              lhs = children[0];
            }else{
              lhs = NodeManager::currentNM()->mkNode( k, children );
            }
            Node sum;
            if( v==d_vars[index] ){
              sum = lhs;
            }else{
              if (d_parent->atConflictEffort())
              {
                Kind kn = k;
                if (d_vars[index].getKind() == ADD)
                {
                  kn = SUB;
                }
                if( kn!=k ){
                  sum = NodeManager::currentNM()->mkNode( kn, v, lhs );
                }
              }
            }
            if( !sum.isNull() ){
              assigned.push_back( slv_v );
              Trace("qcf-tconstraint-debug")
                  << "...set " << d_vars[slv_v] << " = " << sum << std::endl;
              if (!setMatch(slv_v, sum, false, true))
              {
                success = false;
              }
              d_parent->d_tempCache.push_back(sum);
            }
          }else{
            //must show that constraint is met
            Node sum = NodeManager::currentNM()->mkNode( k, children );
            Node eq = sum.eqNode( v );
            if (!entailmentTest(eq))
            {
              success = false;
            }
            d_parent->d_tempCache.push_back(sum);
          }
        }
      }

      if( !success ){
        break;
      }
    }
    if( success ){
      //check what is left to assign
      d_unassigned.clear();
      d_unassigned_tn.clear();
      std::vector<size_t> unassigned[2];
      std::vector< TypeNode > unassigned_tn[2];
      for (size_t i = 0, nvars = getNumVars(); i < nvars; i++)
      {
        if( d_match[i].isNull() ){
          int rindex = d_var_mg.find( i )==d_var_mg.end() ? 1 : 0;
          unassigned[rindex].push_back( i );
          unassigned_tn[rindex].push_back( getVar( i ).getType() );
          assigned.push_back( i );
        }
      }
      d_unassigned_nvar = unassigned[0].size();
      for( unsigned i=0; i<2; i++ ){
        d_unassigned.insert( d_unassigned.end(), unassigned[i].begin(), unassigned[i].end() );
        d_unassigned_tn.insert( d_unassigned_tn.end(), unassigned_tn[i].begin(), unassigned_tn[i].end() );
      }
      d_una_eqc_count.clear();
      d_una_index = 0;
    }
  }

  if( !d_unassigned.empty() && ( success || doContinue ) ){
    Trace("qcf-check") << "Assign to unassigned (" << d_unassigned.size()
                       << ")..." << std::endl;
    do {
      if( doFail ){
        Trace("qcf-check-unassign") << "Failure, try again..." << std::endl;
      }
      bool invalidMatch = false;
      while ((success && d_una_index < d_unassigned.size()) || invalidMatch
             || doFail)
      {
        invalidMatch = false;
        if (!doFail && d_una_index == d_una_eqc_count.size())
        {
          //check if it has now been assigned
          if( d_una_index<d_unassigned_nvar ){
            if( !isConstrainedVar( d_unassigned[d_una_index] ) ){
              d_una_eqc_count.push_back( -1 );
            }else{
              d_var_mg[d_unassigned[d_una_index]]->reset(true);
              d_una_eqc_count.push_back( 0 );
            }
          }else{
            d_una_eqc_count.push_back( 0 );
          }
        }
        else
        {
          bool failed = false;
          if( !doFail ){
            if( d_una_index<d_unassigned_nvar ){
              if( !isConstrainedVar( d_unassigned[d_una_index] ) ){
                Trace("qcf-check-unassign")
                    << "Succeeded, variable unconstrained at " << d_una_index
                    << std::endl;
                d_una_index++;
              }
              else if (d_var_mg[d_unassigned[d_una_index]]->getNextMatch())
              {
                Trace("qcf-check-unassign") << "Succeeded match with mg at "
                                            << d_una_index << std::endl;
                d_una_index++;
              }
              else
              {
                failed = true;
                Trace("qcf-check-unassign")
                    << "Failed match with mg at " << d_una_index << std::endl;
              }
            }else{
              Assert(doFail || d_una_index + 1 == d_una_eqc_count.size());
              const std::vector<TNode>& eqcs =
                  d_parent->d_eqcs[d_unassigned_tn[d_una_index]];
              if (d_una_eqc_count[d_una_index] < static_cast<int>(eqcs.size()))
              {
                int currIndex = d_una_eqc_count[d_una_index];
                d_una_eqc_count[d_una_index]++;
                Trace("qcf-check-unassign") << d_unassigned[d_una_index] << "->"
                                            << eqcs[currIndex] << std::endl;
                if (setMatch(
                        d_unassigned[d_una_index], eqcs[currIndex], true, true))
                {
                  d_match_term[d_unassigned[d_una_index]] = TNode::null();
                  Trace("qcf-check-unassign")
                      << "Succeeded match " << d_una_index << std::endl;
                  d_una_index++;
                }
                else
                {
                  Trace("qcf-check-unassign")
                      << "Failed match " << d_una_index << std::endl;
                  invalidMatch = true;
                }
              }
              else
              {
                failed = true;
                Trace("qcf-check-unassign")
                    << "No more matches " << d_una_index << std::endl;
              }
            }
          }
          if( doFail || failed ){
            do{
              if( !doFail ){
                d_una_eqc_count.pop_back();
              }else{
                doFail = false;
              }
              if (d_una_index == 0)
              {
                success = false;
                break;
              }
              d_una_index--;
            } while (d_una_eqc_count[d_una_index] == -1);
          }
        }
      }
      if( success ){
        doFail = true;
        Trace("qcf-check-unassign") << "  Try: " << std::endl;
        if (TraceIsOn("qcf-check"))
        {
          for (int ui : d_unassigned)
          {
            if (!d_match[ui].isNull())
            {
              Trace("qcf-check-unassign")
                  << "  Assigned #" << ui << " : " << d_vars[ui] << " -> "
                  << d_match[ui] << std::endl;
            }
          }
        }
      }
    } while (success && isMatchSpurious());
    Trace("qcf-check") << "done assigning." << std::endl;
  }
  if( success ){
    if (TraceIsOn("qcf-check"))
    {
      for (int ui : d_unassigned)
      {
        if (!d_match[ui].isNull())
        {
          Trace("qcf-check") << "  Assigned #" << ui << " : " << d_vars[ui]
                             << " -> " << d_match[ui] << std::endl;
        }
      }
    }
    return true;
  }
  revertMatch(assigned);
  assigned.clear();
  return false;
}

void QuantInfo::getMatch( std::vector< Node >& terms ){
  for (size_t i = 0, nvars = d_q[0].getNumChildren(); i < nvars; i++)
  {
    size_t repVar = getCurrentRepVar(i);
    Node cv;
    if( !d_match_term[repVar].isNull() ){
      cv = d_match_term[repVar];
    }else{
      cv = d_match[repVar];
    }
    Trace("qcf-check-inst") << "INST : " << i << " -> " << cv << ", from " << d_match[i] << std::endl;
    terms.push_back( cv );
  }
}

void QuantInfo::revertMatch(const std::vector<size_t>& assigned)
{
  for (size_t a : assigned)
  {
    unsetMatch(a);
  }
}

void QuantInfo::debugPrintMatch(const char* c) const
{
  for (size_t i = 0, nvars = getNumVars(); i < nvars; i++)
  {
    Trace(c) << "  " << d_vars[i] << " -> ";
    if( !d_match[i].isNull() ){
      Trace(c) << d_match[i];
    }else{
      Trace(c) << "(unassigned) ";
    }
    std::map<size_t, std::map<TNode, size_t> >::const_iterator itc =
        d_curr_var_deq.find(i);
    if (!itc->second.empty())
    {
      Trace(c) << ", DEQ{ ";
      for (const std::pair<const TNode, size_t>& d : itc->second)
      {
        Trace(c) << d.first << " ";
      }
      Trace(c) << "}";
    }
    if( !d_match_term[i].isNull() && d_match_term[i]!=d_match[i] ){
      Trace(c) << ", EXP : " << d_match_term[i];
    }
    Trace(c) <<  std::endl;
  }
  if( !d_tconstraints.empty() ){
    Trace(c) << "ADDITIONAL CONSTRAINTS : " << std::endl;
    for (const std::pair<const Node, bool>& tc : d_tconstraints)
    {
      Trace(c) << "   " << tc.first << " -> " << tc.second << std::endl;
    }
  }
}

MatchGen::MatchGen(Env& env, QuantConflictFind* p, QuantInfo* qi, Node n, bool isVar)
    : EnvObj(env), 
      d_tgt(),
      d_tgt_orig(),
      d_wasSet(),
      d_n(),
      d_type(),
      d_type_not(),
      d_parent(p),
      d_qi(qi),
      d_matched_basis(),
      d_binding()
{
  //initialize temporary
  d_child_counter = -1;
  d_use_children = true;

  Trace("qcf-qregister-debug")
      << "Make match gen for " << n << ", isVar = " << isVar << std::endl;
  std::vector< Node > qni_apps;
  d_qni_size = 0;
  if( isVar ){
    Assert(qi->d_var_num.find(n) != qi->d_var_num.end());
    // rare case where we have a free variable in an operator, we are invalid
    if (n.getKind() == ITE
        || (n.getKind() == APPLY_UF && expr::hasFreeVar(n.getOperator())))
    {
      d_type = typ_invalid;
    }else{
      d_type = isHandledUfTerm( n ) ? typ_var : typ_tsym;
      int vn = qi->getVarNum(n);
      Assert(vn >= 0);
      d_qni_var_num[0] = static_cast<size_t>(vn);
      d_qni_size++;
      d_type_not = false;
      d_n = n;
      //Node f = getMatchOperator( n );
      for( unsigned j=0; j<d_n.getNumChildren(); j++ ){
        Node nn = d_n[j];
        Trace("qcf-qregister-debug") << "  " << d_qni_size;
        if( qi->isVar( nn ) ){
          size_t v = qi->d_var_num[nn];
          Trace("qcf-qregister-debug") << " is var #" << v << std::endl;
          d_qni_var_num[d_qni_size] = v;
          //qi->addFuncParent( v, f, j );
        }else{
          Trace("qcf-qregister-debug") << " is gterm " << nn << std::endl;
          d_qni_gterm[d_qni_size] = nn;
        }
        d_qni_size++;
      }
    }
  }else{
    if (expr::hasBoundVar(n))
    {
      d_type_not = false;
      d_n = n;
      if( d_n.getKind()==NOT ){
        d_n = d_n[0];
        d_type_not = !d_type_not;
      }

      if( isHandledBoolConnective( d_n ) ){
        //non-literals
        d_type = typ_formula;
        for( unsigned i=0; i<d_n.getNumChildren(); i++ ){
          if( d_n.getKind()!=FORALL || i==1 ){
            std::unique_ptr<MatchGen> mg =
                std::make_unique<MatchGen>(d_env, p, qi, d_n[i], false);
            if (!mg->isValid())
            {
              setInvalid();
              break;
            }
            d_children.push_back(std::move(mg));
          }
        }
      }else{
        d_type = typ_invalid;
        //literals
        if( isHandledUfTerm( d_n ) ){
          Assert(qi->isVar(d_n));
          d_type = typ_pred;
        }else if( d_n.getKind()==BOUND_VARIABLE ){
          Assert(d_n.getType().isBoolean());
          d_type = typ_bool_var;
        }
        else if (d_n.getKind() == EQUAL || options().quantifiers.cbqiTConstraint)
        {
          for (unsigned i = 0; i < d_n.getNumChildren(); i++)
          {
            if (expr::hasBoundVar(d_n[i]))
            {
              if (!qi->isVar(d_n[i]))
              {
                Trace("qcf-qregister-debug")
                    << "ERROR : not var " << d_n[i] << std::endl;
              }
              Assert(qi->isVar(d_n[i]));
              if (d_n.getKind() != EQUAL && qi->isVar(d_n[i]))
              {
                d_qni_var_num[i + 1] = qi->d_var_num[d_n[i]];
              }
            }
            else
            {
              d_qni_gterm[i] = d_n[i];
            }
          }
          d_type = d_n.getKind() == EQUAL ? typ_eq : typ_tconstraint;
          Trace("qcf-tconstraint") << "T-Constraint : " << d_n << std::endl;
        }
      }
    }else{
      //we will just evaluate
      d_n = n;
      d_type = typ_ground;
    }
  }
  Trace("qcf-qregister-debug")  << "Done make match gen " << n << ", type = ";
  debugPrintType( "qcf-qregister-debug", d_type );
  Trace("qcf-qregister-debug") << std::endl;
}

void MatchGen::collectBoundVar(Node n,
                               std::vector<int>& cbvars,
                               std::map<Node, bool>& visited,
                               bool& hasNested)
{
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==FORALL ){
      hasNested = true;
    }
    int v = d_qi->getVarNum(n);
    if( v!=-1 && std::find( cbvars.begin(), cbvars.end(), v )==cbvars.end() ){
      cbvars.push_back( v );
    }
    for (const Node& nc : n)
    {
      collectBoundVar(nc, cbvars, visited, hasNested);
    }
  }
}

void MatchGen::determineVariableOrder(std::vector<size_t>& bvars)
{
  Trace("qcf-qregister-debug") << "Determine variable order " << d_n
                               << ", #bvars = " << bvars.size() << std::endl;
  bool isComm = d_type==typ_formula && ( d_n.getKind()==OR || d_n.getKind()==AND || d_n.getKind()==EQUAL );
  if( isComm ){
    std::map< int, std::vector< int > > c_to_vars;
    std::map< int, std::vector< int > > vars_to_c;
    std::map< int, int > vb_count;
    std::map< int, int > vu_count;
    std::map< int, bool > has_nested;
    std::vector< bool > assigned;
    Trace("qcf-qregister-debug") << "Calculate bound variables..." << std::endl;
    for (size_t i = 0, nchild = d_children.size(); i < nchild; i++)
    {
      std::map< Node, bool > visited;
      has_nested[i] = false;
      collectBoundVar(
          d_children[i]->getNode(), c_to_vars[i], visited, has_nested[i]);
      assigned.push_back( false );
      vb_count[i] = 0;
      vu_count[i] = 0;
      for( unsigned j=0; j<c_to_vars[i].size(); j++ ){
        int v = c_to_vars[i][j];
        vars_to_c[v].push_back( i );
        if( std::find( bvars.begin(), bvars.end(), v )==bvars.end() ){
          vu_count[i]++;
        }else{
          vb_count[i]++;
        }
      }
    }
    //children that bind no unbound variable, then the most number of bound, unbound variables go first
    Trace("qcf-qregister-vo")
        << "Variable order for " << d_n << " : " << std::endl;
    size_t nqvars = d_qi->d_vars.size();
    do {
      int min_score0 = -1;
      int min_score = -1;
      int min_score_index = -1;
      for (size_t i = 0, nchild = d_children.size(); i < nchild; i++)
      {
        if( !assigned[i] ){
          Trace("qcf-qregister-debug2")
              << "Child " << i << " has b/ub : " << vb_count[i] << "/"
              << vu_count[i] << std::endl;
          int score0 = 0;//has_nested[i] ? 0 : 1;
          int score;
          if (!options().quantifiers.cbqiVoExp)
          {
            score = vu_count[i];
          }
          else
          {
            score = vu_count[i] == 0 ? 0
                                     : (1 + nqvars * (nqvars - vb_count[i])
                                        + (nqvars - vu_count[i]));
          }
          if( min_score==-1 || score0<min_score0 || ( score0==min_score0 && score<min_score ) ){
            min_score0 = score0;
            min_score = score;
            min_score_index = i;
          }
        }
      }
      Trace("qcf-qregister-vo")
          << "  " << d_children_order.size() + 1 << ": "
          << d_children[min_score_index]->getNode() << " : ";
      Trace("qcf-qregister-vo")
          << vu_count[min_score_index] << " " << vb_count[min_score_index]
          << " " << has_nested[min_score_index] << std::endl;
      Trace("qcf-qregister-debug")
          << "...assign child " << min_score_index << std::endl;
      Trace("qcf-qregister-debug") << "...score : " << min_score << std::endl;
      Assert(min_score_index != -1);
      //add to children order
      d_children_order.push_back( min_score_index );
      assigned[min_score_index] = true;
      //determine order internal to children
      d_children[min_score_index]->determineVariableOrder(bvars);
      Trace("qcf-qregister-debug") << "...bind variables" << std::endl;
      //now, make it a bound variable
      if( vu_count[min_score_index]>0 ){
        for( unsigned i=0; i<c_to_vars[min_score_index].size(); i++ ){
          int v = c_to_vars[min_score_index][i];
          if( std::find( bvars.begin(), bvars.end(), v )==bvars.end() ){
            for( unsigned j=0; j<vars_to_c[v].size(); j++ ){
              int vc = vars_to_c[v][j];
              vu_count[vc]--;
              vb_count[vc]++;
            }
            bvars.push_back( v );
          }
        }
      }
      Trace("qcf-qregister-debug")
          << "...done assign child " << min_score_index << std::endl;
    }while( d_children_order.size()!=d_children.size() );
    Trace("qcf-qregister-debug")
        << "Done assign variable ordering for " << d_n << std::endl;
  }else{
    for (size_t i = 0, nchild = d_children.size(); i < nchild; i++)
    {
      d_children_order.push_back( i );
      d_children[i]->determineVariableOrder(bvars);
      //now add to bvars
      std::map< Node, bool > visited;
      std::vector< int > cvars;
      bool has_nested = false;
      collectBoundVar(d_children[i]->getNode(), cvars, visited, has_nested);
      for( unsigned j=0; j<cvars.size(); j++ ){
        if( std::find( bvars.begin(), bvars.end(), cvars[j] )==bvars.end() ){
          bvars.push_back( cvars[j] );
        }
      }
    }
  }
}

bool MatchGen::reset_round()
{
  d_wasSet = false;
  for (std::unique_ptr<MatchGen>& mg : d_children)
  {
    if (!mg->reset_round())
    {
      return false;
    }
  }
  if( d_type==typ_ground ){
    EntailmentCheck* echeck = d_parent->getTermRegistry().getEntailmentCheck();
    QuantifiersState& qs = d_parent->getState();
    for (unsigned i = 0; i < 2; i++)
    {
      if (echeck->isEntailed(d_n, i == 0))
      {
        d_ground_eval[0] = NodeManager::currentNM()->mkConst(i == 0);
      }
      if (qs.isInConflict())
      {
        return false;
      }
    }
  }else if( d_type==typ_eq ){
    EntailmentCheck* echeck = d_parent->getTermRegistry().getEntailmentCheck();
    QuantifiersState& qs = d_parent->getState();
    for (unsigned i = 0, size = d_n.getNumChildren(); i < size; i++)
    {
      if (!expr::hasBoundVar(d_n[i]))
      {
        TNode t = echeck->getEntailedTerm(d_n[i]);
        if (qs.isInConflict())
        {
          return false;
        }
        if (t.isNull())
        {
          d_ground_eval[i] = d_n[i];
        }
        else
        {
          d_ground_eval[i] = t;
        }
      }
    }
  }
  d_qni_bound_cons.clear();
  d_qni_bound_cons_var.clear();
  d_qni_bound.clear();
  return true;
}

void MatchGen::reset(bool tgt)
{
  d_tgt = d_type_not ? !tgt : tgt;
  Trace("qcf-match") << "     Reset for : " << d_n << ", type : ";
  debugPrintType( "qcf-match", d_type );
  Trace("qcf-match") << ", tgt = " << d_tgt << ", children = " << d_children.size() << " " << d_children_order.size() << std::endl;
  d_qn.clear();
  d_qni.clear();
  d_qni_bound.clear();
  d_child_counter = -1;
  d_use_children = true;
  d_tgt_orig = d_tgt;

  //set up processing matches
  if( d_type==typ_invalid ){
    d_use_children = false;
  }else if( d_type==typ_ground ){
    d_use_children = false;
    if (d_ground_eval[0].isConst()
        && d_ground_eval[0].getConst<bool>() == d_tgt)
    {
      d_child_counter = 0;
    }
  }
  else if (d_qi->isBaseMatchComplete() && options().quantifiers.cbqiEagerTest)
  {
    d_use_children = false;
    d_child_counter = 0;
  }
  else if (d_type == typ_bool_var)
  {
    //get current value of the variable
    TNode n = d_qi->getCurrentValue(d_n);
    int vnn = d_qi->getVarNum(n);
    if (vnn == -1)
    {
      // evaluate the value, see if it is compatible
      EntailmentCheck* echeck =
          d_parent->getTermRegistry().getEntailmentCheck();
      if (echeck->isEntailed(n, d_tgt))
      {
        d_child_counter = 0;
      }
    }
    else
    {
      size_t vn = d_qi->getCurrentRepVar(static_cast<size_t>(vnn));
      //unassigned, set match to true/false
      d_qni_bound[0] = vn;
      d_qi->setMatch(vn, NodeManager::currentNM()->mkConst(d_tgt), false, true);
      d_child_counter = 0;
    }
    if( d_child_counter==0 ){
      d_qn.push_back( NULL );
    }
  }
  else if (d_type == typ_var)
  {
    Assert(isHandledUfTerm(d_n));
    TNode f = d_parent->getTermDatabase()->getMatchOperator(d_n);
    Trace("qcf-match-debug") << "       reset: Var will match operators of " << f << std::endl;
    TNodeTrie* qni =
        d_parent->getTermDatabase()->getTermArgTrie(Node::null(), f);
    if (qni == nullptr || qni->empty())
    {
      //inform irrelevant quantifiers
      d_parent->setIrrelevantFunction(f);
    }
    else
    {
      d_qn.push_back(qni);
    }
    d_matched_basis = false;
  }
  else if (d_type == typ_tsym || d_type == typ_tconstraint)
  {
    for (std::pair<const size_t, size_t>& qvn : d_qni_var_num)
    {
      size_t repVar = d_qi->getCurrentRepVar(qvn.second);
      if (d_qi->d_match[repVar].isNull())
      {
        Trace("qcf-match-debug") << "Force matching on child #" << qvn.first
                                 << ", which is var #" << repVar << std::endl;
        d_qni_bound[qvn.first] = repVar;
      }
    }
    d_qn.push_back( NULL );
  }
  else if (d_type == typ_pred || d_type == typ_eq)
  {
    //add initial constraint
    Node nn[2];
    int vn[2];
    if( d_type==typ_pred ){
      nn[0] = d_qi->getCurrentValue(d_n);
      int vnn = d_qi->getVarNum(nn[0]);
      vn[0] =
          vnn == -1 ? vnn : d_qi->getCurrentRepVar(static_cast<size_t>(vnn));
      nn[1] = NodeManager::currentNM()->mkConst(d_tgt);
      vn[1] = -1;
      d_tgt = true;
    }else{
      for( unsigned i=0; i<2; i++ ){
        TNode nc;
        std::map<size_t, TNode>::iterator it = d_qni_gterm.find(i);
        if (it != d_qni_gterm.end())
        {
          nc = it->second;
        }else{
          nc = d_n[i];
        }
        nn[i] = d_qi->getCurrentValue(nc);
        int vnn = d_qi->getVarNum(nn[i]);
        vn[i] =
            vnn == -1 ? vnn : d_qi->getCurrentRepVar(static_cast<size_t>(vnn));
      }
    }
    bool success;
    if( vn[0]==-1 && vn[1]==-1 ){
      //Trace("qcf-explain") << "    reset : " << d_n << " check ground values " << nn[0] << " " << nn[1] << " (tgt=" << d_tgt << ")" << std::endl;
      Trace("qcf-match-debug") << "       reset: check ground values " << nn[0] << " " << nn[1] << " (" << d_tgt << ")" << std::endl;
      //just compare values
      if( d_tgt ){
        success = nn[0] == nn[1];
      }else{
        if (d_parent->atConflictEffort())
        {
          success = d_parent->areDisequal(nn[0], nn[1]);
        }
        else
        {
          success = (nn[0] != nn[1]);
        }
      }
    }else{
      //otherwise, add a constraint to a variable  TODO: this may be over-eager at effort > conflict, since equality may be a propagation
      if( vn[1]!=-1 && vn[0]==-1 ){
        //swap
        Node t = nn[1];
        nn[1] = nn[0];
        nn[0] = t;
        vn[0] = vn[1];
        vn[1] = -1;
      }
      Trace("qcf-match-debug") << "       reset: add constraint " << vn[0] << " -> " << nn[1] << " (vn=" << vn[1] << ")" << std::endl;
      //add some constraint
      int addc = d_qi->addConstraint(vn[0], nn[1], vn[1], d_tgt, false);
      success = addc!=-1;
      //if successful and non-redundant, store that we need to cleanup this
      if( addc==1 ){
        for (size_t i = 0; i < 2; i++)
        {
          if( vn[i]!=-1 && std::find( d_qni_bound_except.begin(), d_qni_bound_except.end(), i )==d_qni_bound_except.end() ){
            d_qni_bound[vn[i]] = vn[i];
          }
        }
        d_qni_bound_cons[vn[0]] = nn[1];
        d_qni_bound_cons_var[vn[0]] = vn[1];
      }
    }
    //if successful, we will bind values to variables
    if( success ){
      d_qn.push_back( NULL );
    }
  }
  else
  {
    if( d_children.empty() ){
      //add dummy
      d_qn.push_back( NULL );
    }else{
      if( d_tgt && d_n.getKind()==FORALL ){
        //fail
      }
      else if (d_n.getKind() == FORALL && d_parent->atConflictEffort())
      {
        //fail
      }
      else
      {
        //reset the first child to d_tgt
        d_child_counter = 0;
        getChild(d_child_counter)->reset(d_tgt);
      }
    }
  }
  d_binding = false;
  d_wasSet = true;
  Trace("qcf-match") << "     reset: Finished reset for " << d_n << ", success = " << ( !d_qn.empty() || d_child_counter!=-1 ) << std::endl;
}

bool MatchGen::getNextMatch()
{
  Trace("qcf-match") << "     Get next match for : " << d_n << ", type = ";
  debugPrintType( "qcf-match", d_type );
  Trace("qcf-match") << ", children = " << d_children.size() << ", binding = " << d_binding << std::endl;
  if( !d_use_children ){
    if( d_child_counter==0 ){
      d_child_counter = -1;
      return true;
    }else{
      d_wasSet = false;
      return false;
    }
  }else if( d_type==typ_var || d_type==typ_eq || d_type==typ_pred || d_type==typ_bool_var || d_type==typ_tconstraint || d_type==typ_tsym ){
    bool success = false;
    bool terminate = false;
    do {
      bool doReset = false;
      bool doFail = false;
      if( !d_binding ){
        if (doMatching())
        {
          Trace("qcf-match-debug") << "     - Matching succeeded" << std::endl;
          d_binding = true;
          d_binding_it = d_qni_bound.begin();
          doReset = true;
          //for tconstraint, add constraint
          if( d_type==typ_tconstraint ){
            std::map<Node, bool>::iterator it = d_qi->d_tconstraints.find(d_n);
            if (it == d_qi->d_tconstraints.end())
            {
              d_qi->d_tconstraints[d_n] = d_tgt;
              //store that we added this constraint
              d_qni_bound_cons[0] = d_n;
            }
            else if (d_tgt != it->second)
            {
              success = false;
              terminate = true;
            }
          }
        }
        else
        {
          Trace("qcf-match-debug") << "     - Matching failed" << std::endl;
          success = false;
          terminate = true;
        }
      }else{
        doFail = true;
      }
      if( d_binding ){
        //also need to create match for each variable we bound
        success = true;
        Trace("qcf-match-debug") << "     Produce matches for bound variables by " << d_n << ", type = ";
        debugPrintType( "qcf-match-debug", d_type );
        Trace("qcf-match-debug") << "..." << std::endl;

        while( ( success && d_binding_it!=d_qni_bound.end() ) || doFail ){
          QuantInfo::VarMgMap::const_iterator itm;
          if( !doFail ){
            Trace("qcf-match-debug") << "       check variable " << d_binding_it->second << std::endl;
            itm = d_qi->var_mg_find(d_binding_it->second);
          }
          if (doFail || (d_binding_it->first != 0 && itm != d_qi->var_mg_end()))
          {
            Trace("qcf-match-debug") << "       we had bound variable " << d_binding_it->second << ", reset = " << doReset << std::endl;
            if( doReset ){
              itm->second->reset(true);
            }
            if (doFail || !itm->second->getNextMatch())
            {
              do {
                if( d_binding_it==d_qni_bound.begin() ){
                  Trace("qcf-match-debug") << "       failed." << std::endl;
                  success = false;
                }else{
                  --d_binding_it;
                  Trace("qcf-match-debug") << "       decrement..." << std::endl;
                }
              } while (success
                       && (d_binding_it->first == 0
                           || (!d_qi->containsVarMg(d_binding_it->second))));
              doReset = false;
              doFail = false;
            }
            else
            {
              Trace("qcf-match-debug") << "       increment..." << std::endl;
              ++d_binding_it;
              doReset = true;
            }
          }
          else
          {
            Trace("qcf-match-debug") << "       skip..." << d_binding_it->second << std::endl;
            ++d_binding_it;
            doReset = true;
          }
        }
        if( !success ){
          d_binding = false;
        }else{
          terminate = true;
          if( d_binding_it==d_qni_bound.begin() ){
            d_binding = false;
          }
        }
      }
    }while( !terminate );
    //if not successful, clean up the variables you bound
    if( !success ){
      if( d_type==typ_eq || d_type==typ_pred ){
        //clean up the constraints you added
        std::map<size_t, size_t>::iterator itb;
        for (const std::pair<const size_t, TNode>& qb : d_qni_bound_cons)
        {
          if (!qb.second.isNull())
          {
            Trace("qcf-match")
                << "       Clean up bound var " << qb.first
                << (d_tgt ? "!" : "") << " = " << qb.second << std::endl;
            itb = d_qni_bound_cons_var.find(qb.first);
            int vn = itb!=d_qni_bound_cons_var.end() ? itb->second : -1;
            d_qi->addConstraint(qb.first, qb.second, vn, d_tgt, true);
          }
        }
        d_qni_bound_cons.clear();
        d_qni_bound_cons_var.clear();
        d_qni_bound.clear();
      }else{
        //clean up the matches you set
        for (const std::pair<const size_t, size_t>& qb : d_qni_bound)
        {
          Trace("qcf-match")
              << "       Clean up bound var " << qb.second << std::endl;
          Assert(qb.second < d_qi->getNumVars());
          d_qi->unsetMatch(qb.second);
          d_qi->d_match_term[qb.second] = TNode::null();
        }
        d_qni_bound.clear();
      }
      if( d_type==typ_tconstraint ){
        //remove constraint if applicable
        if( d_qni_bound_cons.find( 0 )!=d_qni_bound_cons.end() ){
          d_qi->d_tconstraints.erase(d_n);
          d_qni_bound_cons.clear();
        }
      }
    }
    Trace("qcf-match") << "    ...finished matching for " << d_n << ", success = " << success << std::endl;
    d_wasSet = success;
    return success;
  }
  else if (d_type == typ_formula)
  {
    bool success = false;
    if( d_child_counter<0 ){
      if( d_child_counter<-1 ){
        success = true;
        d_child_counter = -1;
      }
    }else{
      while( !success && d_child_counter>=0 ){
        //transition system based on d_child_counter
        if( d_n.getKind()==OR || d_n.getKind()==AND ){
          if( (d_n.getKind()==AND)==d_tgt ){
            //all children must match simultaneously
            if (getChild(d_child_counter)->getNextMatch())
            {
              if( d_child_counter<(int)(getNumChildren()-1) ){
                d_child_counter++;
                Trace("qcf-match-debug") << "       Reset child " << d_child_counter << " of " << d_n << std::endl;
                getChild(d_child_counter)->reset(d_tgt);
              }else{
                success = true;
              }
            }
            else
            {
              d_child_counter--;
            }
          }else{
            //one child must match
            if (!getChild(d_child_counter)->getNextMatch())
            {
              if( d_child_counter<(int)(getNumChildren()-1) ){
                d_child_counter++;
                Trace("qcf-match-debug") << "       Reset child " << d_child_counter << " of " << d_n << ", one match" << std::endl;
                getChild(d_child_counter)->reset(d_tgt);
              }else{
                d_child_counter = -1;
              }
            }
            else
            {
              success = true;
            }
          }
        }else if( d_n.getKind()==EQUAL ){
          //construct match based on both children
          if( d_child_counter%2==0 ){
            if (getChild(0)->getNextMatch())
            {
              d_child_counter++;
              getChild(1)->reset(d_child_counter == 1);
            }
            else
            {
              if( d_child_counter==0 ){
                d_child_counter = 2;
                getChild(0)->reset(!d_tgt);
              }else{
                d_child_counter = -1;
              }
            }
          }
          if( d_child_counter>=0 && d_child_counter%2==1 ){
            if (getChild(1)->getNextMatch())
            {
              success = true;
            }
            else
            {
              d_child_counter--;
            }
          }
        }else if( d_n.getKind()==ITE ){
          if( d_child_counter%2==0 ){
            int index1 = d_child_counter==4 ? 1 : 0;
            if (getChild(index1)->getNextMatch())
            {
              d_child_counter++;
              getChild(d_child_counter == 5
                           ? 2
                           : (d_tgt == (d_child_counter == 1) ? 1 : 2))
                  ->reset(d_tgt);
            }
            else
            {
              if (d_child_counter == 4)
              {
                d_child_counter = -1;
              }else{
                d_child_counter +=2;
                getChild(d_child_counter == 2 ? 0 : 1)
                    ->reset(d_child_counter == 2 ? !d_tgt : d_tgt);
              }
            }
          }
          if( d_child_counter>=0 && d_child_counter%2==1 ){
            int index2 = d_child_counter==5 ? 2 : (d_tgt==(d_child_counter==1) ? 1 : 2);
            if (getChild(index2)->getNextMatch())
            {
              success = true;
            }
            else
            {
              d_child_counter--;
            }
          }
        }else if( d_n.getKind()==FORALL ){
          if (getChild(d_child_counter)->getNextMatch())
          {
            success = true;
          }
          else
          {
            d_child_counter = -1;
          }
        }
      }
      d_wasSet = success;
      Trace("qcf-match") << "    ...finished construct match for " << d_n << ", success = " << success << std::endl;
      return success;
    }
  }
  Trace("qcf-match") << "    ...already finished for " << d_n << std::endl;
  return false;
}

bool MatchGen::doMatching()
{
  if (d_qn.empty())
  {
    return false;
  }
  if (d_qn[0] == NULL)
  {
    d_qn.clear();
    return true;
  }
  Assert(d_type == typ_var);
  Assert(d_qni_size > 0);
  bool invalidMatch;
  do
  {
    invalidMatch = false;
    Trace("qcf-match-debug") << "       Do matching " << d_n << " "
                             << d_qn.size() << " " << d_qni.size() << std::endl;
    if (d_qn.size() == d_qni.size() + 1)
    {
      size_t index = d_qni.size();
      // initialize
      TNode val;
      std::map<size_t, size_t>::iterator itv = d_qni_var_num.find(index);
      if (itv != d_qni_var_num.end())
      {
        // get the representative variable this variable is equal to
        size_t repVar = d_qi->getCurrentRepVar(itv->second);
        Trace("qcf-match-debug")
            << "       Match " << index << " is a variable " << itv->second
            << ", which is repVar " << repVar << std::endl;
        // get the value the rep variable
        if (!d_qi->d_match[repVar].isNull())
        {
          val = d_qi->d_match[repVar];
          Trace("qcf-match-debug")
              << "       Variable is already bound to " << val << std::endl;
        }
        else
        {
          // binding a variable
          d_qni_bound[index] = repVar;
          std::map<TNode, TNodeTrie>::iterator it = d_qn[index]->d_data.begin();
          if (it != d_qn[index]->d_data.end())
          {
            d_qni.push_back(it);
            // set the match
            if (it->first.getType() == d_qi->d_var_types[repVar]
                && d_qi->setMatch(d_qni_bound[index], it->first, true, true))
            {
              Trace("qcf-match-debug")
                  << "       Binding variable" << std::endl;
              if( d_qn.size()<d_qni_size ){
                d_qn.push_back( &it->second );
              }
            }
            else
            {
              Trace("qcf-match")
                  << "       Binding variable, currently fail." << std::endl;
              invalidMatch = true;
            }
          }
          else
          {
            Trace("qcf-match-debug")
                << "       Binding variable, fail, no more variables to bind"
                << std::endl;
            d_qn.pop_back();
          }
        }
      }
      else
      {
        Trace("qcf-match-debug")
            << "       Match " << index << " is ground term" << std::endl;
        Assert(d_qni_gterm.find(index) != d_qni_gterm.end());
        val = d_qni_gterm[index];
        Assert(!val.isNull());
      }
      if (!val.isNull())
      {
        Node valr = d_parent->getRepresentative(val);
        // constrained by val
        std::map<TNode, TNodeTrie>::iterator it =
            d_qn[index]->d_data.find(valr);
        if (it != d_qn[index]->d_data.end())
        {
          Trace("qcf-match-debug") << "       Match" << std::endl;
          d_qni.push_back(it);
          if (d_qn.size() < d_qni_size)
          {
            d_qn.push_back(&it->second);
          }
        }
        else
        {
          Trace("qcf-match-debug") << "       Failed to match" << std::endl;
          d_qn.pop_back();
        }
      }
    }
    else
    {
      Assert(d_qn.size() == d_qni.size());
      size_t index = d_qni.size() - 1;
      // increment if binding this variable
      bool success = false;
      std::map<size_t, size_t>::iterator itb = d_qni_bound.find(index);
      if (itb != d_qni_bound.end())
      {
        d_qni[index]++;
        if (d_qni[index] != d_qn[index]->d_data.end())
        {
          success = true;
          if (d_qi->setMatch(itb->second, d_qni[index]->first, true, true))
          {
            Trace("qcf-match-debug")
                << "       Bind next variable" << std::endl;
            if (d_qn.size() < d_qni_size)
            {
              d_qn.push_back(&d_qni[index]->second);
            }
          }
          else
          {
            Trace("qcf-match-debug")
                << "       Bind next variable, currently fail" << std::endl;
            invalidMatch = true;
          }
        }
        else
        {
          d_qi->unsetMatch(itb->second);
          d_qi->d_match_term[itb->second] = TNode::null();
          Trace("qcf-match-debug")
              << "       Bind next variable, no more variables to bind"
              << std::endl;
        }
      }
      else
      {
        // TODO : if it equal to something else, also try that
      }
      // if not incrementing, move to next
      if (!success)
      {
        d_qn.pop_back();
        d_qni.pop_back();
      }
    }
  } while ((!d_qn.empty() && d_qni.size() != d_qni_size) || invalidMatch);
  if (d_qni.size() == d_qni_size)
  {
    Assert(!d_qni[d_qni.size() - 1]->second.d_data.empty());
    TNode t = d_qni[d_qni.size() - 1]->second.d_data.begin()->first;
    Trace("qcf-match-debug")
        << "       " << d_n << " matched " << t << std::endl;
    d_qi->d_match_term[d_qni_var_num[0]] = t;
    // set the match terms
    Node q = d_qi->getQuantifiedFormula();
    for (const std::pair<const size_t, size_t>& qb : d_qni_bound)
    {
      Trace("qcf-match-debug")
          << "       position " << qb.first << " bounded " << qb.second << " / "
          << q[0].getNumChildren() << std::endl;
      if (qb.first > 0)
      {
        Assert(!d_qi->d_match[qb.second].isNull());
        Assert(d_parent->areEqual(t[qb.first - 1], d_qi->d_match[qb.second]));
        d_qi->d_match_term[qb.second] = t[qb.first - 1];
      }
    }
  }
  return !d_qn.empty();
}

void MatchGen::debugPrintType(const char* c, short typ)
{
  switch (typ)
  {
    case typ_invalid: Trace(c) << "invalid"; break;
    case typ_ground: Trace(c) << "ground"; break;
    case typ_eq: Trace(c) << "eq"; break;
    case typ_pred: Trace(c) << "pred"; break;
    case typ_formula: Trace(c) << "formula"; break;
    case typ_var: Trace(c) << "var"; break;
    case typ_bool_var: Trace(c) << "bool_var"; break;
  }
}

void MatchGen::setInvalid() {
  d_type = typ_invalid;
  d_children.clear();
}

bool MatchGen::isHandledBoolConnective( TNode n ) {
  return TermUtil::isBoolConnectiveTerm( n ) && n.getKind()!=SEP_STAR;
}

bool MatchGen::isHandledUfTerm( TNode n ) {
  return inst::TriggerTermInfo::isAtomicTriggerKind(n.getKind());
}

bool MatchGen::isHandled( TNode n ) {
  if (n.getKind() != BOUND_VARIABLE && expr::hasBoundVar(n))
  {
    if( !isHandledBoolConnective( n ) && !isHandledUfTerm( n ) && n.getKind()!=EQUAL && n.getKind()!=ITE ){
      return false;
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !isHandled( n[i] ) ){
        return false;
      }
    }
  }
  return true;
}

QuantConflictFind::QuantConflictFind(Env& env,
                                     QuantifiersState& qs,
                                     QuantifiersInferenceManager& qim,
                                     QuantifiersRegistry& qr,
                                     TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_statistics(statisticsRegistry()),
      d_conflict(context(), false),
      d_effort(EFFORT_INVALID)
{
}

//-------------------------------------------------- registration

void QuantConflictFind::registerQuantifier( Node q ) {
  if (!d_qreg.hasOwnership(q, this))
  {
    return;
  }
  d_quants.push_back(q);
  d_quant_id[q] = d_quants.size();
  if (TraceIsOn("qcf-qregister"))
  {
    Trace("qcf-qregister") << "Register ";
    debugPrintQuant("qcf-qregister", q);
    Trace("qcf-qregister") << " : " << q << std::endl;
  }
  // make QcfNode structure
  Trace("qcf-qregister")
      << "- Get relevant equality/disequality pairs, calculate flattening..."
      << std::endl;
  d_qinfo[q].reset(new QuantInfo(d_env, d_qstate, d_treg, this, q));

  // debug print
  if (TraceIsOn("qcf-qregister"))
  {
    QuantInfo* qi = d_qinfo[q].get();
    Trace("qcf-qregister") << "- Flattened structure is :" << std::endl;
    Trace("qcf-qregister") << "    ";
    debugPrintQuantBody("qcf-qregister", q, q[1]);
    Trace("qcf-qregister") << std::endl;
    if (qi->d_vars.size() > q[0].getNumChildren())
    {
      Trace("qcf-qregister") << "  with additional constraints : " << std::endl;
      for (size_t j = q[0].getNumChildren(), nvars = qi->d_vars.size();
           j < nvars;
           j++)
      {
        Trace("qcf-qregister") << "    ?x" << j << " = ";
        debugPrintQuantBody("qcf-qregister", q, qi->d_vars[j], false);
        Trace("qcf-qregister") << std::endl;
      }
    }
    Trace("qcf-qregister") << "Done registering quantifier." << std::endl;
  }
}

//-------------------------------------------------- check function

bool QuantConflictFind::needsCheck( Theory::Effort level ) {
  return !d_conflict && (level == Theory::EFFORT_FULL);
}

void QuantConflictFind::reset_round( Theory::Effort level ) {
  Trace("qcf-check") << "QuantConflictFind::reset_round" << std::endl;
  Trace("qcf-check") << "Compute relevant equivalence classes..." << std::endl;
  d_eqcs.clear();

  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(getEqualityEngine());
  TermDb* tdb = getTermDatabase();
  while (!eqcs_i.isFinished())
  {
    Node r = (*eqcs_i);
    if (tdb->hasTermCurrent(r))
    {
      TypeNode rtn = r.getType();
      if (!options().quantifiers.cegqi || !TermUtil::hasInstConstAttr(r))
      {
        d_eqcs[rtn].push_back(r);
      }
    }
    ++eqcs_i;
  }
}

void QuantConflictFind::setIrrelevantFunction( TNode f ) {
  if( d_irr_func.find( f )==d_irr_func.end() ){
    d_irr_func[f] = true;
    std::map< TNode, std::vector< Node > >::iterator it = d_func_rel_dom.find( f );
    if( it != d_func_rel_dom.end()){
      for( unsigned j=0; j<it->second.size(); j++ ){
        d_irr_quant[it->second[j]] = true;
      }
    }
  }
}

namespace {

// Returns the beginning of a range of efforts. The range can be iterated
// through as unsigned using operator++.
inline QuantConflictFind::Effort QcfEffortStart() {
  return QuantConflictFind::EFFORT_CONFLICT;
}

// Returns the beginning of a range of efforts. The value returned is included
// in the range.
inline QuantConflictFind::Effort QcfEffortEnd(options::QcfMode m) {
  return m == options::QcfMode::PROP_EQ
             ? QuantConflictFind::EFFORT_PROP_EQ
             : QuantConflictFind::EFFORT_CONFLICT;
}

}  // namespace

/** check */
void QuantConflictFind::check(Theory::Effort level, QEffort quant_e)
{
  CodeTimer codeTimer(d_qstate.getStats().d_cbqi_time);
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  Trace("qcf-check") << "QCF : check : " << level << std::endl;
  if (d_conflict)
  {
    Trace("qcf-check2") << "QCF : finished check : already in conflict."
                        << std::endl;
    if (level >= Theory::EFFORT_FULL)
    {
      Trace("qcf-warn") << "ALREADY IN CONFLICT? " << level << std::endl;
    }
    return;
  }
  unsigned addedLemmas = 0;
  ++(d_statistics.d_inst_rounds);
  double clSet = 0;
  int prevEt = 0;
  if (TraceIsOn("qcf-engine"))
  {
    prevEt = d_statistics.d_entailment_checks.get();
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("qcf-engine") << "---Conflict Find Engine Round, effort = " << level
                        << "---" << std::endl;
  }

  // reset the round-specific information
  d_irr_func.clear();
  d_irr_quant.clear();

  if (TraceIsOn("qcf-debug"))
  {
    Trace("qcf-debug") << std::endl;
    debugPrint("qcf-debug");
    Trace("qcf-debug") << std::endl;
  }
  bool isConflict = false;
  FirstOrderModel* fm = d_treg.getModel();
  size_t nquant = fm->getNumAssertedQuantifiers();
  // for each effort level (find conflict, find propagating)
  unsigned end = QcfEffortEnd(options().quantifiers.cbqiMode);
  for (unsigned e = QcfEffortStart(); e <= end; ++e)
  {
    // set the effort (data member for convienence of access)
    d_effort = static_cast<Effort>(e);
    Trace("qcf-check") << "Checking quantified formulas at effort " << e
                       << "..." << std::endl;
    // for each quantified formula
    for (size_t i = 0; i < nquant; i++)
    {
      Node q = fm->getAssertedQuantifier(i, true);
      if (d_qreg.hasOwnership(q, this)
          && d_irr_quant.find(q) == d_irr_quant.end()
          && fm->isQuantifierActive(q))
      {
        // check this quantified formula
        checkQuantifiedFormula(q, isConflict, addedLemmas);
        if (d_conflict || d_qstate.isInConflict())
        {
          break;
        }
      }
    }
    // We are done if we added a lemma, or discovered a conflict in another
    // way. An example of the latter case is when two disequal congruent terms
    // are discovered during term indexing.
    if (addedLemmas > 0 || d_qstate.isInConflict())
    {
      break;
    }
  }
  if (isConflict)
  {
    d_conflict.set(true);
  }
  if (TraceIsOn("qcf-engine"))
  {
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("qcf-engine") << "Finished conflict find engine, time = "
                        << (clSet2 - clSet);
    if (addedLemmas > 0)
    {
      Trace("qcf-engine") << ", effort = "
                          << (d_effort == EFFORT_CONFLICT
                                  ? "conflict"
                                  : (d_effort == EFFORT_PROP_EQ ? "prop_eq"
                                                                : "mc"));
      Trace("qcf-engine") << ", addedLemmas = " << addedLemmas;
    }
    Trace("qcf-engine") << std::endl;
    int currEt = d_statistics.d_entailment_checks.get();
    if (currEt != prevEt)
    {
      Trace("qcf-engine") << "  Entailment checks = " << (currEt - prevEt)
                          << std::endl;
    }
  }
  Trace("qcf-check2") << "QCF : finished check : " << level << std::endl;
}

void QuantConflictFind::checkQuantifiedFormula(Node q,
                                               bool& isConflict,
                                               unsigned& addedLemmas)
{
  Assert(d_qinfo.find(q) != d_qinfo.end());
  QuantInfo* qi = d_qinfo[q].get();
  if (!qi->matchGeneratorIsValid())
  {
    // quantified formula is not properly set up for matching
    return;
  }
  if (TraceIsOn("qcf-check"))
  {
    Trace("qcf-check") << "Check quantified formula ";
    debugPrintQuant("qcf-check", q);
    Trace("qcf-check") << " : " << q << "..." << std::endl;
  }

  Trace("qcf-check-debug") << "Reset round..." << std::endl;
  if (!qi->reset_round())
  {
    // it is typically the case that another conflict (e.g. in the term
    // database) was discovered if we fail here.
    return;
  }
  // try to make a matches making the body false or propagating
  Trace("qcf-check-debug") << "Get next match..." << std::endl;
  Instantiate* qinst = d_qim.getInstantiate();
  while (qi->getNextMatch())
  {
    if (d_qstate.isInConflict())
    {
      Trace("qcf-check") << "   ... Quantifiers engine discovered conflict, ";
      Trace("qcf-check") << "probably related to disequal congruent terms in "
                            "master equality engine"
                         << std::endl;
      return;
    }
    if (TraceIsOn("qcf-inst"))
    {
      Trace("qcf-inst") << "*** Produced match at effort " << d_effort << " : "
                        << std::endl;
      qi->debugPrintMatch("qcf-inst");
      Trace("qcf-inst") << std::endl;
    }
    // check whether internal match constraints are satisfied
    if (qi->isMatchSpurious())
    {
      Trace("qcf-inst") << "   ... Spurious (match is inconsistent)"
                        << std::endl;
      continue;
    }
    // check whether match can be completed
    std::vector<size_t> assigned;
    if (!qi->completeMatch(assigned))
    {
      Trace("qcf-inst") << "   ... Spurious (cannot assign unassigned vars)"
                        << std::endl;
      continue;
    }
    // check whether the match is spurious according to (T-)entailment checks
    std::vector<Node> terms;
    qi->getMatch(terms);
    bool tcs = qi->isTConstraintSpurious(terms);
    if (tcs)
    {
      Trace("qcf-inst") << "   ... Spurious (match is T-inconsistent)"
                        << std::endl;
    }
    else
    {
      // otherwise, we have a conflict/propagating instance
      // for debugging
      if (TraceIsOn("qcf-check-inst"))
      {
        Node inst = qinst->getInstantiation(q, terms);
        Trace("qcf-check-inst")
            << "Check instantiation " << inst << "..." << std::endl;
        Assert(!d_treg.getEntailmentCheck()->isEntailed(inst, true));
        Assert(d_treg.getEntailmentCheck()->isEntailed(inst, false)
               || d_effort > EFFORT_CONFLICT);
      }
      // Process the lemma: either add an instantiation or specific lemmas
      // constructed during the isTConstraintSpurious call, or both.
      InferenceId id = (d_effort == EFFORT_CONFLICT
                            ? InferenceId::QUANTIFIERS_INST_CBQI_CONFLICT
                            : InferenceId::QUANTIFIERS_INST_CBQI_PROP);
      if (!qinst->addInstantiation(q, terms, id))
      {
        Trace("qcf-inst") << "   ... Failed to add instantiation" << std::endl;
        // This should only happen if the algorithm generates the same
        // propagating instance twice this round. In this case, return
        // to avoid exponential behavior.
        return;
      }
      Trace("qcf-check") << "   ... Added instantiation" << std::endl;
      if (TraceIsOn("qcf-inst"))
      {
        Trace("qcf-inst") << "*** Was from effort " << d_effort << " : "
                          << std::endl;
        qi->debugPrintMatch("qcf-inst");
        Trace("qcf-inst") << std::endl;
      }
      ++addedLemmas;
      if (d_effort == EFFORT_CONFLICT)
      {
        // mark relevant: this ensures that quantified formula q is
        // checked first on the next round. This is an optimization to
        // ensure that quantified formulas that are more likely to have
        // conflicting instances are checked earlier.
        d_treg.getModel()->markRelevant(q);
        if (options().quantifiers.cbqiAllConflict)
        {
          isConflict = true;
        }
        else
        {
          d_conflict.set(true);
        }
        return;
      }
      else if (d_effort == EFFORT_PROP_EQ)
      {
        d_treg.getModel()->markRelevant(q);
      }
    }
    // clean up assigned
    qi->revertMatch(assigned);
    d_tempCache.clear();
  }
  Trace("qcf-check") << "Done, conflict = " << d_conflict << std::endl;
}

//-------------------------------------------------- debugging

void QuantConflictFind::debugPrint(const char* c) const
{
  //print the equivalance classes
  Trace(c) << "----------EQ classes" << std::endl;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( getEqualityEngine() );
  while( !eqcs_i.isFinished() ){
    Node n = (*eqcs_i);
    //if( !n.getType().isInteger() ){
    Trace(c) << "  - " << n << " : {";
    eq::EqClassIterator eqc_i = eq::EqClassIterator( n, getEqualityEngine() );
    bool pr = false;
    while( !eqc_i.isFinished() ){
      Node nn = (*eqc_i);
      if( nn.getKind()!=EQUAL && nn!=n ){
        Trace(c) << (pr ? "," : "" ) << " " << nn;
        pr = true;
      }
      ++eqc_i;
    }
    Trace(c) << (pr ? " " : "" ) << "}" << std::endl;
    ++eqcs_i;
  }
}

void QuantConflictFind::debugPrintQuant(const char* c, Node q) const
{
  std::map<Node, size_t>::const_iterator it = d_quant_id.find(q);
  if (it == d_quant_id.end())
  {
    Trace(c) << q;
    return;
  }
  Trace(c) << "Q" << it->second;
}

void QuantConflictFind::debugPrintQuantBody(const char* c,
                                            Node q,
                                            Node n,
                                            bool doVarNum) const
{
  if( n.getNumChildren()==0 ){
    Trace(c) << n;
    return;
  }
  std::map<Node, std::unique_ptr<QuantInfo> >::const_iterator itq =
      d_qinfo.find(q);
  if (itq != d_qinfo.end())
  {
    const QuantInfo* qi = itq->second.get();
    std::map<TNode, size_t>::const_iterator itv = qi->d_var_num.find(n);
    if (doVarNum && itv != qi->d_var_num.end())
    {
      Trace(c) << "?x" << itv->second;
      return;
    }
  }
  Trace(c) << "(";
  if (n.getKind() == APPLY_UF)
  {
    Trace(c) << n.getOperator();
  }
  else
  {
    Trace(c) << n.getKind();
  }
  for (const Node& nc : n)
  {
    Trace(c) << " ";
    debugPrintQuantBody(c, q, nc);
  }
  Trace(c) << ")";
}

QuantConflictFind::Statistics::Statistics(StatisticsRegistry& sr)
    : d_inst_rounds(sr.registerInt("QuantConflictFind::Inst_Rounds")),
      d_entailment_checks(
          sr.registerInt("QuantConflictFind::Entailment_Checks"))
{
}

TNode QuantConflictFind::getZero(TypeNode tn, Kind k)
{
  std::pair<TypeNode, Kind> key(tn, k);
  std::map<std::pair<TypeNode, Kind>, Node>::iterator it = d_zero.find(key);
  if (it == d_zero.end())
  {
    Node nn;
    if (k == ADD)
    {
      nn = NodeManager::currentNM()->mkConstRealOrInt(tn, Rational(0));
    }
    d_zero[key] = nn;
    return nn;
  }
  return it->second;
}

std::ostream& operator<<(std::ostream& os, const QuantConflictFind::Effort& e) {
  switch (e) {
    case QuantConflictFind::EFFORT_INVALID:
      os << "Invalid";
      break;
    case QuantConflictFind::EFFORT_CONFLICT:
      os << "Conflict";
      break;
    case QuantConflictFind::EFFORT_PROP_EQ:
      os << "PropEq";
      break;
  }
  return os;
}

bool QuantConflictFind::isPropagatingInstance(Node n) const
{
  std::unordered_set<TNode> visited;
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
      Kind ck = cur.getKind();
      if (ck == FORALL)
      {
        // do nothing
      }
      else if (TermUtil::isBoolConnective(ck))
      {
        for (TNode cc : cur)
        {
          visit.push_back(cc);
        }
      }
      else if (!getEqualityEngine()->hasTerm(cur))
      {
        Trace("qcf-instance-check-debug")
            << "...not propagating instance because of " << cur << " " << ck
            << std::endl;
        return false;
      }
    }
  } while (!visit.empty());
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

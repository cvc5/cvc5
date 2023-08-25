/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of theory uf candidate generator class.
 */

#include "theory/quantifiers/ematching/candidate_generator.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

CandidateGenerator::CandidateGenerator(Env& env,
                                       QuantifiersState& qs,
                                       TermRegistry& tr)
    : EnvObj(env), d_qs(qs), d_treg(tr)
{
}

bool CandidateGenerator::isLegalCandidate( Node n ){
  return d_treg.getTermDatabase()->isTermActive(n)
         && !quantifiers::TermUtil::hasInstConstAttr(n);
}

CandidateGeneratorQE::CandidateGeneratorQE(Env& env,
                                           QuantifiersState& qs,
                                           TermRegistry& tr,
                                           Node pat)
    : CandidateGenerator(env, qs, tr),
      d_termIter(0),
      d_termIterList(nullptr),
      d_mode(cand_term_none)
{
  d_op = d_treg.getTermDatabase()->getMatchOperator(pat);
  Assert(!d_op.isNull());
}

void CandidateGeneratorQE::reset(Node eqc) { resetForOperator(eqc, d_op); }

void CandidateGeneratorQE::resetForOperator(Node eqc, Node op)
{
  d_termIter = 0;
  d_eqc = eqc;
  d_op = op;
  d_termIterList = d_treg.getTermDatabase()->getGroundTermList(d_op);
  if (eqc.isNull())
  {
    d_mode = cand_term_db;
  }else{
    if( isExcludedEqc( eqc ) ){
      d_mode = cand_term_none;
    }else{
      eq::EqualityEngine* ee = d_qs.getEqualityEngine();
      if( ee->hasTerm( eqc ) ){
        TNodeTrie* tat = d_treg.getTermDatabase()->getTermArgTrie(eqc, op);
        if( tat ){
          //create an equivalence class iterator in eq class eqc
          Node rep = ee->getRepresentative( eqc );
          d_eqc_iter = eq::EqClassIterator( rep, ee );
          d_mode = cand_term_eqc;
        }else{
          d_mode = cand_term_none;
        }   
      }else{
        //the only match is this term itself
        d_mode = cand_term_ident;
      }
    }
  }
}
bool CandidateGeneratorQE::isLegalOpCandidate( Node n ) {
  if( n.hasOperator() ){
    if( isLegalCandidate( n ) ){
      return d_treg.getTermDatabase()->getMatchOperator(n) == d_op;
    }
  }
  return false;
}

Node CandidateGeneratorQE::getNextCandidate(){
  return getNextCandidateInternal();
}

Node CandidateGeneratorQE::getNextCandidateInternal()
{
  if( d_mode==cand_term_db ){
    if (d_termIterList == nullptr)
    {
      d_mode = cand_term_none;
      return Node::null();
    }
    Trace("cand-gen-qe") << "...get next candidate in tbd" << std::endl;
    //get next candidate term in the uf term database
    size_t tlLimit = d_termIterList->d_list.size();
    while (d_termIter < tlLimit)
    {
      Node n = d_termIterList->d_list[d_termIter];
      d_termIter++;
      if( isLegalCandidate( n ) ){
        if (d_treg.getTermDatabase()->hasTermCurrent(n))
        {
          if( d_exclude_eqc.empty() ){
            return n;
          }else{
            Node r = d_qs.getRepresentative(n);
            if( d_exclude_eqc.find( r )==d_exclude_eqc.end() ){
              Trace("cand-gen-qe") << "...returning " << n << std::endl;
              return n;
            }
          }
        }
      }
    }
  }else if( d_mode==cand_term_eqc ){
    Trace("cand-gen-qe") << "...get next candidate in eqc" << std::endl;
    while( !d_eqc_iter.isFinished() ){
      Node n = *d_eqc_iter;
      ++d_eqc_iter;
      if( isLegalOpCandidate( n ) ){
        Trace("cand-gen-qe") << "...returning " << n << std::endl;
        return n;
      }
    }
  }else if( d_mode==cand_term_ident ){
    Trace("cand-gen-qe") << "...get next candidate identity" << std::endl;
    if (!d_eqc.isNull())
    {
      Node n = d_eqc;
      d_eqc = Node::null();
      if( isLegalOpCandidate( n ) ){
        return n;
      }
    }
  }
  return Node::null();
}

CandidateGeneratorQELitDeq::CandidateGeneratorQELitDeq(Env& env,
                                                       QuantifiersState& qs,
                                                       TermRegistry& tr,
                                                       Node mpat)
    : CandidateGenerator(env, qs, tr), d_match_pattern(mpat)
{
  Assert(d_match_pattern.getKind() == EQUAL);
  d_match_pattern_type = d_match_pattern[0].getType();
}

void CandidateGeneratorQELitDeq::reset( Node eqc ){
  eq::EqualityEngine* ee = d_qs.getEqualityEngine();
  Node falset = NodeManager::currentNM()->mkConst(false);
  d_eqc_false = eq::EqClassIterator(falset, ee);
}

Node CandidateGeneratorQELitDeq::getNextCandidate(){
  //get next candidate term in equivalence class
  while( !d_eqc_false.isFinished() ){
    Node n = (*d_eqc_false);
    ++d_eqc_false;
    if( n.getKind()==d_match_pattern.getKind() ){
      if (n[0].getType() == d_match_pattern_type && isLegalCandidate(n))
      {
        //found an iff or equality, try to match it
        //DO_THIS: cache to avoid redundancies?
        //DO_THIS: do we need to try the symmetric equality for n?  or will it also exist in the eq class of false?
        return n;
      }
    }
  }
  return Node::null();
}

CandidateGeneratorQEAll::CandidateGeneratorQEAll(Env& env,
                                                 QuantifiersState& qs,
                                                 TermRegistry& tr,
                                                 Node mpat)
    : CandidateGenerator(env, qs, tr), d_match_pattern(mpat)
{
  d_match_pattern_type = mpat.getType();
  Assert(mpat.getKind() == INST_CONSTANT);
  d_f = quantifiers::TermUtil::getInstConstAttr( mpat );
  d_index = mpat.getAttribute(InstVarNumAttribute());
  d_firstTime = false;
}

void CandidateGeneratorQEAll::reset( Node eqc ) {
  d_eq = eq::EqClassesIterator(d_qs.getEqualityEngine());
  d_firstTime = true;
}

Node CandidateGeneratorQEAll::getNextCandidate() {
  quantifiers::TermDb* tdb = d_treg.getTermDatabase();
  while( !d_eq.isFinished() ){
    TNode n = (*d_eq);
    ++d_eq;
    if (n.getType() == d_match_pattern_type)
    {
      TNode nh = tdb->getEligibleTermInEqc(n);
      if( !nh.isNull() ){
        if (options().quantifiers.instMaxLevel != -1)
        {
          nh = d_treg.getModel()->getInternalRepresentative(nh, d_f, d_index);
          //don't consider this if already the instantiation is ineligible
          if (!nh.isNull() && !tdb->isTermEligibleForInstantiation(nh, d_f))
          {
            nh = Node::null();
          }
        }
        if( !nh.isNull() ){
          d_firstTime = false;
          //an equivalence class with the same type as the pattern, return it
          return nh;
        }
      }
    }
  }
  if( d_firstTime ){
    //must return something
    d_firstTime = false;
    return d_treg.getTermForType(d_match_pattern_type);
  }
  return Node::null();
}

CandidateGeneratorConsExpand::CandidateGeneratorConsExpand(Env& env,
                                                           QuantifiersState& qs,
                                                           TermRegistry& tr,
                                                           Node mpat)
    : CandidateGeneratorQE(env, qs, tr, mpat)
{
  Assert(mpat.getKind() == APPLY_CONSTRUCTOR);
  d_mpat_type = mpat.getType();
}

void CandidateGeneratorConsExpand::reset(Node eqc)
{
  d_termIter = 0;
  if (eqc.isNull())
  {
    // generates too many instantiations at top-level when eqc is null, thus
    // set mode to none unless option is set.
    if (options().quantifiers.consExpandTriggers)
    {
      d_termIterList = d_treg.getTermDatabase()->getGroundTermList(d_op);
      d_mode = cand_term_db;
    }
    else
    {
      d_mode = cand_term_none;
    }
  }
  else
  {
    d_eqc = eqc;
    d_mode = cand_term_ident;
    Assert(d_eqc.getType() == d_mpat_type);
  }
}

Node CandidateGeneratorConsExpand::getNextCandidate()
{
  // get the next term from the base class
  Node curr = getNextCandidateInternal();
  if (curr.isNull() || (curr.hasOperator() && curr.getOperator() == d_op))
  {
    return curr;
  }
  // expand it
  std::vector<Node> children;
  const DType& dt = d_mpat_type.getDType();
  Assert(dt.getNumConstructors() == 1);
  return datatypes::utils::getInstCons(
      curr, dt, 0, options().datatypes.dtSharedSelectors);
}

bool CandidateGeneratorConsExpand::isLegalOpCandidate(Node n)
{
  return isLegalCandidate(n);
}

CandidateGeneratorSelector::CandidateGeneratorSelector(Env& env,
                                                       QuantifiersState& qs,
                                                       TermRegistry& tr,
                                                       Node mpat)
    : CandidateGeneratorQE(env, qs, tr, mpat)
{
  Trace("sel-trigger") << "Selector trigger: " << mpat << std::endl;
  Assert(mpat.getKind() == APPLY_SELECTOR);
  // Get the expanded form of the selector, meaning that we will match on
  // the shared selector if shared selectors are enabled.
  Node mpatExp = datatypes::DatatypesRewriter::expandApplySelector(
      mpat, options().datatypes.dtSharedSelectors);
  Trace("sel-trigger") << "Expands to: " << mpatExp << std::endl;
  Assert (mpatExp.getKind() == APPLY_SELECTOR);
  d_selOp = d_treg.getTermDatabase()->getMatchOperator(mpatExp);
}

void CandidateGeneratorSelector::reset(Node eqc)
{
  Trace("sel-trigger-debug") << "Reset in eqc=" << eqc << std::endl;
  // start with d_selOp, if it exists
  resetForOperator(eqc, d_selOp);
}

Node CandidateGeneratorSelector::getNextCandidate()
{
  Node nextc = getNextCandidateInternal();
  if (!nextc.isNull())
  {
    Trace("sel-trigger-debug") << "...next candidate is " << nextc << std::endl;
    return nextc;
  }
  Trace("sel-trigger-debug") << "...finished" << std::endl;
  // no more candidates
  return Node::null();
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

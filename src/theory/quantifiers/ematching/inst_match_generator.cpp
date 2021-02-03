/*********************                                                        */
/*! \file inst_match_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inst match generator class
 **/

#include "theory/quantifiers/ematching/inst_match_generator.h"

#include "options/quantifiers_options.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/ematching/candidate_generator.h"
#include "theory/quantifiers/ematching/inst_match_generator_multi.h"
#include "theory/quantifiers/ematching/inst_match_generator_multi_linear.h"
#include "theory/quantifiers/ematching/inst_match_generator_simple.h"
#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/ematching/var_match_generator.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace inst {

bool IMGenerator::sendInstantiation(Trigger* tparent, InstMatch& m)
{
  return tparent->sendInstantiation(m);
}

InstMatchGenerator::InstMatchGenerator( Node pat ){
  d_cg = nullptr;
  d_needsReset = true;
  d_active_add = true;
  Assert(quantifiers::TermUtil::hasInstConstAttr(pat));
  d_pattern = pat;
  d_match_pattern = pat;
  d_match_pattern_type = pat.getType();
  d_next = nullptr;
  d_independent_gen = false;
}

InstMatchGenerator::InstMatchGenerator() {
  d_cg = nullptr;
  d_needsReset = true;
  d_active_add = true;
  d_next = nullptr;
  d_independent_gen = false;
}

InstMatchGenerator::~InstMatchGenerator()
{
  for( unsigned i=0; i<d_children.size(); i++ ){
    delete d_children[i];
  }
  delete d_cg;
}

void InstMatchGenerator::setActiveAdd(bool val){
  d_active_add = val;
  if (d_next != nullptr)
  {
    d_next->setActiveAdd(val);
  }
}

int InstMatchGenerator::getActiveScore( QuantifiersEngine * qe ) {
  if( d_match_pattern.isNull() ){
    return -1;
  }
  else if (TriggerTermInfo::isAtomicTrigger(d_match_pattern))
  {
    Node f = qe->getTermDatabase()->getMatchOperator( d_match_pattern );
    unsigned ngt = qe->getTermDatabase()->getNumGroundTerms( f );
    Trace("trigger-active-sel-debug") << "Number of ground terms for " << f << " is " << ngt << std::endl;
    return ngt;
  }else if( d_match_pattern.getKind()==INST_CONSTANT ){
    TypeNode tn = d_match_pattern.getType();
    unsigned ngtt = qe->getTermDatabase()->getNumTypeGroundTerms( tn );
    Trace("trigger-active-sel-debug") << "Number of ground terms for " << tn << " is " << ngtt << std::endl;
    return ngtt;
  }
  return -1;
}

void InstMatchGenerator::initialize(Node q,
                                    QuantifiersEngine* qe,
                                    std::vector<InstMatchGenerator*>& gens)
{
  if (d_pattern.isNull())
  {
    gens.insert(gens.end(), d_children.begin(), d_children.end());
    return;
  }
  Trace("inst-match-gen") << "Initialize, pattern term is " << d_pattern
                          << std::endl;
  if (d_match_pattern.getKind() == NOT)
  {
    Assert(d_pattern.getKind() == NOT);
    // we want to add the children of the NOT
    d_match_pattern = d_match_pattern[0];
  }

  if (d_pattern.getKind() == NOT && d_match_pattern.getKind() == EQUAL
      && d_match_pattern[0].getKind() == INST_CONSTANT
      && d_match_pattern[1].getKind() == INST_CONSTANT)
  {
    // special case: disequalities between variables x != y will match ground
    // disequalities.
  }
  else if (d_match_pattern.getKind() == EQUAL
           || d_match_pattern.getKind() == GEQ)
  {
    // We are one of the following cases:
    //   f(x)~a, f(x)~y, x~a, x~y
    // If we are the first or third case, we ensure that f(x)/x is on the left
    // hand side of the relation d_pattern, d_match_pattern is f(x)/x and
    // d_eq_class_rel (indicating the equivalence class that we are related
    // to) is set to a.
    for (size_t i = 0; i < 2; i++)
    {
      Node mp = d_match_pattern[i];
      Node mpo = d_match_pattern[1 - i];
      // If this side has free variables, and the other side does not or
      // it is a free variable, then we will match on this side of the
      // relation.
      if (quantifiers::TermUtil::hasInstConstAttr(mp)
          && (!quantifiers::TermUtil::hasInstConstAttr(mpo)
              || mpo.getKind() == INST_CONSTANT))
      {
        if (i == 1)
        {
          if (d_match_pattern.getKind() == GEQ)
          {
            d_pattern = NodeManager::currentNM()->mkNode(kind::GT, mp, mpo);
            d_pattern = d_pattern.negate();
          }
          else
          {
            d_pattern = NodeManager::currentNM()->mkNode(
                d_match_pattern.getKind(), mp, mpo);
          }
        }
        d_eq_class_rel = mpo;
        d_match_pattern = mp;
        // we won't find a term in the other direction
        break;
      }
    }
  }
  d_match_pattern_type = d_match_pattern.getType();
  Trace("inst-match-gen") << "Pattern is " << d_pattern << ", match pattern is "
                          << d_match_pattern << std::endl;
  d_match_pattern_op = qe->getTermDatabase()->getMatchOperator(d_match_pattern);

  // now, collect children of d_match_pattern
  Kind mpk = d_match_pattern.getKind();
  if (mpk == INST_CONSTANT)
  {
    d_children_types.push_back(
        d_match_pattern.getAttribute(InstVarNumAttribute()));
  }
  else
  {
    for (size_t i = 0, size = d_match_pattern.getNumChildren(); i < size; i++)
    {
      Node pat = d_match_pattern[i];
      Node qa = quantifiers::TermUtil::getInstConstAttr(pat);
      if (!qa.isNull())
      {
        if (pat.getKind() == INST_CONSTANT && qa == q)
        {
          d_children_types.push_back(pat.getAttribute(InstVarNumAttribute()));
        }
        else
        {
          InstMatchGenerator* cimg = getInstMatchGenerator(q, pat);
          if (cimg)
          {
            d_children.push_back(cimg);
            d_children_index.push_back(i);
            d_children_types.push_back(-2);
          }
          else
          {
            d_children_types.push_back(-1);
          }
        }
      }
      else
      {
        d_children_types.push_back(-1);
      }
    }
  }

  // create candidate generator
  if (mpk == APPLY_SELECTOR)
  {
    // candidates for apply selector are a union of correctly and incorrectly
    // applied selectors
    d_cg = new inst::CandidateGeneratorSelector(qe, d_match_pattern);
  }
  else if (TriggerTermInfo::isAtomicTriggerKind(mpk))
  {
    if (mpk == APPLY_CONSTRUCTOR)
    {
      // 1-constructors have a trivial way of generating candidates in a
      // given equivalence class
      const DType& dt = d_match_pattern.getType().getDType();
      if (dt.getNumConstructors() == 1)
      {
        d_cg = new inst::CandidateGeneratorConsExpand(qe, d_match_pattern);
      }
    }
    if (d_cg == nullptr)
    {
      CandidateGeneratorQE* cg = new CandidateGeneratorQE(qe, d_match_pattern);
      // we will be scanning lists trying to find ground terms whose operator
      // is the same as d_match_operator's.
      d_cg = cg;
      // if matching on disequality, inform the candidate generator not to
      // match on eqc
      if (d_pattern.getKind() == NOT && d_pattern[0].getKind() == EQUAL)
      {
        cg->excludeEqc(d_eq_class_rel);
        d_eq_class_rel = Node::null();
      }
    }
  }
  else if (mpk == INST_CONSTANT)
  {
    if (d_pattern.getKind() == APPLY_SELECTOR_TOTAL)
    {
      Node selectorExpr = qe->getTermDatabase()->getMatchOperator(d_pattern);
      size_t selectorIndex = datatypes::utils::cindexOf(selectorExpr);
      const DType& dt = datatypes::utils::datatypeOf(selectorExpr);
      const DTypeConstructor& c = dt[selectorIndex];
      Node cOp = c.getConstructor();
      Trace("inst-match-gen")
          << "Purify dt trigger " << d_pattern << ", will match terms of op "
          << cOp << std::endl;
      d_cg = new inst::CandidateGeneratorQE(qe, cOp);
    }else{
      d_cg = new CandidateGeneratorQEAll(qe, d_match_pattern);
    }
  }
  else if (mpk == EQUAL)
  {
    // we will be producing candidates via literal matching heuristics
    if (d_pattern.getKind() == NOT)
    {
      // candidates will be all disequalities
      d_cg = new inst::CandidateGeneratorQELitDeq(qe, d_match_pattern);
    }
  }
  else
  {
    Trace("inst-match-gen-warn")
        << "(?) Unknown matching pattern is " << d_match_pattern << std::endl;
  }
  gens.insert( gens.end(), d_children.begin(), d_children.end() );
}

/** get match (not modulo equality) */
int InstMatchGenerator::getMatch(
    Node f, Node t, InstMatch& m, QuantifiersEngine* qe, Trigger* tparent)
{
  Trace("matching") << "Matching " << t << " against pattern " << d_match_pattern << " ("
                    << m << ")" << ", " << d_children.size() << ", pattern is " << d_pattern << std::endl;
  Assert(!d_match_pattern.isNull());
  if (d_cg == nullptr)
  {
    Trace("matching-fail") << "Internal error for match generator." << std::endl;
    return -2;
  }
  quantifiers::QuantifiersState& qs = qe->getState();
  bool success = true;
  std::vector<int> prev;
  // if t is null
  Assert(!t.isNull());
  Assert(!quantifiers::TermUtil::hasInstConstAttr(t));
  // notice that t may have a different kind or operator from our match
  // pattern, e.g. for APPLY_SELECTOR triggers.
  // first, check if ground arguments are not equal, or a match is in conflict
  Trace("matching-debug2") << "Setting immediate matches..." << std::endl;
  for (size_t i = 0, size = d_match_pattern.getNumChildren(); i < size; i++)
  {
    int64_t ct = d_children_types[i];
    if (ct >= 0)
    {
      Trace("matching-debug2")
          << "Setting " << ct << " to " << t[i] << "..." << std::endl;
      bool addToPrev = m.get(ct).isNull();
      if (!m.set(qs, ct, t[i]))
      {
        // match is in conflict
        Trace("matching-fail")
            << "Match fail: " << m.get(ct) << " and " << t[i] << std::endl;
        success = false;
        break;
      }
      else if (addToPrev)
      {
        Trace("matching-debug2") << "Success." << std::endl;
        prev.push_back(ct);
      }
    }
    else if (ct == -1)
    {
      if (!qs.areEqual(d_match_pattern[i], t[i]))
      {
        Trace("matching-fail") << "Match fail arg: " << d_match_pattern[i]
                               << " and " << t[i] << std::endl;
        // ground arguments are not equal
        success = false;
        break;
      }
    }
  }
  Trace("matching-debug2") << "Done setting immediate matches, success = "
                           << success << "." << std::endl;
  // for variable matching
  if (d_match_pattern.getKind() == INST_CONSTANT)
  {
    bool addToPrev = m.get(d_children_types[0]).isNull();
    if (!m.set(qs, d_children_types[0], t))
    {
      success = false;
    }
    else
    {
      if (addToPrev)
      {
        prev.push_back(d_children_types[0]);
      }
    }
  }
  // for relational matching
  if (!d_eq_class_rel.isNull() && d_eq_class_rel.getKind() == INST_CONSTANT)
  {
    NodeManager* nm = NodeManager::currentNM();
    int v = d_eq_class_rel.getAttribute(InstVarNumAttribute());
    // also must fit match to equivalence class
    bool pol = d_pattern.getKind() != NOT;
    Node pat = d_pattern.getKind() == NOT ? d_pattern[0] : d_pattern;
    Node t_match;
    if (pol)
    {
      if (pat.getKind() == GT)
      {
        t_match = nm->mkNode(MINUS, t, nm->mkConst(Rational(1)));
      }else{
        t_match = t;
      }
    }
    else
    {
      if (pat.getKind() == EQUAL)
      {
        if (t.getType().isBoolean())
        {
          t_match = nm->mkConst(!qs.areEqual(nm->mkConst(true), t));
        }
        else
        {
          Assert(t.getType().isReal());
          t_match = nm->mkNode(PLUS, t, nm->mkConst(Rational(1)));
        }
      }
      else if (pat.getKind() == GEQ)
      {
        t_match = nm->mkNode(PLUS, t, nm->mkConst(Rational(1)));
      }
      else if (pat.getKind() == GT)
      {
        t_match = t;
      }
    }
    if (!t_match.isNull())
    {
      bool addToPrev = m.get(v).isNull();
      if (!m.set(qs, v, t_match))
      {
        success = false;
      }
      else if (addToPrev)
      {
        prev.push_back(v);
      }
    }
  }
  int ret_val = -1;
  if (success)
  {
    Trace("matching-debug2") << "Reset children..." << std::endl;
    // now, fit children into match
    // we will be requesting candidates for matching terms for each child
    for (size_t i = 0, size = d_children.size(); i < size; i++)
    {
      if (!d_children[i]->reset(t[d_children_index[i]], qe))
      {
        success = false;
        break;
      }
    }
    if (success)
    {
      Trace("matching-debug2") << "Continue next " << d_next << std::endl;
      ret_val = continueNextMatch(f, m, qe, tparent);
    }
  }
  if (ret_val < 0)
  {
    for (int& pv : prev)
    {
      m.d_vals[pv] = Node::null();
    }
  }
  return ret_val;
}

int InstMatchGenerator::continueNextMatch(Node q,
                                          InstMatch& m,
                                          QuantifiersEngine* qe,
                                          Trigger* tparent)
{
  if( d_next!=NULL ){
    return d_next->getNextMatch(q, m, qe, tparent);
  }
  if (d_active_add)
  {
    return sendInstantiation(tparent, m) ? 1 : -1;
  }
  return 1;
}

/** reset instantiation round */
void InstMatchGenerator::resetInstantiationRound( QuantifiersEngine* qe ){
  if( !d_match_pattern.isNull() ){
    Trace("matching-debug2") << this << " reset instantiation round." << std::endl;
    d_needsReset = true;
    if( d_cg ){
      d_cg->resetInstantiationRound();
    }
  }
  if( d_next ){
    d_next->resetInstantiationRound( qe );
  }
  d_curr_exclude_match.clear();
}

bool InstMatchGenerator::reset( Node eqc, QuantifiersEngine* qe ){
  if (d_cg == nullptr)
  {
    // we did not properly initialize the candidate generator, thus we fail
    return false;
  }
  eqc = qe->getState().getRepresentative(eqc);
  Trace("matching-debug2") << this << " reset " << eqc << "." << std::endl;
  if( !d_eq_class_rel.isNull() && d_eq_class_rel.getKind()!=INST_CONSTANT ){
    d_eq_class = d_eq_class_rel;
  }else if( !eqc.isNull() ){
    d_eq_class = eqc;
  }
  //we have a specific equivalence class in mind
  //we are producing matches for f(E) ~ t, where E is a non-ground vector of terms, and t is a ground term
  //just look in equivalence class of the RHS
  d_cg->reset( d_eq_class );
  d_needsReset = false;
  
  //generate the first candidate preemptively
  d_curr_first_candidate = Node::null();
  Node t;
  do {
    t = d_cg->getNextCandidate();
    if( d_curr_exclude_match.find( t )==d_curr_exclude_match.end() ){
      d_curr_first_candidate = t;
    }
  }while( !t.isNull() && d_curr_first_candidate.isNull() );
  Trace("matching-summary") << "Reset " << d_match_pattern << " in " << eqc << " returns " << !d_curr_first_candidate.isNull() << "." << std::endl;

  return !d_curr_first_candidate.isNull();
}

int InstMatchGenerator::getNextMatch(Node f,
                                     InstMatch& m,
                                     QuantifiersEngine* qe,
                                     Trigger* tparent)
{
  if( d_needsReset ){
    Trace("matching") << "Reset not done yet, must do the reset..." << std::endl;
    reset( d_eq_class, qe );
  }
  d_curr_matched = Node::null();
  Trace("matching") << this << " " << d_match_pattern << " get next match " << m << " in eq class " << d_eq_class << std::endl;
  int success = -1;
  Node t = d_curr_first_candidate;
  do{
    Trace("matching-debug2") << "Matching candidate : " << t << std::endl;
    Assert(!qe->getState().isInConflict());
    //if t not null, try to fit it into match m
    if( !t.isNull() ){
      if( d_curr_exclude_match.find( t )==d_curr_exclude_match.end() ){
        Assert(t.getType().isComparableTo(d_match_pattern_type));
        Trace("matching-summary") << "Try " << d_match_pattern << " : " << t << std::endl;
        success = getMatch(f, t, m, qe, tparent);
        if( d_independent_gen && success<0 ){
          Assert(d_eq_class.isNull() || !d_eq_class_rel.isNull());
          d_curr_exclude_match[t] = true;
        }
      }
      //get the next candidate term t
      if( success<0 ){
        t = qe->getState().isInConflict() ? Node::null()
                                          : d_cg->getNextCandidate();
      }else{
        d_curr_first_candidate = d_cg->getNextCandidate();
      }
    }
  }while( success<0 && !t.isNull() );
  d_curr_matched = t;
  if( success<0 ){
    Trace("matching-summary") << "..." << d_match_pattern << " failed, reset." << std::endl;
    Trace("matching") << this << " failed, reset " << d_eq_class << std::endl;
    //we failed, must reset
    reset( d_eq_class, qe );
  }else{
    Trace("matching-summary") << "..." << d_match_pattern << " success." << std::endl;
  }
  return success;
}

uint64_t InstMatchGenerator::addInstantiations(Node f,
                                               QuantifiersEngine* qe,
                                               Trigger* tparent)
{
  //try to add instantiation for each match produced
  uint64_t addedLemmas = 0;
  InstMatch m( f );
  while (getNextMatch(f, m, qe, tparent) > 0)
  {
    if( !d_active_add ){
      if (sendInstantiation(tparent, m))
      {
        addedLemmas++;
        if (qe->getState().isInConflict())
        {
          break;
        }
      }
    }else{
      addedLemmas++;
      if (qe->getState().isInConflict())
      {
        break;
      }
    }
    m.clear();
  }
  //return number of lemmas added
  return addedLemmas;
}


InstMatchGenerator* InstMatchGenerator::mkInstMatchGenerator( Node q, Node pat, QuantifiersEngine* qe ) {
  std::vector< Node > pats;
  pats.push_back( pat );
  std::map< Node, InstMatchGenerator * > pat_map_init;
  return mkInstMatchGenerator( q, pats, qe, pat_map_init );
}

InstMatchGenerator* InstMatchGenerator::mkInstMatchGeneratorMulti( Node q, std::vector< Node >& pats, QuantifiersEngine* qe ) {
  Assert(pats.size() > 1);
  InstMatchGeneratorMultiLinear * imgm = new InstMatchGeneratorMultiLinear( q, pats, qe );
  std::vector< InstMatchGenerator* > gens;
  imgm->initialize(q, qe, gens);
  Assert(gens.size() == pats.size());
  std::vector< Node > patsn;
  std::map< Node, InstMatchGenerator * > pat_map_init;
  for (InstMatchGenerator* g : gens)
  {
    Node pn = g->d_match_pattern;
    patsn.push_back( pn );
    pat_map_init[pn] = g;
  }
  //return mkInstMatchGenerator( q, patsn, qe, pat_map_init );
  imgm->d_next = mkInstMatchGenerator( q, patsn, qe, pat_map_init );
  return imgm;
}

InstMatchGenerator* InstMatchGenerator::mkInstMatchGenerator( Node q, std::vector< Node >& pats, QuantifiersEngine* qe, 
                                                              std::map< Node, InstMatchGenerator * >& pat_map_init ) {
  size_t pCounter = 0;
  InstMatchGenerator* prev = NULL;
  InstMatchGenerator* oinit = NULL;
  while( pCounter<pats.size() ){
    size_t counter = 0;
    std::vector< InstMatchGenerator* > gens;
    InstMatchGenerator* init;
    std::map< Node, InstMatchGenerator * >::iterator iti = pat_map_init.find( pats[pCounter] );
    if( iti==pat_map_init.end() ){
      init = new InstMatchGenerator(pats[pCounter]);
    }else{
      init = iti->second;
    }
    if(pCounter==0){
      oinit = init;
    }
    gens.push_back(init);
    //chain the resulting match generators together
    while (counter<gens.size()) {
      InstMatchGenerator* curr = gens[counter];
      if( prev ){
        prev->d_next = curr;
      }
      curr->initialize(q, qe, gens);
      prev = curr;
      counter++;
    }
    pCounter++;
  }
  return oinit;
}

InstMatchGenerator* InstMatchGenerator::getInstMatchGenerator(Node q, Node n)
{
  if (n.getKind() != INST_CONSTANT)
  {
    Trace("var-trigger-debug")
        << "Is " << n << " a variable trigger?" << std::endl;
    Node x;
    if (options::purifyTriggers())
    {
      Node xi = PatternTermSelector::getInversionVariable(n);
      if (!xi.isNull())
      {
        Node qa = quantifiers::TermUtil::getInstConstAttr(xi);
        if (qa == q)
        {
          x = xi;
        }
      }
    }
    if (!x.isNull())
    {
      Node s = PatternTermSelector::getInversion(n, x);
      VarMatchGeneratorTermSubs* vmg = new VarMatchGeneratorTermSubs(x, s);
      Trace("var-trigger") << "Term substitution trigger : " << n
                           << ", var = " << x << ", subs = " << s << std::endl;
      return vmg;
    }
  }
  return new InstMatchGenerator(n);
}

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

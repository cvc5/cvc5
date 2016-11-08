/*********************                                                        */
/*! \file theory.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Dejan Jovanovic, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base for theory interface.
 **
 ** Base for theory interface.
 **/

#include "theory/theory.h"

#include <vector>
#include <sstream>
#include <iostream>
#include <string>

#include "base/cvc4_assert.h"
#include "smt/smt_statistics_registry.h"
#include "theory/substitutions.h"
#include "theory/quantifiers_engine.h"


using namespace std;

namespace CVC4 {
namespace theory {

/** Default value for the uninterpreted sorts is the UF theory */
TheoryId Theory::s_uninterpretedSortOwner = THEORY_UF;

std::ostream& operator<<(std::ostream& os, Theory::Effort level){
  switch(level){
  case Theory::EFFORT_STANDARD:
    os << "EFFORT_STANDARD"; break;
  case Theory::EFFORT_FULL:
    os << "EFFORT_FULL"; break;
  case Theory::EFFORT_COMBINATION:
    os << "EFFORT_COMBINATION"; break;
  case Theory::EFFORT_LAST_CALL:
    os << "EFFORT_LAST_CALL"; break;
  default:
      Unreachable();
  }
  return os;
}/* ostream& operator<<(ostream&, Theory::Effort) */


Theory::Theory(TheoryId id, context::Context* satContext,
               context::UserContext* userContext, OutputChannel& out,
               Valuation valuation, const LogicInfo& logicInfo,
               std::string name) throw()
    : d_id(id)
    , d_instanceName(name)
    , d_satContext(satContext)
    , d_userContext(userContext)
    , d_logicInfo(logicInfo)
    , d_facts(satContext)
    , d_factsHead(satContext, 0)
    , d_sharedTermsIndex(satContext, 0)
    , d_careGraph(NULL)
    , d_quantEngine(NULL)
    , d_extt(NULL)
    , d_checkTime(getFullInstanceName() + "::checkTime")
    , d_computeCareGraphTime(getFullInstanceName() + "::computeCareGraphTime")
    , d_sharedTerms(satContext)
    , d_out(&out)
    , d_valuation(valuation)
    , d_proofsEnabled(false)
{
  smtStatisticsRegistry()->registerStat(&d_checkTime);
  smtStatisticsRegistry()->registerStat(&d_computeCareGraphTime);
}

Theory::~Theory() {
  smtStatisticsRegistry()->unregisterStat(&d_checkTime);
  smtStatisticsRegistry()->unregisterStat(&d_computeCareGraphTime);
}

TheoryId Theory::theoryOf(TheoryOfMode mode, TNode node) {
  TheoryId tid = THEORY_BUILTIN;
  switch(mode) {
  case THEORY_OF_TYPE_BASED:
    // Constants, variables, 0-ary constructors
    if (node.isVar() || node.isConst()) {
      tid = Theory::theoryOf(node.getType());
    } else if (node.getKind() == kind::EQUAL) {
      // Equality is owned by the theory that owns the domain
      tid = Theory::theoryOf(node[0].getType());
    } else {
      // Regular nodes are owned by the kind
      tid = kindToTheoryId(node.getKind());
    }
    break;
  case THEORY_OF_TERM_BASED:
    // Variables
    if (node.isVar()) {
      if (Theory::theoryOf(node.getType()) != theory::THEORY_BOOL) {
        // We treat the variables as uninterpreted
        tid = s_uninterpretedSortOwner;
      } else {
        // Except for the Boolean ones, which we just ignore anyhow
        tid = theory::THEORY_BOOL;
      }
    } else if (node.isConst()) {
      // Constants go to the theory of the type
      tid = Theory::theoryOf(node.getType());
    } else if (node.getKind() == kind::EQUAL) { // Equality
      // If one of them is an ITE, it's irelevant, since they will get replaced out anyhow
      if (node[0].getKind() == kind::ITE) {
        tid = Theory::theoryOf(node[0].getType());
      } else if (node[1].getKind() == kind::ITE) {
        tid = Theory::theoryOf(node[1].getType());
      } else {
        TNode l = node[0];
        TNode r = node[1];
        TypeNode ltype = l.getType();
        TypeNode rtype = r.getType();
        if( ltype != rtype ){
          tid = Theory::theoryOf(l.getType());
        }else {
          // If both sides belong to the same theory the choice is easy
          TheoryId T1 = Theory::theoryOf(l);
          TheoryId T2 = Theory::theoryOf(r);
          if (T1 == T2) {
            tid = T1;
          } else {
            TheoryId T3 = Theory::theoryOf(ltype);
            // This is a case of
            // * x*y = f(z) -> UF
            // * x = c      -> UF
            // * f(x) = read(a, y) -> either UF or ARRAY
            // at least one of the theories has to be parametric, i.e. theory of the type is different
            // from the theory of the term
            if (T1 == T3) {
              tid = T2;
            } else if (T2 == T3) {
              tid = T1;
            } else {
              // If both are parametric, we take the smaller one (arbitrary)
              tid = T1 < T2 ? T1 : T2;
            }
          }
        }
      }
    } else {
      // Regular nodes are owned by the kind
      tid = kindToTheoryId(node.getKind());
    }
    break;
  default:
    Unreachable();
  }
  Trace("theory::internal") << "theoryOf(" << mode << ", " << node << ") -> " << tid << std::endl;
  return tid;
}

void Theory::addSharedTermInternal(TNode n) {
  Debug("sharing") << "Theory::addSharedTerm<" << getId() << ">(" << n << ")" << endl;
  Debug("theory::assertions") << "Theory::addSharedTerm<" << getId() << ">(" << n << ")" << endl;
  d_sharedTerms.push_back(n);
  addSharedTerm(n);
}

void Theory::computeCareGraph() {
  Debug("sharing") << "Theory::computeCareGraph<" << getId() << ">()" << endl;
  for (unsigned i = 0; i < d_sharedTerms.size(); ++ i) {
    TNode a = d_sharedTerms[i];
    TypeNode aType = a.getType();
    for (unsigned j = i + 1; j < d_sharedTerms.size(); ++ j) {
      TNode b = d_sharedTerms[j];
      if (b.getType() != aType) {
        // We don't care about the terms of different types
        continue;
      }
      switch (d_valuation.getEqualityStatus(a, b)) {
      case EQUALITY_TRUE_AND_PROPAGATED:
      case EQUALITY_FALSE_AND_PROPAGATED:
  	// If we know about it, we should have propagated it, so we can skip
  	break;
      default:
  	// Let's split on it
  	addCarePair(a, b);
  	break;
      }
    }
  }
}

void Theory::printFacts(std::ostream& os) const {
  unsigned i, n = d_facts.size();
  for(i = 0; i < n; i++){
    const Assertion& a_i = d_facts[i];
    Node assertion  = a_i;
    os << d_id << '[' << i << ']' << " " << assertion << endl;
  }
}

void Theory::debugPrintFacts() const{
  DebugChannel.getStream() << "Theory::debugPrintFacts()" << endl;
  printFacts(DebugChannel.getStream());
}

std::hash_set<TNode, TNodeHashFunction> Theory::currentlySharedTerms() const{
  std::hash_set<TNode, TNodeHashFunction> currentlyShared;
  for (shared_terms_iterator i = shared_terms_begin(),
           i_end = shared_terms_end(); i != i_end; ++i) {
    currentlyShared.insert (*i);
  }
  return currentlyShared;
}


void Theory::collectTerms(TNode n, set<Node>& termSet) const
{
  if (termSet.find(n) != termSet.end()) {
    return;
  }
  Trace("theory::collectTerms") << "Theory::collectTerms: adding " << n << endl;
  termSet.insert(n);
  if (n.getKind() == kind::NOT || n.getKind() == kind::EQUAL || !isLeaf(n)) {
    for(TNode::iterator child_it = n.begin(); child_it != n.end(); ++child_it) {
      collectTerms(*child_it, termSet);
    }
  }
}


void Theory::computeRelevantTerms(set<Node>& termSet, bool includeShared) const
{
  // Collect all terms appearing in assertions
  context::CDList<Assertion>::const_iterator assert_it = facts_begin(), assert_it_end = facts_end();
  for (; assert_it != assert_it_end; ++assert_it) {
    collectTerms(*assert_it, termSet);
  }

  if (!includeShared) return;

  // Add terms that are shared terms
  context::CDList<TNode>::const_iterator shared_it = shared_terms_begin(), shared_it_end = shared_terms_end();
  for (; shared_it != shared_it_end; ++shared_it) {
    collectTerms(*shared_it, termSet);
  }
}


Theory::PPAssertStatus Theory::ppAssert(TNode in,
                                        SubstitutionMap& outSubstitutions)
{
  if (in.getKind() == kind::EQUAL) {
    // (and (= x t) phi) can be replaced by phi[x/t] if
    // 1) x is a variable
    // 2) x is not in the term t
    // 3) x : T and t : S, then S <: T
    if (in[0].isVar() && !in[1].hasSubterm(in[0]) &&
        (in[1].getType()).isSubtypeOf(in[0].getType()) ){
      outSubstitutions.addSubstitution(in[0], in[1]);
      return PP_ASSERT_STATUS_SOLVED;
    }
    if (in[1].isVar() && !in[0].hasSubterm(in[1]) &&
        (in[0].getType()).isSubtypeOf(in[1].getType())){
      outSubstitutions.addSubstitution(in[1], in[0]);
      return PP_ASSERT_STATUS_SOLVED;
    }
    if (in[0].isConst() && in[1].isConst()) {
      if (in[0] != in[1]) {
        return PP_ASSERT_STATUS_CONFLICT;
      }
    }
  }

  return PP_ASSERT_STATUS_UNSOLVED;
}

std::pair<bool, Node> Theory::entailmentCheck(
    TNode lit,
    const EntailmentCheckParameters* params,
    EntailmentCheckSideEffects* out) {
  return make_pair(false, Node::null());
}

EntailmentCheckParameters::EntailmentCheckParameters(TheoryId tid)
  : d_tid(tid) {
}

std::string Theory::getFullInstanceName() const {
  std::stringstream ss;
  ss << "theory<" << d_id << ">" << d_instanceName;
  return ss.str();
}

EntailmentCheckParameters::~EntailmentCheckParameters(){}

TheoryId EntailmentCheckParameters::getTheoryId() const {
  return d_tid;
}

EntailmentCheckSideEffects::EntailmentCheckSideEffects(TheoryId tid)
  : d_tid(tid)
{}

TheoryId EntailmentCheckSideEffects::getTheoryId() const {
  return d_tid;
}

EntailmentCheckSideEffects::~EntailmentCheckSideEffects() {
}


ExtTheory::ExtTheory( Theory * p ) : d_parent( p ), 
d_ext_func_terms( p->getSatContext() ), d_ci_inactive( p->getUserContext() ), 
d_lemmas( p->getUserContext() ), d_pp_lemmas( p->getUserContext() ), d_has_extf( p->getSatContext() ){
  d_true = NodeManager::currentNM()->mkConst( true );
}

//gets all leaf terms in n
void ExtTheory::collectVars( Node n, std::vector< Node >& vars, std::map< Node, bool >& visited ) {
  if( !n.isConst() ){
    if( visited.find( n )==visited.end() ){
      visited[n] = true;
      //treat terms not belonging to this theory as leaf  
      //  AJR TODO : should include terms not belonging to this theory (commented below)
      if( n.getNumChildren()>0 ){//&& Theory::theoryOf(n)==d_parent->getId() ){
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          collectVars( n[i], vars, visited );
        }
      }else{
        vars.push_back( n );
      }
    }
  }
}

//do inferences 
void ExtTheory::getSubstitutedTerms( int effort, std::vector< Node >& terms, std::vector< Node >& sterms, std::vector< std::vector< Node > >& exp ) {
  Trace("extt-debug") << "Currently " << d_ext_func_terms.size() << " extended functions." << std::endl;
  Trace("extt-debug") << "..." << terms.size() << " to reduce." << std::endl;
  if( !terms.empty() ){
    //all variables we need to find a substitution for
    std::vector< Node > vars;
    std::vector< Node > sub;
    std::map< Node, std::vector< Node > > expc;
    for( unsigned i=0; i<terms.size(); i++ ){
      //do substitution, rewrite
      Node n = terms[i];
      std::map< Node, ExtfInfo >::iterator iti = d_extf_info.find( n );
      Trace("extt-debug") << "Check extf : " << n << std::endl;
      Assert( iti!=d_extf_info.end() );
      for( unsigned i=0; i<iti->second.d_vars.size(); i++ ){
        if( std::find( vars.begin(), vars.end(), iti->second.d_vars[i] )==vars.end() ){
          vars.push_back( iti->second.d_vars[i] );
        } 
      }
    }
    //get the current substitution for all variables
    if( d_parent->getCurrentSubstitution( effort, vars, sub, expc ) ){
      Assert( vars.size()==sub.size() );
      for( unsigned i=0; i<terms.size(); i++ ){
        //do substitution
        Node n = terms[i];
        Node ns = n.substitute( vars.begin(), vars.end(), sub.begin(), sub.end() );
        std::vector< Node > expn;
        if( ns!=n ){
          //build explanation: explanation vars = sub for each vars in FV( n )
          std::map< Node, ExtfInfo >::iterator iti = d_extf_info.find( n );
          Assert( iti!=d_extf_info.end() );
          for( unsigned j=0; j<iti->second.d_vars.size(); j++ ){
            Node v = iti->second.d_vars[j];
            std::map< Node, std::vector< Node > >::iterator itx = expc.find( v );
            if( itx!=expc.end() ){
              for( unsigned k=0; k<itx->second.size(); k++ ){
                if( std::find( expn.begin(), expn.end(), itx->second[k] )==expn.end() ){
                  expn.push_back( itx->second[k] );
                }
              }
            }
          }
        }
        Trace("extt-debug") << "  have " << n << " == " << ns << ", exp size=" << expn.size() << "." << std::endl;
        //add to vector
        sterms.push_back( ns );
        exp.push_back( expn );
      }
    }else{
      for( unsigned i=0; i<terms.size(); i++ ){
        sterms.push_back( terms[i] );
      }
    }
  }
}

bool ExtTheory::doInferencesInternal( int effort, std::vector< Node >& terms, std::vector< Node >& nred, bool batch, bool isRed ) {
  if( batch ){
    bool addedLemma = false;
    if( isRed ){
      for( unsigned i=0; i<terms.size(); i++ ){
        Node n = terms[i];
        Node nr;
        //TODO: reduction with substitution?
        int ret = d_parent->getReduction( effort, n, nr );
        if( ret==0 ){
          nred.push_back( n );
        }else{
          if( !nr.isNull() && n!=nr ){
            Node lem = NodeManager::currentNM()->mkNode( n.getType().isBoolean() ? kind::IFF : kind::EQUAL, n, nr );
            if( sendLemma( lem, true ) ){
              Trace("extt-lemma") << "ExtTheory : Reduction lemma : " << lem << std::endl;
              addedLemma = true;
            }
          }
          markReduced( terms[i], ret<0 );
        }
      }
    }else{
      std::vector< Node > sterms; 
      std::vector< std::vector< Node > > exp;
      getSubstitutedTerms( effort, terms, sterms, exp );
      for( unsigned i=0; i<terms.size(); i++ ){
        bool processed = false;
        if( sterms[i]!=terms[i] ){
          Node sr = Rewriter::rewrite( sterms[i] );
          if( sr.isConst() ){
            processed = true;
            markReduced( terms[i] );
            Node eq = terms[i].eqNode( sr );
            Node expn = exp[i].size()>1 ? NodeManager::currentNM()->mkNode( kind::AND, exp[i] ) : ( exp[i].size()==1 ? exp[i][0] : d_true );
            Trace("extt-debug") << "ExtTheory::doInferences : infer : " << eq << " by " << expn << std::endl;
            Node lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, expn, eq );
            Trace("extt-debug") << "...send lemma " << lem << std::endl;
            if( sendLemma( lem ) ){
              Trace("extt-lemma") << "ExtTheory : Constant rewrite lemma : " << lem << std::endl;
              addedLemma = true;
            }
          }
        }
        if( !processed ){
          nred.push_back( terms[i] );
        }
      }
    }
    return addedLemma;
  }else{
    std::vector< Node > nnred;
    if( terms.empty() ){
      for( NodeBoolMap::iterator it = d_ext_func_terms.begin(); it != d_ext_func_terms.end(); ++it ){
        if( (*it).second && !isContextIndependentInactive( (*it).first ) ){
          std::vector< Node > nterms;
          nterms.push_back( (*it).first );
          if( doInferencesInternal( effort, nterms, nnred, true, isRed ) ){
            return true;
          }       
        }
      }
    }else{
      for( unsigned i=0; i<terms.size(); i++ ){
        std::vector< Node > nterms;
        nterms.push_back( terms[i] );
        if( doInferencesInternal( effort, nterms, nnred, true, isRed ) ){
          return true;
        }   
      }
    }
    return false;
  }
}

bool ExtTheory::sendLemma( Node lem, bool preprocess ) {
  if( preprocess ){
    if( d_pp_lemmas.find( lem )==d_pp_lemmas.end() ){
      d_pp_lemmas.insert( lem );
      d_parent->getOutputChannel().lemma( lem, false, true );
      return true;
    }
  }else{
    if( d_lemmas.find( lem )==d_lemmas.end() ){
      d_lemmas.insert( lem );
      d_parent->getOutputChannel().lemma( lem );
      return true;
    }
  }
  return false;
}

bool ExtTheory::doInferences( int effort, std::vector< Node >& terms, std::vector< Node >& nred, bool batch ) {
  if( !terms.empty() ){
    return doInferencesInternal( effort, terms, nred, batch, false );
  }else{
    return false;
  }
}

bool ExtTheory::doInferences( int effort, std::vector< Node >& nred, bool batch ) {
  std::vector< Node > terms;
  getActive( terms );
  return doInferencesInternal( effort, terms, nred, batch, false );
}

bool ExtTheory::doReductions( int effort, std::vector< Node >& terms, std::vector< Node >& nred, bool batch ) {
  if( !terms.empty() ){
    return doInferencesInternal( effort, terms, nred, batch, true );
  }else{
    return false;
  }
}

bool ExtTheory::doReductions( int effort, std::vector< Node >& nred, bool batch ) {
  std::vector< Node > terms;
  getActive( terms );
  return doInferencesInternal( effort, terms, nred, batch, true );
}


//register term
void ExtTheory::registerTerm( Node n ) {
  if( d_extf_kind.find( n.getKind() )!=d_extf_kind.end() ){
    if( d_ext_func_terms.find( n )==d_ext_func_terms.end() ){
      Trace("extt-debug") << "Found extended function : " << n << " in " << d_parent->getId() << std::endl;
      d_ext_func_terms[n] = true;
      d_has_extf = n;
      std::map< Node, bool > visited;
      collectVars( n, d_extf_info[n].d_vars, visited );
    }
  }
}

void ExtTheory::registerTermRec( Node n ) {
  std::map< Node, bool > visited;
  registerTermRec( n, visited );
}

void ExtTheory::registerTermRec( Node n, std::map< Node, bool >& visited ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    registerTerm( n );
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      registerTermRec( n[i], visited );
    }
  }
}

//mark reduced
void ExtTheory::markReduced( Node n, bool contextDepend ) {
  registerTerm( n );
  Assert( d_ext_func_terms.find( n )!=d_ext_func_terms.end() );
  d_ext_func_terms[n] = false;
  if( !contextDepend ){
    d_ci_inactive.insert( n );
  }
  
  //update has_extf
  if( d_has_extf.get()==n ){
    for( NodeBoolMap::iterator it = d_ext_func_terms.begin(); it != d_ext_func_terms.end(); ++it ){
      //if not already reduced
      if( (*it).second && !isContextIndependentInactive( (*it).first ) ){
         d_has_extf = (*it).first;
      }
    }
  
  }
}

//mark congruent
void ExtTheory::markCongruent( Node a, Node b ) {
  Trace("extt-debug") << "Mark congruent : " << a << " " << b << std::endl;
  registerTerm( a );
  registerTerm( b );
  NodeBoolMap::const_iterator it = d_ext_func_terms.find( b );
  if( it!=d_ext_func_terms.end() ){
    if( d_ext_func_terms.find( a )!=d_ext_func_terms.end() ){
      d_ext_func_terms[a] = d_ext_func_terms[a] && (*it).second;
    }else{
      Assert( false );
    }
    d_ext_func_terms[b] = false;
  }else{
    Assert( false );
  }
}

bool ExtTheory::isContextIndependentInactive( Node n ) {
  return d_ci_inactive.find( n )!=d_ci_inactive.end();
}

bool ExtTheory::hasActiveTerm() {
  return !d_has_extf.get().isNull();
}
  
//is active
bool ExtTheory::isActive( Node n ) {
  NodeBoolMap::const_iterator it = d_ext_func_terms.find( n );
  if( it!=d_ext_func_terms.end() ){
    return (*it).second && !isContextIndependentInactive( n );
  }else{
    return false;
  }
}
//get active 
void ExtTheory::getActive( std::vector< Node >& active ) {
  for( NodeBoolMap::iterator it = d_ext_func_terms.begin(); it != d_ext_func_terms.end(); ++it ){
    //if not already reduced
    if( (*it).second && !isContextIndependentInactive( (*it).first ) ){
      active.push_back( (*it).first );
    }
  }
}

void ExtTheory::getActive( std::vector< Node >& active, Kind k ) {
  for( NodeBoolMap::iterator it = d_ext_func_terms.begin(); it != d_ext_func_terms.end(); ++it ){
    //if not already reduced
    if( (*it).first.getKind()==k && (*it).second && !isContextIndependentInactive( (*it).first ) ){
      active.push_back( (*it).first );
    }
  }
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

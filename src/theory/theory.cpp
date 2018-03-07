/*********************                                                        */
/*! \file theory.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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

Theory::Theory(TheoryId id,
               context::Context* satContext,
               context::UserContext* userContext,
               OutputChannel& out,
               Valuation valuation,
               const LogicInfo& logicInfo,
               std::string name)
    : d_id(id),
      d_instanceName(name),
      d_satContext(satContext),
      d_userContext(userContext),
      d_logicInfo(logicInfo),
      d_facts(satContext),
      d_factsHead(satContext, 0),
      d_sharedTermsIndex(satContext, 0),
      d_careGraph(NULL),
      d_quantEngine(NULL),
      d_extTheory(NULL),
      d_checkTime(getStatsPrefix(id) + "::checkTime"),
      d_computeCareGraphTime(getStatsPrefix(id) + "::computeCareGraphTime"),
      d_sharedTerms(satContext),
      d_out(&out),
      d_valuation(valuation),
      d_proofsEnabled(false)
{
  smtStatisticsRegistry()->registerStat(&d_checkTime);
  smtStatisticsRegistry()->registerStat(&d_computeCareGraphTime);
}

Theory::~Theory() {
  smtStatisticsRegistry()->unregisterStat(&d_checkTime);
  smtStatisticsRegistry()->unregisterStat(&d_computeCareGraphTime);

  delete d_extTheory;
}

TheoryId Theory::theoryOf(TheoryOfMode mode, TNode node) {
  TheoryId tid = THEORY_BUILTIN;
  switch(mode) {
  case THEORY_OF_TYPE_BASED:
    // Constants, variables, 0-ary constructors
    if (node.isVar()) {
      if( node.getKind() == kind::BOOLEAN_TERM_VARIABLE ){
        tid = THEORY_UF;
      }else{
        tid = Theory::theoryOf(node.getType());
      }
    }else if (node.isConst()) {
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
        if( node.getKind() == kind::BOOLEAN_TERM_VARIABLE ){
          //Boolean vars go to UF
          tid = THEORY_UF;
        }else{
          // Except for the Boolean ones
          tid = THEORY_BOOL;
        }
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

std::unordered_set<TNode, TNodeHashFunction> Theory::currentlySharedTerms() const{
  std::unordered_set<TNode, TNodeHashFunction> currentlyShared;
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

ExtTheory* Theory::getExtTheory() {
  Assert(d_extTheory != NULL);
  return d_extTheory;
}

void Theory::addCarePair(TNode t1, TNode t2) {
  if (d_careGraph) {
    d_careGraph->insert(CarePair(t1, t2, d_id));
  }
}

void Theory::getCareGraph(CareGraph* careGraph) {
  Assert(careGraph != NULL);

  Trace("sharing") << "Theory<" << getId() << ">::getCareGraph()" << std::endl;
  TimerStat::CodeTimer computeCareGraphTime(d_computeCareGraphTime);
  d_careGraph = careGraph;
  computeCareGraph();
  d_careGraph = NULL;
}

void Theory::setQuantifiersEngine(QuantifiersEngine* qe) {
  Assert(d_quantEngine == NULL);
  Assert(qe != NULL);
  d_quantEngine = qe;
}

void Theory::setupExtTheory() {
  Assert(d_extTheory == NULL);
  d_extTheory = new ExtTheory(this);
}


EntailmentCheckParameters::EntailmentCheckParameters(TheoryId tid)
  : d_tid(tid) {
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



ExtTheory::ExtTheory( Theory * p, bool cacheEnabled ) : d_parent( p ), 
d_ext_func_terms( p->getSatContext() ), d_ci_inactive( p->getUserContext() ), d_has_extf( p->getSatContext() ),
d_lemmas( p->getUserContext() ), d_pp_lemmas( p->getUserContext() ), d_cacheEnabled( cacheEnabled ){
  d_true = NodeManager::currentNM()->mkConst( true );
}

// Gets all leaf terms in n.
std::vector<Node> ExtTheory::collectVars(Node n) {
  std::vector<Node> vars;
  std::set<Node> visited;
  std::vector<Node> worklist;
  worklist.push_back(n);
  while (!worklist.empty()) {
    Node current = worklist.back();
    worklist.pop_back();
    if (current.isConst() || visited.count(current) > 0) {
      continue;
    }
    visited.insert(current);
    // Treat terms not belonging to this theory as leaf
    // AJR TODO : should include terms not belonging to this theory
    // (commented below)
    if (current.getNumChildren() > 0) {
      //&& Theory::theoryOf(n)==d_parent->getId() ){
      worklist.insert(worklist.end(), current.begin(), current.end());
    } else {
      vars.push_back(current);
    }
  }
  return vars;
}

Node ExtTheory::getSubstitutedTerm( int effort, Node term, std::vector< Node >& exp, bool useCache ) {
  if( useCache ){
    Assert( d_gst_cache[effort].find( term )!=d_gst_cache[effort].end() );
    exp.insert( exp.end(), d_gst_cache[effort][term].d_exp.begin(), d_gst_cache[effort][term].d_exp.end() );
    return d_gst_cache[effort][term].d_sterm;
  }else{
    std::vector< Node > terms;
    terms.push_back( term );
    std::vector< Node > sterms;
    std::vector< std::vector< Node > > exps;
    getSubstitutedTerms( effort, terms, sterms, exps, useCache );
    Assert( sterms.size()==1 );
    Assert( exps.size()==1 );
    exp.insert( exp.end(), exps[0].begin(), exps[0].end() );
    return sterms[0];
  }
}

//do inferences
void ExtTheory::getSubstitutedTerms(int effort, const std::vector<Node>& terms,
                                    std::vector<Node>& sterms,
                                    std::vector<std::vector<Node> >& exp,
                                    bool useCache) {
  if (useCache) {
    for( unsigned i=0; i<terms.size(); i++ ){
      Node n = terms[i];
      Assert( d_gst_cache[effort].find( n )!=d_gst_cache[effort].end() );
      sterms.push_back( d_gst_cache[effort][n].d_sterm );
      exp.push_back( std::vector< Node >() );
      exp[0].insert( exp[0].end(), d_gst_cache[effort][n].d_exp.begin(), d_gst_cache[effort][n].d_exp.end() );
    }
  }else{
    Trace("extt-debug") << "getSubstitutedTerms for " << terms.size() << " / " << d_ext_func_terms.size() << " extended functions." << std::endl;
    if( !terms.empty() ){
      //all variables we need to find a substitution for
      std::vector< Node > vars;
      std::vector< Node > sub;
      std::map< Node, std::vector< Node > > expc;
      for( unsigned i=0; i<terms.size(); i++ ){
        //do substitution, rewrite
        Node n = terms[i];
        std::map< Node, ExtfInfo >::iterator iti = d_extf_info.find( n );
        Assert( iti!=d_extf_info.end() );
        for( unsigned i=0; i<iti->second.d_vars.size(); i++ ){
          if( std::find( vars.begin(), vars.end(), iti->second.d_vars[i] )==vars.end() ){
            vars.push_back( iti->second.d_vars[i] );
          } 
        }
      }
      bool useSubs = d_parent->getCurrentSubstitution( effort, vars, sub, expc );
      //get the current substitution for all variables
      Assert( !useSubs || vars.size()==sub.size() );
      for( unsigned i=0; i<terms.size(); i++ ){
        Node n = terms[i];
        Node ns = n;
        std::vector< Node > expn;
        if( useSubs ){
          //do substitution
          ns = n.substitute( vars.begin(), vars.end(), sub.begin(), sub.end() );
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
        }
        //add to vector
        sterms.push_back( ns );
        exp.push_back( expn );
        //add to cache
        if( d_cacheEnabled ){
          d_gst_cache[effort][n].d_sterm = ns;
          d_gst_cache[effort][n].d_exp.clear();
          d_gst_cache[effort][n].d_exp.insert( d_gst_cache[effort][n].d_exp.end(), expn.begin(), expn.end() );
        }
      }
    }
  }
}

bool ExtTheory::doInferencesInternal(int effort, const std::vector<Node>& terms,
                                     std::vector<Node>& nred, bool batch,
                                     bool isRed) {
  if (batch) {
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
            Node lem = NodeManager::currentNM()->mkNode( kind::EQUAL, n, nr );
            if( sendLemma( lem, true ) ){
              Trace("extt-lemma") << "ExtTheory : reduction lemma : " << lem << std::endl;
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
      std::map< Node, unsigned > sterm_index;
      for( unsigned i=0; i<terms.size(); i++ ){
        bool processed = false;
        if( sterms[i]!=terms[i] ){
          Node sr = Rewriter::rewrite( sterms[i] );
          //ask the theory if this term is reduced, e.g. is it constant or it is a non-extf term.
          if( d_parent->isExtfReduced( effort, sr, terms[i], exp[i] ) ){
            processed = true;
            markReduced( terms[i] );
            Node eq = terms[i].eqNode( sr );
            Node expn = exp[i].size()>1 ? NodeManager::currentNM()->mkNode( kind::AND, exp[i] ) : ( exp[i].size()==1 ? exp[i][0] : d_true );
            Trace("extt-debug") << "ExtTheory::doInferences : infer : " << eq << " by " << expn << std::endl;
            Node lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, expn, eq );
            Trace("extt-debug") << "...send lemma " << lem << std::endl;
            if( sendLemma( lem ) ){
              Trace("extt-lemma") << "ExtTheory : substitution + rewrite lemma : " << lem << std::endl;
              addedLemma = true;
            }
          }else{
            //check if we have already reduced this
            std::map< Node, unsigned >::iterator itsi = sterm_index.find( sr );
            if( itsi!=sterm_index.end() ){
              //unsigned j = itsi->second;
              //can add (non-reducing) lemma : exp[j] ^ exp[i] => sterms[i] = sterms[j]
              //TODO
            }else{
              sterm_index[sr] = i;
            }
            //check if we reduce to another active term?
          
            Trace("extt-nred") << "Non-reduced term : " << sr << std::endl;
          }
        }else{
          Trace("extt-nred") << "Non-reduced term : " << sterms[i] << std::endl;
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

bool ExtTheory::doInferences(int effort, const std::vector<Node>& terms,
                             std::vector<Node>& nred, bool batch) {
  if (!terms.empty()) {
    return doInferencesInternal( effort, terms, nred, batch, false );
  }else{
    return false;
  }
}

bool ExtTheory::doInferences( int effort, std::vector< Node >& nred, bool batch ) {
  std::vector< Node > terms = getActive();
  return doInferencesInternal( effort, terms, nred, batch, false );
}

bool ExtTheory::doReductions(int effort, const std::vector<Node>& terms,
                             std::vector<Node>& nred, bool batch) {
  if (!terms.empty()) {
    return doInferencesInternal( effort, terms, nred, batch, true );
  }else{
    return false;
  }
}

bool ExtTheory::doReductions(int effort, std::vector<Node>& nred, bool batch) {
  const std::vector<Node> terms = getActive();
  return doInferencesInternal(effort, terms, nred, batch, true);
}

// Register term.
void ExtTheory::registerTerm(Node n) {
  if (d_extf_kind.find(n.getKind()) != d_extf_kind.end()) {
    if (d_ext_func_terms.find(n) == d_ext_func_terms.end()) {
      Trace("extt-debug") << "Found extended function : " << n << " in "
                          << d_parent->getId() << std::endl;
      d_ext_func_terms[n] = true;
      d_has_extf = n;
      d_extf_info[n].d_vars = collectVars(n);
    }
  }
}

void ExtTheory::registerTermRec(Node n) {
  std::set<Node> visited;
  registerTermRec(n, &visited);
}

void ExtTheory::registerTermRec(Node n, std::set<Node>* visited) {
  if (visited->find(n) == visited->end()) {
    visited->insert(n);
    registerTerm(n);
    for (unsigned i = 0; i < n.getNumChildren(); i++) {
      registerTermRec(n[i], visited);
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

bool ExtTheory::isContextIndependentInactive(Node n) const {
  return d_ci_inactive.find(n) != d_ci_inactive.end();
}


void ExtTheory::getTerms( std::vector< Node >& terms ) {
  for( NodeBoolMap::iterator it = d_ext_func_terms.begin(); it != d_ext_func_terms.end(); ++it ){
    terms.push_back( (*it).first );
  }
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

// get active
std::vector<Node> ExtTheory::getActive() const {
  std::vector<Node> active;
  for (NodeBoolMap::iterator it = d_ext_func_terms.begin();
       it != d_ext_func_terms.end(); ++it) {
    // if not already reduced
    if ((*it).second && !isContextIndependentInactive((*it).first)) {
      active.push_back((*it).first);
    }
  }
  return active;
}

std::vector<Node> ExtTheory::getActive(Kind k) const {
  std::vector<Node> active;
  for (NodeBoolMap::iterator it = d_ext_func_terms.begin();
       it != d_ext_func_terms.end(); ++it) {
    // if not already reduced
    if ((*it).first.getKind() == k && (*it).second &&
        !isContextIndependentInactive((*it).first)) {
      active.push_back((*it).first);
    }
  }
  return active;
}

void ExtTheory::clearCache() {
  d_gst_cache.clear();
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

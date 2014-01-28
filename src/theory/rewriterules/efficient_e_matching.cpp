/*********************                                                        */
/*! \file efficient_e_matching.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of theory uf instantiator class
 **/

#include "theory/rewriterules/efficient_e_matching.h"
#include "theory/rewriterules/rr_candidate_generator.h"
#include "theory/quantifiers/candidate_generator.h"
#include "theory/quantifiers/options.h"
#include "theory/rewriterules/options.h"
#include "theory/quantifiers/term_database.h"

#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;

namespace CVC4 {
namespace theory {

inline std::ostream& operator<<(std::ostream& out, const EfficientEMatcher::Ips& ips) {
  return out;
};

EqClassInfo::EqClassInfo( context::Context* c ) : d_funs( c ), d_pfuns( c ), d_disequal( c ){

}

//set member
void EqClassInfo::setMember( Node n, quantifiers::TermDb* db ){
  if( n.hasOperator() ){
    d_funs.insertAtContextLevelZero(n.getOperator(),true);
  }
  //add parent functions
  for( std::hash_map< Node, std::hash_map< int, std::vector< Node >  >, NodeHashFunction >::iterator it = db->d_parents[n].begin();
    it != db->d_parents[n].end(); ++it ){
    //TODO Is it true to do it at level 0? That depend when SetMember is called
    // At worst it is a good overapproximation
    d_pfuns.insertAtContextLevelZero( it->first, true);
  }
}

//get has function
bool EqClassInfo::hasFunction( Node op ){
  return d_funs.find( op )!=d_funs.end();
}

bool EqClassInfo::hasParent( Node op ){
  return d_pfuns.find( op )!=d_pfuns.end();
}

//merge with another eq class info
void EqClassInfo::merge( EqClassInfo* eci ){
  for( BoolMap::iterator it = eci->d_funs.begin(); it != eci->d_funs.end(); it++ ) {
    d_funs[ (*it).first ] = true;
  }
  for( BoolMap::iterator it = eci->d_pfuns.begin(); it != eci->d_pfuns.end(); it++ ) {
    d_pfuns[ (*it).first ] = true;
  }
}

inline void outputEqClassInfo( const char* c, const EqClassInfo* eci){
  Debug(c) << " funs:";
  for( EqClassInfo::BoolMap::iterator it = eci->d_funs.begin(); it != eci->d_funs.end(); it++ ) {
    Debug(c) << (*it).first << ",";
  }
  Debug(c) << std::endl << "pfuns:";
  for( EqClassInfo::BoolMap::iterator it = eci->d_pfuns.begin(); it != eci->d_pfuns.end(); it++ ) {
    Debug(c) << (*it).first << ",";
  }
  Debug(c) << std::endl;
}



EfficientEMatcher::EfficientEMatcher( CVC4::theory::QuantifiersEngine* qe ) : d_quantEngine( qe )
{

}

eq::EqualityEngine* EfficientEMatcher::getEqualityEngine(){
  //return ((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->theoryOf( THEORY_UF ))->getEqualityEngine();
  return d_quantEngine->getMasterEqualityEngine();
}

/** new node */
void EfficientEMatcher::newEqClass( TNode n ){

}

void EfficientEMatcher::newTerms(SetNode& s){
  static NoMatchAttribute rewrittenNodeAttribute;
  /* op -> nodes (if the set is empty, the op is not interesting) */
  std::hash_map< TNode, SetNode, TNodeHashFunction > h;
  /* types -> nodes (if the set is empty, the type is not interesting) */
  std::hash_map< TypeNode, SetNode, TypeNodeHashFunction > tyh;
  for(SetNode::iterator i=s.begin(), end=s.end(); i != end; ++i){
    if (i->getAttribute(rewrittenNodeAttribute)) continue; /* skip it */
    if( !d_cand_gens.empty() ){
      // op
      TNode op = i->getOperator();
      std::hash_map< TNode, SetNode, TNodeHashFunction >::iterator
        is = h.find(op);
      if(is == h.end()){
        std::pair<std::hash_map< TNode, SetNode, TNodeHashFunction >::iterator,bool>
          p = h.insert(make_pair(op,SetNode()));
        is = p.first;
        if(d_cand_gens.find(op) != d_cand_gens.end()){
          is->second.insert(*i);
        } /* else we have inserted an empty set */
      }else if(!is->second.empty()){
        is->second.insert(*i);
      }
    }
    if( !d_cand_gen_types.empty() ){
      //type
      TypeNode ty = i->getType();
      std::hash_map< TypeNode, SetNode, TypeNodeHashFunction >::iterator
        is = tyh.find(ty);
      if(is == tyh.end()){
        std::pair<std::hash_map< TypeNode, SetNode, TypeNodeHashFunction >::iterator,bool>
          p = tyh.insert(make_pair(ty,SetNode()));
        is = p.first;
        if(d_cand_gen_types.find(ty) != d_cand_gen_types.end()){
          is->second.insert(*i);
        } /* else we have inserted an empty set */
      }else if(!is->second.empty()){
        is->second.insert(*i);
      }
    }
  }
  //op
  for(std::hash_map< TNode, SetNode, TNodeHashFunction >::iterator i=h.begin(), end=h.end();
      i != end; ++i){
    //new term, add n to candidate generators
    if(i->second.empty()) continue;
    std::map< Node, NodeNewTermDispatcher >::iterator
      inpc = d_cand_gens.find(i->first);
    //we know that this op exists
    Assert(inpc != d_cand_gens.end());
    inpc->second.send(i->second);
  }
  //type
  for(std::hash_map< TypeNode, SetNode, TypeNodeHashFunction >::iterator i=tyh.begin(), end=tyh.end();
      i != end; ++i){
    //new term, add n to candidate generators
    if(i->second.empty()) continue;
    std::map< TypeNode, NodeNewTermDispatcher >::iterator
      inpc = d_cand_gen_types.find(i->first);
    //we know that this op exists
    Assert(inpc != d_cand_gen_types.end());
    inpc->second.send(i->second);
  }

}


/** merge */
void EfficientEMatcher::merge( TNode a, TNode b ){
  if( options::efficientEMatching() ){
    //merge eqc_ops of b into a
    EqClassInfo* eci_a = getOrCreateEquivalenceClassInfo( a );
    EqClassInfo* eci_b = getOrCreateEquivalenceClassInfo( b );

    if( a.getKind()!=IFF && a.getKind()!=EQUAL && b.getKind()!=IFF && b.getKind()!=EQUAL ){
      Debug("efficient-e-match") << "Merging " << a << " with " << b << std::endl;

      //determine new candidates for instantiation
      computeCandidatesPcPairs( a, eci_a, b, eci_b );
      computeCandidatesPcPairs( b, eci_b, a, eci_a );
      computeCandidatesPpPairs( a, eci_a, b, eci_b );
      computeCandidatesPpPairs( b, eci_b, a, eci_a );
    }
    computeCandidatesConstants( a, eci_a, b, eci_b);
    computeCandidatesConstants( b, eci_b, a, eci_a);

    eci_a->merge( eci_b );
  }
}

/** assert terms are disequal */
void EfficientEMatcher::assertDisequal( TNode a, TNode b, TNode reason ){

}

EqClassInfo* EfficientEMatcher::getEquivalenceClassInfo( Node n ) {
  return d_eqc_ops.find( n )==d_eqc_ops.end() ? NULL : d_eqc_ops[n];
}
EqClassInfo* EfficientEMatcher::getOrCreateEquivalenceClassInfo( Node n ){
  Assert( n==getEqualityEngine()->getRepresentative( n ) );
  if( d_eqc_ops.find( n )==d_eqc_ops.end() ){
    EqClassInfo* eci = new EqClassInfo( d_quantEngine->getSatContext() );
    eci->setMember( n, d_quantEngine->getTermDatabase() );
    d_eqc_ops[n] = eci;
  }
  return d_eqc_ops[n];
}

void EfficientEMatcher::computeCandidatesPcPairs( Node a, EqClassInfo* eci_a, Node b, EqClassInfo* eci_b ){
  Debug("efficient-e-match") << "Compute candidates for pc pairs..." << std::endl;
  Debug("efficient-e-match") << "  Eq class = [";
  outputEqClass( "efficient-e-match", a);
  Debug("efficient-e-match") << "]" << std::endl;
  outputEqClassInfo("efficient-e-match",eci_a);
  for( EqClassInfo::BoolMap::iterator it = eci_a->d_funs.begin(); it != eci_a->d_funs.end(); it++ ) {
    //the child function:  a member of eq_class( a ) has top symbol g, in other words g is in funs( a )
    Node g = (*it).first;
    Debug("efficient-e-match") << "  Checking application " << g << std::endl;
    //look at all parent/child pairs
    for( std::map< Node, std::vector< std::pair< NodePcDispatcher*, Ips > > >::iterator itf = d_pc_pairs[g].begin();
         itf != d_pc_pairs[g].end(); ++itf ){
      //f/g is a parent/child pair
      Node f = itf->first;
      if( eci_b->hasParent( f ) ){
        //DO_THIS: determine if f in pfuns( b ), only do the follow if so
        Debug("efficient-e-match") << "    Checking parent application " << f << std::endl;
        //scan through the list of inverted path strings/candidate generators
        for( std::vector< std::pair< NodePcDispatcher*, Ips > >::iterator cit = itf->second.begin();
             cit != itf->second.end(); ++cit ){
#ifdef CVC4_DEBUG
          Debug("efficient-e-match") << "      Checking pattern " << cit->first->pat << std::endl;
#endif
          Debug("efficient-e-match") << "          Check inverted path string for pattern ";
          outputIps( "efficient-e-match", cit->second );
          Debug("efficient-e-match") << std::endl;

          //collect all new relevant terms
          SetNode terms;
          terms.insert( b );
          collectTermsIps( cit->second, terms );
          if( terms.empty() ) continue;
          Debug("efficient-e-match") << "        -> Added terms (" << terms.size() << "): ";
          for( SetNode::const_iterator t=terms.begin(), end=terms.end();
               t!=end; ++t ){
            Debug("efficient-e-match") << (*t) << " ";
          }
          Debug("efficient-e-match") << std::endl;
          //add them as candidates to the candidate generator
          cit->first->send(terms);
        }
      }
    }
  }
}

void EfficientEMatcher::computeCandidatesPpPairs( Node a, EqClassInfo* eci_a, Node b, EqClassInfo* eci_b ){
  Debug("efficient-e-match") << "Compute candidates for pp pairs..." << std::endl;
  for( std::map< Node, std::map< Node, std::vector< triple< NodePpDispatcher*, Ips, Ips > > > >::iterator it = d_pp_pairs.begin();
       it != d_pp_pairs.end(); ++it ){
    Node f = it->first;
    if( eci_a->hasParent( f ) ){
      Debug("efficient-e-match") << "  Checking parent application " << f << std::endl;
      for( std::map< Node, std::vector< triple<NodePpDispatcher*, Ips, Ips> > >::iterator it2 = it->second.begin();
           it2 != it->second.end(); ++it2 ){
        Node g = it2->first;
        if( eci_b->hasParent( g ) ){
          Debug("efficient-e-match") << "    Checking parent application " << g << std::endl;
          //if f in pfuns( a ) and g is in pfuns( b ), only do the follow if so
          for( std::vector< triple<NodePpDispatcher*, Ips, Ips> > ::iterator cit = it2->second.begin();
               cit != it2->second.end(); ++cit ){
#ifdef CVC4_DEBUG
            Debug("efficient-e-match") << "    Checking pattern " << cit->first->pat1 << " and " << cit->first->pat2 << std::endl;
#endif
            Debug("efficient-e-match") << "          Check inverted path string ";
            outputIps( "efficient-e-match", cit->second );
            SetNode a_terms;
            a_terms.insert( a );
            collectTermsIps( cit->second, a_terms );
            if( a_terms.empty() ) continue;
            Debug("efficient-e-match") << "          And check inverted path string ";
            outputIps( "efficient-e-match", cit->third );
            SetNode b_terms;
            b_terms.insert( b );
            collectTermsIps( cit->third, b_terms );
            if( b_terms.empty() ) continue;
            //Start debug
            Debug("efficient-e-match") << "        -> Possibly Added termsA (" << a_terms.size() << "): ";
            for( SetNode::const_iterator t=a_terms.begin(), end=a_terms.end();
                 t!=end; ++t ){
              Debug("efficient-e-match") << (*t) << " ";
            }
            Debug("efficient-e-match") << std::endl;
            Debug("efficient-e-match") << "        -> Possibly Added termsB (" << b_terms.size() << "): ";
            for( SetNode::const_iterator t=b_terms.begin(), end=b_terms.end();
                 t!=end; ++t ){
              Debug("efficient-e-match") << (*t) << " ";
            }
            Debug("efficient-e-match") << std::endl;
            //End debug

            cit->first->send(a_terms,b_terms);
          }
        }
      }
    }
  }
}


void EfficientEMatcher::computeCandidatesConstants( Node a, EqClassInfo* eci_a, Node b, EqClassInfo* eci_b ){
  Debug("efficient-e-match") << "Compute candidates constants for cc pairs..." << std::endl;
  Debug("efficient-e-match") << "  Eq class = [";
  outputEqClass( "efficient-e-match", a);
  Debug("efficient-e-match") << "]" << std::endl;
  outputEqClassInfo("efficient-e-match",eci_a);
  for( std::map< Node, std::map< Node, NodePcDispatcher* > >::iterator
         it = d_cc_pairs.begin(), end = d_cc_pairs.end();
       it != end; ++it ) {
    Debug("efficient-e-match") << "  Checking application " << it->first << std::endl;
    if( !eci_b->hasFunction(it->first) ) continue;
    for( std::map< Node, NodePcDispatcher* >::iterator
           itc = it->second.begin(), end = it->second.end();
       itc != end; ++itc ) {
      //The constant
      Debug("efficient-e-match") << "    Checking constant " << a << std::endl;
      if(getEqualityEngine()->getRepresentative(itc->first) != a) continue;
      SetNode s;
      eq::EqClassIterator eqc_iter( b, getEqualityEngine() );
      while( !eqc_iter.isFinished() ){
        Debug("efficient-e-match-debug") << "> look at " << (*eqc_iter)
                                         << std::endl;
        if( (*eqc_iter).hasOperator() && (*eqc_iter).getOperator() == it->first ) s.insert(*eqc_iter);
        eqc_iter++;
      }

      if( s.empty() ) continue;
      Debug("efficient-e-match") << "        -> Added terms (" << s.size() << "): ";
      for( SetNode::const_iterator t=s.begin(), end=s.end();
           t!=end; ++t ){
        Debug("efficient-e-match") << (*t) << " ";
      }
      Debug("efficient-e-match") << std::endl;
      itc->second->send(s);
    }
  }
}

void EfficientEMatcher::collectTermsIps( Ips& ips, SetNode & terms ){
  Assert( ips.size() > 0);
  return collectTermsIps( ips, terms,  ips.size() - 1);
}

void EfficientEMatcher::collectTermsIps( Ips& ips, SetNode& terms, int index ){
  if( !terms.empty() ){
    Debug("efficient-e-match-debug") << "> Process " << index << std::endl;
    Node f = ips[index].first;
    int arg = ips[index].second;

    //for each term in terms, determine if any term (modulo equality) has parent "f" from position "arg"
    bool addRep = ( index!=0 ); // We want to keep the top symbol for the last
    SetNode newTerms;
    for( SetNode::const_iterator t=terms.begin(), end=terms.end();
         t!=end; ++t ){
      collectParentsTermsIps( *t, f, arg, newTerms, addRep );
    }
    terms.swap(newTerms);

    Debug("efficient-e-match-debug") << "> Terms are now: ";
    for( SetNode::const_iterator t=terms.begin(), end=terms.end();
         t!=end; ++t ){
      Debug("efficient-e-match-debug") << *t << " ";
    }
    Debug("efficient-e-match-debug") << std::endl;

    if(index!=0) collectTermsIps( ips, terms, index-1 );
  }
}

bool EfficientEMatcher::collectParentsTermsIps( Node n, Node f, int arg, SetNode & terms, bool addRep, bool modEq ){ //modEq default true
  bool addedTerm = false;

  if( modEq && getEqualityEngine()->hasTerm( n )){
    Assert( getEqualityEngine()->getRepresentative( n )==n );
    //collect modulo equality
    //DO_THIS: this should (if necessary) compute a current set of (f, arg) parents for n and cache it
    eq::EqClassIterator eqc_iter( n, getEqualityEngine() );
    while( !eqc_iter.isFinished() ){
      Debug("efficient-e-match-debug") << "> look at " << (*eqc_iter)
                                       << std::endl;
      if( collectParentsTermsIps( (*eqc_iter), f, arg, terms, addRep, false ) ){
        //if only one argument, we know we can stop (since all others added will be congruent)
        if( f.getType().getNumChildren()==2 ){
          return true;
        }
        addedTerm = true;
      }
      eqc_iter++;
    }
  }else{
    quantifiers::TermDb* db = d_quantEngine->getTermDatabase();
    //see if parent f exists from argument arg
    const std::vector<Node> & parents = db->getParents(n,f,arg);
    for( size_t i=0; i<parents.size(); ++i ){
      TNode t = parents[i];
      if(!CandidateGenerator::isLegalCandidate(t)) continue;
      if( addRep ) t = getEqualityEngine()->getRepresentative( t );
      terms.insert(t);
      addedTerm = true;
    }
  }
  return addedTerm;
}

void EfficientEMatcher::registerPatternElementPairs2( Node pat, Ips& ips, PpIpsMap & pp_ips_map, NodePcDispatcher* npc ){
  Assert( pat.hasOperator() );
  //add information for possible pp-pair
  ips.push_back( std::pair< Node, int >( pat.getOperator(), 0 ) ); //0 is just a dumb value

  for( int i=0; i<(int)pat.getNumChildren(); i++ ){
    if( pat[i].getKind()==INST_CONSTANT ){
      ips.back().second = i;
      pp_ips_map[ pat[i] ].push_back( make_pair( pat.getOperator(), Ips( ips ) ) );
    }
  }

  for( int i=0; i<(int)pat.getNumChildren(); i++ ){
    if( pat[i].getKind()==APPLY_UF ){
      ips.back().second = i;
      registerPatternElementPairs2( pat[i], ips, pp_ips_map, npc );
      Debug("pattern-element-opt") << "Found pc-pair ( " << pat.getOperator() << ", " << pat[i].getOperator() << " )" << std::endl;
      Debug("pattern-element-opt") << "   Path = ";
      outputIps( "pattern-element-opt", ips );
      Debug("pattern-element-opt") << std::endl;
      //pat.getOperator() and pat[i].getOperator() are a pc-pair
      d_pc_pairs[ pat[i].getOperator() ][ pat.getOperator() ]
        .push_back( make_pair(npc,Ips(ips)) );
    }
  }
  ips.pop_back();
}

void EfficientEMatcher::registerPatternElementPairs( Node pat, PpIpsMap & pp_ips_map,
                                                     NodePcDispatcher* npc,
                                                     NodePpDispatcher* npp){
  Ips ips;
  registerPatternElementPairs2( pat, ips, pp_ips_map, npc );
  for( PpIpsMap::iterator it = pp_ips_map.begin(); it != pp_ips_map.end(); ++it ){
    // for each variable construct all the pp-pair
    for( size_t j=0; j<it->second.size(); j++ ){
      for( size_t k=j+1; k<it->second.size(); k++ ){
        //found a pp-pair
        Debug("pattern-element-opt") << "Found pp-pair ( " << it->second[j].first << ", " << it->second[k].first << " )" << std::endl;
        Debug("pattern-element-opt") << "   Paths = ";
        outputIps( "pattern-element-opt", it->second[j].second );
        Debug("pattern-element-opt") << " and ";
        outputIps( "pattern-element-opt", it->second[k].second );
        Debug("pattern-element-opt") << std::endl;
        d_pp_pairs[ it->second[j].first ][ it->second[k].first ]
          .push_back( make_triple( npp, it->second[j].second, it->second[k].second ));
      }
    }
  }
};

void findPpSite(Node pat, EfficientEMatcher::Ips& ips, EfficientEMatcher::PpIpsMap & pp_ips_map){
  Assert( pat.getKind()==APPLY_UF );
  //add information for possible pp-pair

  ips.push_back( make_pair( pat.getOperator(), 0) );
  for( size_t i=0; i<pat.getNumChildren(); i++ ){
    if( pat[i].getKind()==INST_CONSTANT ){
      ips.back().second = i;
      pp_ips_map[ pat[i] ].push_back( make_pair( pat.getOperator(), EfficientEMatcher::Ips( ips ) ) );
    }
  }

  for( size_t i=0; i<pat.getNumChildren(); i++ ){
    if( pat[i].getKind()==APPLY_UF ){
      ips.back().second = i;
      findPpSite( pat[i], ips, pp_ips_map );
    }
  }
  ips.pop_back();
}

void EfficientEMatcher::combineMultiPpIpsMap(PpIpsMap & pp_ips_map, MultiPpIpsMap & multi_pp_ips_map,
                                                EfficientHandler& eh, size_t index2,const std::vector<Node> & pats){
  hash_map<size_t,NodePpDispatcher*> npps;
  for( PpIpsMap::iterator it = pp_ips_map.begin(); it != pp_ips_map.end(); ++it ){
    MultiPpIpsMap::iterator mit = multi_pp_ips_map.find(it->first);
    if(mit == multi_pp_ips_map.end()) continue;
    // for each variable construct all the pp-pair
    // j the last pattern treated
    for( std::vector< std::pair< Node, Ips > >::iterator j=it->second.begin(), jend = it->second.end() ;
         j != jend; ++j){
      // k one of the previous one
      for( std::vector< triple< size_t, Node, Ips > >::iterator k=mit->second.begin(), kend = mit->second.end() ;
           k != kend; ++k){
        //found a pp-pair
        Debug("pattern-element-opt") << "Found multi-pp-pair ( " << j->first
                                     << ", " << k->second << " in "<< k->first
                                     << " )" << std::endl;
        Debug("pattern-element-opt") << "   Paths = ";
        outputIps( "pattern-element-opt", j->second );
        Debug("pattern-element-opt") << " and ";
        outputIps( "pattern-element-opt", k->third );
        Debug("pattern-element-opt") << std::endl;
        NodePpDispatcher* dispatcher;
        hash_map<size_t,NodePpDispatcher*>::iterator inpp = npps.find(k->first);
        if( inpp != npps.end() ) dispatcher = inpp->second;
        else{
          dispatcher = new NodePpDispatcher();
#ifdef CVC4_DEBUG
          dispatcher->pat1 = pats[index2];
          dispatcher->pat2 = pats[k->first];
#endif
          dispatcher->addPpDispatcher(&eh,index2,k->first);
        };
        d_pp_pairs[ j->first ][ k->second ].push_back( make_triple( dispatcher, j->second, k->third ));
      }
    }
  }

  /** Put pp_ips_map to multi_pp_ips_map */
  for( PpIpsMap::iterator it = pp_ips_map.begin(); it != pp_ips_map.end(); ++it ){
    for( std::vector< std::pair< Node, Ips > >::iterator j=it->second.begin(), jend = it->second.end() ;
         j != jend; ++j){
      multi_pp_ips_map[it->first].push_back(make_triple(index2, j->first, j->second));
    }
  }

}


void EfficientEMatcher::registerEfficientHandler( EfficientHandler& handler,
                                                     const std::vector< Node > & pats ){
  Assert(pats.size() > 0);

  MultiPpIpsMap multi_pp_ips_map;
  PpIpsMap pp_ips_map;
  //In a multi-pattern Pattern that is only a variable are specials,
  //if the variable appears in another pattern, it can be discarded.
  //Otherwise new term of this term can be candidate. So we stock them
  //here before adding them.
  std::vector< size_t > patVars;

  Debug("pattern-element-opt") << "Register patterns" << pats << std::endl;
  for(size_t i = 0; i < pats.size(); ++i){
    if( pats[i].getKind() == kind::INST_CONSTANT){
      patVars.push_back(i);
      continue;
    }
    //to complete
    if( pats[i].getKind() == kind::NOT && pats[i][0].getKind() == kind::EQUAL){
      Node cst = NodeManager::currentNM()->mkConst<bool>(false);
      TNode op = pats[i][0].getOperator();
      if(d_cc_pairs[op][cst] == NULL){
        d_cc_pairs[op][cst] = new NodePcDispatcher();
      }
      d_cc_pairs[op][cst]->addPcDispatcher(&handler,i);
      continue;
    }
    //end to complete
    Debug("pattern-element-opt") << " Register candidate generator..." << pats[i] << std::endl;
    /* Has the pattern already been seen */
    if( d_pat_cand_gens.find( pats[i] )==d_pat_cand_gens.end() ){
      NodePcDispatcher* npc = new NodePcDispatcher();
      NodePpDispatcher* npp = new NodePpDispatcher();
#ifdef CVC4_DEBUG
      npc->pat = pats[i];
      npp->pat1 = pats[i];
      npp->pat2 = pats[i];
#endif
      d_pat_cand_gens[pats[i]] = make_pair(npc,npp);
      registerPatternElementPairs( pats[i], pp_ips_map, npc, npp );
    }else{
      Ips ips;
      findPpSite(pats[i],ips,pp_ips_map);
    }
    //Has the top operator already been seen */
    TNode op = pats[i].getOperator();
    d_pat_cand_gens[pats[i]].first->addPcDispatcher(&handler,i);
    d_pat_cand_gens[pats[i]].second->addPpDispatcher(&handler,i,i);
    d_cand_gens[op].addNewTermDispatcher(&handler,i);

    combineMultiPpIpsMap(pp_ips_map,multi_pp_ips_map,handler,i,pats);

    pp_ips_map.clear();
  }

  for(size_t i = 0; i < patVars.size(); ++i){
    TNode var = pats[patVars[i]];
    Assert( var.getKind() == kind::INST_CONSTANT );
    if( multi_pp_ips_map.find(var) != multi_pp_ips_map.end() ){
      //The variable appear in another pattern, skip it
      continue;
    };
    d_cand_gen_types[var.getType()].addNewTermDispatcher(&handler,patVars[i]);
  }

  //take all terms from the uf term db and add to candidate generator
  if( pats[0].getKind() == kind::INST_CONSTANT ){
    TypeNode ty = pats[0].getType();
    rrinst::CandidateGenerator* cg = new GenericCandidateGeneratorClasses(d_quantEngine);
    cg->reset(Node::null());
    TNode c;
    SetNode ele;
    while( !(c = cg->getNextCandidate()).isNull() ){
      if( c.getType() == ty ) ele.insert(c);
    }
    if( !ele.empty() ){
      if(Debug.isOn("efficient-e-match-stats")){
        Debug("efficient-e-match-stats") << "pattern " << pats << " initialized with " << ele.size() << " terms"<< std::endl;
      }
      handler.addMonoCandidate(ele, 0);
    }

  } else if( pats[0].getKind() == kind::NOT && pats[0][0].getKind() == kind::EQUAL){
    Node cst = NodeManager::currentNM()->mkConst<bool>(false);
    TNode op = pats[0][0].getOperator();
    cst = getEqualityEngine()->getRepresentative(cst);
    SetNode ele;
    eq::EqClassIterator eqc_iter( cst, getEqualityEngine() );
    while( !eqc_iter.isFinished() ){
      Debug("efficient-e-match-debug") << "> look at " << (*eqc_iter)
                                       << std::endl;
      if( (*eqc_iter).hasOperator() && (*eqc_iter).getOperator() == op ) ele.insert(*eqc_iter);
      eqc_iter++;
    }
    if( !ele.empty() ){
      if(Debug.isOn("efficient-e-match-stats")){
        Debug("efficient-e-match-stats") << "pattern " << pats << " initialized with " << ele.size() << " terms"<< std::endl;
      }
      handler.addMonoCandidate(ele, 0);
    }

  } else {
    TermDb* db = d_quantEngine->getTermDatabase();
    Node op = db->getOperator( pats[0] );
    if(db->d_op_map[op].begin() != db->d_op_map[op].end()){
      SetNode ele;
      ele.insert(db->d_op_map[op].begin(), db->d_op_map[op].end());
      if(Debug.isOn("efficient-e-match-stats")){
        Debug("efficient-e-match-stats") << "pattern " << pats << " initialized with " << ele.size() << " terms"<< std::endl;
      }
      handler.addMonoCandidate(ele, 0);
    }
  }
  Debug("efficient-e-match") << "Done." << std::endl;
}

void EfficientEMatcher::outputEqClass( const char* c, Node n ){
  if( getEqualityEngine()->hasTerm( n ) ){
    eq::EqClassIterator eqc_iter( getEqualityEngine()->getRepresentative( n ),
                                  getEqualityEngine() );
    bool firstTime = true;
    while( !eqc_iter.isFinished() ){
      if( !firstTime ){ Debug(c) << ", "; }
      Debug(c) << (*eqc_iter);
      firstTime = false;
      eqc_iter++;
    }
  }else{
    Debug(c) << n;
  }
}

void EfficientEMatcher::outputIps( const char* c, Ips& ips ){
  for( int i=0; i<(int)ips.size(); i++ ){
    if( i>0 ){ Debug( c ) << "."; }
    Debug( c ) << ips[i].first << "." << ips[i].second;
  }
}


} /* namespace theory */
} /* namespace cvc4 */

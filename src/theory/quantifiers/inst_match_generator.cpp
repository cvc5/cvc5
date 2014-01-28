/*********************                                                        */
/*! \file inst_match_generator.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
**/

#include "theory/quantifiers/inst_match_generator.h"
#include "theory/quantifiers/trigger.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/candidate_generator.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

namespace CVC4 {
namespace theory {
namespace inst {


InstMatchGenerator::InstMatchGenerator( Node pat, int matchPolicy ) : d_matchPolicy( matchPolicy ){
  d_active_add = false;
  Assert( quantifiers::TermDb::hasInstConstAttr(pat) );
  d_pattern = pat;
  d_match_pattern = pat;
  d_next = NULL;
}

void InstMatchGenerator::setActiveAdd(bool val){
  d_active_add = val;
  if( d_next!=NULL ){
    d_next->setActiveAdd(val);
  }
}

void InstMatchGenerator::initialize( QuantifiersEngine* qe, std::vector< InstMatchGenerator * > & gens ){
  if( !d_pattern.isNull() ){
    Debug("inst-match-gen") << "Pattern term is " << d_pattern << std::endl;
    if( d_match_pattern.getKind()==NOT ){
      //we want to add the children of the NOT
      d_match_pattern = d_pattern[0];
    }
    if( d_match_pattern.getKind()==IFF || d_match_pattern.getKind()==EQUAL || d_match_pattern.getKind()==GEQ ){
      //make sure the matching portion of the equality is on the LHS of d_pattern
      //  and record what d_match_pattern is
      if( !quantifiers::TermDb::hasInstConstAttr(d_match_pattern[0]) ||
          d_match_pattern[0].getKind()==INST_CONSTANT ){
        if( d_match_pattern[1].getKind()!=INST_CONSTANT ){
          Assert( quantifiers::TermDb::hasInstConstAttr(d_match_pattern[1]) );
          Node mp = d_match_pattern[1];
          //swap sides
          Node pat = d_pattern;
          if(d_match_pattern.getKind()==GEQ){
            d_pattern = NodeManager::currentNM()->mkNode( kind::GT, d_match_pattern[1], d_match_pattern[0] );
            d_pattern = d_pattern.negate();
          }else{
            d_pattern = NodeManager::currentNM()->mkNode( d_match_pattern.getKind(), d_match_pattern[1], d_match_pattern[0] );
          }
          d_pattern = pat.getKind()==NOT ? d_pattern.negate() : d_pattern;
          d_match_pattern = mp;
        }
      }else if( !quantifiers::TermDb::hasInstConstAttr(d_match_pattern[1]) ||
                d_match_pattern[1].getKind()==INST_CONSTANT ){
        if( d_match_pattern[0].getKind()!=INST_CONSTANT ){
          Assert( quantifiers::TermDb::hasInstConstAttr(d_match_pattern[0]) );
          if( d_pattern.getKind()!=NOT ){   //TEMPORARY until we do better implementation of disequality matching
            d_match_pattern = d_match_pattern[0];
          }else if( d_match_pattern[1].getKind()==INST_CONSTANT ){
            d_match_pattern = d_match_pattern[0];
          }
        }
      }
    }
    Trace("inst-match-gen") << "Pattern is " << d_pattern << ", match pattern is " << d_match_pattern << std::endl;
    d_match_pattern_op = qe->getTermDatabase()->getOperator( d_match_pattern );

    //now, collect children of d_match_pattern
    int childMatchPolicy = MATCH_GEN_DEFAULT;
    for( int i=0; i<(int)d_match_pattern.getNumChildren(); i++ ){
      if( quantifiers::TermDb::hasInstConstAttr(d_match_pattern[i]) ){
        if( d_match_pattern[i].getKind()!=INST_CONSTANT && !Trigger::isBooleanTermTrigger( d_match_pattern[i] ) ){
          InstMatchGenerator * cimg = new InstMatchGenerator( d_match_pattern[i], childMatchPolicy );
          d_children.push_back( cimg );
          d_children_index.push_back( i );
          gens.push_back( cimg );
        }
      }
    }

    //create candidate generator
    if( d_match_pattern.getKind()==INST_CONSTANT ){
      d_cg = new CandidateGeneratorQEAll( qe, d_match_pattern );
    }
    else if( d_match_pattern.getKind()==EQUAL || d_match_pattern.getKind()==IFF ){
      Assert( d_matchPolicy==MATCH_GEN_DEFAULT );
      //we will be producing candidates via literal matching heuristics
      if( d_pattern.getKind()!=NOT ){
        //candidates will be all equalities
        d_cg = new inst::CandidateGeneratorQELitEq( qe, d_match_pattern );
      }else{
        //candidates will be all disequalities
        d_cg = new inst::CandidateGeneratorQELitDeq( qe, d_match_pattern );
      }
    }else if( d_pattern.getKind()==EQUAL || d_pattern.getKind()==IFF ||
              d_pattern.getKind()==GEQ || d_pattern.getKind()==GT || d_pattern.getKind()==NOT ){
      Assert( d_matchPolicy==MATCH_GEN_DEFAULT );
      if( d_pattern.getKind()==NOT ){
        if (d_pattern[0][1].getKind()!=INST_CONSTANT) {
          Unimplemented("Disequal generator unimplemented");
        }else{
          d_eq_class = d_pattern[0][1];
        }
      }else{
        //store the equivalence class that we will call d_cg->reset( ... ) on
        d_eq_class = d_pattern[1];
      }
      Assert( Trigger::isAtomicTrigger( d_match_pattern ) );
      //we are matching only in a particular equivalence class
      d_cg = new inst::CandidateGeneratorQE( qe, d_match_pattern_op );
    }else if( Trigger::isAtomicTrigger( d_match_pattern ) ){
      //we will be scanning lists trying to find d_match_pattern.getOperator()
      d_cg = new inst::CandidateGeneratorQE( qe, d_match_pattern_op );
    }else{
      d_cg = new CandidateGeneratorQueue;
      Trace("inst-match-gen-warn") << "(?) Unknown matching pattern is " << d_match_pattern << std::endl;
      d_matchPolicy = MATCH_GEN_INTERNAL_ERROR;
    }
    for( int i=0; i<(int)d_match_pattern.getNumChildren(); i++ ){
      if( d_match_pattern[i].getKind()==INST_CONSTANT || Trigger::isBooleanTermTrigger( d_match_pattern[i] ) ){
        Node vv = d_match_pattern[i];
        if( Trigger::isBooleanTermTrigger( d_match_pattern[i] ) ){
          vv = d_match_pattern[i][0];
        }
        d_var_num[i] = vv.getAttribute(InstVarNumAttribute());
      }
    }
  }
}

/** get match (not modulo equality) */
bool InstMatchGenerator::getMatch( Node f, Node t, InstMatch& m, QuantifiersEngine* qe ){
  Trace("matching") << "Matching " << t << " against pattern " << d_match_pattern << " ("
                    << m << ")" << ", " << d_children.size() << ", pattern is " << d_pattern << std::endl;
  Assert( !d_match_pattern.isNull() );
  if( qe->d_optMatchIgnoreModelBasis && t.getAttribute(ModelBasisAttribute()) ){
    return true;
  }else if( d_matchPolicy==MATCH_GEN_INTERNAL_ERROR ){
    return false;
  }else{
    EqualityQuery* q = qe->getEqualityQuery();
    bool success = true;
    //save previous match
    //InstMatch prev( &m );
    std::vector< int > prev;
    //if t is null
    Assert( !t.isNull() );
    Assert( !quantifiers::TermDb::hasInstConstAttr(t) );
    Assert( t.getKind()==d_match_pattern.getKind() );
    Assert( !Trigger::isAtomicTrigger( d_match_pattern ) || t.getOperator()==d_match_pattern.getOperator() );
    //first, check if ground arguments are not equal, or a match is in conflict
    for( int i=0; i<(int)d_match_pattern.getNumChildren(); i++ ){
      if( quantifiers::TermDb::hasInstConstAttr(d_match_pattern[i]) ){
        if( d_match_pattern[i].getKind()==INST_CONSTANT || Trigger::isBooleanTermTrigger( d_match_pattern[i] ) ){
          Node tt = t[i];
          if( Trigger::isBooleanTermTrigger( d_match_pattern[i] ) ){
            tt = NodeManager::currentNM()->mkConst(q->areEqual( tt, d_match_pattern[i][1] ));
          }
          bool addToPrev = m.get( d_var_num[i] ).isNull();
          if( !m.set( qe, d_var_num[i], tt ) ){
            //match is in conflict
            Trace("matching-fail") << "Match fail: " << m.get(d_var_num[i]) << " and " << tt << std::endl;
            success = false;
            break;
          }else if( addToPrev ){
            prev.push_back( d_var_num[i] );
          }
        }
      }else{
        if( !q->areEqual( d_match_pattern[i], t[i] ) ){
          Trace("matching-fail") << "Match fail arg: " << d_match_pattern[i] << " and " << t[i] << std::endl;
          //ground arguments are not equal
          success = false;
          break;
        }
      }
    }
    //for relational matching
    if( !d_eq_class.isNull() && d_eq_class.getKind()==INST_CONSTANT ){
      int v = d_eq_class.getAttribute(InstVarNumAttribute());
      //also must fit match to equivalence class
      bool pol = d_pattern.getKind()!=NOT;
      Node pat = d_pattern.getKind()==NOT ? d_pattern[0] : d_pattern;
      Node t_match;
      if( pol ){
        if (pat.getKind()==GT) {
          Node r = NodeManager::currentNM()->mkConst( Rational(-1) );
          t_match = NodeManager::currentNM()->mkNode(PLUS, t, r);
        }else{
          t_match = t;
        }
      }else{
        if(pat.getKind()==EQUAL) {
          Node r = NodeManager::currentNM()->mkConst( Rational(1) );
          t_match = NodeManager::currentNM()->mkNode(PLUS, t, r);
        }else if( pat.getKind()==IFF ){
          t_match = NodeManager::currentNM()->mkConst( !q->areEqual( NodeManager::currentNM()->mkConst(true), t ) );
        }else if( pat.getKind()==GEQ ){
          Node r = NodeManager::currentNM()->mkConst( Rational(1) );
          t_match = NodeManager::currentNM()->mkNode(PLUS, t, r);
        }else if( pat.getKind()==GT ){
          t_match = t;
        }
      }
      if( !t_match.isNull() ){
        bool addToPrev = m.get( v ).isNull();
        if( !m.set( qe, v, t_match ) ){
          success = false;
        }else if( addToPrev ){
          prev.push_back( v );
        }
      }
    }
    if( success ){
      //now, fit children into match
      //we will be requesting candidates for matching terms for each child
      for( int i=0; i<(int)d_children.size(); i++ ){
        Node rep = q->getRepresentative( t[ d_children_index[i] ] );
        d_children[i]->reset( rep, qe );
      }
      if( d_next!=NULL ){
        success = d_next->getNextMatch( f, m, qe );
      }else{
        if( d_active_add ){
          Trace("active-add") << "Active Adding instantiation " << m << std::endl;
          success = qe->addInstantiation( f, m );
          Trace("active-add") << "Success = " << success << std::endl;
        }
      }
    }
    if( !success ){
      //m = InstMatch( &prev );
      for( unsigned i=0; i<prev.size(); i++ ){
        m.d_vals[prev[i]] = Node::null();
      }
    }
    return success;
  }
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
}

void InstMatchGenerator::reset( Node eqc, QuantifiersEngine* qe ){
  Trace("matching-debug2") << this << " reset " << eqc << "." << std::endl;
  if( !eqc.isNull() ){
    d_eq_class = eqc;
  }
  //we have a specific equivalence class in mind
  //we are producing matches for f(E) ~ t, where E is a non-ground vector of terms, and t is a ground term
  //just look in equivalence class of the RHS
  d_cg->reset( d_eq_class.getKind()==INST_CONSTANT ? Node::null() : d_eq_class );
  d_needsReset = false;
}

bool InstMatchGenerator::getNextMatch( Node f, InstMatch& m, QuantifiersEngine* qe ){
  if( d_needsReset ){
    Trace("matching") << "Reset not done yet, must do the reset..." << std::endl;
    reset( d_eq_class.getKind()==INST_CONSTANT ? Node::null() : d_eq_class, qe );
  }
  m.d_matched = Node::null();
  Trace("matching") << this << " " << d_match_pattern << " get next match " << m << " in eq class " << d_eq_class << std::endl;
  bool success = false;
  Node t;
  do{
    //get the next candidate term t
    t = d_cg->getNextCandidate();
    Trace("matching-debug2") << "Matching candidate : " << t << std::endl;
    //if t not null, try to fit it into match m
    if( !t.isNull() && t.getType()==d_match_pattern.getType() ){
      success = getMatch( f, t, m, qe );
    }
  }while( !success && !t.isNull() );
  m.d_matched = t;
  if( !success ){
    Trace("matching") << this << " failed, reset " << d_eq_class << std::endl;
    //we failed, must reset
    reset( d_eq_class.getKind()==INST_CONSTANT ? Node::null() : d_eq_class, qe );
  }
  return success;
}



int InstMatchGenerator::addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe ){
  //try to add instantiation for each match produced
  int addedLemmas = 0;
  InstMatch m( f );
  while( getNextMatch( f, m, qe ) ){
    if( !d_active_add ){
      m.add( baseMatch );
      if( qe->addInstantiation( f, m ) ){
        addedLemmas++;
        if( qe->d_optInstLimitActive && qe->d_optInstLimit<=0 ){
          return addedLemmas;
        }
      }
    }else{
      addedLemmas++;
    }
    m.clear();
  }
  //return number of lemmas added
  return addedLemmas;
}

int InstMatchGenerator::addTerm( Node f, Node t, QuantifiersEngine* qe ){
  Assert( options::eagerInstQuant() );
  if( !d_match_pattern.isNull() ){
    InstMatch m( f );
    if( getMatch( f, t, m, qe ) ){
      if( qe->addInstantiation( f, m ) ){
        return 1;
      }
    }
  }else{
    for( int i=0; i<(int)d_children.size(); i++ ){
      d_children[i]->addTerm( f, t, qe );
    }
  }
  return 0;
}


InstMatchGenerator* InstMatchGenerator::mkInstMatchGenerator( Node pat, QuantifiersEngine* qe ) {
  std::vector< Node > pats;
  pats.push_back( pat );
  return mkInstMatchGenerator( pats, qe );
}

InstMatchGenerator* InstMatchGenerator::mkInstMatchGenerator( std::vector< Node >& pats, QuantifiersEngine* qe ) {
  size_t pCounter = 0;
  InstMatchGenerator* prev = NULL;
  InstMatchGenerator* oinit = NULL;
  while( pCounter<pats.size() ){
    size_t counter = 0;
    std::vector< InstMatchGenerator* > gens;
    InstMatchGenerator* init = new InstMatchGenerator(pats[pCounter]);
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
      curr->initialize(qe, gens);
      prev = curr;
      counter++;
    }
    pCounter++;
  }
  return oinit;
}

/** constructors */
InstMatchGeneratorMulti::InstMatchGeneratorMulti( Node f, std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption ) :
d_f( f ){
  Debug("smart-multi-trigger") << "Making smart multi-trigger for " << f << std::endl;
  std::map< Node, std::vector< Node > > var_contains;
  qe->getTermDatabase()->getVarContains( f, pats, var_contains );
  //convert to indicies
  for( std::map< Node, std::vector< Node > >::iterator it = var_contains.begin(); it != var_contains.end(); ++it ){
    Debug("smart-multi-trigger") << "Pattern " << it->first << " contains: ";
    for( int i=0; i<(int)it->second.size(); i++ ){
      Debug("smart-multi-trigger") << it->second[i] << " ";
      int index = it->second[i].getAttribute(InstVarNumAttribute());
      d_var_contains[ it->first ].push_back( index );
      d_var_to_node[ index ].push_back( it->first );
    }
    Debug("smart-multi-trigger") << std::endl;
  }
  for( int i=0; i<(int)pats.size(); i++ ){
    Node n = pats[i];
    //make the match generator
    d_children.push_back( InstMatchGenerator::mkInstMatchGenerator( n, qe ) );
    //compute unique/shared variables
    std::vector< int > unique_vars;
    std::map< int, bool > shared_vars;
    int numSharedVars = 0;
    for( int j=0; j<(int)d_var_contains[n].size(); j++ ){
      if( d_var_to_node[ d_var_contains[n][j] ].size()==1 ){
        Debug("smart-multi-trigger") << "Var " << d_var_contains[n][j] << " is unique to " << pats[i] << std::endl;
        unique_vars.push_back( d_var_contains[n][j] );
      }else{
        shared_vars[ d_var_contains[n][j] ] = true;
        numSharedVars++;
      }
    }
    //we use the latest shared variables, then unique variables
    std::vector< int > vars;
    int index = i==0 ? (int)(pats.size()-1) : (i-1);
    while( numSharedVars>0 && index!=i ){
      for( std::map< int, bool >::iterator it = shared_vars.begin(); it != shared_vars.end(); ++it ){
        if( it->second ){
          if( std::find( d_var_contains[ pats[index] ].begin(), d_var_contains[ pats[index] ].end(), it->first )!=
              d_var_contains[ pats[index] ].end() ){
            vars.push_back( it->first );
            shared_vars[ it->first ] = false;
            numSharedVars--;
          }
        }
      }
      index = index==0 ? (int)(pats.size()-1) : (index-1);
    }
    vars.insert( vars.end(), unique_vars.begin(), unique_vars.end() );
    Debug("smart-multi-trigger") << "   Index[" << i << "]: ";
    for( int i=0; i<(int)vars.size(); i++ ){
      Debug("smart-multi-trigger") << vars[i] << " ";
    }
    Debug("smart-multi-trigger") << std::endl;
    //make ordered inst match trie
    InstMatchTrie::ImtIndexOrder* imtio = new InstMatchTrie::ImtIndexOrder;
    imtio->d_order.insert( imtio->d_order.begin(), vars.begin(), vars.end() );
    d_children_trie.push_back( InstMatchTrieOrdered( imtio ) );
  }

}

/** reset instantiation round (call this whenever equivalence classes have changed) */
void InstMatchGeneratorMulti::resetInstantiationRound( QuantifiersEngine* qe ){
  for( int i=0; i<(int)d_children.size(); i++ ){
    d_children[i]->resetInstantiationRound( qe );
  }
}

/** reset, eqc is the equivalence class to search in (any if eqc=null) */
void InstMatchGeneratorMulti::reset( Node eqc, QuantifiersEngine* qe ){
  for( int i=0; i<(int)d_children.size(); i++ ){
    d_children[i]->reset( eqc, qe );
  }
}

int InstMatchGeneratorMulti::addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe ){
  int addedLemmas = 0;
  Debug("smart-multi-trigger") << "Process smart multi trigger" << std::endl;
  for( int i=0; i<(int)d_children.size(); i++ ){
    Debug("smart-multi-trigger") << "Calculate matches " << i << std::endl;
    std::vector< InstMatch > newMatches;
    InstMatch m( f );
    while( d_children[i]->getNextMatch( f, m, qe ) ){
      //m.makeRepresentative( qe );
      newMatches.push_back( InstMatch( &m ) );
      m.clear();
    }
    Debug("smart-multi-trigger") << "Made " << newMatches.size() << " new matches for index " << i << std::endl;
    for( int j=0; j<(int)newMatches.size(); j++ ){
      processNewMatch( qe, newMatches[j], i, addedLemmas );
    }
  }
  return addedLemmas;
}

void InstMatchGeneratorMulti::processNewMatch( QuantifiersEngine* qe, InstMatch& m, int fromChildIndex, int& addedLemmas ){
  //see if these produce new matches
  d_children_trie[fromChildIndex].addInstMatch( qe, d_f, m );
  //possibly only do the following if we know that new matches will be produced?
  //the issue is that instantiations are filtered in quantifiers engine, and so there is no guarentee that
  // we can safely skip the following lines, even when we have already produced this match.
  Debug("smart-multi-trigger") << "Child " << fromChildIndex << " produced match " << m << std::endl;
  //process new instantiations
  int childIndex = (fromChildIndex+1)%(int)d_children.size();
  std::vector< IndexedTrie > unique_var_tries;
  processNewInstantiations( qe, m, addedLemmas, d_children_trie[childIndex].getTrie(),
                            unique_var_tries, 0, childIndex, fromChildIndex, true );
}

void InstMatchGeneratorMulti::processNewInstantiations( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas, InstMatchTrie* tr,
                                                        std::vector< IndexedTrie >& unique_var_tries,
                                                        int trieIndex, int childIndex, int endChildIndex, bool modEq ){
  if( childIndex==endChildIndex ){
    //now, process unique variables
    processNewInstantiations2( qe, m, addedLemmas, unique_var_tries, 0 );
  }else if( trieIndex<(int)d_children_trie[childIndex].getOrdering()->d_order.size() ){
    int curr_index = d_children_trie[childIndex].getOrdering()->d_order[trieIndex];
    //Node curr_ic = qe->getTermDatabase()->getInstantiationConstant( d_f, curr_index );
    Node n = m.get( curr_index );
    if( n.isNull() ){
      //if( d_var_to_node[ curr_index ].size()==1 ){    //FIXME
      //  //unique variable(s), defer calculation
      //  unique_var_tries.push_back( IndexedTrie( std::pair< int, int >( childIndex, trieIndex ), tr ) );
      //  int newChildIndex = (childIndex+1)%(int)d_children.size();
      //  processNewInstantiations( qe, m, d_children_trie[newChildIndex].getTrie(), unique_var_tries,
      //                            0, newChildIndex, endChildIndex, modEq );
      //}else{
        //shared and non-set variable, add to InstMatch
        for( std::map< Node, InstMatchTrie >::iterator it = tr->d_data.begin(); it != tr->d_data.end(); ++it ){
          InstMatch mn( &m );
          mn.setValue( curr_index, it->first);
          processNewInstantiations( qe, mn, addedLemmas, &(it->second), unique_var_tries,
                                    trieIndex+1, childIndex, endChildIndex, modEq );
        }
      //}
    }else{
      //shared and set variable, try to merge
      std::map< Node, InstMatchTrie >::iterator it = tr->d_data.find( n );
      if( it!=tr->d_data.end() ){
        processNewInstantiations( qe, m, addedLemmas, &(it->second), unique_var_tries,
                                  trieIndex+1, childIndex, endChildIndex, modEq );
      }
      if( modEq ){
        //check modulo equality for other possible instantiations
        if( qe->getEqualityQuery()->getEngine()->hasTerm( n ) ){
          eq::EqClassIterator eqc( qe->getEqualityQuery()->getEngine()->getRepresentative( n ),
                                   qe->getEqualityQuery()->getEngine() );
          while( !eqc.isFinished() ){
            Node en = (*eqc);
            if( en!=n ){
              std::map< Node, InstMatchTrie >::iterator itc = tr->d_data.find( en );
              if( itc!=tr->d_data.end() ){
                processNewInstantiations( qe, m, addedLemmas, &(itc->second), unique_var_tries,
                                          trieIndex+1, childIndex, endChildIndex, modEq );
              }
            }
            ++eqc;
          }
        }
      }
    }
  }else{
    int newChildIndex = (childIndex+1)%(int)d_children.size();
    processNewInstantiations( qe, m, addedLemmas, d_children_trie[newChildIndex].getTrie(), unique_var_tries,
                              0, newChildIndex, endChildIndex, modEq );
  }
}

void InstMatchGeneratorMulti::processNewInstantiations2( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas,
                                                         std::vector< IndexedTrie >& unique_var_tries,
                                                         int uvtIndex, InstMatchTrie* tr, int trieIndex ){
  if( uvtIndex<(int)unique_var_tries.size() ){
    int childIndex = unique_var_tries[uvtIndex].first.first;
    if( !tr ){
      tr = unique_var_tries[uvtIndex].second;
      trieIndex = unique_var_tries[uvtIndex].first.second;
    }
    if( trieIndex<(int)d_children_trie[childIndex].getOrdering()->d_order.size() ){
      int curr_index = d_children_trie[childIndex].getOrdering()->d_order[trieIndex];
      //Node curr_ic = qe->getTermDatabase()->getInstantiationConstant( d_f, curr_index );
      //unique non-set variable, add to InstMatch
      for( std::map< Node, InstMatchTrie >::iterator it = tr->d_data.begin(); it != tr->d_data.end(); ++it ){
        InstMatch mn( &m );
        mn.setValue( curr_index, it->first);
        processNewInstantiations2( qe, mn, addedLemmas, unique_var_tries, uvtIndex, &(it->second), trieIndex+1 );
      }
    }else{
      processNewInstantiations2( qe, m, addedLemmas, unique_var_tries, uvtIndex+1 );
    }
  }else{
    //m is an instantiation
    if( qe->addInstantiation( d_f, m ) ){
      addedLemmas++;
      Debug("smart-multi-trigger") << "-> Produced instantiation " << m << std::endl;
    }
  }
}

int InstMatchGeneratorMulti::addTerm( Node f, Node t, QuantifiersEngine* qe ){
  Assert( options::eagerInstQuant() );
  int addedLemmas = 0;
  for( int i=0; i<(int)d_children.size(); i++ ){
    Node t_op = qe->getTermDatabase()->getOperator( t );
    if( ((InstMatchGenerator*)d_children[i])->d_match_pattern_op==t_op ){
      InstMatch m( f );
      //if it produces a match, then process it with the rest
      if( ((InstMatchGenerator*)d_children[i])->getMatch( f, t, m, qe ) ){
        processNewMatch( qe, m, i, addedLemmas );
      }
    }
  }
  return addedLemmas;
}

InstMatchGeneratorSimple::InstMatchGeneratorSimple( Node f, Node pat ) : d_f( f ), d_match_pattern( pat ) {
  for( unsigned i=0; i<d_match_pattern.getNumChildren(); i++ ){
    if( d_match_pattern[i].getKind()==INST_CONSTANT ){
      d_var_num[i] = d_match_pattern[i].getAttribute(InstVarNumAttribute());
    }
  }
}

void InstMatchGeneratorSimple::resetInstantiationRound( QuantifiersEngine* qe ) {
  d_op = qe->getTermDatabase()->getOperator( d_match_pattern );
}

int InstMatchGeneratorSimple::addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe ){
  InstMatch m( f );
  m.add( baseMatch );
  int addedLemmas = 0;

  if( d_match_pattern.getType()==NodeManager::currentNM()->booleanType() ){
    for( int i=0; i<2; i++ ){
      addInstantiations( m, qe, addedLemmas, 0, &(qe->getTermDatabase()->d_pred_map_trie[i][ d_op ]) );
    }
  }else{
    addInstantiations( m, qe, addedLemmas, 0, &(qe->getTermDatabase()->d_func_map_trie[ d_op ]) );
  }
  return addedLemmas;
}

void InstMatchGeneratorSimple::addInstantiations( InstMatch& m, QuantifiersEngine* qe, int& addedLemmas, int argIndex, quantifiers::TermArgTrie* tat ){
  if( argIndex==(int)d_match_pattern.getNumChildren() ){
    //m is an instantiation
    if( qe->addInstantiation( d_f, m ) ){
      addedLemmas++;
      Debug("simple-trigger") << "-> Produced instantiation " << m << std::endl;
    }
  }else{
    if( d_match_pattern[argIndex].getKind()==INST_CONSTANT ){
      int v = d_var_num[argIndex];
      for( std::map< Node, quantifiers::TermArgTrie >::iterator it = tat->d_data.begin(); it != tat->d_data.end(); ++it ){
        Node t = it->first;
        Node prev = m.get( v );
        if( ( prev.isNull() || prev==t ) && d_match_pattern[argIndex].getType()==t.getType() ){
          m.setValue( v, t);
          addInstantiations( m, qe, addedLemmas, argIndex+1, &(it->second) );
          m.setValue( v, prev);
        }
      }
    }else{
      Node r = qe->getEqualityQuery()->getRepresentative( d_match_pattern[argIndex] );
      std::map< Node, quantifiers::TermArgTrie >::iterator it = tat->d_data.find( r );
      if( it!=tat->d_data.end() ){
        addInstantiations( m, qe, addedLemmas, argIndex+1, &(it->second) );
      }
    }
  }
}

int InstMatchGeneratorSimple::addTerm( Node f, Node t, QuantifiersEngine* qe ){
  Assert( options::eagerInstQuant() );
  InstMatch m( f );
  for( int i=0; i<(int)t.getNumChildren(); i++ ){
    if( d_match_pattern[i].getKind()==INST_CONSTANT ){
      m.setValue(d_var_num[i], t[i]);
    }else if( !qe->getEqualityQuery()->areEqual( d_match_pattern[i], t[i] ) ){
      return 0;
    }
  }
  return qe->addInstantiation( f, m ) ? 1 : 0;
}

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

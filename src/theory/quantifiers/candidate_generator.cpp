/*********************                                                        */
/*! \file candidate_generator.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of theory uf candidate generator class
 **/

#include "theory/quantifiers/candidate_generator.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;

bool CandidateGenerator::isLegalCandidate( Node n ){
  return ( !n.getAttribute(NoMatchAttribute()) && ( !options::cbqi() || !quantifiers::TermDb::hasInstConstAttr(n) ) );
}

void CandidateGeneratorQueue::addCandidate( Node n ) {
  if( isLegalCandidate( n ) ){
    d_candidates.push_back( n );
  }
}

void CandidateGeneratorQueue::reset( Node eqc ){
  if( d_candidate_index>0 ){
    d_candidates.erase( d_candidates.begin(), d_candidates.begin() + d_candidate_index );
    d_candidate_index = 0;
  }
  if( !eqc.isNull() ){
    d_candidates.push_back( eqc );
  }
}
Node CandidateGeneratorQueue::getNextCandidate(){
  if( d_candidate_index<(int)d_candidates.size() ){
    Node n = d_candidates[d_candidate_index];
    d_candidate_index++;
    return n;
  }else{
    d_candidate_index = 0;
    d_candidates.clear();
    return Node::null();
  }
}

CandidateGeneratorQE::CandidateGeneratorQE( QuantifiersEngine* qe, Node op ) :
  d_op( op ), d_qe( qe ), d_term_iter( -1 ){
  Assert( !d_op.isNull() );
}
void CandidateGeneratorQE::resetInstantiationRound(){
  d_term_iter_limit = d_qe->getTermDatabase()->d_op_map[d_op].size();
}

void CandidateGeneratorQE::reset( Node eqc ){
  d_term_iter = 0;
  if( eqc.isNull() ){
    d_using_term_db = true;
  }else{
    //create an equivalence class iterator in eq class eqc
    d_eqc.clear();
    d_qe->getEqualityQuery()->getEquivalenceClass( eqc, d_eqc );
    d_using_term_db = false;
  }
}

Node CandidateGeneratorQE::getNextCandidate(){
  if( d_term_iter>=0 ){
    if( d_using_term_db ){
      //get next candidate term in the uf term database
      while( d_term_iter<d_term_iter_limit ){
        Node n = d_qe->getTermDatabase()->d_op_map[d_op][d_term_iter];
        d_term_iter++;
        if( isLegalCandidate( n ) ){
          return n;
        }
      }
    }else{
      while( d_term_iter<(int)d_eqc.size() ){
        Node n = d_eqc[d_term_iter];
        d_term_iter++;
        if( n.hasOperator() && n.getOperator()==d_op ){
          if( isLegalCandidate( n ) ){
            return n;
          }
        }
      }
    }
  }
  return Node::null();
}

//CandidateGeneratorQEDisequal::CandidateGeneratorQEDisequal( QuantifiersEngine* qe, Node eqc ) :
//  d_qe( qe ), d_eq_class( eqc ){
//  d_eci = NULL;
//}
//void CandidateGeneratorQEDisequal::resetInstantiationRound(){
//
//}
////we will iterate over all terms that are disequal from eqc
//void CandidateGeneratorQEDisequal::reset( Node eqc ){
//  //Assert( !eqc.isNull() );
//  ////begin iterating over equivalence classes that are disequal from eqc
//  //d_eci = d_ith->getEquivalenceClassInfo( eqc );
//  //if( d_eci ){
//  //  d_eqci_iter = d_eci->d_disequal.begin();
//  //}
//}
//Node CandidateGeneratorQEDisequal::getNextCandidate(){
//  //if( d_eci ){
//  //  while( d_eqci_iter != d_eci->d_disequal.end() ){
//  //    if( (*d_eqci_iter).second ){
//  //      //we have an equivalence class that is disequal from eqc
//  //      d_cg->reset( (*d_eqci_iter).first );
//  //      Node n = d_cg->getNextCandidate();
//  //      //if there is a candidate in this equivalence class, return it
//  //      if( !n.isNull() ){
//  //        return n;
//  //      }
//  //    }
//  //    ++d_eqci_iter;
//  //  }
//  //}
//  return Node::null();
//}


CandidateGeneratorQELitEq::CandidateGeneratorQELitEq( QuantifiersEngine* qe, Node mpat ) :
  d_match_pattern( mpat ), d_qe( qe ){

}
void CandidateGeneratorQELitEq::resetInstantiationRound(){

}
void CandidateGeneratorQELitEq::reset( Node eqc ){
  d_eq = eq::EqClassesIterator( d_qe->getEqualityQuery()->getEngine() );
}
Node CandidateGeneratorQELitEq::getNextCandidate(){
  while( !d_eq.isFinished() ){
    Node n = (*d_eq);
    ++d_eq;
    if( n.getType()==d_match_pattern[0].getType() ){
      //an equivalence class with the same type as the pattern, return reflexive equality
      return NodeManager::currentNM()->mkNode( d_match_pattern.getKind(), n, n );
    }
  }
  return Node::null();
}


CandidateGeneratorQELitDeq::CandidateGeneratorQELitDeq( QuantifiersEngine* qe, Node mpat ) :
  d_match_pattern( mpat ), d_qe( qe ){

}
void CandidateGeneratorQELitDeq::resetInstantiationRound(){

}
void CandidateGeneratorQELitDeq::reset( Node eqc ){
  Node false_term = d_qe->getEqualityQuery()->getEngine()->getRepresentative( NodeManager::currentNM()->mkConst<bool>(false) );
  d_eqc_false = eq::EqClassIterator( false_term, d_qe->getEqualityQuery()->getEngine() );
}
Node CandidateGeneratorQELitDeq::getNextCandidate(){
  //get next candidate term in equivalence class
  while( !d_eqc_false.isFinished() ){
    Node n = (*d_eqc_false);
    ++d_eqc_false;
    if( n.getKind()==d_match_pattern.getKind() ){
      //found an iff or equality, try to match it
      //DO_THIS: cache to avoid redundancies?
      //DO_THIS: do we need to try the symmetric equality for n?  or will it also exist in the eq class of false?
      return n;
    }
  }
  return Node::null();
}


CandidateGeneratorQEAll::CandidateGeneratorQEAll( QuantifiersEngine* qe, Node mpat ) :
  d_match_pattern( mpat ), d_qe( qe ){

}

void CandidateGeneratorQEAll::resetInstantiationRound() {

}

void CandidateGeneratorQEAll::reset( Node eqc ) {
  d_eq = eq::EqClassesIterator( d_qe->getEqualityQuery()->getEngine() );
}

Node CandidateGeneratorQEAll::getNextCandidate() {
  while( !d_eq.isFinished() ){
    Node n = (*d_eq);
    ++d_eq;
    if( n.getType()==d_match_pattern.getType() ){
      //an equivalence class with the same type as the pattern, return it
      return n;
    }
  }
  return Node::null();
}

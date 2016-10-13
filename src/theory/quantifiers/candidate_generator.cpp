/*********************                                                        */
/*! \file candidate_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of theory uf candidate generator class
 **/

#include "options/quantifiers_options.h"
#include "theory/quantifiers/candidate_generator.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;

bool CandidateGenerator::isLegalCandidate( Node n ){
  return d_qe->getTermDatabase()->isTermActive( n ) && ( !options::cbqi() || !quantifiers::TermDb::hasInstConstAttr(n) );
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

CandidateGeneratorQE::CandidateGeneratorQE( QuantifiersEngine* qe, Node pat ) :
CandidateGenerator( qe ), d_term_iter( -1 ){
  d_op = qe->getTermDatabase()->getMatchOperator( pat );
  Assert( !d_op.isNull() );
  d_op_arity = pat.getNumChildren();
}

void CandidateGeneratorQE::resetInstantiationRound(){
  d_term_iter_limit = d_qe->getTermDatabase()->getNumGroundTerms( d_op );
}

void CandidateGeneratorQE::reset( Node eqc ){
  d_term_iter = 0;
  if( eqc.isNull() ){
    d_mode = cand_term_db;
  }else{
    if( isExcludedEqc( eqc ) ){
      d_mode = cand_term_none;
    }else{
      eq::EqualityEngine* ee = d_qe->getEqualityQuery()->getEngine();
      if( ee->hasTerm( eqc ) ){
        quantifiers::TermArgTrie * tat = d_qe->getTermDatabase()->getTermArgTrie( eqc, d_op );
        if( tat ){
#if 1
          //create an equivalence class iterator in eq class eqc
          Node rep = ee->getRepresentative( eqc );
          d_eqc_iter = eq::EqClassIterator( rep, ee );
          d_mode = cand_term_eqc;
#else
          d_tindex.push_back( tat );
          d_tindex_iter.push_back( tat->d_data.begin() );
          d_mode = cand_term_tindex;
#endif     
        }else{
          d_mode = cand_term_none;
        }   
      }else{
        //the only match is this term itself
        d_n = eqc;
        d_mode = cand_term_ident;
      }
    }
  }
}
bool CandidateGeneratorQE::isLegalOpCandidate( Node n ) {
  if( n.hasOperator() ){
    if( isLegalCandidate( n ) ){
      return d_qe->getTermDatabase()->getMatchOperator( n )==d_op;
    }
  }
  return false;
}

Node CandidateGeneratorQE::getNextCandidate(){
  if( d_mode==cand_term_db ){
    Debug("cand-gen-qe") << "...get next candidate in tbd" << std::endl;
    //get next candidate term in the uf term database
    while( d_term_iter<d_term_iter_limit ){
      Node n = d_qe->getTermDatabase()->getGroundTerm( d_op, d_term_iter );
      d_term_iter++;
      if( isLegalCandidate( n ) ){
        if( d_qe->getTermDatabase()->hasTermCurrent( n ) ){
          if( d_exclude_eqc.empty() ){
            return n;
          }else{
            Node r = d_qe->getEqualityQuery()->getRepresentative( n );
            if( d_exclude_eqc.find( r )==d_exclude_eqc.end() ){
              Debug("cand-gen-qe") << "...returning " << n << std::endl;
              return n;
            }
          }
        }
      }
    }
  }else if( d_mode==cand_term_eqc ){
    Debug("cand-gen-qe") << "...get next candidate in eqc" << std::endl;
    while( !d_eqc_iter.isFinished() ){
      Node n = *d_eqc_iter;
      ++d_eqc_iter;
      if( isLegalOpCandidate( n ) ){
        Debug("cand-gen-qe") << "...returning " << n << std::endl;
        return n;
      }
    }
  }else if( d_mode==cand_term_tindex ){
    Debug("cand-gen-qe") << "...get next candidate in tindex " << d_op << " " << d_op_arity << std::endl;
    //increment the term index iterator
    if( !d_tindex.empty() ){
      //populate the vector
      while( d_tindex_iter.size()<=d_op_arity ){
        Assert( !d_tindex_iter.empty() );
        Assert( !d_tindex_iter.back()->second.d_data.empty() );
        d_tindex.push_back( &(d_tindex_iter.back()->second) );
        d_tindex_iter.push_back( d_tindex_iter.back()->second.d_data.begin() );
      }
      //get the current node
      Assert( d_tindex_iter.back()->second.hasNodeData() );
      Node n = d_tindex_iter.back()->second.getNodeData();
      Debug("cand-gen-qe") << "...returning " << n << std::endl;
      Assert( !n.isNull() );
      Assert( isLegalOpCandidate( n ) );
      //increment
      bool success = false;
      do{
        ++d_tindex_iter.back();
        if( d_tindex_iter.back()==d_tindex.back()->d_data.end() ){
          d_tindex.pop_back();
          d_tindex_iter.pop_back();
        }else{
          success = true;
        }
      }while( !success && !d_tindex.empty() );
      return n;   
    } 
  }else if( d_mode==cand_term_ident ){
    Debug("cand-gen-qe") << "...get next candidate identity" << std::endl;
    if( !d_n.isNull() ){
      Node n = d_n;
      d_n = Node::null();
      if( isLegalOpCandidate( n ) ){
        return n;
      }
    }
  }
  return Node::null();
}

CandidateGeneratorQELitEq::CandidateGeneratorQELitEq( QuantifiersEngine* qe, Node mpat ) :
  CandidateGenerator( qe ), d_match_pattern( mpat ){
  Assert( mpat.getKind()==EQUAL );
  for( unsigned i=0; i<2; i++ ){
    if( !quantifiers::TermDb::hasInstConstAttr(mpat[i]) ){
      d_match_gterm = mpat[i];
    }
  }
}
void CandidateGeneratorQELitEq::resetInstantiationRound(){

}
void CandidateGeneratorQELitEq::reset( Node eqc ){
  if( d_match_gterm.isNull() ){
    d_eq = eq::EqClassesIterator( d_qe->getEqualityQuery()->getEngine() );
  }else{
    d_do_mgt = true;
  }
}
Node CandidateGeneratorQELitEq::getNextCandidate(){
  if( d_match_gterm.isNull() ){
    while( !d_eq.isFinished() ){
      Node n = (*d_eq);
      ++d_eq;
      if( n.getType().isComparableTo( d_match_pattern[0].getType() ) ){
        //an equivalence class with the same type as the pattern, return reflexive equality
        return NodeManager::currentNM()->mkNode( d_match_pattern.getKind(), n, n );
      }
    }
  }else{
    if( d_do_mgt ){
      d_do_mgt = false;
      return NodeManager::currentNM()->mkNode( d_match_pattern.getKind(), d_match_gterm, d_match_gterm );
    }
  }
  return Node::null();
}


CandidateGeneratorQELitDeq::CandidateGeneratorQELitDeq( QuantifiersEngine* qe, Node mpat ) :
CandidateGenerator( qe ), d_match_pattern( mpat ){

  Assert( d_match_pattern.getKind()==EQUAL || d_match_pattern.getKind()==IFF );
  d_match_pattern_type = d_match_pattern[0].getType();
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
      if( n[0].getType().isComparableTo( d_match_pattern_type ) ){
        //found an iff or equality, try to match it
        //DO_THIS: cache to avoid redundancies?
        //DO_THIS: do we need to try the symmetric equality for n?  or will it also exist in the eq class of false?
        return n;
      }
    }
  }
  return Node::null();
}


CandidateGeneratorQEAll::CandidateGeneratorQEAll( QuantifiersEngine* qe, Node mpat ) :
  CandidateGenerator( qe ), d_match_pattern( mpat ){
  d_match_pattern_type = mpat.getType();
  Assert( mpat.getKind()==INST_CONSTANT );
  d_f = quantifiers::TermDb::getInstConstAttr( mpat );
  d_index = mpat.getAttribute(InstVarNumAttribute());
  d_firstTime = false;
}

void CandidateGeneratorQEAll::resetInstantiationRound() {

}

void CandidateGeneratorQEAll::reset( Node eqc ) {
  d_eq = eq::EqClassesIterator( d_qe->getEqualityQuery()->getEngine() );
  d_firstTime = true;
}

Node CandidateGeneratorQEAll::getNextCandidate() {
  while( !d_eq.isFinished() ){
    TNode n = (*d_eq);
    ++d_eq;
    if( n.getType().isComparableTo( d_match_pattern_type ) ){
      TNode nh = d_qe->getTermDatabase()->getEligibleTermInEqc( n );
      if( !nh.isNull() ){
        if( options::instMaxLevel()!=-1 || options::lteRestrictInstClosure() ){
          nh = d_qe->getEqualityQuery()->getInternalRepresentative( nh, d_f, d_index );
          //don't consider this if already the instantiation is ineligible
          if( !d_qe->getTermDatabase()->isTermEligibleForInstantiation( nh, d_f, false ) ){
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
    return d_qe->getTermDatabase()->getModelBasisTerm( d_match_pattern_type );
  }
  return Node::null();
}

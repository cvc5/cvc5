/*********************                                                        */
/*! \file theory_uf_candidate_generator.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of theory uf candidate generator class
 **/

#include "theory/uf/theory_uf_candidate_generator.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/quantifiers/term_database.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

namespace CVC4{
namespace theory{
namespace uf{
namespace inst{

CandidateGeneratorTheoryUf::CandidateGeneratorTheoryUf( InstantiatorTheoryUf* ith, Node op ) :
  d_op( op ), d_ith( ith ), d_term_iter( -2 ){
  Assert( !d_op.isNull() );
}
void CandidateGeneratorTheoryUf::resetInstantiationRound(){
  d_term_iter_limit = d_ith->getQuantifiersEngine()->getTermDatabase()->d_op_map[d_op].size();
}

void CandidateGeneratorTheoryUf::reset( Node eqc ){
  if( eqc.isNull() ){
    d_term_iter = 0;
  }else{
    //create an equivalence class iterator in eq class eqc
    if( ((TheoryUF*)d_ith->getTheory())->getEqualityEngine()->hasTerm( eqc ) ){
      eqc = ((TheoryUF*)d_ith->getTheory())->getEqualityEngine()->getRepresentative( eqc );
      d_eqc = eq::EqClassIterator( eqc, ((TheoryUF*)d_ith->getTheory())->getEqualityEngine() );
      d_retNode = Node::null();
    }else{
      d_retNode = eqc;

    }
    d_term_iter = -1;
  }
}

Node CandidateGeneratorTheoryUf::getNextCandidate(){
  if( d_term_iter>=0 ){
    //get next candidate term in the uf term database
    while( d_term_iter<d_term_iter_limit ){
      Node n = d_ith->getQuantifiersEngine()->getTermDatabase()->d_op_map[d_op][d_term_iter];
      d_term_iter++;
      if( isLegalCandidate( n ) ){
        return n;
      }
    }
  }else if( d_term_iter==-1 ){
    if( d_retNode.isNull() ){
      //get next candidate term in equivalence class
      while( !d_eqc.isFinished() ){
        Node n = (*d_eqc);
        ++d_eqc;
        if( n.getKind()==APPLY_UF && n.getOperator()==d_op ){
          if( isLegalCandidate( n ) ){
            return n;
          }
        }
      }
    }else{
      Node ret;
      if( d_retNode.hasOperator() && d_retNode.getOperator()==d_op ){
        ret = d_retNode;
      }
      d_term_iter = -2; //done returning matches
      return ret;
    }
  }
  return Node::null();
}


//CandidateGeneratorTheoryUfDisequal::CandidateGeneratorTheoryUfDisequal( InstantiatorTheoryUf* ith, Node eqc ) :
//  d_ith( ith ), d_eq_class( eqc ){
//  d_eci = NULL;
//}
//void CandidateGeneratorTheoryUfDisequal::resetInstantiationRound(){
//
//}
////we will iterate over all terms that are disequal from eqc
//void CandidateGeneratorTheoryUfDisequal::reset( Node eqc ){
//  //Assert( !eqc.isNull() );
//  ////begin iterating over equivalence classes that are disequal from eqc
//  //d_eci = d_ith->getEquivalenceClassInfo( eqc );
//  //if( d_eci ){
//  //  d_eqci_iter = d_eci->d_disequal.begin();
//  //}
//}
//Node CandidateGeneratorTheoryUfDisequal::getNextCandidate(){
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


CandidateGeneratorTheoryUfLitEq::CandidateGeneratorTheoryUfLitEq( InstantiatorTheoryUf* ith, Node mpat ) :
  d_match_pattern( mpat ), d_ith( ith ){

}
void CandidateGeneratorTheoryUfLitEq::resetInstantiationRound(){

}
void CandidateGeneratorTheoryUfLitEq::reset( Node eqc ){
  d_eq = eq::EqClassesIterator( ((TheoryUF*)d_ith->getTheory())->getEqualityEngine() );
}
Node CandidateGeneratorTheoryUfLitEq::getNextCandidate(){
  while( d_eq.isFinished() ){
    Node n = (*d_eq);
    ++d_eq;
    if( n.getType()==d_match_pattern[0].getType() ){
      //an equivalence class with the same type as the pattern, return reflexive equality
      return NodeManager::currentNM()->mkNode( d_match_pattern.getKind(), n, n );
    }
  }
  return Node::null();
}


CandidateGeneratorTheoryUfLitDeq::CandidateGeneratorTheoryUfLitDeq( InstantiatorTheoryUf* ith, Node mpat ) :
  d_match_pattern( mpat ), d_ith( ith ){

}
void CandidateGeneratorTheoryUfLitDeq::resetInstantiationRound(){

}
void CandidateGeneratorTheoryUfLitDeq::reset( Node eqc ){
  Node false_term = ((TheoryUF*)d_ith->getTheory())->getEqualityEngine()->getRepresentative(
                      NodeManager::currentNM()->mkConst<bool>(false) );
  d_eqc_false = eq::EqClassIterator( false_term, ((TheoryUF*)d_ith->getTheory())->getEqualityEngine() );
}
Node CandidateGeneratorTheoryUfLitDeq::getNextCandidate(){
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

}
}
}
}

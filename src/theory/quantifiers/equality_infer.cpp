/*********************                                                        */
/*! \file equality_infer.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief  Method for inferring equalities between arithmetic equivalence classes, 
 **         inspired by "A generalization of Shostak's method for combining decision procedures" Barrett et al. Figure 1.
 **
 **/

#include "theory/quantifiers/equality_infer.h"
#include "theory/quantifiers/quant_util.h"
#include "context/context_mm.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

EqualityInference::EqcInfo::EqcInfo(context::Context* c) : d_rep( c ), d_valid( c, false ), d_rep_exp(c) {

}

EqualityInference::EqualityInference( context::Context* c, bool trackExp ) : 
d_c( c ), d_trackExplain( trackExp ), d_elim_vars( c ), d_rep_to_eqc( c ), d_uselist( c ), d_pending_merges( c ), d_pending_merge_exp( c ){
  d_one = NodeManager::currentNM()->mkConst( Rational( 1 ) );
}

EqualityInference::~EqualityInference(){
  for( std::map< Node, EqcInfo * >::iterator it = d_eqci.begin(); it != d_eqci.end(); ++it ){
    delete it->second;
  }
}

void EqualityInference::eqNotifyNewClass(TNode t) {
  if( t.getType().isReal() ){
    Trace("eq-infer") << "Notify equivalence class : " << t << std::endl;
    EqcInfo * eqci;
    std::map< Node, EqcInfo * >::iterator itec = d_eqci.find( t );
    if( itec==d_eqci.end() ){
      eqci = new EqcInfo( d_c );
      d_eqci[t] = eqci;
    }else{
      eqci = itec->second;
    }
    std::map< Node, Node > msum;
    if( QuantArith::getMonomialSum( t, msum ) ){
      eqci->d_valid = true;
      bool changed = false;
      std::vector< Node > children;
      for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ) {
        Node n = it->first;
        if( !n.isNull() ){
          NodeMap::const_iterator itv = d_elim_vars.find( n );
          if( itv!=d_elim_vars.end() ){
            changed = true;
            n = (*itv).second;
          }
          if( it->second.isNull() ){
            children.push_back( n );
          }else{
            children.push_back( NodeManager::currentNM()->mkNode( MULT, it->second, n ) );
          }
        }else{
          children.push_back( it->second );
        }
      }
      Node r;
      bool mvalid = true;
      if( changed ){
        r = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( PLUS, children );
        r = Rewriter::rewrite( r );
        msum.clear();
        if( !QuantArith::getMonomialSum( r, msum ) ){
          mvalid = false;
        }
      }else{
        r = t;
      }
      Trace("eq-infer") << "...value is " << r << std::endl;
      setEqcRep( t, r, eqci );
      if( mvalid ){
        for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
          if( !it->first.isNull() ){
            addToUseList( it->first, t );
          }
        }        
      }
    }else{
      eqci->d_valid = false;
    }
  }
}

void EqualityInference::addToUseList( Node used, Node eqc ) {
  NodeListMap::iterator ul_i = d_uselist.find( used );
  NodeList* ul;
  if( ul_i != d_uselist.end() ){
    ul = (*ul_i).second;
  }else{
    ul = new(d_c->getCMM()) NodeList( true, d_c, false, context::ContextMemoryAllocator<TNode>(d_c->getCMM()) );
    d_uselist.insertDataFromContextMemory( used, ul );
  }
  Trace("eq-infer-debug") << "      add to use list : " << used << " -> " << eqc << std::endl;
  (*ul).push_back( eqc );
}

void EqualityInference::setEqcRep( Node t, Node r, EqcInfo * eqci ) {
  eqci->d_rep = r;
  NodeMap::const_iterator itr = d_rep_to_eqc.find( r );
  if( itr==d_rep_to_eqc.end() ){
    d_rep_to_eqc[r] = t;
  }else{
    //merge two equivalence classes
    Node t2 = (*itr).second;
    //check if it is valid
    std::map< Node, EqcInfo * >::iterator itc = d_eqci.find( t2 );
    if( itc!=d_eqci.end() && itc->second->d_valid ){
      Trace("eq-infer") << "Infer two equivalence classes are equal : " << t << " " << t2 << std::endl;
      Trace("eq-infer") << "  since they both normalize to : " << r << std::endl;
      d_pending_merges.push_back( t.eqNode( t2 ) );
      if( d_trackExplain ){
        //TODO
        d_pending_merge_exp.push_back( t.eqNode( t2 ) );
      }
    }
  }
}

void EqualityInference::eqNotifyMerge(TNode t1, TNode t2) {
  Assert( !t1.isNull() );
  Assert( !t2.isNull() );
  std::map< Node, EqcInfo * >::iterator itv1 = d_eqci.find( t1 );
  if( itv1!=d_eqci.end() ){
    std::map< Node, EqcInfo * >::iterator itv2 = d_eqci.find( t2 );
    if( itv2!=d_eqci.end() ){
      Trace("eq-infer") << "Merge equivalence classes : " << t2 << " into " << t1 << std::endl;
      Node tr1 = itv1->second->d_rep;
      Node tr2 = itv2->second->d_rep;
      itv2->second->d_valid = false;
      Trace("eq-infer") << "Representatives : " << tr2 << " into " << tr1 << std::endl;
      if( tr1!=tr2 ){
        Node eq = tr1.eqNode( tr2 );
        std::map< Node, Node > msum;
        if( QuantArith::getMonomialSumLit( eq, msum ) ){
          Node v_solve;
          //solve for variables with no coefficient
          for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ) {
            Node n = it->first;
            if( !n.isNull() && it->second.isNull() ){
              v_solve = n;
              break;
            }
          }
          if( !v_solve.isNull() ){
            //solve for v_solve
            Node veq;
            if( QuantArith::isolate( v_solve, msum, veq, kind::EQUAL, true )==1 ){
              Node v_value = veq[1];
              Trace("eq-infer") << "...solved " << v_solve << " == " << v_value << std::endl;
              Assert( d_elim_vars.find( v_solve )==d_elim_vars.end() );
              d_elim_vars[v_solve] = v_value;
              
              std::vector< Node > new_use;
              for( std::map< Node, Node >::iterator itmm = msum.begin(); itmm != msum.end(); ++itmm ){
                Node n = itmm->first;
                if( !n.isNull() && n!=v_solve ){
                  new_use.push_back( n );
                }
              }
              
              //go through all equivalence classes that may refer to v_solve
              std::map< Node, bool > processed;
              NodeListMap::iterator ul_i = d_uselist.find( v_solve );
              if( ul_i != d_uselist.end() ){
                NodeList* ul = (*ul_i).second;
                Trace("eq-infer-debug") << "      use list size = " << ul->size() << std::endl;
                for( unsigned j=0; j<ul->size(); j++ ){
                  Node r = (*ul)[j];
                  if( processed.find( r )==processed.end() ){
                    processed[r] = true;
                    std::map< Node, EqcInfo * >::iterator itt = d_eqci.find( r );
                    if( itt!=d_eqci.end() && itt->second->d_valid ){
                      std::map< Node, Node > msum2;
                      if( QuantArith::getMonomialSum( itt->second->d_rep.get(), msum2 ) ){
                        std::map< Node, Node >::iterator itm = msum2.find( v_solve );
                        if( itm!=msum2.end() ){
                          //substitute in solved form
                          std::map< Node, Node >::iterator itm2 = msum2.find( v_value );
                          if( itm2 == msum2.end() ){
                            msum2[v_value] = itm->second;
                          }else{
                            msum2[v_value] = NodeManager::currentNM()->mkNode( PLUS, itm2->second.isNull() ? d_one : itm2->second, 
                                                                                    itm->second.isNull() ? d_one : itm->second );
                          }
                          msum2.erase( itm );
                          Node rr = QuantArith::mkNode( msum2 );
                          rr = Rewriter::rewrite( rr );
                          Trace("eq-infer") << "......update " << itt->first << " => " << rr << std::endl;
                          setEqcRep( itt->first, rr, itt->second );
                          //update use list
                          for( unsigned i=0; i<new_use.size(); i++ ){
                            addToUseList( new_use[i], r );
                          }
                        }
                      }else{
                        itt->second->d_valid = false;
                      }
                    }
                  }
                }
              }
              Trace("eq-infer") << "...finished solved." << std::endl;
            }
          }
        }
      }
    }else{
      //no information to merge
    }
  }else{
    //carry information (this might happen for non-linear t1 and linear t2?)
    std::map< Node, EqcInfo * >::iterator itv2 = d_eqci.find( t2 );
    if( itv2!=d_eqci.end() ){
      d_eqci[t1] = d_eqci[t2];
      d_eqci[t2] = NULL;
    }
  }
}

Node EqualityInference::getPendingMergeExplanation( unsigned i ) { 
  Assert( d_trackExplain );
  return d_pending_merge_exp[i]; 
}  

}

/*********************                                                        */
/*! \file equality_infer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief  Method for inferring equalities between arithmetic equivalence classes, 
 **         inspired by "A generalization of Shostak's method for combining decision procedures" Barrett et al. Figure 1.
 **
 **/

#include "theory/quantifiers/equality_infer.h"

#include "context/context_mm.h"
#include "theory/rewriter.h"
#include "theory/arith/arith_msum.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

EqualityInference::EqcInfo::EqcInfo(context::Context* c) : d_rep( c ), d_valid( c, false ), d_solved( c, false ), d_master(c)
//, d_rep_exp(c), d_uselist(c) 
{

}

EqualityInference::EqualityInference( context::Context* c, bool trackExp ) : 
d_c( c ), d_trackExplain( trackExp ), d_elim_vars( c ), 
d_rep_to_eqc( c ), d_rep_exp( c ), d_uselist( c ), d_pending_merges( c ), d_pending_merge_exp( c ){
  d_one = NodeManager::currentNM()->mkConst( Rational( 1 ) );
  d_true = NodeManager::currentNM()->mkConst( true );
}

EqualityInference::~EqualityInference(){
  for( std::map< Node, EqcInfo * >::iterator it = d_eqci.begin(); it != d_eqci.end(); ++it ){
    delete it->second;
  }
}

void EqualityInference::addToExplanation( std::vector< Node >& exp, Node e ) {
  if( std::find( exp.begin(), exp.end(), e )==exp.end() ){
    Trace("eq-infer-debug2") << "......add to explanation " << e << std::endl;
    exp.push_back( e );
  }
}

void EqualityInference::addToExplanationEqc( std::vector< Node >& exp, Node eqc ) {
  NodeIntMap::iterator re_i = d_rep_exp.find( eqc );
  if( re_i!=d_rep_exp.end() ){
    for( int i=0; i<(*re_i).second; i++ ){
      addToExplanation( exp, d_rep_exp_data[eqc][i] );
    }
  }
  //for( unsigned i=0; i<d_eqci[n]->d_rep_exp.size(); i++ ){
  //  addToExplanation( exp, d_eqci[n]->d_rep_exp[i] );
  //}
}

void EqualityInference::addToExplanationEqc( Node eqc, std::vector< Node >& exp_to_add ) {
  NodeIntMap::iterator re_i = d_rep_exp.find( eqc );
  int n_re = 0;
  if( re_i != d_rep_exp.end() ){
    n_re = (*re_i).second;
  }
  d_rep_exp[eqc] = n_re + exp_to_add.size();
  for( unsigned i=0; i<exp_to_add.size(); i++ ){
    if( n_re<(int)d_rep_exp_data[eqc].size() ){
      d_rep_exp_data[eqc][n_re] = exp_to_add[i];
    }else{
      d_rep_exp_data[eqc].push_back( exp_to_add[i] );
    }
    n_re++;
  }
  //for( unsigned i=0; i<exp_to_add.size(); i++ ){
  //  eqci->d_rep_exp.push_back( exp_to_add[i] );
  //}
}

Node EqualityInference::getMaster( Node t, EqcInfo * eqc, bool& updated, Node new_m ) {
  if( !eqc->d_master.get().isNull() ){
    if( eqc->d_master.get()==t ){
      if( !new_m.isNull() && t!=new_m ){
        eqc->d_master = new_m;
        updated = true;
        return new_m;
      }else{
        return t;
      }
    }else{
      Assert(d_eqci.find(eqc->d_master.get()) != d_eqci.end());
      EqcInfo * eqc_m = d_eqci[eqc->d_master.get()];
      Node m = getMaster( eqc->d_master.get(), eqc_m, updated, new_m );
      eqc->d_master = m;
      return m;
    }
  }else{
    return Node::null();
  }
}

//update the internal "master" representative of the equivalence class, return true if the merge was non-redundant
bool EqualityInference::updateMaster( Node t1, Node t2, EqcInfo * eqc1, EqcInfo * eqc2 ) {
  bool updated = false;
  Node m1 = getMaster( t1, eqc1, updated );
  if( m1.isNull() ){
    eqc1->d_master = t2;
    if( eqc2->d_master.get().isNull() ){
      eqc2->d_master = t2;
    }
    return true;
  }else{
    updated = false;
    Node m2 = getMaster( t2, eqc2, updated, m1);
    if( m2.isNull() ){
      eqc2->d_master = m1;
      return true;
    }else{
      return updated;
    }
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
    Assert(!eqci->d_valid.get());
    if( !eqci->d_solved.get() ){
      //somewhat strange: t may not be in rewritten form    
      Node r = Rewriter::rewrite( t );
      std::map< Node, Node > msum;
      if (ArithMSum::getMonomialSum(r, msum))
      {
        Trace("eq-infer-debug2") << "...process monomial sum, size = " << msum.size() << std::endl;
        eqci->d_valid = true;
        bool changed = false;
        std::vector< Node > exp;
        std::vector< Node > children;
        for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ) {
          Trace("eq-infer-debug2") << "...process child " << it->first << ", " << it->second << std::endl;
          if( !it->first.isNull() ){
            Node n = it->first;
            BoolMap::const_iterator itv = d_elim_vars.find( n );
            if( itv!=d_elim_vars.end() ){
              changed = true;
              Assert(d_eqci.find(n) != d_eqci.end());
              Assert(n != t);
              Assert(d_eqci[n]->d_solved.get());
              Trace("eq-infer-debug2") << "......its solved form is " << d_eqci[n]->d_rep.get() << std::endl;
              if( d_trackExplain ){
                //track the explanation: justified by explanation for each substitution
                addToExplanationEqc( exp, n );
              }
              n = d_eqci[n]->d_rep;
              Assert(!n.isNull());
            }
            if( it->second.isNull() ){
              children.push_back( n );
            }else{
              children.push_back( NodeManager::currentNM()->mkNode( MULT, it->second, n ) );
            }
          }else{
            Assert(!it->second.isNull());
            children.push_back( it->second );
          }
        }
        Trace("eq-infer-debug2") << "...children size = " << children.size() << std::endl;
        bool mvalid = true;
        if( changed ){
          r = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( PLUS, children );
          Trace("eq-infer-debug2") << "...pre-rewrite : " << r << std::endl;
          r = Rewriter::rewrite( r );
          msum.clear();
          if (!ArithMSum::getMonomialSum(r, msum))
          {
            mvalid = false;
          }
        }
        Trace("eq-infer") << "...value is " << r << std::endl;
        setEqcRep( t, r, exp, eqci );
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
}

void EqualityInference::addToUseList( Node used, Node eqc ) {
#if 1
  NodeIntMap::iterator ul_i = d_uselist.find( used );
  int n_ul = 0;
  if( ul_i != d_uselist.end() ){
    n_ul = (*ul_i).second;
  }
  d_uselist[ used ] = n_ul + 1;
  Trace("eq-infer-debug") << "      add to use list : " << used << " -> " << eqc << std::endl;
  if( n_ul<(int)d_uselist_data[used].size() ){
    d_uselist_data[used][n_ul] = eqc;
  }else{
    d_uselist_data[used].push_back( eqc );  
  }
#else
  std::map< Node, EqcInfo * >::iterator itu = d_eqci.find( used );
  EqcInfo * eqci_used;
  if( itu==d_eqci.end() ){
    eqci_used = new EqcInfo( d_c );
    d_eqci[used] = eqci_used;
  }else{
    eqci_used = itu->second;
  }
  Trace("eq-infer-debug") << "      add to use list : " << used << " -> " << eqc << std::endl;
  eqci_used->d_uselist.push_back( eqc );
#endif
}

void EqualityInference::setEqcRep( Node t, Node r, std::vector< Node >& exp_to_add, EqcInfo * eqci ) {
  eqci->d_rep = r;
  if( d_trackExplain ){
    addToExplanationEqc( t, exp_to_add );
  }
  //if this is an active equivalence class
  if( eqci->d_valid.get() ){
    Trace("eq-infer-debug") << "Set eqc rep " << t << " -> " << r << std::endl;
    NodeMap::const_iterator itr = d_rep_to_eqc.find( r );
    if( itr==d_rep_to_eqc.end() ){
      d_rep_to_eqc[r] = t;
    }else{
      //merge two equivalence classes
      Node t2 = (*itr).second;
      //check if it is valid
      std::map< Node, EqcInfo * >::iterator itc = d_eqci.find( t2 );
      if( itc!=d_eqci.end() && itc->second->d_valid.get() ){
        //if we haven't already determined they should be merged
        if( updateMaster( t, t2, eqci, itc->second ) ){
          Trace("eq-infer") << "Infer two equivalence classes are equal : " << t << " " << t2 << std::endl;
          Trace("eq-infer") << "  since they both normalize to : " << r << std::endl;
          d_pending_merges.push_back( t.eqNode( t2 ) );
          if( d_trackExplain ){
            std::vector< Node > exp;
            for( unsigned j=0; j<2; j++ ){
              addToExplanationEqc( exp, j==0 ? t : t2 );
            }
            Node exp_n = exp.empty() ? d_true : ( exp.size()==1 ? exp[0] : NodeManager::currentNM()->mkNode( AND, exp ) );
            Trace("eq-infer") << "  explanation : " << exp_n << std::endl;
            d_pending_merge_exp.push_back( exp_n );
          }
        }
      }
    }
  }
}

void EqualityInference::eqNotifyMerge(TNode t1, TNode t2) {
  Assert(!t1.isNull());
  Assert(!t2.isNull());
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
        if (ArithMSum::getMonomialSumLit(eq, msum))
        {
          Node v_solve;
          //solve for variables with no coefficient
          if( Trace.isOn("eq-infer-debug2") ){
            Trace("eq-infer-debug2") << "Monomial sum : " << std::endl;
            for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ) {
              Trace("eq-infer-debug2") << "  " << it->first << " * " << it->second << std::endl;
            }
          }
          for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ) {
            Node n = it->first;
            if( !n.isNull() ){
              bool canSolve = false;
              if( it->second.isNull() ){
                canSolve = true;
              }else{
                //Assert( it->second.isConst() );
                Rational r = it->second.getConst<Rational>(); 
                canSolve = r.isOne() || r.isNegativeOne();
              }
              if( canSolve ){
                v_solve = n;
                break;
              }
            }
          }
          Trace("eq-infer-debug") << "solve for variable : " << v_solve << std::endl;
          if( !v_solve.isNull() ){
            //solve for v_solve
            Node veq;
            if (ArithMSum::isolate(v_solve, msum, veq, kind::EQUAL, true) == 1)
            {
              Node v_value = veq[1];
              Trace("eq-infer") << "...solved " << v_solve << " == " << v_value << std::endl;
              Assert(d_elim_vars.find(v_solve) == d_elim_vars.end());
              d_elim_vars[v_solve] = true;
              //store value in eqc info
              EqcInfo * eqci_solved;
              std::map< Node, EqcInfo * >::iterator itec = d_eqci.find( v_solve );
              if( itec==d_eqci.end() ){
                eqci_solved = new EqcInfo( d_c );
                d_eqci[v_solve] =  eqci_solved;
              }else{
                eqci_solved = itec->second;
              }
              eqci_solved->d_solved = true;
              eqci_solved->d_rep = v_value;
              //track the explanation
              std::vector< Node > exp;
              if( d_trackExplain ){
                //explanation is t1 = t2 + their explanations
                exp.push_back( t1.eqNode( t2 ) );
                for( unsigned i=0; i<2; i++ ){
                  addToExplanationEqc( exp, i==0 ? t1 : t2 );
                }
                if( Trace.isOn("eq-infer-debug") ){
                  Trace("eq-infer-debug") << "      explanation for solving " << v_solve << " is ";
                  for( unsigned i=0; i<exp.size(); i++ ){
                    Trace("eq-infer-debug") << exp[i] << " ";
                  }
                  Trace("eq-infer-debug") << std::endl;
                }
                addToExplanationEqc( v_solve, exp );
              }
             
              std::vector< Node > new_use;
              for( std::map< Node, Node >::iterator itmm = msum.begin(); itmm != msum.end(); ++itmm ){
                Node n = itmm->first;
                if( !n.isNull() && n!=v_solve ){
                  new_use.push_back( n );
                  addToUseList( n, v_solve );
                }
              }
              
              //go through all equivalence classes that may refer to v_solve
              std::map< Node, bool > processed;
              processed[v_solve] = true;
              NodeIntMap::iterator ul_i = d_uselist.find( v_solve );
              if( ul_i != d_uselist.end() ){
                int n_ul = (*ul_i).second;
                Trace("eq-infer-debug") << "      use list size = " << n_ul << std::endl;
                for( int j=0; j<n_ul; j++ ){
                  Node r = d_uselist_data[v_solve][j];
                //Trace("eq-infer-debug") << "      use list size = " << eqci_solved->d_uselist.size() << std::endl;
                //for( unsigned j=0; j<eqci_solved->d_uselist.size(); j++ ){
                //  Node r = eqci_solved->d_uselist[j];
                  if( processed.find( r )==processed.end() ){
                    processed[r] = true;
                    std::map< Node, EqcInfo * >::iterator itt = d_eqci.find( r );
                    if( itt!=d_eqci.end() && ( itt->second->d_valid || itt->second->d_solved ) ){
                      std::map< Node, Node > msum2;
                      if (ArithMSum::getMonomialSum(itt->second->d_rep.get(),
                                                    msum2))
                      {
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
                          Node rr = ArithMSum::mkNode(msum2);
                          rr = Rewriter::rewrite( rr );
                          Trace("eq-infer") << "......update " << itt->first << " => " << rr << std::endl;
                          setEqcRep( itt->first, rr, exp, itt->second );
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
  if( d_trackExplain ){
    return d_pending_merge_exp[i]; 
  }else{
    return d_pending_merges[i];
  }
}  

}

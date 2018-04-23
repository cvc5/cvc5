/*********************                                                        */
/*! \file theory_sets_private.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Sets theory implementation.
 **/

#include <algorithm>
#include "theory/sets/theory_sets_private.h"

#include "expr/emptyset.h"
#include "options/sets_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/sets/theory_sets.h"
#include "theory/sets/normal_form.h"
#include "theory/theory_model.h"
#include "util/result.h"
#include "theory/quantifiers/term_database.h"

#define AJR_IMPLEMENTATION

using namespace std;

namespace CVC4 {
namespace theory {
namespace sets {

TheorySetsPrivate::TheorySetsPrivate(TheorySets& external,
                                     context::Context* c,
                                     context::UserContext* u):
  d_rels(NULL),
  d_members(c),
  d_deq(c),
  d_deq_processed(u),
  d_keep(c),
  d_proxy(u),
  d_proxy_to_term(u),
  d_lemmas_produced(u),
  d_card_processed(u),
  d_var_elim(u),
  d_external(external),
  d_notify(*this),
  d_equalityEngine(d_notify, c, "theory::sets::ee", true),
  d_conflict(c)
{

  d_rels = new TheorySetsRels(c, u, &d_equalityEngine, &d_conflict, external);

  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
  d_zero = NodeManager::currentNM()->mkConst( Rational(0) );

  d_equalityEngine.addFunctionKind(kind::SINGLETON);
  d_equalityEngine.addFunctionKind(kind::UNION);
  d_equalityEngine.addFunctionKind(kind::INTERSECTION);
  d_equalityEngine.addFunctionKind(kind::SETMINUS);

  d_equalityEngine.addFunctionKind(kind::MEMBER);
  d_equalityEngine.addFunctionKind(kind::SUBSET);

  // If cardinality is on.
  d_equalityEngine.addFunctionKind(kind::CARD);

  d_card_enabled = false;
  d_rels_enabled = false;

}/* TheorySetsPrivate::TheorySetsPrivate() */

TheorySetsPrivate::~TheorySetsPrivate(){
  delete d_rels;
  for (std::pair<const Node, EqcInfo*>& current_pair : d_eqc_info) {
    delete current_pair.second;
  }
}/* TheorySetsPrivate::~TheorySetsPrivate() */


void TheorySetsPrivate::eqNotifyNewClass(TNode t) {
  if( t.getKind()==kind::SINGLETON || t.getKind()==kind::EMPTYSET ){
    EqcInfo * e = getOrMakeEqcInfo( t, true );
    e->d_singleton = t;
  }
  if( options::setsRelEager() ){
    d_rels->eqNotifyNewClass( t );
  }
}

void TheorySetsPrivate::eqNotifyPreMerge(TNode t1, TNode t2){

}

void TheorySetsPrivate::eqNotifyPostMerge(TNode t1, TNode t2){
  if( !d_conflict ){
    Trace("sets-prop-debug") << "Merge " << t1 << " and " << t2 << "..." << std::endl;
    Node s1, s2;
    EqcInfo * e2 = getOrMakeEqcInfo( t2 );
    if( e2 ){
      s2 = e2->d_singleton;
      EqcInfo * e1 = getOrMakeEqcInfo( t1 );
      Node s1;
      Trace("sets-prop-debug") << "Merging singletons..." << std::endl;
      if( e1 ){
        s1 = e1->d_singleton;
        if( !s1.isNull() && !s2.isNull() ){
          if( s1.getKind()==s2.getKind() ){
            Trace("sets-prop") << "Propagate eq inference : " << s1 << " == " << s2 << std::endl;
            //infer equality between elements of singleton
            Node exp = s1.eqNode( s2 );
            Node eq = s1[0].eqNode( s2[0] );
            d_keep.insert( exp );
            d_keep.insert( eq );
            assertFact( eq, exp );
          }else{
            //singleton equal to emptyset, conflict
            Trace("sets-prop") << "Propagate conflict : " << s1 << " == " << s2 << std::endl;
            conflict( s1, s2 );
            return;
          }
        }
      }else{
        //copy information
        e1 = getOrMakeEqcInfo( t1, true );
        e1->d_singleton.set( e2->d_singleton );
      }
    }
    //merge membership list
    Trace("sets-prop-debug") << "Copying membership list..." << std::endl;
    NodeIntMap::iterator mem_i2 = d_members.find( t2 );
    if( mem_i2 != d_members.end() ) {
      NodeIntMap::iterator mem_i1 = d_members.find( t1 );
      int n_members = 0;
      if( mem_i1 != d_members.end() ) {
        n_members = (*mem_i1).second;
      }
      for( int i=0; i<(*mem_i2).second; i++ ){
        Assert( i<(int)d_members_data[t2].size() && d_members_data[t2][i].getKind()==kind::MEMBER );
        Node m2 = d_members_data[t2][i];
        //check if redundant
        bool add = true;
        for( int j=0; j<n_members; j++ ){
          Assert( j<(int)d_members_data[t1].size() && d_members_data[t1][j].getKind()==kind::MEMBER );
          if( ee_areEqual( m2[0], d_members_data[t1][j][0] ) ){
            add = false;
            break;
          }
        }
        if( add ){
          if( !s1.isNull() && s2.isNull() ){
            Assert( m2[1].getType().isComparableTo( s1.getType() ) );
            Assert( ee_areEqual( m2[1], s1 ) );
            Node exp = NodeManager::currentNM()->mkNode( kind::AND, m2[1].eqNode( s1 ), m2 );
            if( s1.getKind()==kind::SINGLETON ){
              if( s1[0]!=m2[0] ){
                Node eq = s1[0].eqNode( m2[0] );
                d_keep.insert( exp );
                d_keep.insert( eq );
                Trace("sets-prop") << "Propagate eq-mem eq inference : " << exp << " => " << eq << std::endl;
                assertFact( eq, exp );
              }
            }else{
              //conflict
              Trace("sets-prop") << "Propagate eq-mem conflict : " << exp << std::endl;
              d_conflict = true;
              d_external.d_out->conflict( exp );
              return;
            }
          }
          if( n_members<(int)d_members_data[t1].size() ){
            d_members_data[t1][n_members] = m2;
          }else{
            d_members_data[t1].push_back( m2 );
          }
          n_members++;
        }
      }
      d_members[t1] = n_members;
    }
    if( options::setsRelEager() ){
      d_rels->eqNotifyPostMerge( t1, t2 );
    }
  }
}

void TheorySetsPrivate::eqNotifyDisequal(TNode t1, TNode t2, TNode reason){
  if( t1.getType().isSet() ){
    Node eq = t1.eqNode( t2 );
    if( d_deq.find( eq )==d_deq.end() ){
      d_deq[eq] = true;
    }
  }
}

TheorySetsPrivate::EqcInfo::EqcInfo( context::Context* c ) : d_singleton( c ){
  
}

TheorySetsPrivate::EqcInfo* TheorySetsPrivate::getOrMakeEqcInfo( TNode n, bool doMake ){
  std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( n );
  if( eqc_i==d_eqc_info.end() ){
    EqcInfo* ei = NULL;
    if( doMake ){
      ei = new EqcInfo( d_external.getSatContext() );
      d_eqc_info[n] = ei;
    }
    return ei;
  }else{
    return eqc_i->second;
  }
}


bool TheorySetsPrivate::ee_areEqual( Node a, Node b ) {
  if( a==b ){
    return true;
  }else{
    if( d_equalityEngine.hasTerm( a ) && d_equalityEngine.hasTerm( b ) ){
      return d_equalityEngine.areEqual( a, b );
    }else{
      return false;
    }
  }
}

bool TheorySetsPrivate::ee_areDisequal( Node a, Node b ) {
  if( a==b ){
    return false;
  }else{
    if( d_equalityEngine.hasTerm( a ) && d_equalityEngine.hasTerm( b ) ){
      return d_equalityEngine.areDisequal( a, b, false );
    }else{
      return a.isConst() && b.isConst();
    }
  }
}

bool TheorySetsPrivate::ee_areCareDisequal( Node a, Node b ) {
  if( d_equalityEngine.isTriggerTerm(a, THEORY_SETS) && d_equalityEngine.isTriggerTerm(b, THEORY_SETS) ){
    TNode a_shared = d_equalityEngine.getTriggerTermRepresentative(a, THEORY_SETS);
    TNode b_shared = d_equalityEngine.getTriggerTermRepresentative(b, THEORY_SETS);
    EqualityStatus eqStatus = d_external.d_valuation.getEqualityStatus(a_shared, b_shared);
    if( eqStatus==EQUALITY_FALSE_AND_PROPAGATED || eqStatus==EQUALITY_FALSE || eqStatus==EQUALITY_FALSE_IN_MODEL ){
      return true;
    }
  }
  return false;
}

bool TheorySetsPrivate::isEntailed( Node n, bool polarity ) {
  if( n.getKind()==kind::NOT ){
    return isEntailed( n[0], !polarity );
  }else if( n.getKind()==kind::EQUAL ){
    if( polarity ){
      return ee_areEqual( n[0], n[1] );
    }else{
      return ee_areDisequal( n[0], n[1] );
    }
  }else if( n.getKind()==kind::MEMBER ){
    if( ee_areEqual( n, polarity ? d_true : d_false ) ){
      return true;
    }
    //check members cache
    if( polarity && d_equalityEngine.hasTerm( n[1] ) ){
      Node r = d_equalityEngine.getRepresentative( n[1] );
      if( isMember( n[0], r ) ){
        return true;
      }
    }
  }else if( n.getKind()==kind::AND || n.getKind()==kind::OR ){
    bool conj = (n.getKind()==kind::AND)==polarity;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      bool isEnt = isEntailed( n[i], polarity );
      if( isEnt!=conj ){
        return !conj;
      }
    }
    return conj;
  }else if( n.isConst() ){
    return ( polarity && n==d_true ) || ( !polarity && n==d_false );
  }
  return false;
}

bool TheorySetsPrivate::isMember( Node x, Node s ) {
  Assert( d_equalityEngine.hasTerm( s ) && d_equalityEngine.getRepresentative( s )==s );
  NodeIntMap::iterator mem_i = d_members.find( s );
  if( mem_i != d_members.end() ) {
    for( int i=0; i<(*mem_i).second; i++ ){
      if( ee_areEqual( d_members_data[s][i][0], x ) ){
        return true;
      }
    }
  }
  return false;
}

bool TheorySetsPrivate::isSetDisequalityEntailed( Node r1, Node r2 ) {
  Assert( d_equalityEngine.hasTerm( r1 ) && d_equalityEngine.getRepresentative( r1 )==r1 );
  Assert( d_equalityEngine.hasTerm( r2 ) && d_equalityEngine.getRepresentative( r2 )==r2 );
  TypeNode tn = r1.getType();
  Node eqc_es = d_eqc_emptyset[tn];
  bool is_sat = false;
  for( unsigned e=0; e<2; e++ ){
    Node a = e==0 ? r1 : r2;
    Node b = e==0 ? r2 : r1;
    //if there are members in a
    std::map< Node, std::map< Node, Node > >::iterator itpma = d_pol_mems[0].find( a );
    if( itpma!=d_pol_mems[0].end() ){
      Assert( !itpma->second.empty() );
      //if b is empty
      if( b==eqc_es ){
        if( !itpma->second.empty() ){
          is_sat = true;
          Trace("sets-deq") << "Disequality is satisfied because members are in " << a << " and " << b << " is empty" << std::endl;
        }else{
          //a should not be singleton
          Assert( d_eqc_singleton.find( a )==d_eqc_singleton.end() );
        }
      }else{
        std::map< Node, Node >::iterator itsb = d_eqc_singleton.find( b );
        std::map< Node, std::map< Node, Node > >::iterator itpmb = d_pol_mems[1].find( b );
        std::vector< Node > prev;
        for( std::map< Node, Node >::iterator itm = itpma->second.begin(); itm != itpma->second.end(); ++itm ){
          //if b is a singleton
          if( itsb!=d_eqc_singleton.end() ){
            if( ee_areDisequal( itm->first, itsb->second[0] ) ){
              Trace("sets-deq") << "Disequality is satisfied because of " << itm->second << ", singleton eq " << itsb->second[0] << std::endl;
              is_sat = true;
            }
            //or disequal with another member
            for( unsigned k=0; k<prev.size(); k++ ){
              if( ee_areDisequal( itm->first, prev[k] ) ){
                Trace("sets-deq") << "Disequality is satisfied because of disequal members " << itm->first << " " << prev[k] << ", singleton eq " << std::endl;
                is_sat = true;
                break;
              }
            }
          //TODO: this can be generalized : maintain map to abstract domain ( set -> cardinality )
          //if a has positive member that is negative member in b 
          }else if( itpmb!=d_pol_mems[1].end() ){
            for( std::map< Node, Node >::iterator itnm = itpmb->second.begin(); itnm != itpmb->second.end(); ++itnm ){
              if( ee_areEqual( itm->first, itnm->first ) ){
                Trace("sets-deq") << "Disequality is satisfied because of " << itm->second << " " << itnm->second << std::endl;
                is_sat = true;
                break;
              }
            }
          }
          if( is_sat ){
            break;
          }
          prev.push_back( itm->first );
        }
      }
      if( is_sat ){
        break;
      }
    }
  }
  return is_sat;
}
        
bool TheorySetsPrivate::assertFact( Node fact, Node exp ){
  Trace("sets-assert") << "TheorySets::assertFact : " << fact << ", exp = " << exp << std::endl;
  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];
  if( !isEntailed( atom, polarity ) ){
    if( atom.getKind()==kind::EQUAL ){
      d_equalityEngine.assertEquality( atom, polarity, exp );
    }else{
      d_equalityEngine.assertPredicate( atom, polarity, exp );
    }
    if( !d_conflict ){
      if( atom.getKind()==kind::MEMBER && polarity ){
        //check if set has a value, if so, we can propagate
        Node r = d_equalityEngine.getRepresentative( atom[1] );
        EqcInfo * e = getOrMakeEqcInfo( r, true );
        if( e ){
          Node s = e->d_singleton;
          if( !s.isNull() ){
            Node exp = NodeManager::currentNM()->mkNode( kind::AND, atom, atom[1].eqNode( s ) );
            d_keep.insert( exp );
            if( s.getKind()==kind::SINGLETON ){
              if( s[0]!=atom[0] ){
                Trace("sets-prop") << "Propagate mem-eq : " << exp << std::endl;
                Node eq = s[0].eqNode( atom[0] );
                d_keep.insert( eq );
                assertFact( eq, exp ); 
              }
            }else{
              Trace("sets-prop") << "Propagate mem-eq conflict : " << exp << std::endl;
              d_conflict = true;
              d_external.d_out->conflict( exp );
            }
          }
        }
        //add to membership list
        NodeIntMap::iterator mem_i = d_members.find( r );
        int n_members = 0;
        if( mem_i != d_members.end() ) {
          n_members = (*mem_i).second;
        }
        d_members[r] = n_members + 1;
        if( n_members<(int)d_members_data[r].size() ){
          d_members_data[r][n_members] = atom;
        }else{
          d_members_data[r].push_back( atom );
        }
      }
    }
    return true;
  }else{
    return false;
  }
}

bool TheorySetsPrivate::assertFactRec( Node fact, Node exp, std::vector< Node >& lemma, int inferType ) {
  if( ( options::setsInferAsLemmas() && inferType!=-1 ) || inferType==1 ){
    if( !isEntailed( fact, true ) ){
      lemma.push_back( exp==d_true ? fact : NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, fact ) );
      return true;
    }
  }else{
    Trace("sets-fact") << "Assert fact rec : " << fact << ", exp = " << exp << std::endl;
    if( fact.isConst() ){
      //either trivial or a conflict
      if( fact==d_false ){
        Trace("sets-lemma") << "Conflict : " << exp << std::endl;
        d_conflict = true;
        d_external.d_out->conflict( exp );
        return true;
      }
    }else if( fact.getKind()==kind::AND || ( fact.getKind()==kind::NOT && fact[0].getKind()==kind::OR ) ){
      bool ret = false;
      Node f = fact.getKind()==kind::NOT ? fact[0] : fact;
      for( unsigned i=0; i<f.getNumChildren(); i++ ){
        Node factc = fact.getKind()==kind::NOT ? f[i].negate() : f[i];
        bool tret = assertFactRec( factc, exp, lemma, inferType );
        ret = ret || tret;
        if( d_conflict ){
          return true;
        }
      }
      return ret;
    }else{
      bool polarity = fact.getKind() != kind::NOT;
      TNode atom = polarity ? fact : fact[0];
      //things we can assert to equality engine
      if( atom.getKind()==kind::MEMBER || ( atom.getKind()==kind::EQUAL && atom[0].getType().isSet() ) ){
        //send to equality engine
        if( assertFact( fact, exp ) ){
          d_addedFact = true;
          return true;
        }
      }else{
        if( !isEntailed( fact, true ) ){
          //must send as lemma
          lemma.push_back( exp==d_true ? fact : NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, fact ) );
          return true;
        }
      }
    }
  }
  return false;
}
void TheorySetsPrivate::assertInference( Node fact, Node exp, std::vector< Node >& lemmas, const char * c, int inferType ) {
  d_keep.insert( exp );
  d_keep.insert( fact );
  if( assertFactRec( fact, exp, lemmas, inferType ) ){
    Trace("sets-lemma") << "Sets::Lemma : " << fact << " from " << exp << " by " << c << std::endl;
    Trace("sets-assertion") << "(assert (=> " << exp << " " << fact << ")) ; by " << c << std::endl;
  }
}

void TheorySetsPrivate::assertInference( Node fact, std::vector< Node >& exp, std::vector< Node >& lemmas, const char * c, int inferType ){
  Node exp_n = exp.empty() ? d_true : ( exp.size()==1 ? exp[0] : NodeManager::currentNM()->mkNode( kind::AND, exp ) );
  assertInference( fact, exp_n, lemmas, c, inferType );
}

void TheorySetsPrivate::assertInference( std::vector< Node >& conc, Node exp, std::vector< Node >& lemmas, const char * c, int inferType ){
  if( !conc.empty() ){
    Node fact = conc.size()==1 ? conc[0] : NodeManager::currentNM()->mkNode( kind::AND, conc );
    assertInference( fact, exp, lemmas, c, inferType );
  }
}
void TheorySetsPrivate::assertInference( std::vector< Node >& conc, std::vector< Node >& exp, std::vector< Node >& lemmas, const char * c, int inferType ) {
  Node exp_n = exp.empty() ? d_true : ( exp.size()==1 ? exp[0] : NodeManager::currentNM()->mkNode( kind::AND, exp ) );
  assertInference( conc, exp_n, lemmas, c, inferType );
}

void TheorySetsPrivate::split( Node n, int reqPol ) {
  n = Rewriter::rewrite( n );
  Node lem = NodeManager::currentNM()->mkNode( kind::OR, n, n.negate() );
  std::vector< Node > lemmas;
  lemmas.push_back( lem );
  flushLemmas( lemmas );
  Trace("sets-lemma") << "Sets::Lemma split : " << lem << std::endl;
  if( reqPol!=0 ){
    Trace("sets-lemma") << "Sets::Require phase "  << n << " " << (reqPol>0) << std::endl;
    d_external.getOutputChannel().requirePhase( n, reqPol>0 );
  }
}

void TheorySetsPrivate::fullEffortCheck(){
  Trace("sets") << "----- Full effort check ------" << std::endl;
  do{
    Trace("sets") << "...iterate full effort check..." << std::endl;
    Assert( d_equalityEngine.consistent() );
    d_sentLemma = false;
    d_addedFact = false;
    d_full_check_incomplete = false;
    d_set_eqc.clear();
    d_set_eqc_list.clear();
    d_eqc_emptyset.clear();
    d_eqc_univset.clear();
    d_eqc_singleton.clear();
    d_congruent.clear();
    d_nvar_sets.clear();
    d_var_set.clear();
    d_most_common_type.clear();
    d_most_common_type_term.clear();
    d_pol_mems[0].clear();
    d_pol_mems[1].clear();
    d_members_index.clear();
    d_singleton_index.clear();
    d_bop_index.clear();
    d_op_list.clear();
    d_card_enabled = false;
    d_rels_enabled = false;
    d_eqc_to_card_term.clear();

    std::vector< Node > lemmas;
    Trace("sets-eqc") << "Equality Engine:" << std::endl;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
    while( !eqcs_i.isFinished() ){
      Node eqc = (*eqcs_i);
      bool isSet = false;
      TypeNode tn = eqc.getType();
      //common type node and term
      TypeNode tnc;
      Node tnct;
      if( tn.isSet() ){
        isSet = true;
        d_set_eqc.push_back( eqc );
        tnc = tn.getSetElementType();
        tnct = eqc;
      }
      Trace("sets-eqc") << "[" << eqc << "] : ";
      eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
      while( !eqc_i.isFinished() ) {
        Node n = (*eqc_i);
        if( n!=eqc ){
          Trace("sets-eqc") << n << " ";
        }
        TypeNode tnn = n.getType();
        if( isSet ){
          Assert( tnn.isSet() );
          TypeNode tnnel = tnn.getSetElementType();
          tnc = TypeNode::mostCommonTypeNode( tnc, tnnel );
          Assert( !tnc.isNull() );
          //update the common type term
          if( tnc==tnnel ){
            tnct = n;
          }
        }
        if( n.getKind()==kind::MEMBER ){
          if( eqc.isConst() ){
            Node s = d_equalityEngine.getRepresentative( n[1] );
            Node x = d_equalityEngine.getRepresentative( n[0] );
            int pindex = eqc==d_true ? 0 : ( eqc==d_false ? 1 : -1 );
            if( pindex!=-1  ){
              if( d_pol_mems[pindex][s].find( x )==d_pol_mems[pindex][s].end() ){
                d_pol_mems[pindex][s][x] = n;
                Trace("sets-debug2") << "Membership[" << x << "][" << s << "] : " << n << ", pindex = " << pindex << std::endl;
              }
              if( d_members_index[s].find( x )==d_members_index[s].end() ){
                d_members_index[s][x] = n;
                d_op_list[kind::MEMBER].push_back( n );
              }
            }else{
              Assert( false );
            }
          }
        }else if( n.getKind()==kind::SINGLETON || n.getKind()==kind::UNION || n.getKind()==kind::INTERSECTION || 
                  n.getKind()==kind::SETMINUS || n.getKind()==kind::EMPTYSET || n.getKind()==kind::UNIVERSE_SET ){
          if( n.getKind()==kind::SINGLETON ){
            //singleton lemma
            getProxy( n );
            Node r = d_equalityEngine.getRepresentative( n[0] );
            if( d_singleton_index.find( r )==d_singleton_index.end() ){
              d_singleton_index[r] = n;
              d_eqc_singleton[eqc] = n;
              d_op_list[kind::SINGLETON].push_back( n );
            }else{
              d_congruent[n] = d_singleton_index[r];
            }
          }else if( n.getKind()==kind::EMPTYSET ){
            d_eqc_emptyset[tnn] = eqc;
          }else if( n.getKind()==kind::UNIVERSE_SET ){
            Assert( options::setsExt() );
            d_eqc_univset[tnn] = eqc;
          }else{
            Node r1 = d_equalityEngine.getRepresentative( n[0] );
            Node r2 = d_equalityEngine.getRepresentative( n[1] );
            if( d_bop_index[n.getKind()][r1].find( r2 )==d_bop_index[n.getKind()][r1].end() ){
              d_bop_index[n.getKind()][r1][r2] = n;
              d_op_list[n.getKind()].push_back( n );
            }else{
              d_congruent[n] = d_bop_index[n.getKind()][r1][r2];
            }
          }
          d_nvar_sets[eqc].push_back( n );
          Trace("sets-debug2") << "Non-var-set[" << eqc << "] : " << n << std::endl;
          d_set_eqc_list[eqc].push_back( n );
        }else if( n.getKind()==kind::CARD ){
          d_card_enabled = true;
          TypeNode tnc = n[0].getType().getSetElementType();
          if( tnc.isInterpretedFinite() ){
            std::stringstream ss;
            ss << "ERROR: cannot use cardinality on sets with finite element type." << std::endl;
            throw LogicException(ss.str());
            //TODO: extend approach for this case
          }
          Node r = d_equalityEngine.getRepresentative( n[0] );
          if( d_eqc_to_card_term.find( r )==d_eqc_to_card_term.end() ){
            d_eqc_to_card_term[ r ] = n;
            registerCardinalityTerm( n[0], lemmas );
          }
        }else{
          if( d_rels->isRelationKind( n.getKind() ) ){
            d_rels_enabled = true;
          }
          if( isSet ){
            d_set_eqc_list[eqc].push_back( n );
            if( n.getKind()==kind::VARIABLE ){
              if( d_var_set.find( eqc )==d_var_set.end() ){
                d_var_set[eqc] = n;
              }
            }
          }
        }
        ++eqc_i;
      }
      if( isSet ){
        Assert( tnct.getType().getSetElementType()==tnc );
        d_most_common_type[eqc] = tnc;
        d_most_common_type_term[eqc] = tnct;
      }
      Trace("sets-eqc") << std::endl;
      ++eqcs_i;
    }
    
    flushLemmas( lemmas );
    if( !hasProcessed() ){
      if( Trace.isOn("sets-mem") ){
        for( unsigned i=0; i<d_set_eqc.size(); i++ ){
          Node s = d_set_eqc[i];
          Trace("sets-mem") << "Eqc " << s << " : ";
          std::map< Node, std::map< Node, Node > >::iterator it = d_pol_mems[0].find( s );
          if( it!=d_pol_mems[0].end() ){
            Trace("sets-mem") << "Memberships : ";
            for( std::map< Node, Node >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
              Trace("sets-mem") << it2->first << " ";
            }
          }
          std::map< Node, Node >::iterator its = d_eqc_singleton.find( s );
          if( its!=d_eqc_singleton.end() ){
            Trace("sets-mem") << " : Singleton : " << its->second;
          }
          Trace("sets-mem") << std::endl;
        }
      }
      checkSubtypes( lemmas );
      flushLemmas( lemmas, true );
      if( !hasProcessed() ){
      
        checkDownwardsClosure( lemmas );
        if( options::setsInferAsLemmas() ){
          flushLemmas( lemmas );
        }
        if( !hasProcessed() ){
          checkUpwardsClosure( lemmas );
          flushLemmas( lemmas );
          if( !hasProcessed() ){
            std::vector< Node > intro_sets;
            //for cardinality
            if( d_card_enabled ){
              checkCardBuildGraph( lemmas );
              flushLemmas( lemmas );
              if( !hasProcessed() ){
                checkMinCard( lemmas );
                flushLemmas( lemmas );
                if( !hasProcessed() ){
                  checkCardCycles( lemmas );
                  flushLemmas( lemmas );
                  if( !hasProcessed() ){
                    checkNormalForms( lemmas, intro_sets );
                    flushLemmas( lemmas );
                  }
                }
              }
            }
            if( !hasProcessed() ){
              checkDisequalities( lemmas );
              flushLemmas( lemmas );
              if( !hasProcessed() ){
                //introduce splitting on venn regions (absolute last resort)
                if( d_card_enabled && !hasProcessed() && !intro_sets.empty() ){
                  Assert( intro_sets.size()==1 );
                  Trace("sets-intro") << "Introduce term : " << intro_sets[0] << std::endl;
                  Trace("sets-intro") << "  Actual Intro : ";
                  debugPrintSet( intro_sets[0], "sets-nf" );
                  Trace("sets-nf") << std::endl;
                  Node k = getProxy( intro_sets[0] );
                  d_sentLemma = true;
                }
              }
            }
          }
        }
      }
    }
  }while( !d_sentLemma && !d_conflict && d_addedFact );
  Trace("sets") << "----- End full effort check, conflict=" << d_conflict << ", lemma=" << d_sentLemma << std::endl;
}

void TheorySetsPrivate::checkSubtypes( std::vector< Node >& lemmas ) {
 for( unsigned i=0; i<d_set_eqc.size(); i++ ){
    Node s = d_set_eqc[i];
    TypeNode mct = d_most_common_type[s];
    std::map< Node, std::map< Node, Node > >::iterator it = d_pol_mems[0].find( s );
    if( it!=d_pol_mems[0].end() ){
      for( std::map< Node, Node >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        if( !it2->first.getType().isSubtypeOf( mct ) ){          
          Node mctt = d_most_common_type_term[s];
          std::vector< Node > exp;
          exp.push_back( it2->second );
          Assert( ee_areEqual( mctt, it2->second[1] ) );
          exp.push_back( mctt.eqNode( it2->second[1] ) );
          Node etc = TypeNode::getEnsureTypeCondition( it2->first, mct );
          if( !etc.isNull() ){
            assertInference( etc, exp, lemmas, "subtype-clash" );
            if( d_conflict ){
              return;
            } 
          }else{
            // very strange situation : we have a member in a set that is not a subtype, and we do not have a type condition for it
            d_full_check_incomplete = true;
            Trace("sets-incomplete") << "Sets : incomplete because of unknown type constraint." << std::endl;
          }
        }
      }
    }
  }
}

void TheorySetsPrivate::checkDownwardsClosure( std::vector< Node >& lemmas ) {
  Trace("sets") << "Downwards closure..." << std::endl;
  //downwards closure
  for( std::map< Node, std::map< Node, Node > >::iterator it = d_pol_mems[0].begin(); it != d_pol_mems[0].end(); ++it ){
    std::map< Node, std::vector< Node > >::iterator itn = d_nvar_sets.find( it->first );
    if( itn!=d_nvar_sets.end() ){
      for( unsigned j=0; j<itn->second.size(); j++ ){
        if( d_congruent.find( itn->second[j] )==d_congruent.end() ){
          for( std::map< Node, Node >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){ 
            Node mem = it2->second;
            Node eq_set = itn->second[j];
            Assert( d_equalityEngine.areEqual( mem[1], eq_set ) );
            if( mem[1]!=eq_set ){
              Trace("sets-debug") << "Downwards closure based on " << mem << ", eq_set = " << eq_set << std::endl;
              if( !options::setsProxyLemmas() ){
                Node nmem = NodeManager::currentNM()->mkNode( kind::MEMBER, mem[0], eq_set );
                nmem = Rewriter::rewrite( nmem );
                std::vector< Node > exp;
                exp.push_back( mem );
                exp.push_back( mem[1].eqNode( eq_set ) );
                assertInference( nmem, exp, lemmas, "downc" );
                if( d_conflict ){
                  return;
                }
              }else{
                //use proxy set
                Node k = getProxy( eq_set );
                Node pmem = NodeManager::currentNM()->mkNode( kind::MEMBER, mem[0], k );
                Node nmem = NodeManager::currentNM()->mkNode( kind::MEMBER, mem[0], eq_set );
                nmem = Rewriter::rewrite( nmem );
                std::vector< Node > exp;
                if( ee_areEqual( mem, pmem ) ){
                  exp.push_back( pmem );
                }else{
                  nmem = NodeManager::currentNM()->mkNode( kind::OR, pmem.negate(), nmem );
                }
                assertInference( nmem, exp, lemmas, "downc" );
              }
            }
          }
        }
      }
    }
  }
}

void TheorySetsPrivate::checkUpwardsClosure( std::vector< Node >& lemmas ) {
  //upwards closure
  for( std::map< Kind, std::map< Node, std::map< Node, Node > > >::iterator itb = d_bop_index.begin(); itb != d_bop_index.end(); ++itb ){
    Kind k = itb->first;
    Trace("sets") << "Upwards closure " << k << "..." << std::endl;
    for( std::map< Node, std::map< Node, Node > >::iterator it = itb->second.begin(); it != itb->second.end(); ++it ){
      Node r1 = it->first;
      //see if there are members in first argument r1
      std::map< Node, std::map< Node, Node > >::iterator itm1 = d_pol_mems[0].find( r1 );
      if( itm1!=d_pol_mems[0].end() || k==kind::UNION ){
        for( std::map< Node, Node >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
          Node r2 = it2->first;
          //see if there are members in second argument
          std::map< Node, std::map< Node, Node > >::iterator itm2 = d_pol_mems[0].find( r2 );
          std::map< Node, std::map< Node, Node > >::iterator itm2n = d_pol_mems[1].find( r2 );
          if( itm2!=d_pol_mems[0].end() || k!=kind::INTERSECTION ){
            Trace("sets-debug") << "Checking " << it2->second << ", members = " << (itm1!=d_pol_mems[0].end()) << ", " << (itm2!=d_pol_mems[0].end()) << std::endl;
            //for all members of r1
            if( itm1!=d_pol_mems[0].end() ){
              for( std::map< Node, Node >::iterator itm1m = itm1->second.begin(); itm1m != itm1->second.end(); ++itm1m ){
                Node xr = itm1m->first;
                Node x = itm1m->second[0];
                Trace("sets-debug") << "checking membership " << xr << " " << itm1m->second << std::endl;
                std::vector< Node > exp;
                exp.push_back( itm1m->second );
                addEqualityToExp( it2->second[0], itm1m->second[1], exp );
                bool valid = false;
                int inferType = 0;
                if( k==kind::UNION ){
                  valid = true;
                }else if( k==kind::INTERSECTION ){
                  //conclude x is in it2->second
                  //if also existing in members of r2
                  bool in_r2 = itm2!=d_pol_mems[0].end() && itm2->second.find( xr )!=itm2->second.end();
                  if( in_r2 ){
                    exp.push_back( itm2->second[xr] );
                    addEqualityToExp( it2->second[1], itm2->second[xr][1], exp );
                    addEqualityToExp( x, itm2->second[xr][0], exp );
                    valid = true;
                  }else{
                    // if not, check whether it is definitely not a member, if unknown, split
                    bool not_in_r2 = itm2n!=d_pol_mems[1].end() && itm2n->second.find( xr )!=itm2n->second.end();
                    if( !not_in_r2 ){
                      exp.push_back( NodeManager::currentNM()->mkNode( kind::MEMBER, x, it2->second[1] ) );
                      valid = true;
                      inferType = 1;
                    }
                  }
                }else{
                  Assert( k==kind::SETMINUS );
                  /*
                  std::map< Node, std::map< Node, Node > >::iterator itnm2 = d_pol_mems[1].find( r2 );
                  if( itnm2!=d_pol_mems[1].end() ){
                    bool not_in_r2 = itnm2->second.find( xr )!=itnm2->second.end();
                    if( not_in_r2 ){
                      exp.push_back( itnm2->second[xr] );
                      if( it2->second[1]!=itnm2->second[xr][1] ){
                        Assert( d_equalityEngine.areEqual( it2->second[1], itnm2->second[xr][1] ) );
                        exp.push_back( it2->second[1].eqNode( itnm2->second[xr][1] ) );
                      }
                      if( x!=itnm2->second[xr][0] ){
                        Assert( d_equalityEngine.areEqual( x, itnm2->second[xr][0] ) );
                        exp.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, x, itnm2->second[xr][0] ) );
                      }
                      valid = true;
                    }
                  }
                  */
                  if( !valid ){
                    bool in_r2 = itm2!=d_pol_mems[0].end() && itm2->second.find( xr )!=itm2->second.end();
                    if( !in_r2 ){
                      // must add lemma for set minus since non-membership in this case is not explained
                      exp.push_back( NodeManager::currentNM()->mkNode( kind::MEMBER, x, it2->second[1] ).negate() );
                      valid = true;
                      inferType = 1;
                    }
                  }
                }
                if( valid ){
                  Node rr = d_equalityEngine.getRepresentative( it2->second );
                  if( !isMember( x, rr ) ){
                    Node kk = getProxy( it2->second );
                    Node fact = NodeManager::currentNM()->mkNode( kind::MEMBER, x, kk );
                    assertInference( fact, exp, lemmas, "upc", inferType );
                    if( d_conflict ){
                      return;
                    }
                  }
                }
                Trace("sets-debug") << "done checking membership " << xr << " " << itm1m->second << std::endl;
              }
            }
            if( k==kind::UNION ){
              if( itm2!=d_pol_mems[0].end() ){
                //for all members of r2
                for( std::map< Node, Node >::iterator itm2m = itm2->second.begin(); itm2m != itm2->second.end(); ++itm2m ){
                  Node x = itm2m->second[0];
                  Node rr = d_equalityEngine.getRepresentative( it2->second );
                  if( !isMember( x, rr ) ){
                    std::vector< Node > exp;
                    exp.push_back( itm2m->second );
                    addEqualityToExp( it2->second[1], itm2m->second[1], exp );
                    Node k = getProxy( it2->second );
                    Node fact = NodeManager::currentNM()->mkNode( kind::MEMBER, x, k );
                    assertInference( fact, exp, lemmas, "upc2" );
                    if( d_conflict ){
                      return;
                    }
                  }
                }
              }
            }   
          }      
        }
      }
    }
  }
  if( !hasProcessed() ){
    if( options::setsExt() ){
      //universal sets
      Trace("sets-debug") << "Check universe sets..." << std::endl;
      //all elements must be in universal set
      for( std::map< Node, std::map< Node, Node > >::iterator it = d_pol_mems[0].begin(); it != d_pol_mems[0].end(); ++it ){
        //if equivalence class contains a variable
        std::map< Node, Node >::iterator itv = d_var_set.find( it->first );
        if( itv!=d_var_set.end() ){
          //the variable in the equivalence class
          Node v = itv->second;
          std::map< TypeNode, Node > univ_set;
          for( std::map< Node, Node >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
            Node e = it2->second[0];
            TypeNode tn = NodeManager::currentNM()->mkSetType( e.getType() );
            Node u;
            std::map< TypeNode, Node >::iterator itu = univ_set.find( tn );
            if( itu==univ_set.end() ){
              std::map< TypeNode, Node >::iterator itu = d_eqc_univset.find( tn );
              // if the universe does not yet exist, or is not in this equivalence class
              if( itu==d_eqc_univset.end() || itu->second!=it->first ){
                u = getUnivSet( tn );
              }
              univ_set[tn] = u;
            }else{
              u = itu->second;
            }
            if( !u.isNull() ){
              Assert( it2->second.getKind()==kind::MEMBER );
              std::vector< Node > exp;
              exp.push_back( it2->second );
              if( v!=it2->second[1] ){
                exp.push_back( v.eqNode( it2->second[1] ) );
              }
              Node fact = NodeManager::currentNM()->mkNode( kind::MEMBER, it2->second[0], u );
              assertInference( fact, exp, lemmas, "upuniv" );
              if( d_conflict ){
                return;
              }
            }
          }
        }
      }
    }
  }
}

void TheorySetsPrivate::checkDisequalities( std::vector< Node >& lemmas ) {
  //disequalities
  Trace("sets") << "Disequalities..." << std::endl;
  for(NodeBoolMap::const_iterator it=d_deq.begin(); it !=d_deq.end(); ++it) {
    if( (*it).second ){
      Node deq = (*it).first;
      //check if it is already satisfied
      Assert( d_equalityEngine.hasTerm( deq[0] ) && d_equalityEngine.hasTerm( deq[1] ) );
      Node r1 = d_equalityEngine.getRepresentative( deq[0] );
      Node r2 = d_equalityEngine.getRepresentative( deq[1] );
      bool is_sat = isSetDisequalityEntailed( r1, r2 );
      /*
      if( !is_sat ){
        //try to make one of them empty
        for( unsigned e=0; e<2; e++ ){
        }
      }
      */
      Trace("sets-debug") << "Check disequality " << deq << ", is_sat = " << is_sat << std::endl;
      //will process regardless of sat/processed/unprocessed
      d_deq[deq] = false;
      
      if( !is_sat ){
        if( d_deq_processed.find( deq )==d_deq_processed.end() ){
          d_deq_processed.insert( deq );
          d_deq_processed.insert( deq[1].eqNode( deq[0] ) );
          Trace("sets") << "Process Disequality : " << deq.negate() << std::endl;
          TypeNode elementType = deq[0].getType().getSetElementType();
          Node x = NodeManager::currentNM()->mkSkolem("sde_", elementType);
          Node mem1 = NodeManager::currentNM()->mkNode( kind::MEMBER, x, deq[0] );
          Node mem2 = NodeManager::currentNM()->mkNode( kind::MEMBER, x, deq[1] );
          Node lem = NodeManager::currentNM()->mkNode( kind::OR, deq, NodeManager::currentNM()->mkNode( kind::EQUAL, mem1, mem2 ).negate() );
          lem = Rewriter::rewrite( lem );
          assertInference( lem, d_emp_exp, lemmas, "diseq", 1 );
          flushLemmas( lemmas );
          if( hasProcessed() ){
            return;
          }
        }
      }
    }
  }
}

void TheorySetsPrivate::checkCardBuildGraph( std::vector< Node >& lemmas ) {
  Trace("sets") << "Cardinality graph..." << std::endl;
  //first, ensure cardinality relationships are added as lemmas for all non-basic set terms
  for( unsigned i=0; i<d_set_eqc.size(); i++ ){
    Node eqc = d_set_eqc[i];
    std::map< Node, std::vector< Node > >::iterator itn = d_nvar_sets.find( eqc );
    if( itn!=d_nvar_sets.end() ){
      for( unsigned j=0; j<itn->second.size(); j++ ){
        Node n = itn->second[j];
        if( d_congruent.find( n )==d_congruent.end() ){
          //if setminus, do for intersection instead
          if( n.getKind()==kind::SETMINUS ){
            n = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::INTERSECTION, n[0], n[1] ) );
          }
          registerCardinalityTerm( n, lemmas );
        }
      }
    }
  }
  Trace("sets") << "Done cardinality graph" << std::endl;
}

void TheorySetsPrivate::registerCardinalityTerm( Node n, std::vector< Node >& lemmas ){
  if( d_card_processed.find( n )==d_card_processed.end() ){
    d_card_processed.insert( n );
    Trace("sets-card") << "Cardinality lemmas for " << n << " : " << std::endl;
    std::vector< Node > cterms;
    if( n.getKind()==kind::INTERSECTION ){
      for( unsigned e=0; e<2; e++ ){
        Node s = NodeManager::currentNM()->mkNode( kind::SETMINUS, n[e], n[1-e] );
        cterms.push_back( s );
      }
      Node pos_lem = NodeManager::currentNM()->mkNode( kind::GEQ, NodeManager::currentNM()->mkNode( kind::CARD, n ), d_zero );
      assertInference( pos_lem, d_emp_exp, lemmas, "pcard", 1 );
    }else{
      cterms.push_back( n );
    }
    for( unsigned k=0; k<cterms.size(); k++ ){
      Node nn = cterms[k];
      Node nk = getProxy( nn );
      Node pos_lem = NodeManager::currentNM()->mkNode( kind::GEQ, NodeManager::currentNM()->mkNode( kind::CARD, nk ), d_zero );
      assertInference( pos_lem, d_emp_exp, lemmas, "pcard", 1 );
      if( nn!=nk ){
        Node lem = NodeManager::currentNM()->mkNode( kind::EQUAL, NodeManager::currentNM()->mkNode( kind::CARD, nk ),
                                                                  NodeManager::currentNM()->mkNode( kind::CARD, nn ) );
        lem = Rewriter::rewrite( lem );
        Trace("sets-card") << "  " << k << " : " << lem << std::endl;
        assertInference( lem, d_emp_exp, lemmas, "card", 1 );
      }
    }
  }
}

void TheorySetsPrivate::checkCardCycles( std::vector< Node >& lemmas ) {
  Trace("sets") << "Check cardinality cycles..." << std::endl;
  //build order of equivalence classes, also build cardinality graph
  std::vector< Node > set_eqc_tmp;
  set_eqc_tmp.insert( set_eqc_tmp.end(), d_set_eqc.begin(), d_set_eqc.end() );
  d_set_eqc.clear();
  d_card_parent.clear();
  for( unsigned i=0; i<set_eqc_tmp.size(); i++ ){
    std::vector< Node > curr;
    std::vector< Node > exp;
    checkCardCyclesRec( set_eqc_tmp[i], curr, exp, lemmas );
    flushLemmas( lemmas );
    if( hasProcessed() ){
      return;
    }
  }
  Trace("sets") << "Done check cardinality cycles" << std::endl;
}

void TheorySetsPrivate::checkCardCyclesRec( Node eqc, std::vector< Node >& curr, std::vector< Node >& exp, std::vector< Node >& lemmas ) {
  if( std::find( curr.begin(), curr.end(), eqc )!=curr.end() ){
    Trace("sets-debug") << "Found venn region loop..." << std::endl;
    if( curr.size()>1 ){
      //all regions must be equal
      std::vector< Node > conc;
      for( unsigned i=1; i<curr.size(); i++ ){
        conc.push_back( curr[0].eqNode( curr[i] ) );
      }
      Node fact = conc.size()==1 ? conc[0] : NodeManager::currentNM()->mkNode( kind::AND, conc );
      assertInference( fact, exp, lemmas, "card_cycle" );
      flushLemmas( lemmas );
    }else{
      //should be guaranteed based on not exploring equal parents
      Assert( false );
    }
  }else if( std::find( d_set_eqc.begin(), d_set_eqc.end(), eqc )==d_set_eqc.end() ){
    curr.push_back( eqc );
    TypeNode tn = eqc.getType();
    bool is_empty = eqc==d_eqc_emptyset[tn];
    Node emp_set = getEmptySet( tn );
    std::map< Node, std::vector< Node > >::iterator itn = d_nvar_sets.find( eqc );
    if( itn!=d_nvar_sets.end() ){
      for( unsigned j=0; j<itn->second.size(); j++ ){
        Node n = itn->second[j];
        if( n.getKind()==kind::INTERSECTION || n.getKind()==kind::SETMINUS ){
          Trace("sets-debug") << "Build cardinality parents for " << n << "..." << std::endl;
          std::vector< Node > sib;
          unsigned true_sib = 0;
          if( n.getKind()==kind::INTERSECTION ){
            d_card_base[n] = n;
            for( unsigned e=0; e<2; e++ ){
              Node sm = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::SETMINUS, n[e], n[1-e] ) );
              sib.push_back( sm );
            }
            true_sib = 2;
          }else{
            Node si = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::INTERSECTION, n[0], n[1] ) );
            sib.push_back( si );
            d_card_base[n] = si;
            Node osm = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::SETMINUS, n[1], n[0] ) );
            sib.push_back( osm );
            true_sib = 1;
          }
          Node u = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::UNION, n[0], n[1] ) );
          if( !d_equalityEngine.hasTerm( u ) ){
            u = Node::null();
          }
          unsigned n_parents = true_sib + ( u.isNull() ? 0 : 1 );
          //if this set is empty
          if( is_empty ){
            Assert( ee_areEqual( n, emp_set ) );
            Trace("sets-debug") << "  empty, parents equal siblings" << std::endl;
            std::vector< Node > conc;
            //parent equal siblings
            for( unsigned e=0; e<true_sib; e++ ){
              if( d_equalityEngine.hasTerm( sib[e] ) && !ee_areEqual( n[e], sib[e] ) ){
                conc.push_back( n[e].eqNode( sib[e] ) );
              }
            }
            assertInference( conc, n.eqNode( emp_set ), lemmas, "cg_emp" );
            flushLemmas( lemmas );
            if( hasProcessed() ){
              return;
            }else{
              //justify why there is no edge to parents (necessary?)
              for( unsigned e=0; e<n_parents; e++ ){
                Node p = (e==true_sib) ? u : n[e];
                
              }
            }
          }else{
            std::vector< Node > card_parents;
            std::vector< int > card_parent_ids;
            //check if equal to a parent
            for( unsigned e=0; e<n_parents; e++ ){
              Trace("sets-debug") << "  check parent " << e << "/" << n_parents << std::endl;
              bool is_union = e==true_sib;
              Node p = (e==true_sib) ? u : n[e];
              Trace("sets-debug") << "  check relation to parent " << p << ", isu=" << is_union << "..." << std::endl;
              //if parent is empty
              if( ee_areEqual( p, emp_set ) ){
                Trace("sets-debug") << "  it is empty..." << std::endl;
                Assert( !ee_areEqual( n, emp_set ) );
                assertInference( n.eqNode( emp_set ), p.eqNode( emp_set ), lemmas, "cg_emppar" );
                if( hasProcessed() ){
                  return;
                }
              //if we are equal to a parent
              }else if( ee_areEqual( p, n ) ){
                Trace("sets-debug") << "  it is equal to this..." << std::endl;
                std::vector< Node > conc;
                std::vector< int > sib_emp_indices;
                if( is_union ){
                  for( unsigned s=0; s<sib.size(); s++ ){
                    sib_emp_indices.push_back( s );
                  }
                }else{
                  sib_emp_indices.push_back( e );
                }
                //sibling(s) are empty
                for( unsigned s=0; s<sib_emp_indices.size(); s++ ){
                  unsigned si = sib_emp_indices[s];
                  if( !ee_areEqual( sib[si], emp_set ) ){
                    conc.push_back( sib[si].eqNode( emp_set ) );
                  }else{
                    Trace("sets-debug") << "Sibling " << sib[si] << " is already empty." << std::endl;
                  }
                }
                if( !is_union && n.getKind()==kind::INTERSECTION && !u.isNull() ){
                  //union is equal to other parent
                  if( !ee_areEqual( u, n[1-e] ) ){
                    conc.push_back( u.eqNode( n[1-e] ) );
                  }
                }
                Trace("sets-debug") << "...derived " << conc.size() << " conclusions" << std::endl;
                assertInference( conc, n.eqNode( p ), lemmas, "cg_eqpar" );
                flushLemmas( lemmas );
                if( hasProcessed() ){
                  return;
                }
              }else{
                Trace("sets-cdg") << "Card graph : " << n << " -> " << p << std::endl;
                //otherwise, we a syntactic subset of p
                card_parents.push_back( p );
                card_parent_ids.push_back( is_union ? 2 : e );
              }
            }
            Assert( d_card_parent[n].empty() );
            Trace("sets-debug") << "get parent representatives..." << std::endl;
            //for each parent, take their representatives
            for( unsigned k=0; k<card_parents.size(); k++ ){
              Node eqcc = d_equalityEngine.getRepresentative( card_parents[k] );
              Trace("sets-debug") << "Check card parent " << k << "/" << card_parents.size() << std::endl;
              
              //if parent is singleton, then we should either be empty to equal to it
              std::map< Node, Node >::iterator itps = d_eqc_singleton.find( eqcc );
              if( itps!=d_eqc_singleton.end() ){
                bool eq_parent = false;
                std::vector< Node > exp;
                addEqualityToExp( card_parents[k], itps->second, exp );
                if( ee_areDisequal( n, emp_set ) ){
                  exp.push_back( n.eqNode( emp_set ).negate() );
                  eq_parent = true;
                }else{
                  std::map< Node, std::map< Node, Node > >::iterator itpm = d_pol_mems[0].find( eqc );
                  if( itpm!=d_pol_mems[0].end() && !itpm->second.empty() ){
                    Node pmem = itpm->second.begin()->second;
                    exp.push_back( pmem );
                    addEqualityToExp( n, pmem[1], exp );
                    eq_parent = true;
                  }
                }
                //must be equal to parent
                if( eq_parent ){
                  Node conc = n.eqNode(  card_parents[k] );
                  assertInference( conc, exp, lemmas, "cg_par_sing" );
                  flushLemmas( lemmas );
                }else{
                  //split on empty
                  Trace("sets-nf") << "Split empty : " << n << std::endl;
                  split( n.eqNode( emp_set ), 1 );
                }
                Assert( hasProcessed() );
                return;
              }else{
                bool dup = false;
                for( unsigned l=0; l<d_card_parent[n].size(); l++ ){
                  if( eqcc==d_card_parent[n][l] ){
                    Trace("sets-debug") << "  parents " << l << " and " << k << " are equal, ids = " << card_parent_ids[l] << " " << card_parent_ids[k] << std::endl;
                    dup = true;
                    if( n.getKind()==kind::INTERSECTION ){
                      Assert( card_parent_ids[l]!=2 );
                      std::vector< Node > conc;
                      if( card_parent_ids[k]==2 ){
                        //intersection is equal to other parent
                        unsigned pid = 1-card_parent_ids[l];
                        if( !ee_areEqual( n[pid], n ) ){
                          Trace("sets-debug") << "  one of them is union, make equal to other..." << std::endl;
                          conc.push_back( n[pid].eqNode( n ) );
                        }
                      }else{
                        if( !ee_areEqual( card_parents[k], n ) ){
                          Trace("sets-debug") << "  neither is union, make equal to one parent..." << std::endl;
                          //intersection is equal to one of the parents
                          conc.push_back( card_parents[k].eqNode( n ) );
                        }
                      }
                      assertInference( conc, card_parents[k].eqNode( d_card_parent[n][l] ), lemmas, "cg_pareq" );
                      flushLemmas( lemmas );
                      if( hasProcessed() ){
                        return;
                      }
                    }
                  }
                }
                if( !dup ){
                  d_card_parent[n].push_back( eqcc );
                }
              }
            }
            //now recurse on parents (to ensure their normal will be computed after this eqc)
            exp.push_back( eqc.eqNode( n ) );
            for( unsigned k=0; k<d_card_parent[n].size(); k++ ){
              checkCardCyclesRec( d_card_parent[n][k], curr, exp, lemmas );
              if( hasProcessed() ){
                return;
              }
            }
            exp.pop_back();
          }
        }
      }
    }
    curr.pop_back();
    //parents now processed, can add to ordered list
    d_set_eqc.push_back( eqc );
  }else{
    //already processed
  }  
}

void TheorySetsPrivate::checkNormalForms( std::vector< Node >& lemmas, std::vector< Node >& intro_sets ){
  Trace("sets") << "Check normal forms..." << std::endl;
  // now, build normal form for each equivalence class
  //   d_set_eqc is now sorted such that for each d_set_eqc[i], d_set_eqc[j], 
  //      if d_set_eqc[i] is a strict syntactic subterm of d_set_eqc[j], then i<j.
  d_ff.clear();
  d_nf.clear();
  for( int i=(int)(d_set_eqc.size()-1); i>=0; i-- ){
    checkNormalForm( d_set_eqc[i], intro_sets );
    if( hasProcessed() || !intro_sets.empty() ){
      return;
    }
  }
  Trace("sets") << "Done check normal forms" << std::endl;
}

void TheorySetsPrivate::checkNormalForm( Node eqc, std::vector< Node >& intro_sets ){
  TypeNode tn = eqc.getType();
  Trace("sets") << "Compute normal form for " << eqc << std::endl;
  Trace("sets-nf") << "Compute N " << eqc << "..." << std::endl;
  if( eqc==d_eqc_emptyset[tn] ){
    d_nf[eqc].clear();
    Trace("sets-nf") << "----> N " << eqc << " => {}" << std::endl;
  }else{
    //flat/normal forms are sets of equivalence classes
    Node base;
    std::vector< Node > comps;
    std::map< Node, std::map< Node, std::vector< Node > > >::iterator it = d_ff.find( eqc );
    if( it!=d_ff.end() ){
      for( std::map< Node, std::vector< Node > >::iterator itf = it->second.begin(); itf != it->second.end(); ++itf ){
        std::sort( itf->second.begin(), itf->second.end() );
        if( base.isNull() ){
          base = itf->first;
        }else{
          comps.push_back( itf->first );
        }
        Trace("sets-nf") << "  F " << itf->first << " : ";
        if( Trace.isOn("sets-nf") ){
          Trace("sets-nf") << "{ ";
          for( unsigned k=0; k<itf->second.size(); k++ ){
            if( k>0 ){ Trace("sets-nf") << ", "; }
            Trace("sets-nf") << "[" << itf->second[k] << "]";
          }
          Trace("sets-nf") << " }" << std::endl;
        }
        Trace("sets-nf-debug") << " ...";
        debugPrintSet( itf->first, "sets-nf-debug" );
        Trace("sets-nf-debug") << std::endl;
      }
    }else{
      Trace("sets-nf") << "(no flat forms)" << std::endl;
    }

    Assert( d_nf.find( eqc )==d_nf.end() );
    bool success = true;
    if( !base.isNull() ){
      Node emp_set = getEmptySet( tn );
      for( unsigned j=0; j<comps.size(); j++ ){
        //compare if equal
        std::vector< Node > c;
        c.push_back( base );
        c.push_back( comps[j] );
        std::vector< Node > only[2];
        std::vector< Node > common;
        Trace("sets-nf-debug") << "Compare venn regions of " << base << " vs " << comps[j] << std::endl;
        unsigned k[2] = { 0, 0 };
        while( k[0]<d_ff[eqc][c[0]].size() || k[1]<d_ff[eqc][c[1]].size() ){
          bool proc = true;
          for( unsigned e=0; e<2; e++ ){
            if( k[e]==d_ff[eqc][c[e]].size() ){
              for( ; k[1-e]<d_ff[eqc][c[1-e]].size(); ++k[1-e] ){
                only[1-e].push_back( d_ff[eqc][c[1-e]][k[1-e]] );
              }
              proc = false;
            }
          }
          if( proc ){
            if( d_ff[eqc][c[0]][k[0]]==d_ff[eqc][c[1]][k[1]] ){
              common.push_back( d_ff[eqc][c[0]][k[0]] );
              k[0]++;
              k[1]++;
            }else if( d_ff[eqc][c[0]][k[0]]<d_ff[eqc][c[1]][k[1]] ){
              only[0].push_back( d_ff[eqc][c[0]][k[0]] );
              k[0]++;
            }else{
              only[1].push_back( d_ff[eqc][c[1]][k[1]] );
              k[1]++;
            }
          }
        }
        if( !only[0].empty() || !only[1].empty() ){
          if( Trace.isOn("sets-nf-debug") ){
            Trace("sets-nf-debug") << "Unique venn regions : " << std::endl;
            for( unsigned e=0; e<2; e++ ){
              Trace("sets-nf-debug") << "  " << c[e] << " : { ";
              for( unsigned l=0; l<only[e].size(); l++ ){
                if( l>0 ){ Trace("sets-nf-debug") << ", "; }
                Trace("sets-nf-debug") << "[" << only[e][l] << "]";
              }
              Trace("sets-nf-debug") << " }" << std::endl;
            }
          }
          //try to make one empty, prefer the unique ones first
          for( unsigned e=0; e<3; e++ ){
            unsigned sz = e==2 ? common.size() : only[e].size();
            for( unsigned l=0; l<sz; l++ ){
              Node r = e==2 ? common[l] : only[e][l];
              Trace("sets-nf-debug") << "Try split empty : " << r << std::endl;
              Trace("sets-nf-debug") << "         actual : ";
              debugPrintSet( r, "sets-nf-debug" );
              Trace("sets-nf-debug") << std::endl;
              Assert( !ee_areEqual( r, emp_set ) );
              if( !ee_areDisequal( r, emp_set ) && ( d_pol_mems[0].find( r )==d_pol_mems[0].end() || d_pol_mems[0][r].empty() ) ){
                //guess that its equal empty if it has no explicit members
                Trace("sets-nf") << " Split empty : " << r << std::endl;
                Trace("sets-nf") << "Actual Split : ";
                debugPrintSet( r, "sets-nf" );
                Trace("sets-nf") << std::endl;
                split( r.eqNode( emp_set ), 1 );
                Assert( hasProcessed() );
                return;
              }
            }
          }
          for( unsigned l=0; l<only[0].size(); l++ ){
            for( unsigned m=0; m<only[1].size(); m++ ){
              bool disjoint = false;
              Trace("sets-nf-debug") << "Try split " << only[0][l] << " against " << only[1][m] << std::endl;
              //split them
              for( unsigned e=0; e<2; e++ ){
                Node r1 = e==0 ? only[0][l] : only[1][m];
                Node r2 = e==0 ? only[1][m] : only[0][l];
                //check if their intersection exists modulo equality
                std::map< Node, Node >::iterator itb = d_bop_index[kind::INTERSECTION][r1].find( r2 );
                if( itb!=d_bop_index[kind::INTERSECTION][r1].end() ){
                  Trace("sets-nf-debug") << "Split term already exists, but not in cardinality graph : " << itb->second << ", should be empty." << std::endl;
                  //their intersection is empty (probably?)
                  // e.g. these are two disjoint venn regions, proceed to next pair
                  Assert( ee_areEqual( emp_set, itb->second ) );
                  disjoint = true;
                  break;
                }
              }
              if( !disjoint ){
                //simply introduce their intersection
                Assert( only[0][l]!=only[1][m] );
                Node kca = getProxy( only[0][l] );
                Node kcb = getProxy( only[1][m] );
                Node intro = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::INTERSECTION, kca, kcb ) );
                Trace("sets-nf") << "   Intro split : " << only[0][l] << " against " << only[1][m] << ", term is " << intro << std::endl;
                intro_sets.push_back( intro );
                Assert( !d_equalityEngine.hasTerm( intro ) );
                return;
              }
            }
          }
          //should never get here
          success = false;
        }
      }
      if( success ){
        //normal form is flat form of base
        d_nf[eqc].insert( d_nf[eqc].end(), d_ff[eqc][base].begin(), d_ff[eqc][base].end() );
        Trace("sets-nf") << "----> N " << eqc << " => F " << base << std::endl;
      }else{
        Trace("sets-nf") << "failed to build N " << eqc << std::endl;
        Assert( false );
      }
    }else{
      //normal form is this equivalence class
      d_nf[eqc].push_back( eqc );
      Trace("sets-nf") << "----> N " << eqc << " => { " << eqc << " }" << std::endl;
    }
    if( success ){
      //send to parents
      std::map< Node, std::vector< Node > >::iterator itn = d_nvar_sets.find( eqc );
      if( itn!=d_nvar_sets.end() ){
        std::map< Node, std::map< Node, bool > > parents_proc;
        for( unsigned j=0; j<itn->second.size(); j++ ){
          Node n = itn->second[j];
          Trace("sets-nf-debug") << "Carry nf for term " << n << std::endl;
          if( !d_card_parent[n].empty() ){
            Assert( d_card_base.find( n )!=d_card_base.end() );
            Node cbase = d_card_base[n];
            Trace("sets-nf-debug") << "Card base is " << cbase << std::endl;
            for( unsigned k=0; k<d_card_parent[n].size(); k++ ){
              Node p = d_card_parent[n][k];
              Trace("sets-nf-debug") << "Check parent " << p << std::endl;
              if( parents_proc[cbase].find( p )==parents_proc[cbase].end() ){
                parents_proc[cbase][p] = true;
                Trace("sets-nf-debug") << "Carry nf to parent ( " << cbase << ", [" << p << "] ), from " << n << "..." << std::endl;
                //for( unsigned i=0; i<d_nf[eqc].size(); i++ ){
                //  Assert( std::find( d_ff[p][cbase].begin(), d_ff[p][cbase].end(), d_nf[eqc][i] )==d_ff[p][cbase].end() );
                //}
                for( unsigned i=0; i<d_nf[eqc].size(); i++ ){
                  if( std::find( d_ff[p][cbase].begin(), d_ff[p][cbase].end(), d_nf[eqc][i] )==d_ff[p][cbase].end() ){
                    d_ff[p][cbase].insert( d_ff[p][cbase].end(), d_nf[eqc].begin(), d_nf[eqc].end() );
                  }else{
                    //if it is a duplicate venn region, it must be empty since it is coming from syntactically disjoint siblings TODO?
                  }
                }
              }else{
                Trace("sets-nf-debug") << "..already processed parent " << p << " for " << cbase << std::endl;
              }
            }
          }
        }
      }
    }else{
      Assert( hasProcessed() );
    }
  }
}

void TheorySetsPrivate::checkMinCard( std::vector< Node >& lemmas ) {

  for( int i=(int)(d_set_eqc.size()-1); i>=0; i-- ){
    Node eqc = d_set_eqc[i];
    //get members in class
    std::map< Node, std::map< Node, Node > >::iterator itm = d_pol_mems[0].find( eqc );
    if( itm!=d_pol_mems[0].end() ){
      std::vector< Node > exp;
      std::vector< Node > members;
      Node cardTerm;
      std::map< Node, Node >::iterator it = d_eqc_to_card_term.find( eqc );
      if( it!=d_eqc_to_card_term.end() ){
        cardTerm = it->second;
      }else{
        cardTerm = NodeManager::currentNM()->mkNode( kind::CARD, eqc );
      }
      for( std::map< Node, Node >::iterator itmm = itm->second.begin(); itmm != itm->second.end(); ++itmm ){
      /*
        for( unsigned j=0; j<members.size(); j++ ){
          if( !ee_areDisequal( members[j], itmm->second ) ){
            Assert( !ee_areEqual( members[j], itmm->second ) );
            
          }
        }
      */
        members.push_back( itmm->first );
        exp.push_back( NodeManager::currentNM()->mkNode( kind::MEMBER, itmm->first, cardTerm[0] ) );
      }
      if( members.size()>1 ){
        exp.push_back( NodeManager::currentNM()->mkNode( kind::DISTINCT, members ) );
      }
      if( !members.empty() ){
        Node conc = NodeManager::currentNM()->mkNode( kind::GEQ, cardTerm, NodeManager::currentNM()->mkConst( Rational( members.size() ) ) );
        Node lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp.size()==1 ? exp[0] : NodeManager::currentNM()->mkNode( kind::AND, exp ), conc );
        Trace("sets-lemma") << "Sets::Lemma : " << lem << " by mincard" << std::endl;
        lemmas.push_back( lem );
      }
    }
  }
}

void TheorySetsPrivate::flushLemmas( std::vector< Node >& lemmas, bool preprocess ) {
  for( unsigned i=0; i<lemmas.size(); i++ ){
    flushLemma( lemmas[i], preprocess );
  }
  lemmas.clear();
}

void TheorySetsPrivate::flushLemma( Node lem, bool preprocess ) {
  if( d_lemmas_produced.find(lem)==d_lemmas_produced.end() ){
    Trace("sets-lemma-debug") << "Send lemma : " << lem << std::endl;
    d_lemmas_produced.insert(lem);
    d_external.d_out->lemma(lem, false, preprocess);
    d_sentLemma = true;
  }else{
    Trace("sets-lemma-debug") << "Already sent lemma : " << lem << std::endl;
  }
}

Node TheorySetsPrivate::getProxy( Node n ) {
  if( n.getKind()==kind::EMPTYSET || n.getKind()==kind::SINGLETON || n.getKind()==kind::INTERSECTION || n.getKind()==kind::SETMINUS || n.getKind()==kind::UNION ){
    NodeMap::const_iterator it = d_proxy.find( n );
    if( it==d_proxy.end() ){
      Node k = NodeManager::currentNM()->mkSkolem( "sp", n.getType(), "proxy for set" );
      d_proxy[n] = k;
      d_proxy_to_term[k] = n;
      Node eq = k.eqNode( n );
      Trace("sets-lemma") << "Sets::Lemma : " << eq << " by proxy" << std::endl;
      d_external.d_out->lemma( eq );
      if( n.getKind()==kind::SINGLETON ){
        Node slem = NodeManager::currentNM()->mkNode( kind::MEMBER, n[0], k );
        Trace("sets-lemma") << "Sets::Lemma : " << slem << " by singleton" << std::endl;
        d_external.d_out->lemma( slem );
        d_sentLemma = true;
      }
      return k;
    }else{
      return (*it).second;
    }
  }else{
    return n;
  }
}

Node TheorySetsPrivate::getCongruent( Node n ) {
  Assert( d_equalityEngine.hasTerm( n ) );
  std::map< Node, Node >::iterator it = d_congruent.find( n );
  if( it==d_congruent.end() ){
    return n;
  }else{
    return it->second;
  }
}

Node TheorySetsPrivate::getEmptySet( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_emptyset.find( tn );
  if( it==d_emptyset.end() ){
    Node n = NodeManager::currentNM()->mkConst(EmptySet(tn.toType()));
    d_emptyset[tn] = n;
    return n;
  }else{
    return it->second;
  }
}
Node TheorySetsPrivate::getUnivSet( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_univset.find( tn );
  if( it==d_univset.end() ){
    Node n = NodeManager::currentNM()->mkNullaryOperator(tn, kind::UNIVERSE_SET);
    for( it = d_univset.begin(); it != d_univset.end(); ++it ){
      Node n1;
      Node n2;
      if( tn.isSubtypeOf( it->first ) ){
        n1 = n;
        n2 = it->second;
      }else if( it->first.isSubtypeOf( tn ) ){
        n1 = it->second;
        n2 = n;
      }
      if( !n1.isNull() ){
        Node ulem = NodeManager::currentNM()->mkNode( kind::SUBSET, n1, n2 );
        Trace("sets-lemma") << "Sets::Lemma : " << ulem << " by univ-type" << std::endl;
        d_external.d_out->lemma( ulem );
        d_sentLemma = true;
      }
    }
    d_univset[tn] = n;
    return n;
  }else{
    return it->second;
  }
}

bool TheorySetsPrivate::hasLemmaCached( Node lem ) {
  return d_lemmas_produced.find(lem)!=d_lemmas_produced.end();
}

bool TheorySetsPrivate::hasProcessed() {
  return d_conflict || d_sentLemma || d_addedFact;
}

void TheorySetsPrivate::debugPrintSet( Node s, const char * c ) {
  if( s.getNumChildren()==0 ){
    NodeMap::const_iterator it = d_proxy_to_term.find( s );
    if( it!=d_proxy_to_term.end() ){
      debugPrintSet( (*it).second, c );
    }else{
      Trace(c) << s;
    }
  }else{
    Trace(c) << "(" << s.getOperator();
    for( unsigned i=0; i<s.getNumChildren(); i++ ){
      Trace(c) << " ";
      debugPrintSet( s[i], c );
    }
    Trace(c) << ")";
  }
}

void TheorySetsPrivate::lastCallEffortCheck() {
  Trace("sets") << "----- Last call effort check ------" << std::endl;

}

/**************************** TheorySetsPrivate *****************************/
/**************************** TheorySetsPrivate *****************************/
/**************************** TheorySetsPrivate *****************************/

void TheorySetsPrivate::check(Theory::Effort level) {
  Trace("sets-check") << "Sets check effort " << level << std::endl;
  if( level == Theory::EFFORT_LAST_CALL ){
    lastCallEffortCheck();
    return;
  }
  while(!d_external.done() && !d_conflict) {
    // Get all the assertions
    Assertion assertion = d_external.get();
    TNode fact = assertion.assertion;
    Trace("sets-assert") << "Assert from input " << fact << std::endl;
    //assert the fact
    assertFact( fact, fact );
  }
  d_sentLemma = false;
  Trace("sets-check") << "Sets finished assertions effort " << level << std::endl;
  //invoke full effort check, relations check
  if( !d_conflict ){
    if( level == Theory::EFFORT_FULL ){
      if( !d_external.d_valuation.needCheck() ){
        fullEffortCheck();
        if( !d_conflict && !d_sentLemma ){
          //invoke relations solver
          d_rels->check(level);  
          if( d_card_enabled && ( d_rels_enabled || options::setsExt() ) ){
            //if cardinality constraints are enabled,
            //  then model construction may fail in there are relational operators, or universe set.
            // TODO: should internally check model, return unknown if fail
            d_full_check_incomplete = true;
            Trace("sets-incomplete") << "Sets : incomplete because of extended operators." << std::endl;
          }
        }
        if( d_full_check_incomplete ){
          d_external.d_out->setIncomplete();
        }
      }
    }else{
      if( options::setsRelEager() ){
        d_rels->check(level);  
      }
    }
  }
  Trace("sets-check") << "Sets finish Check effort " << level << std::endl;
}/* TheorySetsPrivate::check() */

bool TheorySetsPrivate::needsCheckLastEffort() {
  if( !d_var_elim.empty() ){
    return true;
  }
  return false;
}

/************************ Sharing ************************/
/************************ Sharing ************************/
/************************ Sharing ************************/

void TheorySetsPrivate::addSharedTerm(TNode n) {
  Debug("sets") << "[sets] ThoerySetsPrivate::addSharedTerm( " << n << ")" << std::endl;
  d_equalityEngine.addTriggerTerm(n, THEORY_SETS);
}

void TheorySetsPrivate::addCarePairs( quantifiers::TermArgTrie * t1, quantifiers::TermArgTrie * t2, unsigned arity, unsigned depth, unsigned& n_pairs ){
  if( depth==arity ){
    if( t2!=NULL ){
      Node f1 = t1->getNodeData();
      Node f2 = t2->getNodeData();
      if( !ee_areEqual( f1, f2 ) ){
        Trace("sets-cg") << "Check " << f1 << " and " << f2 << std::endl;
        vector< pair<TNode, TNode> > currentPairs;
        for (unsigned k = 0; k < f1.getNumChildren(); ++ k) {
          TNode x = f1[k];
          TNode y = f2[k];
          Assert( d_equalityEngine.hasTerm(x) );
          Assert( d_equalityEngine.hasTerm(y) );
          Assert( !ee_areDisequal( x, y ) );
          Assert( !ee_areCareDisequal( x, y ) );
          if( !d_equalityEngine.areEqual( x, y ) ){
            Trace("sets-cg") << "Arg #" << k << " is " << x << " " << y << std::endl;
            if( d_equalityEngine.isTriggerTerm(x, THEORY_SETS) && d_equalityEngine.isTriggerTerm(y, THEORY_SETS) ){
              TNode x_shared = d_equalityEngine.getTriggerTermRepresentative(x, THEORY_SETS);
              TNode y_shared = d_equalityEngine.getTriggerTermRepresentative(y, THEORY_SETS);
              currentPairs.push_back(make_pair(x_shared, y_shared));
            }else if( isCareArg( f1, k ) && isCareArg( f2, k ) ){
              //splitting on sets (necessary for handling set of sets properly)
              if( x.getType().isSet() ){
                Assert( y.getType().isSet() );
                if( !ee_areDisequal( x, y ) ){
                  Trace("sets-cg-lemma") << "Should split on : " << x << "==" << y << std::endl;
                  split( x.eqNode( y ) );
                }
              }
            }
          }
        }
        for (unsigned c = 0; c < currentPairs.size(); ++ c) {
          Trace("sets-cg-pair") << "Pair : " << currentPairs[c].first << " " << currentPairs[c].second << std::endl;
          d_external.addCarePair(currentPairs[c].first, currentPairs[c].second);
          n_pairs++;
        }
      }
    }
  }else{
    if( t2==NULL ){
      if( depth<(arity-1) ){
        //add care pairs internal to each child
        for( std::map< TNode, quantifiers::TermArgTrie >::iterator it = t1->d_data.begin(); it != t1->d_data.end(); ++it ){
          addCarePairs( &it->second, NULL, arity, depth+1, n_pairs );
        }
      }
      //add care pairs based on each pair of non-disequal arguments
      for( std::map< TNode, quantifiers::TermArgTrie >::iterator it = t1->d_data.begin(); it != t1->d_data.end(); ++it ){
        std::map< TNode, quantifiers::TermArgTrie >::iterator it2 = it;
        ++it2;
        for( ; it2 != t1->d_data.end(); ++it2 ){
          if( !d_equalityEngine.areDisequal(it->first, it2->first, false) ){
            if( !ee_areCareDisequal(it->first, it2->first) ){
              addCarePairs( &it->second, &it2->second, arity, depth+1, n_pairs );
            }
          }
        }
      }
    }else{
      //add care pairs based on product of indices, non-disequal arguments
      for( std::map< TNode, quantifiers::TermArgTrie >::iterator it = t1->d_data.begin(); it != t1->d_data.end(); ++it ){
        for( std::map< TNode, quantifiers::TermArgTrie >::iterator it2 = t2->d_data.begin(); it2 != t2->d_data.end(); ++it2 ){
          if( !d_equalityEngine.areDisequal(it->first, it2->first, false) ){
            if( !ee_areCareDisequal(it->first, it2->first) ){
              addCarePairs( &it->second, &it2->second, arity, depth+1, n_pairs );
            }
          }
        }
      }
    }
  }
}

void TheorySetsPrivate::computeCareGraph() {
  for( std::map< Kind, std::vector< Node > >::iterator it = d_op_list.begin(); it != d_op_list.end(); ++it ){
    if( it->first==kind::SINGLETON || it->first==kind::MEMBER ){
      unsigned n_pairs = 0;
      Trace("sets-cg-summary") << "Compute graph for sets, op=" << it->first << "..." << it->second.size() << std::endl;
      Trace("sets-cg") << "Build index for " << it->first << "..." << std::endl;
      std::map< TypeNode, quantifiers::TermArgTrie > index;
      unsigned arity = 0;
      //populate indices
      for( unsigned i=0; i<it->second.size(); i++ ){
        TNode f1 = it->second[i];
        Assert(d_equalityEngine.hasTerm(f1));
        Trace("sets-cg-debug") << "...build for " << f1 << std::endl;
        //break into index based on operator, and type of first argument (since some operators are parametric)
        TypeNode tn = f1[0].getType();
        std::vector< TNode > reps;
        bool hasCareArg = false;
        for( unsigned j=0; j<f1.getNumChildren(); j++ ){
          reps.push_back( d_equalityEngine.getRepresentative( f1[j] ) );
          if( isCareArg( f1, j ) ){
            hasCareArg = true;
          }
        }
        if( hasCareArg ){
          Trace("sets-cg-debug") << "......adding." << std::endl;
          index[tn].addTerm( f1, reps );
          arity = reps.size();
        }else{
          Trace("sets-cg-debug") << "......skip." << std::endl;
        }
      }
      if( arity>0 ){
        //for each index
        for( std::map< TypeNode, quantifiers::TermArgTrie >::iterator iti = index.begin(); iti != index.end(); ++iti ){
          Trace("sets-cg") << "Process index " << iti->first << "..." << std::endl;
          addCarePairs( &iti->second, NULL, arity, 0, n_pairs );
        }
      }
      Trace("sets-cg-summary") << "...done, # pairs = " << n_pairs << std::endl;
    }
  }
}

bool TheorySetsPrivate::isCareArg( Node n, unsigned a ) {
  if( d_equalityEngine.isTriggerTerm( n[a], THEORY_SETS ) ){
    return true;
  }else if( ( n.getKind()==kind::MEMBER || n.getKind()==kind::SINGLETON ) && a==0 && n[0].getType().isSet() ){
    return true;
  }else{
    return false;
  }
}

EqualityStatus TheorySetsPrivate::getEqualityStatus(TNode a, TNode b) {
  Assert(d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b));
  if (d_equalityEngine.areEqual(a, b)) {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }
  if (d_equalityEngine.areDisequal(a, b, false)) {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }
  return EQUALITY_UNKNOWN;
  /*
  Node aModelValue = d_external.d_valuation.getModelValue(a);
  if(aModelValue.isNull()) { return EQUALITY_UNKNOWN; }
  Node bModelValue = d_external.d_valuation.getModelValue(b);
  if(bModelValue.isNull()) { return EQUALITY_UNKNOWN; }
  if( aModelValue == bModelValue ) {
    // The term are true in current model
    return EQUALITY_TRUE_IN_MODEL;
  } else {
    return EQUALITY_FALSE_IN_MODEL;
  }
  */
  // }
  // //TODO: can we be more precise sometimes?
  // return EQUALITY_UNKNOWN;
}

/******************** Model generation ********************/
/******************** Model generation ********************/
/******************** Model generation ********************/

bool TheorySetsPrivate::collectModelInfo(TheoryModel* m)
{
  Trace("sets-model") << "Set collect model info" << std::endl;
  set<Node> termSet;
  // Compute terms appearing in assertions and shared terms
  d_external.computeRelevantTerms(termSet);
  
  // Assert equalities and disequalities to the model
  if (!m->assertEqualityEngine(&d_equalityEngine, &termSet))
  {
    return false;
  }

  std::map< Node, Node > mvals;
  for( int i=(int)(d_set_eqc.size()-1); i>=0; i-- ){
    Node eqc = d_set_eqc[i];
    if( termSet.find( eqc )==termSet.end() ){
      Trace("sets-model") << "* Do not assign value for " << eqc << " since is not relevant." << std::endl;
    }else{
      std::vector< Node > els;
      bool is_base = !d_card_enabled || ( d_nf[eqc].size()==1 && d_nf[eqc][0]==eqc );
      if( is_base ){
        Trace("sets-model") << "Collect elements of base eqc " << eqc << std::endl;
        // members that must be in eqc
        std::map< Node, std::map< Node, Node > >::iterator itm = d_pol_mems[0].find( eqc );
        if( itm!=d_pol_mems[0].end() ){
          for( std::map< Node, Node >::iterator itmm = itm->second.begin(); itmm != itm->second.end(); ++itmm ){
            Node t = NodeManager::currentNM()->mkNode( kind::SINGLETON, itmm->first );
            els.push_back( t );
          }
        }
      }
      if( d_card_enabled ){
        TypeNode elementType = eqc.getType().getSetElementType();
        if( is_base ){
          std::map< Node, Node >::iterator it = d_eqc_to_card_term.find( eqc );
          if( it!=d_eqc_to_card_term.end() ){
            //slack elements from cardinality value
            Node v = d_external.d_valuation.getModelValue(it->second);
            Trace("sets-model") << "Cardinality of " << eqc << " is " << v << std::endl;
            Assert(v.getConst<Rational>() <= LONG_MAX, "Exceeded LONG_MAX in sets model");
            unsigned vu = v.getConst<Rational>().getNumerator().toUnsignedInt();
            Assert( els.size()<=vu );
            while( els.size()<vu ){
              els.push_back( NodeManager::currentNM()->mkNode( kind::SINGLETON, NodeManager::currentNM()->mkSkolem( "msde", elementType ) ) );
            }
          }else{
            Trace("sets-model") << "No slack elements for " << eqc << std::endl;
          }
        }else{
          Trace("sets-model") << "Build value for " << eqc << " based on normal form, size = " << d_nf[eqc].size() << std::endl;
          //it is union of venn regions
          for( unsigned j=0; j<d_nf[eqc].size(); j++ ){
            Assert( mvals.find( d_nf[eqc][j] )!=mvals.end() );
            els.push_back( mvals[d_nf[eqc][j]] );
          }
        }
      }
      Node rep = NormalForm::mkBop( kind::UNION, els, eqc.getType() );
      rep = Rewriter::rewrite( rep );
      Trace("sets-model") << "* Assign representative of " << eqc << " to " << rep << std::endl;
      mvals[eqc] = rep;
      if (!m->assertEquality(eqc, rep, true))
      {
        return false;
      }
      m->assertSkeleton(rep);
    }
  }
  return true;
}

/********************** Helper functions ***************************/
/********************** Helper functions ***************************/
/********************** Helper functions ***************************/

void TheorySetsPrivate::addEqualityToExp( Node a, Node b, std::vector< Node >& exp ) {
  if( a!=b ){
    Assert( ee_areEqual( a, b ) );
    exp.push_back( a.eqNode( b ) );
  }
}

Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  for (unsigned i = 0; i < conjunctions.size(); ++i) {
    TNode t = conjunctions[i];
    if (t.getKind() == kind::AND) {
      for(TNode::iterator child_it = t.begin();
          child_it != t.end(); ++child_it) {
        Assert((*child_it).getKind() != kind::AND);
        all.insert(*child_it);
      }
    }
    else {
      all.insert(t);
    }
  }

  Assert(all.size() > 0);
  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}/* mkAnd() */


TheorySetsPrivate::Statistics::Statistics() :
  d_getModelValueTime("theory::sets::getModelValueTime")
  , d_mergeTime("theory::sets::merge_nodes::time")
  , d_processCard2Time("theory::sets::processCard2::time")
  , d_memberLemmas("theory::sets::lemmas::member", 0)
  , d_disequalityLemmas("theory::sets::lemmas::disequality", 0)
  , d_numVertices("theory::sets::vertices", 0)
  , d_numVerticesMax("theory::sets::vertices-max", 0)
  , d_numMergeEq1or2("theory::sets::merge1or2", 0)
  , d_numMergeEq3("theory::sets::merge3", 0)
  , d_numLeaves("theory::sets::leaves", 0)
  , d_numLeavesMax("theory::sets::leaves-max", 0)
{
  smtStatisticsRegistry()->registerStat(&d_getModelValueTime);
  smtStatisticsRegistry()->registerStat(&d_mergeTime);
  smtStatisticsRegistry()->registerStat(&d_processCard2Time);
  smtStatisticsRegistry()->registerStat(&d_memberLemmas);
  smtStatisticsRegistry()->registerStat(&d_disequalityLemmas);
  smtStatisticsRegistry()->registerStat(&d_numVertices);
  smtStatisticsRegistry()->registerStat(&d_numVerticesMax);
  smtStatisticsRegistry()->registerStat(&d_numMergeEq1or2);
  smtStatisticsRegistry()->registerStat(&d_numMergeEq3);
  smtStatisticsRegistry()->registerStat(&d_numLeaves);
  smtStatisticsRegistry()->registerStat(&d_numLeavesMax);
}


TheorySetsPrivate::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&d_getModelValueTime);
  smtStatisticsRegistry()->unregisterStat(&d_mergeTime);
  smtStatisticsRegistry()->unregisterStat(&d_processCard2Time);
  smtStatisticsRegistry()->unregisterStat(&d_memberLemmas);
  smtStatisticsRegistry()->unregisterStat(&d_disequalityLemmas);
  smtStatisticsRegistry()->unregisterStat(&d_numVertices);
  smtStatisticsRegistry()->unregisterStat(&d_numVerticesMax);
  smtStatisticsRegistry()->unregisterStat(&d_numMergeEq1or2);
  smtStatisticsRegistry()->unregisterStat(&d_numMergeEq3);
  smtStatisticsRegistry()->unregisterStat(&d_numLeaves);
  smtStatisticsRegistry()->unregisterStat(&d_numLeavesMax);
}

void TheorySetsPrivate::propagate(Theory::Effort effort) {

}

bool TheorySetsPrivate::propagate(TNode literal) {
  Debug("sets-prop") << " propagate(" << literal  << ")" << std::endl;

  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("sets-prop") << "TheoryUF::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }

  // Propagate out
  bool ok = d_external.d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }

  return ok;
}/* TheorySetsPrivate::propagate(TNode) */


void TheorySetsPrivate::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}


void TheorySetsPrivate::conflict(TNode a, TNode b)
{
  d_conflictNode = explain(a.eqNode(b));
  d_external.d_out->conflict(d_conflictNode);
  Debug("sets") << "[sets] conflict: " << a << " iff " << b
                << ", explaination " << d_conflictNode << std::endl;
  Trace("sets-lemma") << "Equality Conflict : " << d_conflictNode << std::endl;
  d_conflict = true;
}

Node TheorySetsPrivate::explain(TNode literal)
{
  Debug("sets") << "TheorySetsPrivate::explain(" << literal << ")"
                << std::endl;

  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  std::vector<TNode> assumptions;

  if(atom.getKind() == kind::EQUAL) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else if(atom.getKind() == kind::MEMBER) {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
  } else {
    Debug("sets") << "unhandled: " << literal << "; (" << atom << ", "
                  << polarity << "); kind" << atom.getKind() << std::endl;
    Unhandled();
  }

  return mkAnd(assumptions);
}

void TheorySetsPrivate::preRegisterTerm(TNode node)
{
  Debug("sets") << "TheorySetsPrivate::preRegisterTerm(" << node << ")"
                << std::endl;
  switch(node.getKind()) {
  case kind::EQUAL:
    // TODO: what's the point of this
    d_equalityEngine.addTriggerEquality(node);
    break;
  case kind::MEMBER:
    // TODO: what's the point of this
    d_equalityEngine.addTriggerPredicate(node);
    break;
  case kind::CARD:
    d_equalityEngine.addTriggerTerm(node, THEORY_SETS);
    break;
  default:
    //if( node.getType().isSet() ){
    //  d_equalityEngine.addTriggerTerm(node, THEORY_SETS);
    //}else{
    d_equalityEngine.addTerm(node);
    //}
    break;
  }
}

Node TheorySetsPrivate::expandDefinition(LogicRequest &logicRequest, Node n) {
  Debug("sets-proc") << "expandDefinition : " << n << std::endl;
  if( n.getKind()==kind::UNIVERSE_SET || n.getKind()==kind::COMPLEMENT || n.getKind()==kind::JOIN_IMAGE ){
    if( !options::setsExt() ){
      std::stringstream ss;
      ss << "Extended set operators are not supported in default mode, try --sets-ext.";
      throw LogicException(ss.str());
    }
  }
  return n;
}

Theory::PPAssertStatus TheorySetsPrivate::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  Debug("sets-proc") << "ppAssert : " << in << std::endl;
  Theory::PPAssertStatus status = Theory::PP_ASSERT_STATUS_UNSOLVED;
  
  //TODO: allow variable elimination for sets when setsExt = true
  
  //this is based off of Theory::ppAssert
  Node var;
  if (in.getKind() == kind::EQUAL) {
    if (in[0].isVar() && !in[1].hasSubterm(in[0]) &&
        (in[1].getType()).isSubtypeOf(in[0].getType()) ){
      if( !in[0].getType().isSet() || !options::setsExt() ){
        outSubstitutions.addSubstitution(in[0], in[1]);
        var = in[0];
        status = Theory::PP_ASSERT_STATUS_SOLVED;
      }
    }else if (in[1].isVar() && !in[0].hasSubterm(in[1]) &&
        (in[0].getType()).isSubtypeOf(in[1].getType())){
      if( !in[1].getType().isSet() || !options::setsExt() ){
        outSubstitutions.addSubstitution(in[1], in[0]);
        var = in[1];
        status = Theory::PP_ASSERT_STATUS_SOLVED;
      }
    }else if (in[0].isConst() && in[1].isConst()) {
      if (in[0] != in[1]) {
        status = Theory::PP_ASSERT_STATUS_CONFLICT;
      }
    }
  }
  
  if( status==Theory::PP_ASSERT_STATUS_SOLVED ){
    Trace("sets-var-elim") << "Sets : ppAssert variable eliminated : " << in << ", var = " << var << std::endl;
    /*
    if( var.getType().isSet() ){
      //we must ensure that subs is included in the universe set
      d_var_elim[var] = true;
    } 
    */
    if( options::setsExt() ){
      Assert( !var.getType().isSet() ); 
    }
  }
  return status;
}
  
void TheorySetsPrivate::presolve() {

}

/**************************** eq::NotifyClass *****************************/
/**************************** eq::NotifyClass *****************************/
/**************************** eq::NotifyClass *****************************/


bool TheorySetsPrivate::NotifyClass::eqNotifyTriggerEquality(TNode equality, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerEquality: equality = " << equality
                   << " value = " << value << std::endl;
  if (value) {
    return d_theory.propagate(equality);
  } else {
    // We use only literal triggers so taking not is safe
    return d_theory.propagate(equality.notNode());
  }
}

bool TheorySetsPrivate::NotifyClass::eqNotifyTriggerPredicate(TNode predicate, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerPredicate: predicate = " << predicate
                   << " value = " << value << std::endl;
  if (value) {
    return d_theory.propagate(predicate);
  } else {
    return d_theory.propagate(predicate.notNode());
  }
}

bool TheorySetsPrivate::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerTermEquality: tag = " << tag
                   << " t1 = " << t1 << "  t2 = " << t2 << "  value = " << value << std::endl;
  d_theory.propagate( value ? t1.eqNode( t2 ) : t1.eqNode( t2 ).negate() );
  return true;
}

void TheorySetsPrivate::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyConstantTermMerge " << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.conflict(t1, t2);
}

void TheorySetsPrivate::NotifyClass::eqNotifyNewClass(TNode t)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyNewClass:" << " t = " << t << std::endl;
  d_theory.eqNotifyNewClass(t);
}

void TheorySetsPrivate::NotifyClass::eqNotifyPreMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyPreMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.eqNotifyPreMerge(t1, t2);
}

void TheorySetsPrivate::NotifyClass::eqNotifyPostMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.eqNotifyPostMerge(t1, t2);
}

void TheorySetsPrivate::NotifyClass::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyDisequal:" << " t1 = " << t1 << " t2 = " << t2 << " reason = " << reason << std::endl;
  d_theory.eqNotifyDisequal(t1, t2, reason);
}

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

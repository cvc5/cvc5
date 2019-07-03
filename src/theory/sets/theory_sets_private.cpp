/*********************                                                        */
/*! \file theory_sets_private.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
#include "expr/node_algorithm.h"
#include "options/sets_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/sets/normal_form.h"
#include "theory/sets/theory_sets.h"
#include "theory/theory_model.h"
#include "util/result.h"

#define AJR_IMPLEMENTATION

using namespace std;

namespace CVC4 {
namespace theory {
namespace sets {

TheorySetsPrivate::TheorySetsPrivate(TheorySets& external,
                                     context::Context* c,
                                     context::UserContext* u)
    : d_members(c),
      d_deq(c),
      d_deq_processed(u),
      d_keep(c),
      d_sentLemma(false),
      d_addedFact(false),
      d_full_check_incomplete(false),
      d_lemmas_produced(u),
      d_card_enabled(false),
      d_var_elim(u),
      d_external(external),
      d_notify(*this),
      d_equalityEngine(d_notify, c, "theory::sets::ee", true),
      d_conflict(c),
      d_state(*this,d_equalityEngine,c,u),
      d_rels(
          new TheorySetsRels(c, u, &d_equalityEngine, &d_conflict, external)),
          d_cardSolver(new CardinalityExtension(*this,d_state,d_equalityEngine,c,u)),
      d_rels_enabled(false)
{
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
  d_zero = NodeManager::currentNM()->mkConst( Rational(0) );

  d_equalityEngine.addFunctionKind(kind::SINGLETON);
  d_equalityEngine.addFunctionKind(kind::UNION);
  d_equalityEngine.addFunctionKind(kind::INTERSECTION);
  d_equalityEngine.addFunctionKind(kind::SETMINUS);

  d_equalityEngine.addFunctionKind(kind::MEMBER);
  d_equalityEngine.addFunctionKind(kind::SUBSET);
}

TheorySetsPrivate::~TheorySetsPrivate(){
  for (std::pair<const Node, EqcInfo*>& current_pair : d_eqc_info) {
    delete current_pair.second;
  }
}

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
          if( d_state.areEqual( m2[0], d_members_data[t1][j][0] ) ){
            add = false;
            break;
          }
        }
        if( add ){
          if( !s1.isNull() && s2.isNull() ){
            Assert( m2[1].getType().isComparableTo( s1.getType() ) );
            Assert( d_state.areEqual( m2[1], s1 ) );
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

bool TheorySetsPrivate::areCareDisequal( Node a, Node b ) {
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

bool TheorySetsPrivate::isMember( Node x, Node s ) {
  Assert( d_equalityEngine.hasTerm( s ) && d_equalityEngine.getRepresentative( s )==s );
  NodeIntMap::iterator mem_i = d_members.find( s );
  if( mem_i != d_members.end() ) {
    for( int i=0; i<(*mem_i).second; i++ ){
      if( d_state.areEqual( d_members_data[s][i][0], x ) ){
        return true;
      }
    }
  }
  return false;
}
        
bool TheorySetsPrivate::assertFact( Node fact, Node exp ){
  Trace("sets-assert") << "TheorySets::assertFact : " << fact << ", exp = " << exp << std::endl;
  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];
  if( !d_state.isEntailed( atom, polarity ) ){
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
    if( !d_state.isEntailed( fact, true ) ){
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
        if( !d_state.isEntailed( fact, true ) ){
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
    d_most_common_type.clear();
    d_most_common_type_term.clear();
    d_card_enabled = false;
    d_rels_enabled = false;
    d_state.reset();
    d_cardSolver->reset();

    std::vector< Node > lemmas;
    Trace("sets-eqc") << "Equality Engine:" << std::endl;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
    while( !eqcs_i.isFinished() ){
      Node eqc = (*eqcs_i);
      bool isSet = false;
      TypeNode tn = eqc.getType();
      d_state.registerEqc(tn,eqc);
      //common type node and term
      TypeNode tnc;
      Node tnct;
      if( tn.isSet() ){
        isSet = true;
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
        d_state.registerTerm(eqc,tnn,n);
        if( n.getKind()==kind::CARD ){
          d_card_enabled = true;
          d_cardSolver->registerTerm(n,lemmas);
          // if we do not handle the kind, set incomplete
          Kind nk = n[0].getKind();
          if (nk == kind::UNIVERSE_SET || d_rels->isRelationKind(nk))
          {
            d_full_check_incomplete = true;
            Trace("sets-incomplete")
                << "Sets : incomplete because of " << n << "." << std::endl;
            // TODO (#1124) handle this case
          }
        }else{
          if( d_rels->isRelationKind( n.getKind() ) ){
            d_rels_enabled = true;
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
    Trace("sets-eqc") << "...finished equality engine." << std::endl;
    
    flushLemmas( lemmas );
    if( !hasProcessed() ){
      // FIXME
      /*
      if( Trace.isOn("sets-mem") ){
        std::vector< Node >& sec = d_state.getSetsEqClasses();
        for( const Node& s : sec ){
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
      */
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
            checkDisequalities(lemmas);
            flushLemmas(lemmas);
            if (!hasProcessed() && d_card_enabled)
            {
              d_cardSolver->check();
            }
          }
        }
      }
    }
  }while( !d_sentLemma && !d_conflict && d_addedFact );
  Trace("sets") << "----- End full effort check, conflict=" << d_conflict << ", lemma=" << d_sentLemma << std::endl;
}

void TheorySetsPrivate::checkSubtypes( std::vector< Node >& lemmas ) {
  Trace("sets") << "TheorySetsPrivate: check Subtypes..." << std::endl; 
  std::vector< Node >& sec = d_state.getSetsEqClasses();
  for( const Node& s : sec ){
    TypeNode mct = d_most_common_type[s];
    Assert( !mct.isNull() );
    std::map< Node, Node >& smems = d_state.getMembers(s);
    if( !smems.empty() ){
      for( std::map< Node, Node >::iterator it2 = smems.begin(); it2 != smems.end(); ++it2 ){
        Trace("sets") << "  check subtype " << it2->first << " " << it2->second << std::endl;
        Trace("sets") << "    types : " << it2->first.getType() << " " << mct << std::endl;
        if (!it2->first.getType().isSubtypeOf(mct))
        {
          Node mctt = d_most_common_type_term[s];
          Assert( !mctt.isNull() );
          Trace("sets") << "    most common type term is " << mctt << std::endl;
          std::vector< Node > exp;
          exp.push_back( it2->second );
          Assert( d_state.areEqual( mctt, it2->second[1] ) );
          exp.push_back( mctt.eqNode( it2->second[1] ) );
          Node tc_k = d_state.getTypeConstraintSkolem(it2->first, mct);
          if (!tc_k.isNull())
          {
            Node etc = tc_k.eqNode(it2->first);
            assertInference( etc, exp, lemmas, "subtype-clash" );
            if( d_conflict ){
              return;
            }
          }
        }
      }
    }
  }
  Trace("sets") << "TheorySetsPrivate: finished." << std::endl;
}

void TheorySetsPrivate::checkDownwardsClosure( std::vector< Node >& lemmas ) {
  Trace("sets") << "Downwards closure..." << std::endl;
  //downwards closure
  // FIXME
  for( std::map< Node, std::map< Node, Node > >::iterator it = d_state.d_pol_mems[0].begin(); it != d_state.d_pol_mems[0].end(); ++it ){
    std::vector< Node >& nvsets = d_state.getNonVariableSets( it->first );
    if( !nvsets.empty() ){
      for( unsigned j=0; j<nvsets.size(); j++ ){
        if( !d_state.isCongruent( nvsets[j] ) ){
          for( std::map< Node, Node >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){ 
            Node mem = it2->second;
            Node eq_set = nvsets[j];
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
                Node k = d_state.getProxy( eq_set );
                Node pmem = NodeManager::currentNM()->mkNode( kind::MEMBER, mem[0], k );
                Node nmem = NodeManager::currentNM()->mkNode( kind::MEMBER, mem[0], eq_set );
                nmem = Rewriter::rewrite( nmem );
                std::vector< Node > exp;
                if( d_state.areEqual( mem, pmem ) ){
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
  // FIXME
  for( std::map< Kind, std::map< Node, std::map< Node, Node > > >::iterator itb = d_state.d_bop_index.begin(); itb != d_state.d_bop_index.end(); ++itb ){
    Kind k = itb->first;
    Trace("sets") << "Upwards closure " << k << "..." << std::endl;
    for( std::map< Node, std::map< Node, Node > >::iterator it = itb->second.begin(); it != itb->second.end(); ++it ){
      Node r1 = it->first;
      //see if there are members in first argument r1
      std::map< Node, Node >& r1mem = d_state.getMembers(r1);
      if( !r1mem.empty() || k==kind::UNION ){
        for( std::map< Node, Node >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
          Node r2 = it2->first;
          //see if there are members in second argument
          std::map< Node, Node >& r2mem = d_state.getMembers(r2);
          std::map< Node, Node >& r2nmem = d_state.getNegativeMembers(r2);
          if( !r2mem.empty() || k!=kind::INTERSECTION ){
            Trace("sets-debug") << "Checking " << it2->second << ", members = " << (!r1mem.empty()) << ", " << (!r2mem.empty()) << std::endl;
            //for all members of r1
            if( !r1mem.empty() ){
              for( std::map< Node, Node >::iterator itm1m = r1mem.begin(); itm1m != r1mem.end(); ++itm1m ){
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
                  std::map< Node, Node >::iterator itm = r2mem.find(xr);
                  if( itm!=r2mem.end() ){
                    exp.push_back( itm->second );
                    addEqualityToExp( it2->second[1], itm->second[1], exp );
                    addEqualityToExp( x, itm->second[0], exp );
                    valid = true;
                  }else{
                    // if not, check whether it is definitely not a member, if unknown, split
                    if( r2nmem.find(xr)==r2nmem.end() ){
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
                    std::map< Node, Node >::iterator itm = r2mem.find(xr);
                    if( itm==r2mem.end() ){
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
                    Node kk = d_state.getProxy( it2->second );
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
              if( !r2mem.empty() ){
                //for all members of r2
                for( std::map< Node, Node >::iterator itm2m = r2mem.begin(); itm2m != r2mem.end(); ++itm2m ){
                  Node x = itm2m->second[0];
                  Node rr = d_equalityEngine.getRepresentative( it2->second );
                  if( !isMember( x, rr ) ){
                    std::vector< Node > exp;
                    exp.push_back( itm2m->second );
                    addEqualityToExp( it2->second[1], itm2m->second[1], exp );
                    Node k = d_state.getProxy( it2->second );
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
      for( std::map< Node, std::map< Node, Node > >::iterator it = d_state.d_pol_mems[0].begin(); it != d_state.d_pol_mems[0].end(); ++it ){
        //if equivalence class contains a variable
        Node v = d_state.getVariableSet( it->first );
        if( !v.isNull() ){
          //the variable in the equivalence class
          std::map< TypeNode, Node > univ_set;
          for( std::map< Node, Node >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
            Node e = it2->second[0];
            TypeNode tn = NodeManager::currentNM()->mkSetType( e.getType() );
            Node u;
            std::map< TypeNode, Node >::iterator itu = univ_set.find( tn );
            if( itu==univ_set.end() ){
              Node ueqc = d_state.getUnivSetEqClass(tn);
              // if the universe does not yet exist, or is not in this equivalence class
              if( itu->second!=ueqc ){
                u = d_state.getUnivSet( tn );
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
      bool is_sat = d_state.isSetDisequalityEntailed( r1, r2 );
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

bool TheorySetsPrivate::hasLemmaCached( Node lem ) {
  return d_lemmas_produced.find(lem)!=d_lemmas_produced.end();
}

bool TheorySetsPrivate::hasProcessed() {
  return d_conflict || d_sentLemma || d_addedFact;
}

void TheorySetsPrivate::debugPrintSet( Node s, const char * c ) {
  /*
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
  */
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
        }
        if (!d_conflict && !d_sentLemma && d_full_check_incomplete)
        {
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

void TheorySetsPrivate::addCarePairs(TNodeTrie* t1,
                                     TNodeTrie* t2,
                                     unsigned arity,
                                     unsigned depth,
                                     unsigned& n_pairs)
{
  if( depth==arity ){
    if( t2!=NULL ){
      Node f1 = t1->getData();
      Node f2 = t2->getData();
      if( !d_state.areEqual( f1, f2 ) ){
        Trace("sets-cg") << "Check " << f1 << " and " << f2 << std::endl;
        vector< pair<TNode, TNode> > currentPairs;
        for (unsigned k = 0; k < f1.getNumChildren(); ++ k) {
          TNode x = f1[k];
          TNode y = f2[k];
          Assert( d_equalityEngine.hasTerm(x) );
          Assert( d_equalityEngine.hasTerm(y) );
          Assert( !d_state.areDisequal( x, y ) );
          Assert( !areCareDisequal( x, y ) );
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
                if( !d_state.areDisequal( x, y ) ){
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
        for (std::pair<const TNode, TNodeTrie>& t : t1->d_data)
        {
          addCarePairs(&t.second, NULL, arity, depth + 1, n_pairs);
        }
      }
      //add care pairs based on each pair of non-disequal arguments
      for (std::map<TNode, TNodeTrie>::iterator it = t1->d_data.begin();
           it != t1->d_data.end();
           ++it)
      {
        std::map<TNode, TNodeTrie>::iterator it2 = it;
        ++it2;
        for( ; it2 != t1->d_data.end(); ++it2 ){
          if( !d_equalityEngine.areDisequal(it->first, it2->first, false) ){
            if( !areCareDisequal(it->first, it2->first) ){
              addCarePairs( &it->second, &it2->second, arity, depth+1, n_pairs );
            }
          }
        }
      }
    }else{
      //add care pairs based on product of indices, non-disequal arguments
      for (std::pair<const TNode, TNodeTrie>& tt1 : t1->d_data)
      {
        for (std::pair<const TNode, TNodeTrie>& tt2 : t2->d_data)
        {
          if (!d_equalityEngine.areDisequal(tt1.first, tt2.first, false))
          {
            if (!areCareDisequal(tt1.first, tt2.first))
            {
              addCarePairs(&tt1.second, &tt2.second, arity, depth + 1, n_pairs);
            }
          }
        }
      }
    }
  }
}

void TheorySetsPrivate::computeCareGraph() {
  // FIXME
  for( std::map< Kind, std::vector< Node > >::iterator it = d_state.d_op_list.begin(); it != d_state.d_op_list.end(); ++it ){
    if( it->first==kind::SINGLETON || it->first==kind::MEMBER ){
      unsigned n_pairs = 0;
      Trace("sets-cg-summary") << "Compute graph for sets, op=" << it->first << "..." << it->second.size() << std::endl;
      Trace("sets-cg") << "Build index for " << it->first << "..." << std::endl;
      std::map<TypeNode, TNodeTrie> index;
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
        for (std::pair<const TypeNode, TNodeTrie>& tt : index)
        {
          Trace("sets-cg") << "Process index " << tt.first << "..."
                           << std::endl;
          addCarePairs(&tt.second, nullptr, arity, 0, n_pairs);
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
  // FIXME: this is ugly
  std::vector< Node >& sec = d_card_enabled ? d_cardSolver->getSetsEqClasses() : d_state.getSetsEqClasses();
  for( int i=(int)(sec.size()-1); i>=0; i-- ){
    Node eqc = sec[i];
    if( termSet.find( eqc )==termSet.end() ){
      Trace("sets-model") << "* Do not assign value for " << eqc << " since is not relevant." << std::endl;
    }else{
      std::vector< Node > els;
      bool is_base = !d_card_enabled || d_cardSolver->isModelValueBasic(eqc);
      if( is_base ){
        Trace("sets-model") << "Collect elements of base eqc " << eqc << std::endl;
        // members that must be in eqc
        std::map< Node, Node >& emems = d_state.getMembers(eqc);
        if( !emems.empty() ){
          for( std::pair< const Node, Node >& itmm : emems ){
            Node t = NodeManager::currentNM()->mkNode( kind::SINGLETON, itmm.first );
            els.push_back( t );
          }
        }
      }
      if( d_card_enabled ){
        // make the slack elements for the equivalence class based on set cardinality
        d_cardSolver->mkModelValueElementsFor(eqc,els,mvals);
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
    Assert( d_state.areEqual( a, b ) );
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

OutputChannel* TheorySetsPrivate::getOutputChannel()
{
  return d_external.d_out;
}

Valuation& TheorySetsPrivate::getValuation()
{
  return d_external.d_valuation;
}
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
  if (in.getKind() == kind::EQUAL)
  {
    if (in[0].isVar() && !expr::hasSubterm(in[1], in[0])
        && (in[1].getType()).isSubtypeOf(in[0].getType()))
    {
      if (!in[0].getType().isSet() || !options::setsExt())
      {
        outSubstitutions.addSubstitution(in[0], in[1]);
        var = in[0];
        status = Theory::PP_ASSERT_STATUS_SOLVED;
      }
    }
    else if (in[1].isVar() && !expr::hasSubterm(in[0], in[1])
             && (in[0].getType()).isSubtypeOf(in[1].getType()))
    {
      if (!in[1].getType().isSet() || !options::setsExt())
      {
        outSubstitutions.addSubstitution(in[1], in[0]);
        var = in[1];
        status = Theory::PP_ASSERT_STATUS_SOLVED;
      }
    }
    else if (in[0].isConst() && in[1].isConst())
    {
      if (in[0] != in[1])
      {
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
  d_state.reset();
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

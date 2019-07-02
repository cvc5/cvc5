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

#include "theory/sets/sets_state.h"

#include "expr/emptyset.h"
#include "expr/node_algorithm.h"
#include "options/sets_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/sets/normal_form.h"
#include "theory/sets/theory_sets.h"
#include "theory/theory_model.h"
#include "util/result.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

SetsState::SetsState(TheorySetsPrivate& p,
                eq::EqualityEngine& e,
                  context::Context* c,
                  context::UserContext* u) :
      d_ee(e),
      d_proxy(u),
      d_proxy_to_term(u)
{
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}

void SetsState::reset()
{
  d_set_eqc.clear();
  d_eqc_emptyset.clear();
  d_eqc_univset.clear();
  d_eqc_singleton.clear();
  d_congruent.clear();
  d_nvar_sets.clear();
  d_var_set.clear();
  d_pol_mems[0].clear();
  d_pol_mems[1].clear();
  d_members_index.clear();
  d_singleton_index.clear();
  d_bop_index.clear();
  d_op_list.clear();
}

void SetsState::registerEqc(TypeNode tn, Node r)
{
  if( tn.isSet() )
  {
    d_set_eqc.push_back( r );
  }
}
  
void SetsState::registerTerm(Node r, TypeNode tnn, Node n)
{
  Kind nk = n.getKind();
  if( nk==MEMBER ){
    if( r.isConst() ){
      Node s = d_ee.getRepresentative( n[1] );
      Node x = d_ee.getRepresentative( n[0] );
      int pindex = r==d_true ? 0 : ( r==d_false ? 1 : -1 );
      if( pindex!=-1  ){
        if( d_pol_mems[pindex][s].find( x )==d_pol_mems[pindex][s].end() ){
          d_pol_mems[pindex][s][x] = n;
          Trace("sets-debug2") << "Membership[" << x << "][" << s << "] : " << n << ", pindex = " << pindex << std::endl;
        }
        if( d_members_index[s].find( x )==d_members_index[s].end() ){
          d_members_index[s][x] = n;
          d_op_list[MEMBER].push_back( n );
        }
      }else{
        Assert( false );
      }
    }
  }else if( nk==SINGLETON || nk==UNION || nk==INTERSECTION || 
            nk==SETMINUS || nk==EMPTYSET || nk==UNIVERSE_SET ){
    if( nk==SINGLETON ){
      //singleton lemma
      getProxy( n );
      Node r = d_ee.getRepresentative( n[0] );
      if( d_singleton_index.find( r )==d_singleton_index.end() ){
        d_singleton_index[r] = n;
        d_eqc_singleton[r] = n;
        d_op_list[SINGLETON].push_back( n );
      }else{
        d_congruent[n] = d_singleton_index[r];
      }
    }else if( nk==EMPTYSET ){
      d_eqc_emptyset[tnn] = r;
    }else if( nk==UNIVERSE_SET ){
      Assert( options::setsExt() );
      d_eqc_univset[tnn] = r;
    }else{
      Node r1 = d_ee.getRepresentative( n[0] );
      Node r2 = d_ee.getRepresentative( n[1] );
      std::map<Node, Node>& binr1 = d_bop_index[nk][r1];
      std::map<Node, Node>::iterator itb = binr1.find(r2);
      if (itb == binr1.end())
      {
        binr1[r2] = n;
        d_op_list[nk].push_back( n );
      }else{
        d_congruent[n] = itb->second;
      }
    }
    d_nvar_sets[r].push_back( n );
    Trace("sets-debug2") << "Non-var-set[" << r << "] : " << n << std::endl;
  }
  else if( n.isVar() )
  {
    if( tnn.isSet() ){
      if( d_var_set.find( r )==d_var_set.end() ){
        d_var_set[r] = n;
      }
    }
  }
}
  
bool SetsState::ee_areEqual( Node a, Node b ) {
  if( a==b ){
    return true;
  }
  if( d_ee.hasTerm( a ) && d_ee.hasTerm( b ) ){
    return d_ee.areEqual( a, b );
  }
  return false;
}

bool SetsState::ee_areDisequal( Node a, Node b ) {
  if( a==b ){
    return false;
  }else if( d_ee.hasTerm( a ) && d_ee.hasTerm( b ) ){
      return d_ee.areDisequal( a, b, false );
    }
      return a.isConst() && b.isConst();
}

Node SetsState::getEmptySetEqClass( TypeNode tn ) const
{
  std::map< TypeNode, Node >::const_iterator it = d_eqc_emptyset.find(tn);
  if( it != d_eqc_emptyset.end() )
  {
    return it->second;
  }
  return Node::null();
}

Node SetsState::getSingletonEqClass( Node r ) const
{
  std::map< Node, Node >::const_iterator it =  d_eqc_singleton.find(r);
  if( it != d_eqc_singleton.end() )
  {
    return it->second;
  }
  return Node::null();
}

Node SetsState::getBinaryOpTerm( Kind k, Node r1, Node r2 ) const
{
  std::map< Kind, std::map< Node, std::map< Node, Node > > >::const_iterator itk = d_bop_index.find(k);
  if( itk==d_bop_index.end() )
  {
    return Node::null();
  }
  std::map< Node, std::map< Node, Node > >::const_iterator it1 = itk->second.find(r1);
  if( it1==itk->second.end() )
  {
    return Node::null();
  }
  std::map< Node, Node >::const_iterator it2 = it1->second.find(r2);
  if( it2==it1->second.end() )
  {
    return Node::null();
  }
  return it2->second;
}

bool SetsState::isEntailed( Node n, bool polarity ) {
  if( n.getKind()==NOT ){
    return isEntailed( n[0], !polarity );
  }else if( n.getKind()==EQUAL ){
    if( polarity ){
      return ee_areEqual( n[0], n[1] );
    }
    return ee_areDisequal( n[0], n[1] );
  }else if( n.getKind()==AND || n.getKind()==OR ){
    bool conj = (n.getKind()==AND)==polarity;
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
  return ee_areEqual( n, polarity ? d_true : d_false );
}

bool SetsState::isSetDisequalityEntailed( Node r1, Node r2 ) {
  Assert( d_ee.hasTerm( r1 ) && d_ee.getRepresentative( r1 )==r1 );
  Assert( d_ee.hasTerm( r2 ) && d_ee.getRepresentative( r2 )==r2 );
  TypeNode tn = r1.getType();
  Node eqc_es = d_eqc_emptyset[tn];
  bool is_sat = false;
  for( unsigned e=0; e<2; e++ ){
    Node a = e==0 ? r1 : r2;
    Node b = e==0 ? r2 : r1;
    //if there are members in a
    std::map< Node, std::map< Node, Node > >::iterator itpma = d_pol_mems[0].find( a );
    if( itpma==d_pol_mems[0].end() ){
      // no positive members, continue
      continue;
    }
    Assert( !itpma->second.empty() );
    //if b is empty
    if( b==eqc_es ){
      if( !itpma->second.empty() ){
        is_sat = true;
        Trace("sets-deq") << "Disequality is satisfied because members are in " << a << " and " << b << " is empty" << std::endl;
        break;
      }else{
        //a should not be singleton
        Assert( d_eqc_singleton.find( a )==d_eqc_singleton.end() );
      }
      continue;
    }
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
    if( is_sat ){
      break;
    }
  }
  return is_sat;
}

Node SetsState::getProxy( Node n ) {
  Kind nk = n.getKind();
  if( nk!=EMPTYSET && nk!=SINGLETON && nk!=INTERSECTION && nk!=SETMINUS && nk!=UNION ){
    return n;
  }
  NodeMap::const_iterator it = d_proxy.find( n );
  if( it!=d_proxy.end() ){
    return (*it).second;
  }
  NodeManager * nm = NodeManager::currentNM();
  Node k = nm->mkSkolem( "sp", n.getType(), "proxy for set" );
  d_proxy[n] = k;
  d_proxy_to_term[k] = n;
  Node eq = k.eqNode( n );
  // FIXME
  //Trace("sets-lemma") << "Sets::Lemma : " << eq << " by proxy" << std::endl;
  //d_external.d_out->lemma( eq );
  if( nk==SINGLETON ){
    Node slem = nm->mkNode( MEMBER, n[0], k );
    // FIXME
    //Trace("sets-lemma") << "Sets::Lemma : " << slem << " by singleton" << std::endl;
    //d_external.d_out->lemma( slem );
    //d_sentLemma = true;
  }
  return k;
}

Node SetsState::getCongruent( Node n ) {
  Assert( d_ee.hasTerm( n ) );
  std::map< Node, Node >::iterator it = d_congruent.find( n );
  if( it==d_congruent.end() ){
    return n;
  }
  return it->second;
}

Node SetsState::getEmptySet( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_emptyset.find( tn );
  if( it!=d_emptyset.end() ){
    return it->second;
  }
  Node n = NodeManager::currentNM()->mkConst(EmptySet(tn.toType()));
  d_emptyset[tn] = n;
  return n;
}
Node SetsState::getUnivSet( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_univset.find( tn );
  if( it!=d_univset.end() ){
    return it->second;
  }
  NodeManager * nm = NodeManager::currentNM();
  Node n = nm->mkNullaryOperator(tn, UNIVERSE_SET);
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
      Node ulem = nm->mkNode( SUBSET, n1, n2 );
      Trace("sets-lemma") << "Sets::Lemma : " << ulem << " by univ-type" << std::endl;      
      // FIXME
      //d_external.d_out->lemma( ulem );
      //d_sentLemma = true;
    }
  }
  d_univset[tn] = n;
  return n;
}

Node SetsState::getTypeConstraintSkolem(Node n, TypeNode tn)
{
  std::map<TypeNode, Node>::iterator it = d_tc_skolem[n].find(tn);
  if (it != d_tc_skolem[n].end())
  {
    Node k = NodeManager::currentNM()->mkSkolem("tc_k", tn);
    d_tc_skolem[n][tn] = k;
    return k;
  }
  return it->second;
}

bool SetsState::hasMembers(Node r) const
{
  std::map< Node, std::map< Node, Node > >::const_iterator it = d_pol_mems[0].find(r);
  if( it==d_pol_mems[0].end() )
  {
    return false;
  }
  return !it->second.empty();
}

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

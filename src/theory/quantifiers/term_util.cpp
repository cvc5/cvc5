/*********************                                                        */
/*! \file term_util.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term utilities class
 **/

#include "theory/quantifiers/term_util.h"

#include "expr/datatype.h"
#include "options/base_options.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "options/uf_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory::inst;

namespace CVC4 {
namespace theory {
namespace quantifiers {

TermUtil::TermUtil(QuantifiersEngine * qe) :
d_quantEngine(qe),
d_op_id_count(0),
d_typ_id_count(0){
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
}

TermUtil::~TermUtil(){

}

void TermUtil::registerQuantifier( Node q ){
  if( d_inst_constants.find( q )==d_inst_constants.end() ){
    Debug("quantifiers-engine") << "Instantiation constants for " << q << " : " << std::endl;
    for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
      d_vars[q].push_back( q[0][i] );
      d_var_num[q][q[0][i]] = i;
      //make instantiation constants
      Node ic = NodeManager::currentNM()->mkInstConstant( q[0][i].getType() );
      d_inst_constants_map[ic] = q;
      d_inst_constants[ q ].push_back( ic );
      Debug("quantifiers-engine") << "  " << ic << std::endl;
      //set the var number attribute
      InstVarNumAttribute ivna;
      ic.setAttribute( ivna, i );
      InstConstantAttribute ica;
      ic.setAttribute( ica, q );
    }
  }
}

void TermUtil::getBoundVars2( Node n, std::vector< Node >& vars, std::map< Node, bool >& visited ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==BOUND_VARIABLE ){
      if( std::find( vars.begin(), vars.end(), n )==vars.end() ) {
        vars.push_back( n );
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      getBoundVars2( n[i], vars, visited );
    }
  }
}

Node TermUtil::getRemoveQuantifiers2( Node n, std::map< Node, Node >& visited ) {
  std::map< Node, Node >::iterator it = visited.find( n );
  if( it!=visited.end() ){
    return it->second;
  }else{
    Node ret = n;
    if( n.getKind()==FORALL ){
      ret = getRemoveQuantifiers2( n[1], visited );
    }else if( n.getNumChildren()>0 ){
      std::vector< Node > children;
      bool childrenChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node ni = getRemoveQuantifiers2( n[i], visited );
        childrenChanged = childrenChanged || ni!=n[i];
        children.push_back( ni );
      }
      if( childrenChanged ){
        if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
          children.insert( children.begin(), n.getOperator() );
        }
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
    visited[n] = ret;
    return ret;
  }
}

Node TermUtil::getInstConstAttr( Node n ) {
  if (!n.hasAttribute(InstConstantAttribute()) ){
    Node q;
    if (n.hasOperator())
    {
      q = getInstConstAttr(n.getOperator());
    }
    if (q.isNull())
    {
      for (const Node& nc : n)
      {
        q = getInstConstAttr(nc);
        if (!q.isNull())
        {
          break;
        }
      }
    }
    InstConstantAttribute ica;
    n.setAttribute(ica, q);
  }
  return n.getAttribute(InstConstantAttribute());
}

bool TermUtil::hasInstConstAttr( Node n ) {
  return !getInstConstAttr(n).isNull();
}

Node TermUtil::getBoundVarAttr( Node n ) {
  if (!n.hasAttribute(BoundVarAttribute()) ){
    Node bv;
    if( n.getKind()==BOUND_VARIABLE ){
      bv = n;
    }else{
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        bv = getBoundVarAttr(n[i]);
        if( !bv.isNull() ){
          break;
        }
      }
    }
    BoundVarAttribute bva;
    n.setAttribute(bva, bv);
  }
  return n.getAttribute(BoundVarAttribute());
}

bool TermUtil::hasBoundVarAttr( Node n ) {
  return !getBoundVarAttr(n).isNull();
}

void TermUtil::getBoundVars( Node n, std::vector< Node >& vars ) {
  std::map< Node, bool > visited;
  return getBoundVars2( n, vars, visited );
}

//remove quantifiers
Node TermUtil::getRemoveQuantifiers( Node n ) {
  std::map< Node, Node > visited;
  return getRemoveQuantifiers2( n, visited );
}

//quantified simplify
Node TermUtil::getQuantSimplify( Node n ) {
  std::vector< Node > bvs;
  getBoundVars( n, bvs );
  if( bvs.empty() ) {
    return Rewriter::rewrite( n );
  }else{
    Node q = NodeManager::currentNM()->mkNode( FORALL, NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, bvs ), n );
    q = Rewriter::rewrite( q );
    return getRemoveQuantifiers( q );
  }
}

/** get the i^th instantiation constant of q */
Node TermUtil::getInstantiationConstant( Node q, int i ) const {
  std::map< Node, std::vector< Node > >::const_iterator it = d_inst_constants.find( q );
  if( it!=d_inst_constants.end() ){
    return it->second[i];
  }else{
    return Node::null();
  }
}

/** get number of instantiation constants for q */
unsigned TermUtil::getNumInstantiationConstants( Node q ) const {
  std::map< Node, std::vector< Node > >::const_iterator it = d_inst_constants.find( q );
  if( it!=d_inst_constants.end() ){
    return it->second.size();
  }else{
    return 0;
  }
}

Node TermUtil::getInstConstantBody( Node q ){
  std::map< Node, Node >::iterator it = d_inst_const_body.find( q );
  if( it==d_inst_const_body.end() ){
    Node n = substituteBoundVariablesToInstConstants(q[1], q);
    d_inst_const_body[ q ] = n;
    return n;
  }else{
    return it->second;
  }
}

Node TermUtil::getCounterexampleLiteral( Node q ){
  if( d_ce_lit.find( q )==d_ce_lit.end() ){
    /*
    Node ceBody = getInstConstantBody( f );
    //check if any variable are of bad types, and fail if so
    for( size_t i=0; i<d_inst_constants[f].size(); i++ ){
      if( d_inst_constants[f][i].getType().isBoolean() ){
        d_ce_lit[ f ] = Node::null();
        return Node::null();
      }
    }
    */
    Node g = NodeManager::currentNM()->mkSkolem( "g", NodeManager::currentNM()->booleanType() );
    //otherwise, ensure literal
    Node ceLit = d_quantEngine->getValuation().ensureLiteral( g );
    d_ce_lit[ q ] = ceLit;
  }
  return d_ce_lit[ q ];
}

Node TermUtil::substituteBoundVariablesToInstConstants(Node n, Node q)
{
  registerQuantifier( q );
  return n.substitute( d_vars[q].begin(), d_vars[q].end(), d_inst_constants[q].begin(), d_inst_constants[q].end() );
}

Node TermUtil::substituteInstConstantsToBoundVariables(Node n, Node q)
{
  registerQuantifier( q );
  return n.substitute( d_inst_constants[q].begin(), d_inst_constants[q].end(), d_vars[q].begin(), d_vars[q].end() );
}

Node TermUtil::substituteBoundVariables(Node n,
                                        Node q,
                                        std::vector<Node>& terms)
{
  registerQuantifier(q);
  Assert( d_vars[q].size()==terms.size() );
  return n.substitute( d_vars[q].begin(), d_vars[q].end(), terms.begin(), terms.end() );
}

Node TermUtil::substituteInstConstants(Node n, Node q, std::vector<Node>& terms)
{
  registerQuantifier(q);
  Assert(d_inst_constants[q].size() == terms.size());
  return n.substitute(d_inst_constants[q].begin(),
                      d_inst_constants[q].end(),
                      terms.begin(),
                      terms.end());
}

void TermUtil::computeVarContains( Node n, std::vector< Node >& varContains ) {
  std::map< Node, bool > visited;
  computeVarContains2( n, INST_CONSTANT, varContains, visited );
}

void TermUtil::computeQuantContains( Node n, std::vector< Node >& quantContains ) {
  std::map< Node, bool > visited;
  computeVarContains2( n, FORALL, quantContains, visited );
}


void TermUtil::computeVarContains2( Node n, Kind k, std::vector< Node >& varContains, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==k ){
      if( std::find( varContains.begin(), varContains.end(), n )==varContains.end() ){
        varContains.push_back( n );
      }
    }else{
      if (n.hasOperator())
      {
        computeVarContains2(n.getOperator(), k, varContains, visited);
      }
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        computeVarContains2( n[i], k, varContains, visited );
      }
    }
  }
}

void TermUtil::getVarContains( Node f, std::vector< Node >& pats, std::map< Node, std::vector< Node > >& varContains ){
  for( unsigned i=0; i<pats.size(); i++ ){
    varContains[ pats[i] ].clear();
    getVarContainsNode( f, pats[i], varContains[ pats[i] ] );
  }
}

void TermUtil::getVarContainsNode( Node f, Node n, std::vector< Node >& varContains ){
  std::vector< Node > vars;
  computeVarContains( n, vars );
  for( unsigned j=0; j<vars.size(); j++ ){
    Node v = vars[j];
    if( v.getAttribute(InstConstantAttribute())==f ){
      if( std::find( varContains.begin(), varContains.end(), v )==varContains.end() ){
        varContains.push_back( v );
      }
    }
  }
}

int TermUtil::getIdForOperator( Node op ) {
  std::map< Node, int >::iterator it = d_op_id.find( op );
  if( it==d_op_id.end() ){
    d_op_id[op] = d_op_id_count;
    d_op_id_count++;
    return d_op_id[op];
  }else{
    return it->second;
  }
}

int TermUtil::getIdForType( TypeNode t ) {
  std::map< TypeNode, int >::iterator it = d_typ_id.find( t );
  if( it==d_typ_id.end() ){
    d_typ_id[t] = d_typ_id_count;
    d_typ_id_count++;
    return d_typ_id[t];
  }else{
    return it->second;
  }
}

bool TermUtil::getTermOrder( Node a, Node b ) {
  if( a.getKind()==BOUND_VARIABLE ){
    if( b.getKind()==BOUND_VARIABLE ){
      return a.getAttribute(InstVarNumAttribute())<b.getAttribute(InstVarNumAttribute());
    }else{
      return true;
    }
  }else if( b.getKind()!=BOUND_VARIABLE ){
    Node aop = a.hasOperator() ? a.getOperator() : a;
    Node bop = b.hasOperator() ? b.getOperator() : b;
    Trace("aeq-debug2") << a << "...op..." << aop << std::endl;
    Trace("aeq-debug2") << b << "...op..." << bop << std::endl;
    if( aop==bop ){
      if( a.getNumChildren()==b.getNumChildren() ){
        for( unsigned i=0; i<a.getNumChildren(); i++ ){
          if( a[i]!=b[i] ){
            //first distinct child determines the ordering
            return getTermOrder( a[i], b[i] );
          }
        }
      }else{
        return aop.getNumChildren()<bop.getNumChildren();
      }
    }else{
      return getIdForOperator( aop )<getIdForOperator( bop );
    }
  }
  return false;
}



Node TermUtil::getCanonicalFreeVar( TypeNode tn, unsigned i ) {
  Assert( !tn.isNull() );
  while( d_cn_free_var[tn].size()<=i ){
    std::stringstream oss;
    oss << tn;
    std::string typ_name = oss.str();
    while( typ_name[0]=='(' ){
      typ_name.erase( typ_name.begin() );
    }
    std::stringstream os;
    os << typ_name[0] << i;
    Node x = NodeManager::currentNM()->mkBoundVar( os.str().c_str(), tn );
    InstVarNumAttribute ivna;
    x.setAttribute(ivna,d_cn_free_var[tn].size());
    d_cn_free_var[tn].push_back( x );
  }
  return d_cn_free_var[tn][i];
}

struct sortTermOrder {
  TermUtil* d_tu;
  //std::map< Node, std::map< Node, bool > > d_cache;
  bool operator() (Node i, Node j) {
    /*
    //must consult cache since term order is partial?
    std::map< Node, bool >::iterator it = d_cache[j].find( i );
    if( it!=d_cache[j].end() && it->second ){
      return false;
    }else{
      bool ret = d_tdb->getTermOrder( i, j );
      d_cache[i][j] = ret;
      return ret;
    }
    */
    return d_tu->getTermOrder( i, j );
  }
};

//this function makes a canonical representation of a term (
//  - orders variables left to right
//  - if apply_torder, then sort direct subterms of commutative operators
Node TermUtil::getCanonicalTerm( TNode n, std::map< TypeNode, unsigned >& var_count, std::map< TNode, TNode >& subs, bool apply_torder, std::map< TNode, Node >& visited ) {
  Trace("canon-term-debug") << "Get canonical term for " << n << std::endl;
  if( n.getKind()==BOUND_VARIABLE ){
    std::map< TNode, TNode >::iterator it = subs.find( n );
    if( it==subs.end() ){
      TypeNode tn = n.getType();
      //allocate variable
      unsigned vn = var_count[tn];
      var_count[tn]++;
      subs[n] = getCanonicalFreeVar( tn, vn );
      Trace("canon-term-debug") << "...allocate variable." << std::endl;
      return subs[n];
    }else{
      Trace("canon-term-debug") << "...return variable in subs." << std::endl;
      return it->second;
    }
  }else if( n.getNumChildren()>0 ){
    std::map< TNode, Node >::iterator it = visited.find( n );
    if( it!=visited.end() ){
      return it->second;
    }else{
      //collect children
      Trace("canon-term-debug") << "Collect children" << std::endl;
      std::vector< Node > cchildren;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        cchildren.push_back( n[i] );
      }
      //if applicable, first sort by term order
      if( apply_torder && isComm( n.getKind() ) ){
        Trace("canon-term-debug") << "Sort based on commutative operator " << n.getKind() << std::endl;
        sortTermOrder sto;
        sto.d_tu = this;
        std::sort( cchildren.begin(), cchildren.end(), sto );
      }
      //now make canonical
      Trace("canon-term-debug") << "Make canonical children" << std::endl;
      for( unsigned i=0; i<cchildren.size(); i++ ){
        cchildren[i] = getCanonicalTerm( cchildren[i], var_count, subs, apply_torder, visited );
      }
      if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
        Trace("canon-term-debug") << "Insert operator " << n.getOperator() << std::endl;
        cchildren.insert( cchildren.begin(), n.getOperator() );
      }
      Trace("canon-term-debug") << "...constructing for " << n << "." << std::endl;
      Node ret = NodeManager::currentNM()->mkNode( n.getKind(), cchildren );
      Trace("canon-term-debug") << "...constructed " << ret << " for " << n << "." << std::endl;
      visited[n] = ret;
      return ret;
    }
  }else{
    Trace("canon-term-debug") << "...return 0-child term." << std::endl;
    return n;
  }
}

Node TermUtil::getCanonicalTerm( TNode n, bool apply_torder ){
  std::map< TypeNode, unsigned > var_count;
  std::map< TNode, TNode > subs;
  std::map< TNode, Node > visited;
  return getCanonicalTerm( n, var_count, subs, apply_torder, visited );
}

void TermUtil::getVtsTerms( std::vector< Node >& t, bool isFree, bool create, bool inc_delta ) {
  if( inc_delta ){
    Node delta = getVtsDelta( isFree, create );
    if( !delta.isNull() ){
      t.push_back( delta );
    }
  }
  for( unsigned r=0; r<2; r++ ){
    Node inf = getVtsInfinityIndex( r, isFree, create );
    if( !inf.isNull() ){
      t.push_back( inf );
    }
  }
}

Node TermUtil::getVtsDelta( bool isFree, bool create ) {
  if( create ){
    if( d_vts_delta_free.isNull() ){
      d_vts_delta_free = NodeManager::currentNM()->mkSkolem( "delta_free", NodeManager::currentNM()->realType(), "free delta for virtual term substitution" );
      Node delta_lem = NodeManager::currentNM()->mkNode( GT, d_vts_delta_free, d_zero );
      d_quantEngine->getOutputChannel().lemma( delta_lem );
    }
    if( d_vts_delta.isNull() ){
      d_vts_delta = NodeManager::currentNM()->mkSkolem( "delta", NodeManager::currentNM()->realType(), "delta for virtual term substitution" );
      //mark as a virtual term
      VirtualTermSkolemAttribute vtsa;
      d_vts_delta.setAttribute(vtsa,true);
    }
  }
  return isFree ? d_vts_delta_free : d_vts_delta;
}

Node TermUtil::getVtsInfinity( TypeNode tn, bool isFree, bool create ) {
  if( create ){
    if( d_vts_inf_free[tn].isNull() ){
      d_vts_inf_free[tn] = NodeManager::currentNM()->mkSkolem( "inf_free", tn, "free infinity for virtual term substitution" );
    }
    if( d_vts_inf[tn].isNull() ){
      d_vts_inf[tn] = NodeManager::currentNM()->mkSkolem( "inf", tn, "infinity for virtual term substitution" );
      //mark as a virtual term
      VirtualTermSkolemAttribute vtsa;
      d_vts_inf[tn].setAttribute(vtsa,true);
    }
  }
  return isFree ? d_vts_inf_free[tn] : d_vts_inf[tn];
}

Node TermUtil::getVtsInfinityIndex( int i, bool isFree, bool create ) {
  if( i==0 ){
    return getVtsInfinity( NodeManager::currentNM()->realType(), isFree, create );
  }else if( i==1 ){
    return getVtsInfinity( NodeManager::currentNM()->integerType(), isFree, create );
  }else{
    Assert( false );
    return Node::null();
  }
}

Node TermUtil::substituteVtsFreeTerms( Node n ) {
  std::vector< Node > vars;
  getVtsTerms( vars, false, false );
  std::vector< Node > vars_free;
  getVtsTerms( vars_free, true, false );
  Assert( vars.size()==vars_free.size() );
  if( !vars.empty() ){
    return n.substitute( vars.begin(), vars.end(), vars_free.begin(), vars_free.end() );
  }else{
    return n;
  }
}

Node TermUtil::rewriteVtsSymbols( Node n ) {
  if( ( n.getKind()==EQUAL || n.getKind()==GEQ ) ){
    Trace("quant-vts-debug") << "VTS : process " << n << std::endl;
    Node rew_vts_inf;
    bool rew_delta = false;
    //rewriting infinity always takes precedence over rewriting delta
    for( unsigned r=0; r<2; r++ ){
      Node inf = getVtsInfinityIndex( r, false, false );
      if( !inf.isNull() && containsTerm( n, inf ) ){
        if( rew_vts_inf.isNull() ){
          rew_vts_inf = inf;
        }else{
          //for mixed int/real with multiple infinities
          Trace("quant-vts-debug") << "Multiple infinities...equate " << inf << " = " << rew_vts_inf << std::endl;
          std::vector< Node > subs_lhs;
          subs_lhs.push_back( inf );
          std::vector< Node > subs_rhs;
          subs_lhs.push_back( rew_vts_inf );
          n = n.substitute( subs_lhs.begin(), subs_lhs.end(), subs_rhs.begin(), subs_rhs.end() );
          n = Rewriter::rewrite( n );
          //may have cancelled
          if( !containsTerm( n, rew_vts_inf ) ){
            rew_vts_inf = Node::null();
          }
        }
      }
    }
    if( rew_vts_inf.isNull() ){
      if( !d_vts_delta.isNull() && containsTerm( n, d_vts_delta ) ){
        rew_delta = true;
      }
    }
    if( !rew_vts_inf.isNull()  || rew_delta ){
      std::map< Node, Node > msum;
      if (ArithMSum::getMonomialSumLit(n, msum))
      {
        if( Trace.isOn("quant-vts-debug") ){
          Trace("quant-vts-debug") << "VTS got monomial sum : " << std::endl;
          ArithMSum::debugPrintMonomialSum(msum, "quant-vts-debug");
        }
        Node vts_sym = !rew_vts_inf.isNull() ? rew_vts_inf : d_vts_delta;
        Assert( !vts_sym.isNull() );
        Node iso_n;
        Node nlit;
        int res = ArithMSum::isolate(vts_sym, msum, iso_n, n.getKind(), true);
        if( res!=0 ){
          Trace("quant-vts-debug") << "VTS isolated :  -> " << iso_n << ", res = " << res << std::endl;
          Node slv = iso_n[res==1 ? 1 : 0];
          //ensure the vts terms have been eliminated
          if( containsVtsTerm( slv ) ){
            Trace("quant-vts-warn") << "Bad vts literal : " << n << ", contains " << vts_sym << " but bad solved form " << slv << "." << std::endl;
            nlit = substituteVtsFreeTerms( n );
            Trace("quant-vts-debug") << "...return " << nlit << std::endl;
            //Assert( false );
            //safe case: just convert to free symbols
            return nlit;
          }else{
            if( !rew_vts_inf.isNull() ){
              nlit = ( n.getKind()==GEQ && res==1 ) ? d_true : d_false;
            }else{
              Assert( iso_n[res==1 ? 0 : 1]==d_vts_delta );
              if( n.getKind()==EQUAL ){
                nlit = d_false;
              }else if( res==1 ){
                nlit = NodeManager::currentNM()->mkNode( GEQ, d_zero, slv );
              }else{
                nlit = NodeManager::currentNM()->mkNode( GT, slv, d_zero );
              }
            }
          }
          Trace("quant-vts-debug") << "Return " << nlit << std::endl;
          return nlit;
        }else{
          Trace("quant-vts-warn") << "Bad vts literal : " << n << ", contains " << vts_sym << " but could not isolate." << std::endl;
          //safe case: just convert to free symbols
          nlit = substituteVtsFreeTerms( n );
          Trace("quant-vts-debug") << "...return " << nlit << std::endl;
          //Assert( false );
          return nlit;
        }
      }
    }
    return n;
  }else if( n.getKind()==FORALL ){
    //cannot traverse beneath quantifiers
    return substituteVtsFreeTerms( n );
  }else{
    bool childChanged = false;
    std::vector< Node > children;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      Node nn = rewriteVtsSymbols( n[i] );
      children.push_back( nn );
      childChanged = childChanged || nn!=n[i];
    }
    if( childChanged ){
      if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.insert( children.begin(), n.getOperator() );
      }
      Node ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      Trace("quant-vts-debug") << "...make node " << ret << std::endl;
      return ret;
    }else{
      return n;
    }
  }
}

bool TermUtil::containsVtsTerm( Node n, bool isFree ) {
  std::vector< Node > t;
  getVtsTerms( t, isFree, false );
  return containsTerms( n, t );
}

bool TermUtil::containsVtsTerm( std::vector< Node >& n, bool isFree ) {
  std::vector< Node > t;
  getVtsTerms( t, isFree, false );
  if( !t.empty() ){
    for( unsigned i=0; i<n.size(); i++ ){
      if( containsTerms( n[i], t ) ){
        return true;
      }
    }
  }
  return false;
}

bool TermUtil::containsVtsInfinity( Node n, bool isFree ) {
  std::vector< Node > t;
  getVtsTerms( t, isFree, false, false );
  return containsTerms( n, t );
}

Node TermUtil::ensureType( Node n, TypeNode tn ) {
  TypeNode ntn = n.getType();
  Assert( ntn.isComparableTo( tn ) );
  if( ntn.isSubtypeOf( tn ) ){
    return n;
  }else{
    if( tn.isInteger() ){
      return NodeManager::currentNM()->mkNode( TO_INTEGER, n );
    }
    return Node::null();
  }
}

bool TermUtil::containsTerm2( Node n, Node t, std::map< Node, bool >& visited ) {
  if( n==t ){
    return true;
  }else{
    if( visited.find( n )==visited.end() ){
      visited[n] = true;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( containsTerm2( n[i], t, visited ) ){
          return true;
        }
      }
    }
    return false;
  }
}

bool TermUtil::containsTerms2( Node n, std::vector< Node >& t, std::map< Node, bool >& visited ) {
  if( visited.find( n )==visited.end() ){
    if( std::find( t.begin(), t.end(), n )!=t.end() ){
      return true;
    }else{
      visited[n] = true;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( containsTerms2( n[i], t, visited ) ){
          return true;
        }
      }
    }
  }
  return false;
}

bool TermUtil::containsTerm( Node n, Node t ) {
  std::map< Node, bool > visited;
  return containsTerm2( n, t, visited );
}

bool TermUtil::containsTerms( Node n, std::vector< Node >& t ) {
  if( t.empty() ){
    return false;
  }else{
    std::map< Node, bool > visited;
    return containsTerms2( n, t, visited );
  }
}

int TermUtil::getTermDepth( Node n ) {
  if (!n.hasAttribute(TermDepthAttribute()) ){
    int maxDepth = -1;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      int depth = getTermDepth( n[i] );
      if( depth>maxDepth ){
        maxDepth = depth;
      }
    }
    TermDepthAttribute tda;
    n.setAttribute(tda,1+maxDepth);
  }
  return n.getAttribute(TermDepthAttribute());
}

bool TermUtil::containsUninterpretedConstant( Node n ) {
  if (!n.hasAttribute(ContainsUConstAttribute()) ){
    bool ret = false;
    if( n.getKind()==UNINTERPRETED_CONSTANT ){
      ret = true;
    }else{ 
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( containsUninterpretedConstant( n[i] ) ){
          ret = true;
          break;
        }
      }
    }
    ContainsUConstAttribute cuca;
    n.setAttribute(cuca, ret ? 1 : 0);
  }
  return n.getAttribute(ContainsUConstAttribute())!=0;
}

Node TermUtil::simpleNegate( Node n ){
  if( n.getKind()==OR || n.getKind()==AND ){
    std::vector< Node > children;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      children.push_back( simpleNegate( n[i] ) );
    }
    return NodeManager::currentNM()->mkNode( n.getKind()==OR ? AND : OR, children );
  }else{
    return n.negate();
  }
}

bool TermUtil::isAssoc( Kind k ) {
  return k==PLUS || k==MULT || k==AND || k==OR || 
         k==BITVECTOR_PLUS || k==BITVECTOR_MULT || k==BITVECTOR_AND || k==BITVECTOR_OR || k==BITVECTOR_XOR || k==BITVECTOR_XNOR || k==BITVECTOR_CONCAT ||
         k==STRING_CONCAT;
}

bool TermUtil::isComm( Kind k ) {
  return k==EQUAL || k==PLUS || k==MULT || k==AND || k==OR || k==XOR || 
         k==BITVECTOR_PLUS || k==BITVECTOR_MULT || k==BITVECTOR_AND || k==BITVECTOR_OR || k==BITVECTOR_XOR || k==BITVECTOR_XNOR;
}

bool TermUtil::isNonAdditive( Kind k ) {
  return k==AND || k==OR || k==BITVECTOR_AND || k==BITVECTOR_OR;
}

bool TermUtil::isBoolConnective( Kind k ) {
  return k==OR || k==AND || k==EQUAL || k==ITE || k==FORALL || k==NOT || k==SEP_STAR;
}

bool TermUtil::isBoolConnectiveTerm( TNode n ) {
  return isBoolConnective( n.getKind() ) &&
         ( n.getKind()!=EQUAL || n[0].getType().isBoolean() ) && 
         ( n.getKind()!=ITE || n.getType().isBoolean() );
}

Node TermUtil::getTypeValue(TypeNode tn, int val)
{
  std::unordered_map<int, Node>::iterator it = d_type_value[tn].find(val);
  if (it == d_type_value[tn].end())
  {
    Node n = mkTypeValue(tn, val);
    d_type_value[tn][val] = n;
    return n;
  }
  return it->second;
}

Node TermUtil::mkTypeValue(TypeNode tn, int val)
{
  Node n;
  if (tn.isInteger() || tn.isReal())
  {
    Rational c(val);
    n = NodeManager::currentNM()->mkConst(c);
  }
  else if (tn.isBitVector())
  {
    unsigned int uv = val;
    BitVector bval(tn.getConst<BitVectorSize>(), uv);
    n = NodeManager::currentNM()->mkConst<BitVector>(bval);
  }
  else if (tn.isBoolean())
  {
    if (val == 0)
    {
      n = NodeManager::currentNM()->mkConst(false);
    }
  }
  else if (tn.isString())
  {
    if (val == 0)
    {
      n = NodeManager::currentNM()->mkConst(::CVC4::String(""));
    }
  }
  return n;
}

Node TermUtil::getTypeMaxValue(TypeNode tn)
{
  std::unordered_map<TypeNode, Node, TypeNodeHashFunction>::iterator it =
      d_type_max_value.find(tn);
  if (it == d_type_max_value.end())
  {
    Node n = mkTypeMaxValue(tn);
    d_type_max_value[tn] = n;
    return n;
  }
  return it->second;
}

Node TermUtil::mkTypeMaxValue(TypeNode tn)
{
  Node n;
  if (tn.isBitVector())
  {
    n = bv::utils::mkOnes(tn.getConst<BitVectorSize>());
  }
  else if (tn.isBoolean())
  {
    n = NodeManager::currentNM()->mkConst(true);
  }
  return n;
}

Node TermUtil::getTypeValueOffset(TypeNode tn,
                                  Node val,
                                  int offset,
                                  int& status)
{
  std::unordered_map<int, Node>::iterator it =
      d_type_value_offset[tn][val].find(offset);
  if (it == d_type_value_offset[tn][val].end())
  {
    Node val_o;
    Node offset_val = getTypeValue(tn, offset);
    status = -1;
    if (!offset_val.isNull())
    {
      if (tn.isInteger() || tn.isReal())
      {
        val_o = Rewriter::rewrite(
            NodeManager::currentNM()->mkNode(PLUS, val, offset_val));
        status = 0;
      }
      else if (tn.isBitVector())
      {
        val_o = Rewriter::rewrite(
            NodeManager::currentNM()->mkNode(BITVECTOR_PLUS, val, offset_val));
        // TODO : enable?  watch for overflows
      }
    }
    d_type_value_offset[tn][val][offset] = val_o;
    d_type_value_offset_status[tn][val][offset] = status;
    return val_o;
  }
  status = d_type_value_offset_status[tn][val][offset];
  return it->second;
}

bool TermUtil::isAntisymmetric(Kind k, Kind& dk)
{
  if (k == GT)
  {
    dk = LT;
    return true;
  }
  else if (k == GEQ)
  {
    dk = LEQ;
    return true;
  }
  else if (k == BITVECTOR_UGT)
  {
    dk = BITVECTOR_ULT;
    return true;
  }
  else if (k == BITVECTOR_UGE)
  {
    dk = BITVECTOR_ULE;
    return true;
  }
  else if (k == BITVECTOR_SGT)
  {
    dk = BITVECTOR_SLT;
    return true;
  }
  else if (k == BITVECTOR_SGE)
  {
    dk = BITVECTOR_SLE;
    return true;
  }
  return false;
}

bool TermUtil::isIdempotentArg(Node n, Kind ik, int arg)
{
  // these should all be binary operators
  // Assert( ik!=DIVISION && ik!=INTS_DIVISION && ik!=INTS_MODULUS &&
  // ik!=BITVECTOR_UDIV );
  TypeNode tn = n.getType();
  if (n == getTypeValue(tn, 0))
  {
    if (ik == PLUS || ik == OR || ik == XOR || ik == BITVECTOR_PLUS
        || ik == BITVECTOR_OR
        || ik == BITVECTOR_XOR
        || ik == STRING_CONCAT)
    {
      return true;
    }
    else if (ik == MINUS || ik == BITVECTOR_SHL || ik == BITVECTOR_LSHR
             || ik == BITVECTOR_ASHR
             || ik == BITVECTOR_SUB
             || ik == BITVECTOR_UREM
             || ik == BITVECTOR_UREM_TOTAL)
    {
      return arg == 1;
    }
  }
  else if (n == getTypeValue(tn, 1))
  {
    if (ik == MULT || ik == BITVECTOR_MULT)
    {
      return true;
    }
    else if (ik == DIVISION || ik == DIVISION_TOTAL || ik == INTS_DIVISION
             || ik == INTS_DIVISION_TOTAL
             || ik == INTS_MODULUS
             || ik == INTS_MODULUS_TOTAL
             || ik == BITVECTOR_UDIV_TOTAL
             || ik == BITVECTOR_UDIV
             || ik == BITVECTOR_SDIV)
    {
      return arg == 1;
    }
  }
  else if (n == getTypeMaxValue(tn))
  {
    if (ik == EQUAL || ik == BITVECTOR_AND || ik == BITVECTOR_XNOR)
    {
      return true;
    }
  }
  return false;
}

Node TermUtil::isSingularArg(Node n, Kind ik, int arg)
{
  TypeNode tn = n.getType();
  if (n == getTypeValue(tn, 0))
  {
    if (ik == AND || ik == MULT || ik == BITVECTOR_AND || ik == BITVECTOR_MULT)
    {
      return n;
    }
    else if (ik == BITVECTOR_SHL || ik == BITVECTOR_LSHR || ik == BITVECTOR_ASHR
             || ik == BITVECTOR_UREM
             || ik == BITVECTOR_UREM_TOTAL)
    {
      if (arg == 0)
      {
        return n;
      }
    }
    else if (ik == BITVECTOR_UDIV_TOTAL || ik == BITVECTOR_UDIV
             || ik == BITVECTOR_SDIV)
    {
      if (arg == 0)
      {
        return n;
      }
      else if (arg == 1)
      {
        return getTypeMaxValue(tn);
      }
    }
    else if (ik == DIVISION || ik == DIVISION_TOTAL || ik == INTS_DIVISION
             || ik == INTS_DIVISION_TOTAL
             || ik == INTS_MODULUS
             || ik == INTS_MODULUS_TOTAL)
    {
      if (arg == 0)
      {
        return n;
      }
      else
      {
        // TODO?
      }
    }
    else if (ik == STRING_SUBSTR)
    {
      if (arg == 0)
      {
        return n;
      }
      else if (arg == 2)
      {
        return getTypeValue(NodeManager::currentNM()->stringType(), 0);
      }
    }
    else if (ik == STRING_STRIDOF)
    {
      if (arg == 0 || arg == 1)
      {
        return getTypeValue(NodeManager::currentNM()->integerType(), -1);
      }
    }
  }
  else if (n == getTypeValue(tn, 1))
  {
    if (ik == BITVECTOR_UREM_TOTAL)
    {
      return getTypeValue(tn, 0);
    }
  }
  else if (n == getTypeMaxValue(tn))
  {
    if (ik == OR || ik == BITVECTOR_OR)
    {
      return n;
    }
  }
  else
  {
    if (n.getType().isReal() && n.getConst<Rational>().sgn() < 0)
    {
      // negative arguments
      if (ik == STRING_SUBSTR || ik == STRING_CHARAT)
      {
        return getTypeValue(NodeManager::currentNM()->stringType(), 0);
      }
      else if (ik == STRING_STRIDOF)
      {
        Assert(arg == 2);
        return getTypeValue(NodeManager::currentNM()->integerType(), -1);
      }
    }
  }
  return Node::null();
}

bool TermUtil::hasOffsetArg(Kind ik, int arg, int& offset, Kind& ok)
{
  if (ik == LT)
  {
    Assert(arg == 0 || arg == 1);
    offset = arg == 0 ? 1 : -1;
    ok = LEQ;
    return true;
  }
  else if (ik == BITVECTOR_ULT)
  {
    Assert(arg == 0 || arg == 1);
    offset = arg == 0 ? 1 : -1;
    ok = BITVECTOR_ULE;
    return true;
  }
  else if (ik == BITVECTOR_SLT)
  {
    Assert(arg == 0 || arg == 1);
    offset = arg == 0 ? 1 : -1;
    ok = BITVECTOR_SLE;
    return true;
  }
  return false;
}

Node TermUtil::getHoTypeMatchPredicate( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator ithp = d_ho_type_match_pred.find( tn );
  if( ithp==d_ho_type_match_pred.end() ){
    TypeNode ptn = NodeManager::currentNM()->mkFunctionType( tn, NodeManager::currentNM()->booleanType() );
    Node k = NodeManager::currentNM()->mkSkolem( "U", ptn, "predicate to force higher-order types" );
    d_ho_type_match_pred[tn] = k;
    return k;
  }else{
    return ithp->second;  
  }
}


}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

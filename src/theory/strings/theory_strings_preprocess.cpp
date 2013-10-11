/*********************                                                        */
/*! \file theory_strings_preprocess.cpp
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: Tianyi Liang, Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2013-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Strings Preprocess
 **
 ** Strings Preprocess.
 **/

#include "theory/strings/theory_strings_preprocess.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace strings {

void StringsPreprocess::simplifyRegExp( Node s, Node r, std::vector< Node > &ret ) {
	int k = r.getKind();
	switch( k ) {
		case kind::STRING_TO_REGEXP:
		{
			Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, s, r[0] );
			ret.push_back( eq );
		}
			break;
		case kind::REGEXP_CONCAT:
		{
			std::vector< Node > cc;
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				Node sk = NodeManager::currentNM()->mkSkolem( "recsym_$$", s.getType(), "created for regular expression concat" );
				simplifyRegExp( sk, r[i], ret );
				cc.push_back( sk );
			}
			Node cc_eq = NodeManager::currentNM()->mkNode( kind::EQUAL, s, 
						NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, cc ) );
			ret.push_back( cc_eq );
		}
			break;
		case kind::REGEXP_OR:
		{
			std::vector< Node > c_or;
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				simplifyRegExp( s, r[i], c_or );
			}
			Node eq = NodeManager::currentNM()->mkNode( kind::OR, c_or );
			ret.push_back( eq );
		}
			break;
		case kind::REGEXP_INTER:
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				simplifyRegExp( s, r[i], ret );
			}
			break;
		/*
		case kind::REGEXP_OPT:
		{
			Node eq_empty = NodeManager::currentNM()->mkNode( kind::EQUAL, s, NodeManager::currentNM()->mkConst( ::CVC4::String("") ) );
			std::vector< Node > rr;
			simplifyRegExp( s, r[0], rr );
			Node nrr = rr.size()==1 ? rr[0] : NodeManager::currentNM()->mkNode( kind::AND, rr );
			ret.push_back( NodeManager::currentNM()->mkNode( kind::OR, eq_empty, nrr) );
		}
			break;
		//case kind::REGEXP_PLUS:
		*/
		case kind::REGEXP_STAR:
		{
			Node eq = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, s, r );
			ret.push_back( eq );
		}
			break;
		default:
			//TODO: special sym: sigma, none, all
			break;
	}
}

bool StringsPreprocess::checkStarPlus( Node t ) {
	if( t.getKind() != kind::REGEXP_STAR && t.getKind() != kind::REGEXP_PLUS ) {
		for( unsigned i = 0; i<t.getNumChildren(); ++i ) {
			if( checkStarPlus(t[i]) ) return true;
		}
		return false;
	} else {
		return true;
	}
}

Node StringsPreprocess::simplify( Node t, std::vector< Node > &new_nodes ) {
    std::hash_map<TNode, Node, TNodeHashFunction>::const_iterator i = d_cache.find(t);
    if(i != d_cache.end()) {
      return (*i).second.isNull() ? t : (*i).second;
    }

	/*
	if( t.getKind() == kind::STRING_IN_REGEXP ){
		// t0 in t1
		Node t0 = simplify( t[0], new_nodes );
		
		//if(!checkStarPlus( t[1] )) {
			//rewrite it
			std::vector< Node > ret;
			simplifyRegExp( t0, t[1], ret );

			Node n = ret.size() == 1 ? ret[0] : NodeManager::currentNM()->mkNode( kind::AND, ret );
			d_cache[t] = (t == n) ? Node::null() : n;
			return n;
		//} else {
			// TODO
		//	return (t0 == t[0]) ? t : NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, t0, t[1] );
		//}
	}else 
	*/
	if( t.getKind() == kind::STRING_SUBSTR ){
		Node sk1 = NodeManager::currentNM()->mkSkolem( "st1sym_$$", t.getType(), "created for substr" );
		Node sk2 = NodeManager::currentNM()->mkSkolem( "st2sym_$$", t.getType(), "created for substr" );
		Node sk3 = NodeManager::currentNM()->mkSkolem( "st3sym_$$", t.getType(), "created for substr" );
		Node x = simplify( t[0], new_nodes );
		Node x_eq_123 = NodeManager::currentNM()->mkNode( kind::EQUAL,
							NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk1, sk2, sk3 ), x );
		new_nodes.push_back( x_eq_123 );
		Node len_sk1_eq_i = NodeManager::currentNM()->mkNode( kind::EQUAL, t[1],
								NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk1 ) );
		new_nodes.push_back( len_sk1_eq_i );
		Node len_sk2_eq_j = NodeManager::currentNM()->mkNode( kind::EQUAL, t[2],
								NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk2 ) );
		new_nodes.push_back( len_sk2_eq_j );

		d_cache[t] = sk2;
		return sk2;
	} else if( t.getNumChildren()>0 ){
		std::vector< Node > cc;
		if (t.getMetaKind() == kind::metakind::PARAMETERIZED) {
			cc.push_back(t.getOperator());
		}
		bool changed = false;
		for( unsigned i=0; i<t.getNumChildren(); i++ ){
			Node tn = simplify( t[i], new_nodes );
			cc.push_back( tn );
			changed = changed || tn!=t[i];
		}
		if(changed) {
			Node n = NodeManager::currentNM()->mkNode( t.getKind(), cc );
			d_cache[t] = n;
			return n;
		} else {
			d_cache[t] = Node::null();
			return t;
		}
	}else{
		d_cache[t] = Node::null();
		return t;
	}
}

void StringsPreprocess::simplify(std::vector< Node > &vec_node) {
	std::vector< Node > new_nodes;
	for( unsigned i=0; i<vec_node.size(); i++ ){
		vec_node[i] = simplify( vec_node[i], new_nodes );
	}
	vec_node.insert( vec_node.end(), new_nodes.begin(), new_nodes.end() );
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

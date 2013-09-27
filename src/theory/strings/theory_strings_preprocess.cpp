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
		case kind::REGEXP_STAR:
		{
			Node sk = NodeManager::currentNM()->mkSkolem( "ressym_$$", s.getType(), "created for regular expression star" );
			Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL,
						NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk, s ),
						NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, s, sk ));
			ret.push_back( eq );
			simplifyRegExp( sk, r[0], ret );
		}
			break;
		case kind::REGEXP_OPT:
		{
			Node eq_empty = NodeManager::currentNM()->mkNode( kind::EQUAL, s, NodeManager::currentNM()->mkConst( ::CVC4::String("") ) );
			std::vector< Node > rr;
			simplifyRegExp( s, r[0], rr );
			Node nrr = rr.size()==1 ? rr[0] : NodeManager::currentNM()->mkNode( kind::AND, rr );
			ret.push_back( NodeManager::currentNM()->mkNode( kind::OR, eq_empty, nrr) );
		}
			break;
		default:
			//TODO:case kind::REGEXP_PLUS:
			//TODO: special sym: sigma, none, all
			break;
	}
}

Node StringsPreprocess::simplify( Node t ) {
	if( t.getKind() == kind::STRING_IN_REGEXP ){
		// t0 in t1
		//rewrite it
		std::vector< Node > ret;
		simplifyRegExp( t[0], t[1], ret );

		return ret.size() == 1 ? ret[0] : NodeManager::currentNM()->mkNode( kind::AND, ret );
    }else if( t.getNumChildren()>0 ){
		std::vector< Node > cc;
		if (t.getMetaKind() == kind::metakind::PARAMETERIZED) {
			cc.push_back(t.getOperator());
		}
		bool changed = false;
		for( unsigned i=0; i<t.getNumChildren(); i++ ){
			Node tn = simplify( t[i] );
			cc.push_back( tn );
			changed = changed || tn!=t[i];
		}
		return changed ? NodeManager::currentNM()->mkNode( t.getKind(), cc ) : t;
	}else{
		return t;
	}
}

void StringsPreprocess::simplify(std::vector< Node > &vec_node) {
	for( unsigned i=0; i<vec_node.size(); i++ ){
		vec_node[i] = simplify( vec_node[i] );
	}
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

/*********************                                                        */

/*! \file regexp_operation.cpp

 ** \verbatim

 ** Original author: Tianyi Liang
 
 ** Major contributors: none
 
 ** Minor contributors (to current version): none
 
 ** This file is part of the CVC4 project.
 
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 
 ** See the file COPYING in the top-level source directory for licensing
 
 ** information.\endverbatim
 
 **
 
 ** \brief Regular Expresion Operations
 **
 ** Regular Expresion Operations
 **/

#include "theory/strings/regexp_operation.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace strings {

RegExpOpr::RegExpOpr() {
    d_emptyString = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
    d_true = NodeManager::currentNM()->mkConst( true );
    d_false = NodeManager::currentNM()->mkConst( false );
	d_zero = NodeManager::currentNM()->mkConst( ::CVC4::Rational(0) );
	d_one = NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) );
	std::vector< Node > nvec;
    d_emptyRegexp = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
	// All Charactors = all printable ones 32-126
	//d_char_start = 'a';//' ';
	//d_char_end = 'c';//'~';
	//d_sigma = mkAllExceptOne( '\0' );
	d_sigma = NodeManager::currentNM()->mkNode( kind::REGEXP_SIGMA, nvec );
	d_sigma_star = NodeManager::currentNM()->mkNode( kind::REGEXP_STAR, d_sigma );
}

int RegExpOpr::gcd ( int a, int b ) {
  int c;
  while ( a != 0 ) {
     c = a; a = b%a;  b = c;
  }
  return b;
}

bool RegExpOpr::checkConstRegExp( Node r ) {
	Trace("strings-regexp-cstre") << "RegExp-CheckConstRegExp starts with " << mkString( r ) << std::endl;
	bool ret = true;
	if( d_cstre_cache.find( r ) != d_cstre_cache.end() ) {
		ret = d_cstre_cache[r];
	} else {
		if(r.getKind() == kind::STRING_TO_REGEXP) {
			Node tmp = Rewriter::rewrite( r[0] );
			ret = tmp.isConst();
		} else {
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				if(!checkConstRegExp(r[i])) {
					ret = false; break;
				}
			}
		}
		d_cstre_cache[r] = ret;
	}
	return ret;
}

// 0-unknown, 1-yes, 2-no
int RegExpOpr::delta( Node r ) {
	Trace("strings-regexp-delta") << "RegExp-Delta starts with " << mkString( r ) << std::endl;
	int ret = 0;
	if( d_delta_cache.find( r ) != d_delta_cache.end() ) {
		ret = d_delta_cache[r];
	} else {
		int k = r.getKind();
		switch( k ) {
			case kind::REGEXP_EMPTY: {
				ret = 2;
				break;
			}
			case kind::REGEXP_SIGMA: {
				ret = 2;
				break;
			}
			case kind::STRING_TO_REGEXP: {
				if(r[0].isConst()) {
					if(r[0] == d_emptyString) {
						ret = 1;
					} else {
						ret = 2;
					}
				} else {
					ret = 0;
				}
				break;
			}
			case kind::REGEXP_CONCAT: {
				bool flag = false;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					int tmp = delta( r[i] );
					if(tmp == 2) {
						ret = 2;
						break;
					} else if(tmp == 0) {
						flag = true;
					}
				}
				if(!flag && ret != 2) {
					ret = 1;
				}
				break;
			}
			case kind::REGEXP_UNION: {
				bool flag = false;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					int tmp = delta( r[i] );
					if(tmp == 1) {
						ret = 1;
						break;
					} else if(tmp == 0) {
						flag = true;
					}
				}
				if(!flag && ret != 1) {
					ret = 2;
				}
				break;
			}
			case kind::REGEXP_INTER: {
				bool flag = true;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					int tmp = delta( r[i] );
					if(tmp == 2) {
						ret = 2; flag=false;
						break;
					} else if(tmp == 0) {
						flag=false;
						break;
					}
				}
				if(flag) {
					ret = 1;
				}
				break;
			}
			case kind::REGEXP_STAR: {
				ret = 1;
				break;
			}
			case kind::REGEXP_PLUS: {
				ret = delta( r[0] );
				break;
			}
			case kind::REGEXP_OPT: {
				ret = 1;
				break;
			}
			case kind::REGEXP_RANGE: {
				ret = 2;
				break;
			}
			default: {
				Trace("strings-error") << "Unsupported term: " << mkString( r ) << " in delta of RegExp." << std::endl;
				AlwaysAssert( false );
				//return Node::null();
			}
		}
		d_delta_cache[r] = ret;
	}
	Trace("strings-regexp-delta") << "RegExp-Delta returns : " << ret << std::endl;
	return ret;
}

Node RegExpOpr::derivativeSingle( Node r, CVC4::String c ) {
	Assert( c.size() < 2 );
	Trace("strings-regexp-derivative") << "RegExp-derivative starts with R{ " << mkString( r ) << " }, c=" << c << std::endl;
	Node retNode = d_emptyRegexp;
	PairDvStr dv = std::make_pair( r, c );
	if( d_dv_cache.find( dv ) != d_dv_cache.end() ) {
		retNode = d_dv_cache[dv];
	} else if( c.isEmptyString() ){
		int tmp = delta( r );
		if(tmp == 0) {
			// TODO variable
			retNode = d_emptyRegexp;
		} else if(tmp == 1) {
			retNode = r;
		} else {
			retNode = d_emptyRegexp;
		}
	} else {
		int k = r.getKind();
		switch( k ) {
			case kind::REGEXP_EMPTY: {
				retNode = d_emptyRegexp;
				break;
			}
			case kind::REGEXP_SIGMA: {
				retNode = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, d_emptyString );
				break;
			}
			case kind::STRING_TO_REGEXP: {
				if(r[0].isConst()) {
					if(r[0] == d_emptyString) {
						retNode = d_emptyRegexp;
					} else {
						if(r[0].getConst< CVC4::String >().getFirstChar() == c.getFirstChar()) {
							retNode =  NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, 
								r[0].getConst< CVC4::String >().size() == 1 ? d_emptyString : NodeManager::currentNM()->mkConst( r[0].getConst< CVC4::String >().substr(1) ) );
						} else {
							retNode = d_emptyRegexp;
						}
					}
				} else {
					// TODO variable
					retNode = d_emptyRegexp;
				}
				break;
			}
			case kind::REGEXP_CONCAT: {
				Node rees = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, d_emptyString );
				std::vector< Node > vec_nodes;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					Node dc = derivativeSingle(r[i], c);
					if(dc != d_emptyRegexp) {
						std::vector< Node > vec_nodes2;
						if(dc != rees) {
							vec_nodes2.push_back( dc );
						}
						for(unsigned j=i+1; j<r.getNumChildren(); ++j) {
							if(r[j] != rees) {
								vec_nodes2.push_back( r[j] );
							}
						}
						Node tmp = vec_nodes2.size()==0 ? rees : 
							vec_nodes2.size()==1 ? vec_nodes2[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, vec_nodes2 );
						if(std::find(vec_nodes.begin(), vec_nodes.end(), tmp) == vec_nodes.end()) {
							vec_nodes.push_back( tmp );
						}
					}

					if( delta( r[i] ) != 1 ) {
						break;
					}
				}
				retNode = vec_nodes.size() == 0 ? d_emptyRegexp :
							( vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes ) );
				break;
			}
			case kind::REGEXP_UNION: {
				std::vector< Node > vec_nodes;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					Node dc = derivativeSingle(r[i], c);
					if(dc != d_emptyRegexp) {
						if(std::find(vec_nodes.begin(), vec_nodes.end(), dc) == vec_nodes.end()) {
							vec_nodes.push_back( dc );
						}
					}
					Trace("strings-regexp-derivative") << "RegExp-derivative OR R[" << i << "]{ " << mkString(r[i]) << " returns " << mkString(dc) << std::endl;
				}
				retNode = vec_nodes.size() == 0 ? d_emptyRegexp :
							( vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes ) );
				break;
			}
			case kind::REGEXP_INTER: {
				bool flag = true;
				bool flag_sg = false;
				std::vector< Node > vec_nodes;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					Node dc = derivativeSingle(r[i], c);
					if(dc != d_emptyRegexp) {
						if(dc == d_sigma_star) {
							flag_sg = true;
						} else {
							if(std::find(vec_nodes.begin(), vec_nodes.end(), dc) == vec_nodes.end()) {
								vec_nodes.push_back( dc );
							}
						}
					} else {
						flag = false;
						break;
					}
				}
				if(flag) {
					if(vec_nodes.size() == 0 && flag_sg) {
						retNode = d_sigma_star;
					} else {
						retNode = vec_nodes.size() == 0 ? d_emptyRegexp :
									( vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_INTER, vec_nodes ) );
					}
				} else {
					retNode = d_emptyRegexp;
				}
				break;
			}
			case kind::REGEXP_STAR: {
				Node dc = derivativeSingle(r[0], c);
				if(dc != d_emptyRegexp) {
					retNode = dc==NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, d_emptyString ) ? r : NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, dc, r );
				} else {
					retNode = d_emptyRegexp;
				}
				break;
			}
			default: {
				//TODO: special sym: sigma, none, all
				Trace("strings-error") << "Unsupported term: " << mkString( r ) << " in derivative of RegExp." << std::endl;
				Assert( false, "Unsupported Term" );
				//return Node::null();
			}
		}
		if(retNode != d_emptyRegexp) {
			retNode = Rewriter::rewrite( retNode );
		}
		d_dv_cache[dv] = retNode;
	}
	Trace("strings-regexp-derivative") << "RegExp-derivative returns : " << mkString( retNode ) << std::endl;
	return retNode;
}

//TODO:
bool RegExpOpr::guessLength( Node r, int &co ) {
	int k = r.getKind();
	switch( k ) {
		case kind::STRING_TO_REGEXP:
		{
			if(r[0].isConst()) {
				co += r[0].getConst< CVC4::String >().size();
				return true;
			} else {
				return false;
			}
		}
			break;
		case kind::REGEXP_CONCAT:
		{
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				if(!guessLength( r[i], co)) {
					return false;
				}
			}
			return true;
		}
			break;
		case kind::REGEXP_UNION:
		{
			int g_co;
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				int cop = 0;
				if(!guessLength( r[i], cop)) {
					return false;
				}
				if(i == 0) {
					g_co = cop;
				} else {
					g_co = gcd(g_co, cop);
				}
			}
			return true;
		}
			break;
		case kind::REGEXP_INTER:
		{
			int g_co;
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				int cop = 0;
				if(!guessLength( r[i], cop)) {
					return false;
				}
				if(i == 0) {
					g_co = cop;
				} else {
					g_co = gcd(g_co, cop);
				}
			}
			return true;
		}
			break;
		case kind::REGEXP_STAR:
		{
			co = 0;
			return true;
		}
			break;
		default:
			Trace("strings-error") << "Unsupported term: " << mkString( r ) << " in membership of RegExp." << std::endl;
			return false;
	}
}

void RegExpOpr::firstChar( Node r ) {
	Trace("strings-regexp-firstchar") << "Head characters: ";
	for(char ch = d_char_start; ch <= d_char_end; ++ch) {
		CVC4::String c(ch);
		Node dc = derivativeSingle(r, ch);
		if(!dc.isNull()) {
			Trace("strings-regexp-firstchar") << c << " (" << mkString(dc) << ")" << std::endl;
		}
	}
	Trace("strings-regexp-firstchar") << std::endl;
}

bool RegExpOpr::follow( Node r, CVC4::String c, std::vector< char > &vec_chars ) {
	int k = r.getKind();
	switch( k ) {
		case kind::STRING_TO_REGEXP:
		{
			if(r[0].isConst()) {
				if(r[0] != d_emptyString) {
					char t1 = r[0].getConst< CVC4::String >().getFirstChar();
					if(c.isEmptyString()) {
						vec_chars.push_back( t1 );
						return true;
					} else {
						char t2 = c.getFirstChar();
						if(t1 != t2) {
							return false;
						} else {
							if(c.size() >= 2) {
								vec_chars.push_back( c.substr(1,1).getFirstChar() );
							} else {
								vec_chars.push_back( '\0' );
							}
							return true;
						}
					}
				} else {
					return false;
				}
			} else {
				return false;
			}
		}
			break;
		case kind::REGEXP_CONCAT:
		{
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				if( follow(r[i], c, vec_chars) ) {
					if(vec_chars[vec_chars.size() - 1] == '\0') {
						vec_chars.pop_back();
						c = d_emptyString.getConst< CVC4::String >();
					}
				} else {
					return false;
				}
			}
			vec_chars.push_back( '\0' );
			return true;
		}
			break;
		case kind::REGEXP_UNION:
		{
			bool flag = false;
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				if( follow(r[i], c, vec_chars) ) {
					flag=true;
				}
			}
			return flag;
		}
			break;
		case kind::REGEXP_INTER:
		{
			std::vector< char > vt2;
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				std::vector< char > v_tmp;
				if( !follow(r[i], c, v_tmp) ) {
					return false;
				}
				std::vector< char > vt3(vt2);
				vt2.clear();
				std::set_intersection( vt3.begin(), vt3.end(), v_tmp.begin(), v_tmp.end(), vt2.begin() );
				if(vt2.size() == 0) {
					return false;
				}
			}
			vec_chars.insert( vec_chars.end(), vt2.begin(), vt2.end() );
			return true;
		}
			break;
		case kind::REGEXP_STAR:
		{
			if(follow(r[0], c, vec_chars)) {
				if(vec_chars[vec_chars.size() - 1] == '\0') {
					if(c.isEmptyString()) {
						return true;
					} else {
						vec_chars.pop_back();
						c = d_emptyString.getConst< CVC4::String >();
						return follow(r[0], c, vec_chars);
					}
				} else {
					return true;
				}
			} else {
				vec_chars.push_back( '\0' );
				return true;
			}
		}
			break;
			/*
		case kind::REGEXP_PLUS:
		{
			ret = delta( r[0] );
		}
			break;
		case kind::REGEXP_OPT:
		{
			ret = 1;
		}
			break;
		case kind::REGEXP_RANGE:
		{
			ret = 2;
		}
			break;*/
		default:
			//TODO: special sym: sigma, none, all
			Trace("strings-error") << "Unsupported term: " << mkString( r ) << " in delta of RegExp." << std::endl;
			//AlwaysAssert( false );
			//return Node::null();
			return false;
	}
}

Node RegExpOpr::mkAllExceptOne( char exp_c ) {
	std::vector< Node > vec_nodes;
	for(char c=d_char_start; c<=d_char_end; ++c) {
		if(c != exp_c ) {
			Node n = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( ::CVC4::String( c ) ) );
			vec_nodes.push_back( n );
		}
	}
	return NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes );
}

Node RegExpOpr::complement( Node r ) {
	Trace("strings-regexp-compl") << "RegExp-Compl starts with " << mkString( r ) << std::endl;
	Node retNode = r;
	if( d_compl_cache.find( r ) != d_compl_cache.end() ) {
		retNode = d_compl_cache[r];
	} else {
		int k = r.getKind();
		switch( k ) {
			case kind::STRING_TO_REGEXP:
			{
				if(r[0].isConst()) {
					if(r[0] == d_emptyString) {
						retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, d_sigma, d_sigma_star );
					} else {
						std::vector< Node > vec_nodes;
						vec_nodes.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, d_emptyString ) );
						CVC4::String s = r[0].getConst<String>();
						for(unsigned i=0; i<s.size(); ++i) {
							char c = s.substr(i, 1).getFirstChar();
							Node tmp = mkAllExceptOne( c );
							if(i != 0 ) {
								Node tmph = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, 
												NodeManager::currentNM()->mkConst( s.substr(0, i) ) );
								tmp = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, tmph, tmp );
							}
							tmp = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, tmp, d_sigma_star );
							vec_nodes.push_back( tmp );
						}
						Node tmp = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, r, d_sigma, d_sigma_star );
						vec_nodes.push_back( tmp );
						retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes );
					}
				} else {
					Trace("strings-error") << "Unsupported string variable: " << r[0] << " in complement of RegExp." << std::endl;
					//AlwaysAssert( false );
					//return Node::null();
				}
			}
				break;
			case kind::REGEXP_CONCAT:
			{
				std::vector< Node > vec_nodes;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					Node tmp = complement( r[i] );
					for(unsigned j=0; j<i; ++j) {
						tmp = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, r[j], tmp );
					}
					if(i != r.getNumChildren() - 1) {
						tmp = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, tmp,
								NodeManager::currentNM()->mkNode( kind::REGEXP_STAR, d_sigma ) );
					}
					vec_nodes.push_back( tmp );
				}
				retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes );
			}
				break;
			case kind::REGEXP_UNION:
			{
				std::vector< Node > vec_nodes;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					Node tmp = complement( r[i] );
					vec_nodes.push_back( tmp );
				}
				retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_INTER, vec_nodes );
			}
				break;
			case kind::REGEXP_INTER:
			{
				std::vector< Node > vec_nodes;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					Node tmp = complement( r[i] );
					vec_nodes.push_back( tmp );
				}
				retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes );
			}
				break;
			case kind::REGEXP_STAR:
			{
				retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, d_sigma, d_sigma_star );
				Node tmp = complement( r[0] );
				tmp = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, r, tmp );
				retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_INTER, retNode, tmp );
			}
				break;
			default:
				//TODO: special sym: sigma, none, all
				Trace("strings-error") << "Unsupported term: " << mkString( r ) << " in complement of RegExp." << std::endl;
				//AlwaysAssert( false );
				//return Node::null();
		}
		d_compl_cache[r] = retNode;
	}
	Trace("strings-regexp-compl") << "RegExp-Compl returns : " << mkString( retNode ) << std::endl;
	return retNode;
}

//simplify
void RegExpOpr::simplify(Node t, std::vector< Node > &new_nodes, bool polarity) {
	Trace("strings-regexp-simpl") << "RegExp-Simpl starts with " << t << ", polarity=" << polarity << std::endl; 
	Assert(t.getKind() == kind::STRING_IN_REGEXP);
	Node str = Rewriter::rewrite(t[0]);
	Node re  = Rewriter::rewrite(t[1]);
	if(polarity) {
		simplifyPRegExp( str, re, new_nodes );
	} else {
		simplifyNRegExp( str, re, new_nodes );
	}
	Trace("strings-regexp-simpl") << "RegExp-Simpl  returns (" << new_nodes.size() << "):\n";
	for(unsigned i=0; i<new_nodes.size(); i++) {
		Trace("strings-regexp-simpl") << "\t" << new_nodes[i] << std::endl;
	}
}
void RegExpOpr::simplifyNRegExp( Node s, Node r, std::vector< Node > &new_nodes ) {
	std::pair < Node, Node > p(s, r);
	std::map < std::pair< Node, Node >, Node >::const_iterator itr = d_simpl_neg_cache.find(p);
	if(itr != d_simpl_neg_cache.end()) {
		new_nodes.push_back( itr->second );
		return;
	} else {
		int k = r.getKind();
		Node conc;
		switch( k ) {
			case kind::REGEXP_EMPTY: {
				conc = d_true;
				break;
			}
			case kind::REGEXP_SIGMA: {
				conc = d_one.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s)).negate();
				break;
			}
			case kind::STRING_TO_REGEXP: {
				conc = s.eqNode(r[0]).negate();
				break;
			}
			case kind::REGEXP_CONCAT: {
				//TODO: rewrite empty
				Node b1 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
				Node b1v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b1);
				Node g1 = NodeManager::currentNM()->mkNode( kind::AND, NodeManager::currentNM()->mkNode(kind::GEQ, b1, d_zero),
							NodeManager::currentNM()->mkNode( kind::GEQ, NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s), b1 ) );
				Node s1 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->stringType());
				Node s2 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->stringType());
				Node b2v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, s1, s2);
				Node s12 = s.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, s1, s2));
				Node s1len = b1.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s1));
				Node s1r1 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s1, r[0]).negate();
				if(r[0].getKind() == kind::STRING_TO_REGEXP) {
					s1r1 = s1.eqNode(r[0][0]).negate();
				} else if(r[0].getKind() == kind::REGEXP_EMPTY) {
					s1r1 = d_true;
				}
				Node r2 = r[1];
				if(r.getNumChildren() > 2) {
					std::vector< Node > nvec;
					for(unsigned i=1; i<r.getNumChildren(); i++) {
						nvec.push_back( r[i] );
					}
					r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, nvec);
				}
				r2 = Rewriter::rewrite(r2);
				Node s2r2 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s2, r2).negate();
				if(r2.getKind() == kind::STRING_TO_REGEXP) {
					s2r2 = s2.eqNode(r2[0]).negate();
				} else if(r2.getKind() == kind::REGEXP_EMPTY) {
					s2r2 = d_true;
				}

				conc = NodeManager::currentNM()->mkNode(kind::OR, s1r1, s2r2);
				conc = NodeManager::currentNM()->mkNode(kind::AND, s12, s1len, conc);
				conc = NodeManager::currentNM()->mkNode(kind::EXISTS, b2v, conc);
				conc = NodeManager::currentNM()->mkNode(kind::IMPLIES, g1, conc);
				conc = NodeManager::currentNM()->mkNode(kind::FORALL, b1v, conc);
				break;
			}
			case kind::REGEXP_UNION: {
				std::vector< Node > c_and;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					if(r[i].getKind() == kind::STRING_TO_REGEXP) {
						c_and.push_back( r[i][0].eqNode(s).negate() );
					} else if(r[i].getKind() == kind::REGEXP_EMPTY) {
						continue;
					} else {
						c_and.push_back(NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r[i]).negate());
					}
				}
				conc = c_and.size() == 0 ? d_true :
						c_and.size() == 1 ? c_and[0] : NodeManager::currentNM()->mkNode(kind::AND, c_and);
				break;
			}
			case kind::REGEXP_INTER: {
				bool emptyflag = false;
				std::vector< Node > c_or;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					if(r[i].getKind() == kind::STRING_TO_REGEXP) {
						c_or.push_back( r[i][0].eqNode(s).negate() );
					} else if(r[i].getKind() == kind::REGEXP_EMPTY) {
						emptyflag = true;
						break;
					} else {
						c_or.push_back(NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r[i]).negate());
					}
				}
				if(emptyflag) {
					conc = d_true;
				} else {
					conc = c_or.size() == 1 ? c_or[0] : NodeManager::currentNM()->mkNode(kind::OR, c_or);
				}
				break;
			}
			case kind::REGEXP_STAR: {
				if(s == d_emptyString) {
					conc = d_false;
				} else if(r[0].getKind() == kind::REGEXP_EMPTY) {
					conc = s.eqNode(d_emptyString).negate();
				} else if(r[0].getKind() == kind::REGEXP_SIGMA) {
					conc = d_false;
				} else {
					Node lens = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s);
					Node sne = s.eqNode(d_emptyString).negate();
					Node b1 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
					Node b1v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b1);
					Node g1 = NodeManager::currentNM()->mkNode( kind::AND, NodeManager::currentNM()->mkNode(kind::GEQ, b1, d_one),
								NodeManager::currentNM()->mkNode( kind::GEQ, lens, b1 ) );
					//internal
					Node s1 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, s, d_zero, b1);
					Node s2 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, s, b1, NodeManager::currentNM()->mkNode(kind::MINUS, lens, b1));
					//Node s1 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->stringType());
					//Node s2 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->stringType());
					//Node b2v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, s1, s2);
					//Node s12 = s.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, s1, s2));
					//Node s1len = b1.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s1));
					Node s1r1 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s1, r[0]).negate();
					Node s2r2 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s2, r).negate();
					
					conc = NodeManager::currentNM()->mkNode(kind::OR, s1r1, s2r2);
					//conc = NodeManager::currentNM()->mkNode(kind::AND, s12, s1len, conc);
					//conc = NodeManager::currentNM()->mkNode(kind::EXISTS, b2v, conc);
					conc = NodeManager::currentNM()->mkNode(kind::IMPLIES, g1, conc);
					conc = NodeManager::currentNM()->mkNode(kind::FORALL, b1v, conc);
					conc = NodeManager::currentNM()->mkNode(kind::AND, sne, conc);
				}
				break;
			}
			default: {
				Trace("strings-regexp") << "Unsupported term: " << r << " in simplifyNRegExp." << std::endl;
				AlwaysAssert( false, "Unsupported Term" );
			}
		}
		conc = Rewriter::rewrite( conc );
		new_nodes.push_back( conc );
		d_simpl_neg_cache[p] = conc;
	}
}
void RegExpOpr::simplifyPRegExp( Node s, Node r, std::vector< Node > &new_nodes ) {
	std::pair < Node, Node > p(s, r);
	std::map < std::pair< Node, Node >, Node >::const_iterator itr = d_simpl_cache.find(p);
	if(itr != d_simpl_cache.end()) {
		new_nodes.push_back( itr->second );
		return;
	} else {
		int k = r.getKind();
		Node conc;
		switch( k ) {
			case kind::REGEXP_EMPTY: {
				conc = d_false;
				break;
			}
			case kind::REGEXP_SIGMA: {
				conc = d_one.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s));
				break;
			}
			case kind::STRING_TO_REGEXP: {
				conc = s.eqNode(r[0]);
				break;
			}
			case kind::REGEXP_CONCAT: {
				std::vector< Node > nvec;
				std::vector< Node > cc;
				bool emptyflag = false;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					if(r[i].getKind() == kind::STRING_TO_REGEXP) {
						cc.push_back( r[i][0] );
					} else if(r[i].getKind() == kind::REGEXP_EMPTY) {
						emptyflag = true;
						break;
					} else {
						Node sk = NodeManager::currentNM()->mkSkolem( "rc_$$", s.getType(), "created for regular expression concat" );
						Node lem = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, sk, r[i]);
						nvec.push_back(lem);
						cc.push_back(sk);
					}
				}
				if(emptyflag) {
					conc = d_false;
				} else {
					Node lem = s.eqNode( NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, cc) );
					nvec.push_back(lem);
					conc = nvec.size() == 1 ? nvec[0] : NodeManager::currentNM()->mkNode(kind::AND, nvec);
				}
				break;
			}
			case kind::REGEXP_UNION: {
				std::vector< Node > c_or;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					if(r[i].getKind() == kind::STRING_TO_REGEXP) {
						c_or.push_back( r[i][0].eqNode(s) );
					} else if(r[i].getKind() == kind::REGEXP_EMPTY) {
						continue;
					} else {
						c_or.push_back(NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r[i]));
					}
				}
				conc = c_or.size() == 0 ? d_false :
						c_or.size() == 1 ? c_or[0] : NodeManager::currentNM()->mkNode(kind::OR, c_or);
				break;
			}
			case kind::REGEXP_INTER: {
				std::vector< Node > c_and;
				bool emptyflag = false;
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					if(r[i].getKind() == kind::STRING_TO_REGEXP) {
						c_and.push_back( r[i][0].eqNode(s) );
					} else if(r[i].getKind() == kind::REGEXP_EMPTY) {
						emptyflag = true;
						break;
					} else {
						c_and.push_back(NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r[i]));
					}
				}
				if(emptyflag) {
					conc = d_false;
				} else {
					conc = c_and.size() == 1 ? c_and[0] : NodeManager::currentNM()->mkNode(kind::AND, c_and);
				}
				break;
			}
			case kind::REGEXP_STAR: {
				if(s == d_emptyString) {
					conc = d_true;
				} else if(r[0].getKind() == kind::REGEXP_EMPTY) {
					conc = s.eqNode(d_emptyString);
				} else if(r[0].getKind() == kind::REGEXP_SIGMA) {
					conc = d_true;
				} else {
					Node se = s.eqNode(d_emptyString);
					Node sinr = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r[0]);
					Node sk1 = NodeManager::currentNM()->mkSkolem( "rs_$$", s.getType(), "created for regular expression star" );
					Node sk2 = NodeManager::currentNM()->mkSkolem( "rs_$$", s.getType(), "created for regular expression star" );
					Node s1nz = sk1.eqNode(d_emptyString).negate();
					Node s2nz = sk2.eqNode(d_emptyString).negate();
					Node s1inr = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, sk1, r[0]);
					Node s2inrs = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, sk2, r);
					Node s12 = s.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, sk1, sk2));

					conc = NodeManager::currentNM()->mkNode(kind::AND, s12, s1nz, s2nz, s1inr, s2inrs);
					conc = NodeManager::currentNM()->mkNode(kind::OR, se, sinr, conc);
				}
				break;
			}
			default: {
				Trace("strings-regexp") << "Unsupported term: " << r << " in simplifyPRegExp." << std::endl;
				AlwaysAssert( false, "Unsupported Term" );
			}
		}
		conc = Rewriter::rewrite( conc );
		new_nodes.push_back( conc );
		d_simpl_cache[p] = conc;
	}
}

//printing
std::string RegExpOpr::niceChar( Node r ) {
	if(r.isConst()) {
		std::string s = r.getConst<CVC4::String>().toString() ;
		return s == "" ? "{E}" : ( s == " " ? "{ }" : s );
	} else {
		return r.toString();
	}
}
std::string RegExpOpr::mkString( Node r ) {
	std::string retStr;
	if(r.isNull()) {
		retStr = "Empty";
	} else {
		int k = r.getKind();
		switch( k ) {
			case kind::REGEXP_EMPTY: {
				retStr += "Empty";
				break;
			}
			case kind::REGEXP_SIGMA: {
				retStr += "{W}";
				break;
			}
			case kind::STRING_TO_REGEXP: {
				retStr += niceChar( r[0] );
				break;
			}
			case kind::REGEXP_CONCAT: {
				retStr += "(";
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					if(i != 0) retStr += ".";
					retStr += mkString( r[i] );
				}
				retStr += ")";
				break;
			}
			case kind::REGEXP_UNION: {
				if(r == d_sigma) {
					retStr += "{A}";
				} else {
					retStr += "(";
					for(unsigned i=0; i<r.getNumChildren(); ++i) {
						if(i != 0) retStr += "|";
						retStr += mkString( r[i] );
					}
					retStr += ")";
				}
				break;
			}
			case kind::REGEXP_INTER: {
				retStr += "(";
				for(unsigned i=0; i<r.getNumChildren(); ++i) {
					if(i != 0) retStr += "&";
					retStr += mkString( r[i] );
				}
				retStr += ")";
				break;
			}
			case kind::REGEXP_STAR: {
				retStr += mkString( r[0] );
				retStr += "*";
				break;
			}
			case kind::REGEXP_PLUS: {
				retStr += mkString( r[0] );
				retStr += "+";
				break;
			}
			case kind::REGEXP_OPT: {
				retStr += mkString( r[0] );
				retStr += "?";
				break;
			}
			case kind::REGEXP_RANGE: {
				retStr += "[";
				retStr += niceChar( r[0] );
				retStr += "-";
				retStr += niceChar( r[1] );
				retStr += "]";
				break;
			}
			default:
				Trace("strings-error") << "Unsupported term: " << r << " in RegExp." << std::endl;
				//AlwaysAssert( false );
				//return Node::null();
		}
	}

	return retStr;
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

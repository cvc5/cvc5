/*********************                                                        */
/*! \file theory_strings_preprocess.cpp
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Strings Preprocess
 **
 ** Strings Preprocess.
 **/

#include "theory/strings/theory_strings_preprocess.h"
#include "expr/kind.h"
#include "theory/strings/options.h"
#include "smt/logic_exception.h"

namespace CVC4 {
namespace theory {
namespace strings {

StringsPreprocess::StringsPreprocess() {
	std::vector< TypeNode > argTypes;
	argTypes.push_back(NodeManager::currentNM()->stringType());
	argTypes.push_back(NodeManager::currentNM()->integerType());

	//Constants
	d_zero = NodeManager::currentNM()->mkConst( ::CVC4::Rational(0) );
}

void StringsPreprocess::simplifyRegExp( Node s, Node r, std::vector< Node > &ret, std::vector< Node > &nn ) {
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
				if(r[i].getKind() == kind::STRING_TO_REGEXP) {
					cc.push_back( r[i][0] );
				} else {
					Node sk = NodeManager::currentNM()->mkSkolem( "recsym_$$", s.getType(), "created for regular expression concat" );
					simplifyRegExp( sk, r[i], ret, nn );
					cc.push_back( sk );
				}
			}
			Node cc_eq = NodeManager::currentNM()->mkNode( kind::EQUAL, s, 
						NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, cc ) );
			nn.push_back( cc_eq );
		}
			break;
		case kind::REGEXP_OR:
		{
			std::vector< Node > c_or;
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				simplifyRegExp( s, r[i], c_or, nn );
			}
			Node eq = NodeManager::currentNM()->mkNode( kind::OR, c_or );
			ret.push_back( eq );
		}
			break;
		case kind::REGEXP_INTER:
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				simplifyRegExp( s, r[i], ret, nn );
			}
			break;
		case kind::REGEXP_STAR:
		{
			Node eq = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, s, r );
			ret.push_back( eq );
		}
			break;
		default:
			//TODO: special sym: sigma, none, all
			Trace("strings-preprocess") << "Unsupported term: " << r << " in simplifyRegExp." << std::endl;
			Assert( false );
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
int StringsPreprocess::checkFixLenVar( Node t ) {
	int ret = 2;
	if(t.getKind() == kind::EQUAL) {
		if(t[0].getType().isInteger() && t[0].isConst() && t[1].getKind() == kind::STRING_LENGTH) {
			if(t[1][0].getKind() == kind::VARIABLE) {
				ret = 0;
			}
		} else if(t[1].getType().isInteger() && t[1].isConst() && t[0].getKind() == kind::STRING_LENGTH) {
			if(t[0][0].getKind() == kind::VARIABLE) {
				ret = 1;
			}
		}
	}
	if(ret != 2) {
		int len = t[ret].getConst<Rational>().getNumerator().toUnsignedInt();
		if(len < 2) {
			ret = 2;
		}
	}
	if(!options::stringExp()) {
		ret = 2;
	}
	return ret;
}
Node StringsPreprocess::simplify( Node t, std::vector< Node > &new_nodes ) {
    std::hash_map<TNode, Node, TNodeHashFunction>::const_iterator i = d_cache.find(t);
    if(i != d_cache.end()) {
      return (*i).second.isNull() ? t : (*i).second;
    }

	Trace("strings-preprocess") << "StringsPreprocess::simplify: " << t << std::endl;
	Node retNode = t;
	/*int c_id = checkFixLenVar(t);
	if( c_id != 2 ) {
		int v_id = 1 - c_id;
		int len = t[c_id].getConst<Rational>().getNumerator().toUnsignedInt();
		if(len > 1) {
			Node one = NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) );
			std::vector< Node > vec;
			for(int i=0; i<len; i++) {
				Node num = NodeManager::currentNM()->mkConst( ::CVC4::Rational(i) );
				//Node sk = NodeManager::currentNM()->mkNode(kind::STRING_CHARAT, t[v_id][0], num);
				Node sk = NodeManager::currentNM()->mkNode(kind::APPLY_UF, d_ufSubstr, t[v_id][0], num, one);
				vec.push_back(sk);
				Node cc = one.eqNode(NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk ));
				new_nodes.push_back( cc );
			}
			Node lem = t[v_id][0].eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, vec ) );
			lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, t, lem );
			new_nodes.push_back( lem );
			d_cache[t] = t;
			retNode = t;
		}
	} else */if( t.getKind() == kind::STRING_IN_REGEXP ) {
		// t0 in t1
		Node t0 = simplify( t[0], new_nodes );
		
		//if(!checkStarPlus( t[1] )) {
			//rewrite it
			std::vector< Node > ret;
			std::vector< Node > nn;
			simplifyRegExp( t0, t[1], ret, nn );
			new_nodes.insert( new_nodes.end(), nn.begin(), nn.end() );

			Node n = ret.size() == 1 ? ret[0] : NodeManager::currentNM()->mkNode( kind::AND, ret );
			d_cache[t] = (t == n) ? Node::null() : n;
			retNode = n;
		//} else {
			// TODO
		//	return (t0 == t[0]) ? t : NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, t0, t[1] );
		//}
	} else if( t.getKind() == kind::STRING_SUBSTR_TOTAL ) {
		Node lenxgti = NodeManager::currentNM()->mkNode( kind::GEQ, 
							NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, t[0] ),
							NodeManager::currentNM()->mkNode( kind::PLUS, t[1], t[2] ) );
		Node t1geq0 = NodeManager::currentNM()->mkNode(kind::GEQ, t[1], d_zero);
		Node t2geq0 = NodeManager::currentNM()->mkNode(kind::GEQ, t[2], d_zero);
		Node cond = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::AND, lenxgti, t1geq0, t2geq0 ));
		Node sk1 = NodeManager::currentNM()->mkSkolem( "ss1_$$", NodeManager::currentNM()->stringType(), "created for charat/substr" );
		Node sk3 = NodeManager::currentNM()->mkSkolem( "ss3_$$", NodeManager::currentNM()->stringType(), "created for charat/substr" );
		Node x_eq_123 = t[0].eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk1, t, sk3 ) );
		Node len_sk1_eq_i = t[1].eqNode( NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk1 ) );
		Node lemma = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::ITE, cond, 
						NodeManager::currentNM()->mkNode( kind::AND, x_eq_123, len_sk1_eq_i ),
						t.eqNode(NodeManager::currentNM()->mkConst( ::CVC4::String("") )) ));
		new_nodes.push_back( lemma );
		retNode = t;
		d_cache[t] = t;
	} else if( t.getKind() == kind::STRING_STRIDOF ) {
		if(options::stringExp()) {
			Node sk1 = NodeManager::currentNM()->mkSkolem( "io1_$$", t[0].getType(), "created for indexof" );
			Node sk2 = NodeManager::currentNM()->mkSkolem( "io2_$$", t[0].getType(), "created for indexof" );
			Node sk3 = NodeManager::currentNM()->mkSkolem( "io3_$$", t[0].getType(), "created for indexof" );
			Node sk4 = NodeManager::currentNM()->mkSkolem( "io4_$$", t[0].getType(), "created for indexof" );
			Node skk = NodeManager::currentNM()->mkSkolem( "iok_$$", t[2].getType(), "created for indexof" );
			Node eq = t[0].eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk1, sk2, sk3, sk4 ) );
			new_nodes.push_back( eq );
			Node negone = NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
			Node krange = NodeManager::currentNM()->mkNode( kind::GEQ, skk, negone );
			new_nodes.push_back( krange );
			krange = NodeManager::currentNM()->mkNode( kind::GT, 
						NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, t[0] ), skk);
			new_nodes.push_back( krange );

			//str.len(s1) < y + str.len(s2)
			Node c1 = Rewriter::rewrite(NodeManager::currentNM()->mkNode( kind::GT, 
							NodeManager::currentNM()->mkNode( kind::PLUS, t[2], NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, t[1] )),
							NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, t[0] )));
			//str.len(t1) = y
			Node c2 = t[2].eqNode( NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk1 ) );
			//~contain(t234, s2)
			Node c3 = Rewriter::rewrite(NodeManager::currentNM()->mkNode( kind::STRING_STRCTN,
						NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk2, sk3, sk4), t[1] ).negate());
			//left
			Node left = NodeManager::currentNM()->mkNode( kind::OR, c1, NodeManager::currentNM()->mkNode( kind::AND, c2, c3 ) );
			//t3 = s2
			Node c4 = t[1].eqNode( sk3 );
			//~contain(t2, s2)
			Node c5 = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, sk2, t[1] ).negate();
			//k=str.len(s1, s2)
			Node c6 = skk.eqNode( NodeManager::currentNM()->mkNode( kind::STRING_LENGTH,
									NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk1, sk2 )));
			//right
			Node right = Rewriter::rewrite(NodeManager::currentNM()->mkNode( kind::AND, c2, c4, c5, c6 ));
			Node cond = skk.eqNode( negone );
			Node rr = NodeManager::currentNM()->mkNode( kind::ITE, cond, left, right );
			new_nodes.push_back( rr );
			d_cache[t] = skk;
			retNode = skk;
		} else {
			throw LogicException("string indexof not supported in this release");
		}
	} else if( t.getKind() == kind::STRING_ITOS ) {
		if(options::stringExp()) {
			//Node num = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::ITE,
			//				NodeManager::currentNM()->mkNode(kind::GEQ, t[0], d_zero),
			//				t[0], NodeManager::currentNM()->mkNode(kind::UMINUS, t[0])));
			Node num = t[0];
			Node pret = t;//NodeManager::currentNM()->mkNode(kind::STRING_ITOS, num);
			Node lenp = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, pret);

			Node nonneg = NodeManager::currentNM()->mkNode(kind::GEQ, t[0], d_zero);
			Node lem = NodeManager::currentNM()->mkNode(kind::ITE, nonneg,
				NodeManager::currentNM()->mkNode(kind::GT, lenp, d_zero),
				t.eqNode(NodeManager::currentNM()->mkConst( ::CVC4::String("") ))//lenp.eqNode(d_zero)
				);
			new_nodes.push_back(lem);

			//non-neg
			Node b1 = NodeManager::currentNM()->mkBoundVar("x", NodeManager::currentNM()->integerType());
			Node b1v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b1);
			Node g1 = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::AND, NodeManager::currentNM()->mkNode( kind::GEQ, b1, d_zero ),
						NodeManager::currentNM()->mkNode( kind::GT, lenp, b1 ) ) );
			Node one = NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) );
			Node nine = NodeManager::currentNM()->mkConst( ::CVC4::Rational(9) );
			Node ten = NodeManager::currentNM()->mkConst( ::CVC4::Rational(10) );
			
			std::vector< TypeNode > argTypes;
			argTypes.push_back(NodeManager::currentNM()->integerType());
			Node ufP = NodeManager::currentNM()->mkSkolem("ufP_$$", 
								NodeManager::currentNM()->mkFunctionType(
									argTypes, NodeManager::currentNM()->integerType()),
								"uf type conv P");
			Node ufM = NodeManager::currentNM()->mkSkolem("ufM_$$", 
								NodeManager::currentNM()->mkFunctionType(
									argTypes, NodeManager::currentNM()->integerType()),
								"uf type conv M");
			
			lem = num.eqNode(NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufP, d_zero));
			new_nodes.push_back( lem );

			Node ufx = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufP, b1);
			Node ufx1 = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufP, NodeManager::currentNM()->mkNode(kind::MINUS,b1,one));
			Node ufMx = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufM, b1);
			Node b1gtz = NodeManager::currentNM()->mkNode(kind::GT, b1, d_zero);
			Node cc1 = ufx1.eqNode( NodeManager::currentNM()->mkNode(kind::PLUS,
							NodeManager::currentNM()->mkNode(kind::MULT, ufx, ten),
							NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufM, NodeManager::currentNM()->mkNode(kind::MINUS,b1,one)) ));
			cc1 = NodeManager::currentNM()->mkNode(kind::IMPLIES, b1gtz, cc1);
			Node lstx = lenp.eqNode(NodeManager::currentNM()->mkNode(kind::PLUS, b1, one));
			Node cc2 = ufx.eqNode(ufMx);
			cc2 = NodeManager::currentNM()->mkNode(kind::IMPLIES, lstx, cc2);
			// leading zero
			Node cl = NodeManager::currentNM()->mkNode(kind::AND, lstx, d_zero.eqNode(b1).negate());
			Node cc21 = NodeManager::currentNM()->mkNode(kind::IMPLIES, cl, NodeManager::currentNM()->mkNode(kind::GT, ufMx, d_zero));
			//cc3
			Node cc3 = NodeManager::currentNM()->mkNode(kind::GEQ, ufMx, d_zero);
			Node cc4 = NodeManager::currentNM()->mkNode(kind::GEQ, nine, ufMx);
			
			Node b21 = NodeManager::currentNM()->mkBoundVar("y", NodeManager::currentNM()->stringType());
			Node b22 = NodeManager::currentNM()->mkBoundVar("z", NodeManager::currentNM()->stringType());
			Node b2v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b21, b22);

			Node c21 = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, b21).eqNode(
						NodeManager::currentNM()->mkNode(kind::MINUS, lenp,	NodeManager::currentNM()->mkNode(kind::PLUS, b1, one) ));
			Node ch = 
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(0))),
				NodeManager::currentNM()->mkConst(::CVC4::String("0")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(1))),
				NodeManager::currentNM()->mkConst(::CVC4::String("1")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(2))),
				NodeManager::currentNM()->mkConst(::CVC4::String("2")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(3))),
				NodeManager::currentNM()->mkConst(::CVC4::String("3")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(4))),
				NodeManager::currentNM()->mkConst(::CVC4::String("4")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(5))),
				NodeManager::currentNM()->mkConst(::CVC4::String("5")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(6))),
				NodeManager::currentNM()->mkConst(::CVC4::String("6")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(7))),
				NodeManager::currentNM()->mkConst(::CVC4::String("7")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(8))),
				NodeManager::currentNM()->mkConst(::CVC4::String("8")),
				NodeManager::currentNM()->mkConst(::CVC4::String("9")))))))))));
			Node c22 = pret.eqNode( NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, b21, ch, b22) );
			Node cc5 = NodeManager::currentNM()->mkNode(kind::EXISTS, b2v, NodeManager::currentNM()->mkNode(kind::AND, c21, c22));
			std::vector< Node > svec;
			svec.push_back(cc1);svec.push_back(cc2);
			svec.push_back(cc21);
			svec.push_back(cc3);svec.push_back(cc4);svec.push_back(cc5);
			Node conc = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::AND, svec) );
			conc = NodeManager::currentNM()->mkNode( kind::IMPLIES, g1, conc );
			conc = NodeManager::currentNM()->mkNode( kind::FORALL, b1v, conc );
			conc = NodeManager::currentNM()->mkNode( kind::IMPLIES, nonneg, conc );
			new_nodes.push_back( conc );
			
			/*conc = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::IMPLIES, 
							NodeManager::currentNM()->mkNode(kind::LT, t[0], d_zero),
							t.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_CONCAT,
								NodeManager::currentNM()->mkConst(::CVC4::String("-")), pret))));
			new_nodes.push_back( conc );*/

			d_cache[t] = t;
			retNode = t;
		} else {
			throw LogicException("string int.to.str not supported in this release");
		}
	} else if( t.getKind() == kind::STRING_STOI ) {
		if(options::stringExp()) {
			Node negone = NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
			Node one = NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) );
			Node nine = NodeManager::currentNM()->mkConst( ::CVC4::Rational(9) );
			Node ten = NodeManager::currentNM()->mkConst( ::CVC4::Rational(10) );
			std::vector< TypeNode > argTypes;
			argTypes.push_back(NodeManager::currentNM()->integerType());
			Node ufP = NodeManager::currentNM()->mkSkolem("ufP_$$", 
								NodeManager::currentNM()->mkFunctionType(
									argTypes, NodeManager::currentNM()->integerType()),
								"uf type conv P");
			Node ufM = NodeManager::currentNM()->mkSkolem("ufM_$$", 
								NodeManager::currentNM()->mkFunctionType(
									argTypes, NodeManager::currentNM()->integerType()),
								"uf type conv M");

			Node ufP0 = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufP, d_zero);
			new_nodes.push_back(t.eqNode(ufP0));
			//lemma
			Node lem = NodeManager::currentNM()->mkNode(kind::IMPLIES,
				t[0].eqNode(NodeManager::currentNM()->mkConst(::CVC4::String(""))),
				t.eqNode(negone));
			new_nodes.push_back(lem);
			/*lem = NodeManager::currentNM()->mkNode(kind::IFF,
				t[0].eqNode(NodeManager::currentNM()->mkConst(::CVC4::String("0"))),
				t.eqNode(d_zero));
			new_nodes.push_back(lem);*/
			//cc1
			Node cc1 = t[0].eqNode(NodeManager::currentNM()->mkConst(::CVC4::String("")));
			//cc1 = NodeManager::currentNM()->mkNode(kind::AND, ufP0.eqNode(negone), cc1);
			//cc2
			Node b1 = NodeManager::currentNM()->mkBoundVar("x", NodeManager::currentNM()->integerType());
			Node z1 = NodeManager::currentNM()->mkBoundVar("z1", NodeManager::currentNM()->stringType());
			Node z2 = NodeManager::currentNM()->mkBoundVar("z2", NodeManager::currentNM()->stringType());
			Node z3 = NodeManager::currentNM()->mkBoundVar("z3", NodeManager::currentNM()->stringType());
			Node b1v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b1, z1, z2, z3);
			std::vector< Node > vec_n;
			Node g = NodeManager::currentNM()->mkNode(kind::GEQ, b1, d_zero);
			vec_n.push_back(g);
			g = NodeManager::currentNM()->mkNode(kind::GT, NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, t[0]), b1);
			vec_n.push_back(g);
			g = b1.eqNode( NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, z1) );
			vec_n.push_back(g);
			g = one.eqNode( NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, z2) );
			vec_n.push_back(g);
			g = t[0].eqNode( NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, z1, z2, z3) );
			vec_n.push_back(g);
			//Node z2 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, t[0], one);
			char chtmp[2];
			chtmp[1] = '\0';
			for(unsigned i=0; i<=9; i++) {
				chtmp[0] = i + '0';
				std::string stmp(chtmp);
				g = z2.eqNode( NodeManager::currentNM()->mkConst(::CVC4::String(stmp)) ).negate();
				vec_n.push_back(g);
			}
			Node cc2 = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::AND, vec_n));
			cc2 = NodeManager::currentNM()->mkNode(kind::EXISTS, b1v, cc2);
			//cc2 = NodeManager::currentNM()->mkNode(kind::AND, ufP0.eqNode(negone), cc2);
			//cc3
			Node b2 = NodeManager::currentNM()->mkBoundVar("y", NodeManager::currentNM()->integerType());
			Node b2v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b2);
			Node g2 = NodeManager::currentNM()->mkNode(kind::AND,
						NodeManager::currentNM()->mkNode(kind::GEQ, b2, d_zero),
						NodeManager::currentNM()->mkNode(kind::GT, NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, t[0]), b2));
			Node ufx = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufP, b2);
			Node ufx1 = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufP, NodeManager::currentNM()->mkNode(kind::MINUS,b2,one));
			Node ufMx = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufM, b2);
			Node w1 = NodeManager::currentNM()->mkBoundVar("w1", NodeManager::currentNM()->stringType());
			Node w2 = NodeManager::currentNM()->mkBoundVar("w2", NodeManager::currentNM()->stringType());
			Node b3v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, w1, w2);
			Node b2gtz = NodeManager::currentNM()->mkNode(kind::GT, b2, d_zero);
			Node c3c1 = ufx1.eqNode( NodeManager::currentNM()->mkNode(kind::PLUS,
							NodeManager::currentNM()->mkNode(kind::MULT, ufx, ten),
							NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufM, NodeManager::currentNM()->mkNode(kind::MINUS,b2,one)) ));
			c3c1 = NodeManager::currentNM()->mkNode(kind::AND, NodeManager::currentNM()->mkNode(kind::GT, ufx, d_zero), c3c1);
			c3c1 = NodeManager::currentNM()->mkNode(kind::IMPLIES, b2gtz, c3c1);
			Node lstx = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH,t[0]).eqNode(NodeManager::currentNM()->mkNode(kind::PLUS, b2, one));
			Node c3c2 = ufx.eqNode(ufMx);
			c3c2 = NodeManager::currentNM()->mkNode(kind::IMPLIES, lstx, c3c2);
			// leading zero
			Node cl = NodeManager::currentNM()->mkNode(kind::AND, lstx, t[0].eqNode(NodeManager::currentNM()->mkConst(::CVC4::String("0"))).negate());
			Node cc21 = NodeManager::currentNM()->mkNode(kind::IMPLIES, cl, NodeManager::currentNM()->mkNode(kind::GT, ufMx, d_zero));
			// cc3
			Node c3c3 = NodeManager::currentNM()->mkNode(kind::GEQ, ufMx, d_zero);
			Node c3c4 = NodeManager::currentNM()->mkNode(kind::GEQ, nine, ufMx);
			Node rev = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, w1).eqNode(
						NodeManager::currentNM()->mkNode(kind::MINUS, NodeManager::currentNM()->mkNode(kind::STRING_LENGTH,t[0]),
						NodeManager::currentNM()->mkNode(kind::PLUS, b2, one)));
			Node ch = 
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(0))),
				NodeManager::currentNM()->mkConst(::CVC4::String("0")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(1))),
				NodeManager::currentNM()->mkConst(::CVC4::String("1")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(2))),
				NodeManager::currentNM()->mkConst(::CVC4::String("2")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(3))),
				NodeManager::currentNM()->mkConst(::CVC4::String("3")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(4))),
				NodeManager::currentNM()->mkConst(::CVC4::String("4")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(5))),
				NodeManager::currentNM()->mkConst(::CVC4::String("5")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(6))),
				NodeManager::currentNM()->mkConst(::CVC4::String("6")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(7))),
				NodeManager::currentNM()->mkConst(::CVC4::String("7")),
				NodeManager::currentNM()->mkNode(kind::ITE, ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(8))),
				NodeManager::currentNM()->mkConst(::CVC4::String("8")),
				NodeManager::currentNM()->mkConst(::CVC4::String("9")))))))))));
			Node c3c5 = t[0].eqNode(NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, w1, ch, w2));
			c3c5 = NodeManager::currentNM()->mkNode(kind::AND, rev, c3c5);
			c3c5 = NodeManager::currentNM()->mkNode(kind::EXISTS, b3v, c3c5);
			std::vector< Node > svec;
			svec.push_back(c3c1);svec.push_back(c3c2);
			//svec.push_back(cc21);
			svec.push_back(c3c3);svec.push_back(c3c4);svec.push_back(c3c5);
			Node cc3 = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::AND, svec) );
			cc3 = NodeManager::currentNM()->mkNode(kind::IMPLIES, g2, cc3);
			cc3 = NodeManager::currentNM()->mkNode(kind::FORALL, b2v, cc3);
			//conc
			//Node conc = NodeManager::currentNM()->mkNode(kind::OR, cc1, cc2, cc3);
			Node conc = NodeManager::currentNM()->mkNode(kind::ITE, ufP0.eqNode(negone),
							NodeManager::currentNM()->mkNode(kind::OR, cc1, cc2), cc3);
			new_nodes.push_back( conc );
			d_cache[t] = t;
			retNode = t;
		} else {
			throw LogicException("string int.to.str not supported in this release");
		}
	} else if( t.getKind() == kind::STRING_STRREPL ) {
		if(options::stringExp()) {
			Node x = t[0];
			Node y = t[1];
			Node z = t[2];
			Node sk1 = NodeManager::currentNM()->mkSkolem( "rp1_$$", t[0].getType(), "created for replace" );
			Node sk2 = NodeManager::currentNM()->mkSkolem( "rp2_$$", t[0].getType(), "created for replace" );
			Node skw = NodeManager::currentNM()->mkSkolem( "rpw_$$", t[0].getType(), "created for replace" );
			Node cond = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, x, y );
			Node c1 = x.eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk1, y, sk2 ) );
			Node c2 = skw.eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk1, z, sk2 ) );
			Node c3 = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, sk1, y ).negate();
			Node rr = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::ITE, cond,
							NodeManager::currentNM()->mkNode( kind::AND, c1, c2, c3 ),
							skw.eqNode(x) ) );
			new_nodes.push_back( rr );

			d_cache[t] = skw;
			retNode = skw;
		} else {
			throw LogicException("string replace not supported in this release");
		}
	} else{
		d_cache[t] = Node::null();
		retNode = t;
	}
	
	/*if( t.getNumChildren()>0 ) {
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
			retNode = n;
		} else {
			d_cache[t] = Node::null();
			retNode = t;
		}
	}*/

	Trace("strings-preprocess") << "StringsPreprocess::simplify returns: " << retNode << std::endl;
	if(!new_nodes.empty()) {
		Trace("strings-preprocess") << " ... new nodes (" << new_nodes.size() << "):\n";
		for(unsigned int i=0; i<new_nodes.size(); ++i) {
			Trace("strings-preprocess") << "\t" << new_nodes[i] << "\n";
		}
	}

	return retNode;
}

Node StringsPreprocess::decompose(Node t, std::vector< Node > & new_nodes) {
	unsigned num = t.getNumChildren();
	if(num == 0) {
		return simplify(t, new_nodes);
	} else if(num == 1) {
		Node s = decompose(t[0], new_nodes);
		if(s != t[0]) {
			Node tmp = NodeManager::currentNM()->mkNode( t.getKind(), t[0] );
			return simplify(tmp, new_nodes);
		} else {
			return simplify(t, new_nodes);
		}
	} else {
		bool changed = false;
		std::vector< Node > cc;
		for(unsigned i=0; i<t.getNumChildren(); i++) {
			Node s = decompose(t[i], new_nodes);
			cc.push_back( s );
			if(s != t[i]) {
				changed = true;
			}
		}
		if(changed) {
			Node tmp = NodeManager::currentNM()->mkNode( t.getKind(), cc );
			return simplify(tmp, new_nodes);
		} else {
			return simplify(t, new_nodes);
		}
	}
}

void StringsPreprocess::simplify(std::vector< Node > &vec_node, std::vector< Node > &new_nodes) {
	for( unsigned i=0; i<vec_node.size(); i++ ){
		vec_node[i] = decompose( vec_node[i], new_nodes );
	}
}

void StringsPreprocess::simplify(std::vector< Node > &vec_node) {
	std::vector< Node > new_nodes;
	simplify(vec_node, new_nodes);
	vec_node.insert( vec_node.end(), new_nodes.begin(), new_nodes.end() );
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

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
#include <stdint.h>

namespace CVC4 {
namespace theory {
namespace strings {

StringsPreprocess::StringsPreprocess() {
  //Constants
  d_zero = NodeManager::currentNM()->mkConst( ::CVC4::Rational(0) );
}

void StringsPreprocess::processRegExp( Node s, Node r, std::vector< Node > &ret ) {
  int k = r.getKind();
  switch( k ) {
    case kind::REGEXP_EMPTY: {
      Node eq = NodeManager::currentNM()->mkConst( false );
      ret.push_back( eq );
      break;
    }
    case kind::REGEXP_SIGMA: {
      Node one = NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) );
      Node eq = one.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s));
      ret.push_back( eq );
      break;
    }
    case kind::STRING_TO_REGEXP: {
      Node eq = s.eqNode( r[0] );
      ret.push_back( eq );
      break;
    }
    case kind::REGEXP_CONCAT: {
      bool flag = true;
      std::vector< Node > cc;
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        if(r[i].getKind() == kind::STRING_TO_REGEXP) {
          cc.push_back( r[i][0] );
        } else {
          flag = false;
          break;
        }
      }
      if(flag) {
        Node eq = s.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, cc));
        ret.push_back(eq);
      } else {
        Node eq = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, s, r );
        ret.push_back( eq );
      }
      break;
    }
    case kind::REGEXP_UNION: {
      std::vector< Node > c_or;
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        std::vector< Node > ntmp;
        processRegExp( s, r[i], ntmp );
        Node lem = ntmp.size()==1 ? ntmp[0] : NodeManager::currentNM()->mkNode(kind::AND, ntmp);
        c_or.push_back( lem );
      }
      Node eq = NodeManager::currentNM()->mkNode(kind::OR, c_or);
      ret.push_back( eq );
      break;
    }
    case kind::REGEXP_INTER: {
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        processRegExp( s, r[i], ret );
      }
      break;
    }
    case kind::REGEXP_STAR: {
      if(r[0].getKind() == kind::REGEXP_SIGMA) {
        ret.push_back(NodeManager::currentNM()->mkConst(true));
      } else {
        Node eq = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, s, r );
        ret.push_back( eq );
      }
      break;
    }
    default: {
      Trace("strings-error") << "Unsupported term: " << r << " in simplifyRegExp." << std::endl;
      Assert( false, "Unsupported Term" );
    }
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
  } else */
  if( t.getKind() == kind::STRING_IN_REGEXP ) {
    Node t0 = simplify( t[0], new_nodes );

    //rewrite it
    std::vector< Node > ret;
    processRegExp( t0, t[1], ret );

    Node n = ret.size() == 1 ? ret[0] : NodeManager::currentNM()->mkNode( kind::AND, ret );
    n = Rewriter::rewrite(n);
    d_cache[t] = (t == n) ? Node::null() : n;
    retNode = n;
  } else if( t.getKind() == kind::STRING_SUBSTR_TOTAL ) {
    Node lenxgti = NodeManager::currentNM()->mkNode( kind::GEQ,
          NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, t[0] ),
          NodeManager::currentNM()->mkNode( kind::PLUS, t[1], t[2] ) );
    Node t1geq0 = NodeManager::currentNM()->mkNode(kind::GEQ, t[1], d_zero);
    Node t2geq0 = NodeManager::currentNM()->mkNode(kind::GEQ, t[2], d_zero);
    Node cond = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::AND, lenxgti, t1geq0, t2geq0 ));
    Node sk1 = NodeManager::currentNM()->mkSkolem( "ss1", NodeManager::currentNM()->stringType(), "created for charat/substr" );
    Node sk3 = NodeManager::currentNM()->mkSkolem( "ss3", NodeManager::currentNM()->stringType(), "created for charat/substr" );
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
      Node sk1 = NodeManager::currentNM()->mkSkolem( "io1", t[0].getType(), "created for indexof" );
      Node sk2 = NodeManager::currentNM()->mkSkolem( "io2", t[0].getType(), "created for indexof" );
      Node sk3 = NodeManager::currentNM()->mkSkolem( "io3", t[0].getType(), "created for indexof" );
      Node sk4 = NodeManager::currentNM()->mkSkolem( "io4", t[0].getType(), "created for indexof" );
      Node skk = NodeManager::currentNM()->mkSkolem( "iok", t[2].getType(), "created for indexof" );
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
      throw LogicException("string indexof not supported in default mode, try --strings-exp");
    }
  } else if( t.getKind() == kind::STRING_ITOS || t.getKind() == kind::STRING_U16TOS || t.getKind() == kind::STRING_U32TOS ) {
    if(options::stringExp()) {
      //Node num = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::ITE,
      //        NodeManager::currentNM()->mkNode(kind::GEQ, t[0], d_zero),
      //        t[0], NodeManager::currentNM()->mkNode(kind::UMINUS, t[0])));
      Node num = t[0];
      Node pret = NodeManager::currentNM()->mkNode(kind::STRING_ITOS, num);
      Node lenp = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, pret);

      Node nonneg = NodeManager::currentNM()->mkNode(kind::GEQ, t[0], d_zero);
      if(t.getKind()==kind::STRING_U16TOS) {
        nonneg = NodeManager::currentNM()->mkNode(kind::AND, nonneg, NodeManager::currentNM()->mkNode(kind::GEQ, NodeManager::currentNM()->mkConst( ::CVC4::Rational(UINT16_MAX) ), t[0]));
        Node lencond = NodeManager::currentNM()->mkNode(kind::GEQ, NodeManager::currentNM()->mkConst( ::CVC4::Rational(5) ), lenp);
        new_nodes.push_back(lencond);
      } else if(t.getKind()==kind::STRING_U32TOS) {
        nonneg = NodeManager::currentNM()->mkNode(kind::AND, nonneg, NodeManager::currentNM()->mkNode(kind::GEQ, NodeManager::currentNM()->mkConst( ::CVC4::Rational(UINT32_MAX) ), t[0]));
        Node lencond = NodeManager::currentNM()->mkNode(kind::GEQ, NodeManager::currentNM()->mkConst( ::CVC4::Rational(10) ), lenp);
        new_nodes.push_back(lencond);
      }

      Node lem = NodeManager::currentNM()->mkNode(kind::IFF, nonneg.negate(),
        pret.eqNode(NodeManager::currentNM()->mkConst( ::CVC4::String("") ))//lenp.eqNode(d_zero)
        );
      new_nodes.push_back(lem);

      //non-neg
      Node b1 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
      Node b1v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b1);
      Node g1 = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::AND, NodeManager::currentNM()->mkNode( kind::GEQ, b1, d_zero ),
            NodeManager::currentNM()->mkNode( kind::GT, lenp, b1 ) ) );
      Node one = NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) );
      Node nine = NodeManager::currentNM()->mkConst( ::CVC4::Rational(9) );
      Node ten = NodeManager::currentNM()->mkConst( ::CVC4::Rational(10) );

      std::vector< TypeNode > argTypes;
      argTypes.push_back(NodeManager::currentNM()->integerType());
      Node ufP = NodeManager::currentNM()->mkSkolem("ufP",
                NodeManager::currentNM()->mkFunctionType(
                  argTypes, NodeManager::currentNM()->integerType()),
                "uf type conv P");
      Node ufM = NodeManager::currentNM()->mkSkolem("ufM",
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

      Node b21 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->stringType());
      Node b22 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->stringType());
      Node b2v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b21, b22);

      Node c21 = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, b21).eqNode(
            NodeManager::currentNM()->mkNode(kind::MINUS, lenp, NodeManager::currentNM()->mkNode(kind::PLUS, b1, one) ));
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

      d_cache[t] = pret;
      if(t != pret) {
        d_cache[pret] = pret;
      }
      retNode = pret;
    } else {
      throw LogicException("string int.to.str not supported in default mode, try --strings-exp");
    }
  } else if( t.getKind() == kind::STRING_STOI || t.getKind() == kind::STRING_STOU16 || t.getKind() == kind::STRING_STOU32 ) {
    if(options::stringExp()) {
      Node str = t[0];
      Node pret = NodeManager::currentNM()->mkNode(kind::STRING_STOI, str);
      Node lenp = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, str);

      Node negone = NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
      Node one = NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) );
      Node nine = NodeManager::currentNM()->mkConst( ::CVC4::Rational(9) );
      Node ten = NodeManager::currentNM()->mkConst( ::CVC4::Rational(10) );
      std::vector< TypeNode > argTypes;
      argTypes.push_back(NodeManager::currentNM()->integerType());
      Node ufP = NodeManager::currentNM()->mkSkolem("ufP",
                NodeManager::currentNM()->mkFunctionType(
                  argTypes, NodeManager::currentNM()->integerType()),
                "uf type conv P");
      Node ufM = NodeManager::currentNM()->mkSkolem("ufM",
                NodeManager::currentNM()->mkFunctionType(
                  argTypes, NodeManager::currentNM()->integerType()),
                "uf type conv M");

      //Node ufP0 = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufP, d_zero);
      //new_nodes.push_back(pret.eqNode(ufP0));
      //lemma
      Node lem = NodeManager::currentNM()->mkNode(kind::IMPLIES,
        str.eqNode(NodeManager::currentNM()->mkConst(::CVC4::String(""))),
        pret.eqNode(negone));
      new_nodes.push_back(lem);
      /*lem = NodeManager::currentNM()->mkNode(kind::IFF,
        t[0].eqNode(NodeManager::currentNM()->mkConst(::CVC4::String("0"))),
        t.eqNode(d_zero));
      new_nodes.push_back(lem);*/
      if(t.getKind()==kind::STRING_U16TOS) {
        lem = NodeManager::currentNM()->mkNode(kind::GEQ, NodeManager::currentNM()->mkConst(::CVC4::String("5")), lenp);
        new_nodes.push_back(lem);
      } else if(t.getKind()==kind::STRING_U32TOS) {
        lem = NodeManager::currentNM()->mkNode(kind::GEQ, NodeManager::currentNM()->mkConst(::CVC4::String("9")), lenp);
        new_nodes.push_back(lem);
      }
      //cc1
      Node cc1 = str.eqNode(NodeManager::currentNM()->mkConst(::CVC4::String("")));
      //cc1 = NodeManager::currentNM()->mkNode(kind::AND, ufP0.eqNode(negone), cc1);
      //cc2
      std::vector< Node > vec_n;
      Node p = NodeManager::currentNM()->mkSkolem("p", NodeManager::currentNM()->integerType());
      Node g = NodeManager::currentNM()->mkNode(kind::GEQ, p, d_zero);
      vec_n.push_back(g);
      g = NodeManager::currentNM()->mkNode(kind::GT, lenp, p);
      vec_n.push_back(g);
      Node z2 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, str, p, one);
      char chtmp[2];
      chtmp[1] = '\0';
      for(unsigned i=0; i<=9; i++) {
        chtmp[0] = i + '0';
        std::string stmp(chtmp);
        g = z2.eqNode( NodeManager::currentNM()->mkConst(::CVC4::String(stmp)) ).negate();
        vec_n.push_back(g);
      }
      Node cc2 = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::AND, vec_n));
      //cc3
      Node b2 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
      Node b2v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b2);
      Node g2 = NodeManager::currentNM()->mkNode(kind::AND,
            NodeManager::currentNM()->mkNode(kind::GEQ, b2, d_zero),
            NodeManager::currentNM()->mkNode(kind::GT, lenp, b2));
      Node ufx = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufP, b2);
      Node ufx1 = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufP, NodeManager::currentNM()->mkNode(kind::MINUS,b2,one));
      Node ufMx = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufM, b2);
      std::vector< Node > vec_c3;
      std::vector< Node > vec_c3b;
      //qx between 0 and 9
      Node c3cc = NodeManager::currentNM()->mkNode(kind::GEQ, ufMx, d_zero);
      vec_c3b.push_back(c3cc);
      c3cc = NodeManager::currentNM()->mkNode(kind::GEQ, nine, ufMx);
      vec_c3b.push_back(c3cc);
      Node sx = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, str, b2, one);
      for(unsigned i=0; i<=9; i++) {
        chtmp[0] = i + '0';
        std::string stmp(chtmp);
        c3cc = NodeManager::currentNM()->mkNode(kind::IFF,
          ufMx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::Rational(i))),
          sx.eqNode(NodeManager::currentNM()->mkConst(::CVC4::String(stmp))));
        vec_c3b.push_back(c3cc);
      }
      //c312
      Node b2gtz = NodeManager::currentNM()->mkNode(kind::GT, b2, d_zero);
      c3cc = NodeManager::currentNM()->mkNode(kind::IMPLIES, b2gtz,
        ufx.eqNode(NodeManager::currentNM()->mkNode(kind::PLUS,
          NodeManager::currentNM()->mkNode(kind::MULT, ufx1, ten),
          ufMx)));
      vec_c3b.push_back(c3cc);
      c3cc = NodeManager::currentNM()->mkNode(kind::AND, vec_c3b);
      c3cc = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::IMPLIES, g2, c3cc) );
      c3cc = NodeManager::currentNM()->mkNode(kind::FORALL, b2v, c3cc);
      vec_c3.push_back(c3cc);
      //unbound
      c3cc = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufP, d_zero).eqNode(NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufM, d_zero));
      vec_c3.push_back(c3cc);
      Node lstx = NodeManager::currentNM()->mkNode(kind::MINUS, lenp, one);
      Node upflstx = NodeManager::currentNM()->mkNode(kind::APPLY_UF, ufP, lstx);
      c3cc = upflstx.eqNode(pret);
      vec_c3.push_back(c3cc);
      Node cc3 = NodeManager::currentNM()->mkNode(kind::AND, vec_c3);
      Node conc = NodeManager::currentNM()->mkNode(kind::ITE, pret.eqNode(negone),
              NodeManager::currentNM()->mkNode(kind::OR, cc1, cc2), cc3);
      new_nodes.push_back( conc );

      d_cache[t] = pret;
      if(t != pret) {
        d_cache[pret] = pret;
      }
      retNode = pret;
    } else {
      throw LogicException("string int.to.str not supported in default mode, try --strings-exp");
    }
  } else if( t.getKind() == kind::STRING_STRREPL ) {
    if(options::stringExp()) {
      Node x = t[0];
      Node y = t[1];
      Node z = t[2];
      Node sk1 = NodeManager::currentNM()->mkSkolem( "rp1", t[0].getType(), "created for replace" );
      Node sk2 = NodeManager::currentNM()->mkSkolem( "rp2", t[0].getType(), "created for replace" );
      Node skw = NodeManager::currentNM()->mkSkolem( "rpw", t[0].getType(), "created for replace" );
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
      throw LogicException("string replace not supported in default mode, try --strings-exp");
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
  std::hash_map<TNode, Node, TNodeHashFunction>::const_iterator i = d_cache.find(t);
  if(i != d_cache.end()) {
    return (*i).second.isNull() ? t : (*i).second;
  }

  unsigned num = t.getNumChildren();
  if(num == 0) {
    return simplify(t, new_nodes);
  } else {
    bool changed = false;
    std::vector< Node > cc;
    if (t.getMetaKind() == kind::metakind::PARAMETERIZED) {
      cc.push_back(t.getOperator());
    }
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

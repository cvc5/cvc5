/*********************                                                        */
/*! \file theory_strings_preprocess.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Strings Preprocess
 **
 ** Strings Preprocess.
 **/

#include "theory/strings/theory_strings_preprocess.h"

#include <stdint.h>

#include "expr/kind.h"
#include "options/strings_options.h"
#include "proof/proof_manager.h"
#include "smt/logic_exception.h"


namespace CVC4 {
namespace theory {
namespace strings {

StringsPreprocess::StringsPreprocess( context::UserContext* u ){
  //Constants
  d_zero = NodeManager::currentNM()->mkConst( ::CVC4::Rational(0) );
  d_one = NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) );
}

StringsPreprocess::~StringsPreprocess(){

}

Node StringsPreprocess::getUfForNode( Kind k, Node n, unsigned id ) {
  std::map< unsigned, Node >::iterator it = d_uf[k].find( id );
  if( it==d_uf[k].end() ){
    std::vector< TypeNode > types;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      types.push_back( n[i].getType() );
    }
    TypeNode typ = NodeManager::currentNM()->mkFunctionType( types, n.getType() );
    Node f = NodeManager::currentNM()->mkSkolem( "sop", typ, "op created for string op" );
    d_uf[k][id] = f;
    return f;
  }else{
    return it->second;
  }
}

//pro: congruence possible, con: introduces UF/requires theory combination
//  currently hurts performance
//TODO: for all skolems below
Node StringsPreprocess::getUfAppForNode( Kind k, Node n, unsigned id ) {
  std::vector< Node > children;
  children.push_back( getUfForNode( k, n, id ) );
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    children.push_back( n[i] );
  }
  return NodeManager::currentNM()->mkNode( kind::APPLY_UF, children );
}

//returns an n such that t can be replaced by n, under the assumption of lemmas in new_nodes

Node StringsPreprocess::simplify( Node t, std::vector< Node > &new_nodes ) {
  unsigned prev_new_nodes = new_nodes.size();
  Trace("strings-preprocess-debug") << "StringsPreprocess::simplify: " << t << std::endl;
  Node retNode = t;

  if( t.getKind() == kind::STRING_SUBSTR ) {
    Node skt;
    if( options::stringUfReduct() ){
      skt = getUfAppForNode( kind::STRING_SUBSTR, t );
    }else{
      skt = NodeManager::currentNM()->mkSkolem( "sst", NodeManager::currentNM()->stringType(), "created for substr" );
    }
    Node t12 = NodeManager::currentNM()->mkNode( kind::PLUS, t[1], t[2] );
    Node lt0 = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, t[0] );
    //start point is greater than or equal zero
    Node c1 = NodeManager::currentNM()->mkNode( kind::GEQ, t[1], d_zero );
    //start point is less than end of string
    Node c2 = NodeManager::currentNM()->mkNode( kind::GT, lt0, t[1] );
    //length is positive
    Node c3 = NodeManager::currentNM()->mkNode( kind::GT, t[2], d_zero );
    Node cond = NodeManager::currentNM()->mkNode( kind::AND, c1, c2, c3 );
  
    Node sk1 = NodeManager::currentNM()->mkSkolem( "ss1", NodeManager::currentNM()->stringType(), "created for substr" );
    Node sk2 = NodeManager::currentNM()->mkSkolem( "ss2", NodeManager::currentNM()->stringType(), "created for substr" );
    Node b11 = t[0].eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk1, skt, sk2 ) );
    //length of first skolem is second argument
    Node b12 = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk1 ).eqNode( t[1] );
    //length of second skolem is abs difference between end point and end of string
    Node b13 = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk2 ).eqNode(
                 NodeManager::currentNM()->mkNode( kind::ITE, NodeManager::currentNM()->mkNode( kind::GEQ, lt0, t12 ),
                    NodeManager::currentNM()->mkNode( kind::MINUS, lt0, t12 ), d_zero ) );

    Node b1 = NodeManager::currentNM()->mkNode( kind::AND, b11, b12, b13 );
    Node b2 = skt.eqNode( NodeManager::currentNM()->mkConst( ::CVC4::String("") ) );
    Node lemma = NodeManager::currentNM()->mkNode( kind::ITE, cond, b1, b2 );
    new_nodes.push_back( lemma );
    retNode = skt;
  } else if( t.getKind() == kind::STRING_STRIDOF ) {
    Node sk2 = NodeManager::currentNM()->mkSkolem( "io2", NodeManager::currentNM()->stringType(), "created for indexof" );
    Node sk3 = NodeManager::currentNM()->mkSkolem( "io3", NodeManager::currentNM()->stringType(), "created for indexof" );
    Node sk4 = NodeManager::currentNM()->mkSkolem( "io4", NodeManager::currentNM()->stringType(), "created for indexof" );
    Node skk;
    if( options::stringUfReduct() ){
      skk = getUfAppForNode( kind::STRING_STRIDOF, t );
    }else{
      skk = NodeManager::currentNM()->mkSkolem( "iok", NodeManager::currentNM()->integerType(), "created for indexof" );
    }
    Node st = NodeManager::currentNM()->mkNode( kind::STRING_SUBSTR, t[0], t[2], NodeManager::currentNM()->mkNode( kind::MINUS, NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, t[0] ), t[2] ) );
    //TODO: simplify this (only applies when idof != -1)
    Node eq = st.eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk2, sk3, sk4 ) );
    new_nodes.push_back( eq );
    
    //learn range of idof?
    Node negone = NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
    Node krange = NodeManager::currentNM()->mkNode( kind::GEQ, skk, negone );
    new_nodes.push_back( krange );
    krange = NodeManager::currentNM()->mkNode( kind::GT, NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, t[0] ), skk);
    new_nodes.push_back( krange );

    // s2 = ""
    Node c1 = t[1].eqNode( NodeManager::currentNM()->mkConst( ::CVC4::String("") ) );
    //~contain(t234, s2)
    Node c3 = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, st, t[1] ).negate();
    //left
    Node left = NodeManager::currentNM()->mkNode( kind::OR, c1, c3 );
    //t3 = s2
    Node c4 = t[1].eqNode( sk3 );
    //~contain(t2, s2)
    Node c5 = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN,
                NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, sk2,
                  NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, t[1], d_zero,
                    NodeManager::currentNM()->mkNode(kind::MINUS,
                      NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, t[1]),
                      NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) )))),
                t[1] ).negate();
    //k=str.len(s2)
    Node c6 = skk.eqNode( NodeManager::currentNM()->mkNode( kind::PLUS, t[2],
                            NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk2 )) );
    //right
    Node right = NodeManager::currentNM()->mkNode( kind::AND, c4, c5, c6, c1.negate() );
    Node cond = skk.eqNode( negone );
    Node rr = NodeManager::currentNM()->mkNode( kind::ITE, cond, left, right );
    new_nodes.push_back( rr );
    retNode = skk;
  } else if( t.getKind() == kind::STRING_ITOS || t.getKind() == kind::STRING_U16TOS || t.getKind() == kind::STRING_U32TOS ) {
    //Node num = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::ITE,
    //        NodeManager::currentNM()->mkNode(kind::GEQ, t[0], d_zero),
    //        t[0], NodeManager::currentNM()->mkNode(kind::UMINUS, t[0])));
    Node num = t[0];
    Node pret;
    if( options::stringUfReduct() ){
      pret = NodeManager::currentNM()->mkNode(kind::STRING_ITOS, num);
    }else{
      pret = NodeManager::currentNM()->mkSkolem( "itost", NodeManager::currentNM()->stringType(), "created for itos" );
    }
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

    Node lem = NodeManager::currentNM()->mkNode(kind::EQUAL, nonneg.negate(),
      pret.eqNode(NodeManager::currentNM()->mkConst( ::CVC4::String("") ))//lenp.eqNode(d_zero)
      );
    new_nodes.push_back(lem);

    //non-neg
    Node b1 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
    Node b1v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b1);
    Node g1 = NodeManager::currentNM()->mkNode( kind::AND, NodeManager::currentNM()->mkNode( kind::GEQ, b1, d_zero ),
                                                           NodeManager::currentNM()->mkNode( kind::GT, lenp, b1 ) );
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
    Node conc = NodeManager::currentNM()->mkNode(kind::AND, svec);
    conc = NodeManager::currentNM()->mkNode( kind::IMPLIES, g1, conc );
    conc = NodeManager::currentNM()->mkNode( kind::FORALL, b1v, conc );
    conc = NodeManager::currentNM()->mkNode( kind::IMPLIES, nonneg, conc );
    new_nodes.push_back( conc );

    /*conc = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::IMPLIES,
            NodeManager::currentNM()->mkNode(kind::LT, t[0], d_zero),
            t.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_CONCAT,
              NodeManager::currentNM()->mkConst(::CVC4::String("-")), pret))));
    new_nodes.push_back( conc );*/
    retNode = pret;
  } else if( t.getKind() == kind::STRING_STOI || t.getKind() == kind::STRING_STOU16 || t.getKind() == kind::STRING_STOU32 ) {
    Node str = t[0];
    Node pret;
    if( options::stringUfReduct() ){
      pret = getUfAppForNode( kind::STRING_STOI, t );
    }else{
      pret = NodeManager::currentNM()->mkSkolem( "stoit", NodeManager::currentNM()->integerType(), "created for stoi" );
    }
    //Node pret = NodeManager::currentNM()->mkNode(kind::STRING_STOI, str);
    //Node pret = getUfAppForNode( kind::STRING_STOI, t );
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
    /*lem = NodeManager::currentNM()->mkNode(kind::EQUAL,
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
    Node z2 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, str, p, one);
    char chtmp[2];
    chtmp[1] = '\0';
    for(unsigned i=0; i<=9; i++) {
      chtmp[0] = i + '0';
      std::string stmp(chtmp);
      g = z2.eqNode( NodeManager::currentNM()->mkConst(::CVC4::String(stmp)) ).negate();
      vec_n.push_back(g);
    }
    Node cc2 = NodeManager::currentNM()->mkNode(kind::AND, vec_n);
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
    Node sx = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, str, b2, one);
    for(unsigned i=0; i<=9; i++) {
      chtmp[0] = i + '0';
      std::string stmp(chtmp);
      c3cc = NodeManager::currentNM()->mkNode(kind::EQUAL,
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
    c3cc = NodeManager::currentNM()->mkNode(kind::IMPLIES, g2, c3cc);
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
    retNode = pret;
  } else if( t.getKind() == kind::STRING_STRREPL ) {
    Node x = t[0];
    Node y = t[1];
    Node z = t[2];
    Node sk1 = NodeManager::currentNM()->mkSkolem( "rp1", t[0].getType(), "created for replace" );
    Node sk2 = NodeManager::currentNM()->mkSkolem( "rp2", t[0].getType(), "created for replace" );
    Node skw = NodeManager::currentNM()->mkSkolem( "rpw", t[0].getType(), "created for replace" );
    Node cond = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, x, y );
    cond = NodeManager::currentNM()->mkNode( kind::AND, cond, NodeManager::currentNM()->mkNode(kind::GT, NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, y), d_zero) );
    Node c1 = x.eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk1, y, sk2 ) );
    Node c2 = skw.eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk1, z, sk2 ) );
    Node c3 = NodeManager::currentNM()->mkNode(kind::STRING_STRCTN,
                NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, sk1,
                   NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, y, d_zero,
                      NodeManager::currentNM()->mkNode(kind::MINUS,
                        NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, y),
                        NodeManager::currentNM()->mkConst(::CVC4::Rational(1))))), y).negate();
    Node rr = NodeManager::currentNM()->mkNode( kind::ITE, cond,
                                                NodeManager::currentNM()->mkNode( kind::AND, c1, c2, c3),
                                                skw.eqNode(x) );
    new_nodes.push_back( rr );
    retNode = skw;
  } else if( t.getKind() == kind::STRING_STRCTN ){
    Node x = t[0];
    Node s = t[1];
    //negative contains reduces to existential
    Node lenx = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, x);
    Node lens = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s);
    Node b1 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
    Node b1v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b1);
    Node body = NodeManager::currentNM()->mkNode( kind::AND, 
                  NodeManager::currentNM()->mkNode( kind::LEQ, d_zero, b1 ),
                  NodeManager::currentNM()->mkNode( kind::LEQ, b1, NodeManager::currentNM()->mkNode( kind::MINUS, lenx, lens ) ),
                  NodeManager::currentNM()->mkNode( kind::EQUAL, NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, x, b1, lens), s )                
                );
    retNode = NodeManager::currentNM()->mkNode( kind::EXISTS, b1v, body );
  }

  if( t!=retNode ){
    Trace("strings-preprocess") << "StringsPreprocess::simplify: " << t << " -> " << retNode << std::endl;
    if(!new_nodes.empty()) {
      Trace("strings-preprocess") << " ... new nodes (" << (new_nodes.size()-prev_new_nodes) << "):" << std::endl;
      for(unsigned int i=prev_new_nodes; i<new_nodes.size(); ++i) {
        Trace("strings-preprocess") << "   " << new_nodes[i] << std::endl;
      }
    }
  }
  return retNode;
}

Node StringsPreprocess::simplifyRec( Node t, std::vector< Node > & new_nodes, std::map< Node, Node >& visited ){
  std::map< Node, Node >::iterator it = visited.find(t);
  if( it!=visited.end() ){
    return it->second;
  }else{
    Node retNode;
    if( t.getNumChildren()==0 ){
      retNode = simplify( t, new_nodes );
    }else if( t.getKind()!=kind::FORALL ){
      bool changed = false;
      std::vector< Node > cc;
      if( t.getMetaKind() == kind::metakind::PARAMETERIZED ){
        cc.push_back( t.getOperator() );
      }
      for(unsigned i=0; i<t.getNumChildren(); i++) {
        Node s = simplifyRec( t[i], new_nodes, visited );
        cc.push_back( s );
        if( s!=t[i] ) {
          changed = true;
        }
      }
      Node tmp = t;
      if( changed ){
        tmp = NodeManager::currentNM()->mkNode( t.getKind(), cc );
      }
      retNode = simplify( tmp, new_nodes ); 
    }
    visited[t] = retNode;
    return retNode;
  }
}

Node StringsPreprocess::processAssertion( Node n, std::vector< Node > &new_nodes ) {
  std::map< Node, Node > visited;
  std::vector< Node > new_nodes_curr;
  Node ret = simplifyRec( n, new_nodes_curr, visited );
  while( !new_nodes_curr.empty() ){
    Node curr = new_nodes_curr.back();
    new_nodes_curr.pop_back();
    std::vector< Node > new_nodes_tmp;
    curr = simplifyRec( curr, new_nodes_tmp, visited );
    new_nodes_curr.insert( new_nodes_curr.end(), new_nodes_tmp.begin(), new_nodes_tmp.end() );
    new_nodes.push_back( curr );
  }
  return ret;
}

void StringsPreprocess::processAssertions( std::vector< Node > &vec_node ){
  std::map< Node, Node > visited;
  for( unsigned i=0; i<vec_node.size(); i++ ){
    Trace("strings-preprocess-debug") << "Preprocessing assertion " << vec_node[i] << std::endl;
    //preprocess until fixed point
    std::vector< Node > new_nodes;
    std::vector< Node > new_nodes_curr;
    new_nodes_curr.push_back( vec_node[i] );
    while( !new_nodes_curr.empty() ){
      Node curr = new_nodes_curr.back();
      new_nodes_curr.pop_back();
      std::vector< Node > new_nodes_tmp;
      curr = simplifyRec( curr, new_nodes_tmp, visited );
      new_nodes_curr.insert( new_nodes_curr.end(), new_nodes_tmp.begin(), new_nodes_tmp.end() );
      new_nodes.push_back( curr );
    }
    Node res = new_nodes.size()==1 ? new_nodes[0] : NodeManager::currentNM()->mkNode( kind::AND, new_nodes );
    if( res!=vec_node[i] ){
      res = Rewriter::rewrite( res );
      PROOF( ProofManager::currentPM()->addDependence( res, vec_node[i] ); );
      vec_node[i] = res;
    }
  }
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

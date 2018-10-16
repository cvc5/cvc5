/*********************                                                        */
/*! \file theory_strings_preprocess.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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
#include "theory/strings/theory_strings_rewriter.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

StringsPreprocess::StringsPreprocess(SkolemCache *sc, context::UserContext *u)
    : d_sc(sc)
{
  //Constants
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));
  d_empty_str = NodeManager::currentNM()->mkConst(String(""));
}

StringsPreprocess::~StringsPreprocess(){

}

Node StringsPreprocess::simplify( Node t, std::vector< Node > &new_nodes ) {
  unsigned prev_new_nodes = new_nodes.size();
  Trace("strings-preprocess-debug") << "StringsPreprocess::simplify: " << t << std::endl;
  Node retNode = t;
  NodeManager *nm = NodeManager::currentNM();

  if( t.getKind() == kind::STRING_SUBSTR ) {
    // processing term:  substr( s, n, m )
    Node s = t[0];
    Node n = t[1];
    Node m = t[2];
    Node skt = d_sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "sst");
    Node t12 = nm->mkNode(PLUS, n, m);
    t12 = Rewriter::rewrite(t12);
    Node lt0 = nm->mkNode(STRING_LENGTH, s);
    //start point is greater than or equal zero
    Node c1 = nm->mkNode(GEQ, n, d_zero);
    //start point is less than end of string
    Node c2 = nm->mkNode(GT, lt0, n);
    //length is positive
    Node c3 = nm->mkNode(GT, m, d_zero);
    Node cond = nm->mkNode(AND, c1, c2, c3);

    Node sk1 = n == d_zero ? d_empty_str
                           : d_sc->mkSkolemCached(
                                 s, n, SkolemCache::SK_PREFIX, "sspre");
    Node sk2 = TheoryStringsRewriter::checkEntailArith(t12, lt0)
                   ? d_empty_str
                   : d_sc->mkSkolemCached(
                         s, t12, SkolemCache::SK_SUFFIX_REM, "sssufr");
    Node b11 = s.eqNode(nm->mkNode(STRING_CONCAT, sk1, skt, sk2));
    //length of first skolem is second argument
    Node b12 = nm->mkNode(STRING_LENGTH, sk1).eqNode(n);
    //length of second skolem is abs difference between end point and end of string
    Node b13 = nm->mkNode(STRING_LENGTH, sk2)
                   .eqNode(nm->mkNode(ITE,
                                      nm->mkNode(GEQ, lt0, t12),
                                      nm->mkNode(MINUS, lt0, t12),
                                      d_zero));

    Node b1 = nm->mkNode(AND, b11, b12, b13);
    Node b2 = skt.eqNode(d_empty_str);
    Node lemma = nm->mkNode(ITE, cond, b1, b2);

    // assert:
    // IF    n >=0 AND n < len( s ) AND m > 0
    // THEN: s = sk1 ++ skt ++ sk2 AND
    //       len( sk1 ) = n AND
    //       len( sk2 ) = ite( len( s ) >= n+m, len( s )-(n+m), 0 )
    // ELSE: skt = ""
    new_nodes.push_back( lemma );

    // Thus, substr( s, n, m ) = skt
    retNode = skt;
  }
  else if (t.getKind() == kind::STRING_STRIDOF)
  {
    // processing term:  indexof( x, y, n )
    Node x = t[0];
    Node y = t[1];
    Node n = t[2];
    Node skk = nm->mkSkolem("iok", nm->integerType(), "created for indexof");

    Node negone = nm->mkConst(Rational(-1));
    Node krange = nm->mkNode(GEQ, skk, negone);
    // assert:   indexof( x, y, n ) >= -1
    new_nodes.push_back( krange );
    krange = nm->mkNode(GEQ, nm->mkNode(STRING_LENGTH, x), skk);
    // assert:   len( x ) >= indexof( x, y, z )
    new_nodes.push_back( krange );

    // substr( x, n, len( x ) - n )
    Node st = nm->mkNode(STRING_SUBSTR,
                         x,
                         n,
                         nm->mkNode(MINUS, nm->mkNode(STRING_LENGTH, x), n));
    Node io2 =
        d_sc->mkSkolemCached(st, y, SkolemCache::SK_FIRST_CTN_PRE, "iopre");
    Node io4 =
        d_sc->mkSkolemCached(st, y, SkolemCache::SK_FIRST_CTN_POST, "iopost");

    // ~contains( substr( x, n, len( x ) - n ), y )
    Node c11 = nm->mkNode(STRING_STRCTN, st, y).negate();
    // n > len( x )
    Node c12 = nm->mkNode(GT, n, nm->mkNode(STRING_LENGTH, x));
    // 0 > n
    Node c13 = nm->mkNode(GT, d_zero, n);
    Node cond1 = nm->mkNode(OR, c11, c12, c13);
    // skk = -1
    Node cc1 = skk.eqNode(negone);

    // y = ""
    Node cond2 = y.eqNode(d_empty_str);
    // skk = n
    Node cc2 = skk.eqNode(t[2]);

    // substr( x, n, len( x ) - n ) = str.++( io2, y, io4 )
    Node c31 = st.eqNode(nm->mkNode(STRING_CONCAT, io2, y, io4));
    // ~contains( str.++( io2, substr( y, 0, len( y ) - 1) ), y )
    Node c32 =
        nm->mkNode(
              STRING_STRCTN,
              nm->mkNode(
                  STRING_CONCAT,
                  io2,
                  nm->mkNode(
                      STRING_SUBSTR,
                      y,
                      d_zero,
                      nm->mkNode(MINUS, nm->mkNode(STRING_LENGTH, y), d_one))),
              y)
            .negate();
    // skk = n + len( io2 )
    Node c33 = skk.eqNode(nm->mkNode(PLUS, n, nm->mkNode(STRING_LENGTH, io2)));
    Node cc3 = nm->mkNode(AND, c31, c32, c33);

    // assert:
    // IF:   ~contains( substr( x, n, len( x ) - n ), y ) OR n > len(x) OR 0 > n
    // THEN: skk = -1
    // ELIF: y = ""
    // THEN: skk = n
    // ELSE: substr( x, n, len( x ) - n ) = str.++( io2, y, io4 ) ^
    //       ~contains( str.++( io2, substr( y, 0, len( y ) - 1) ), y ) ^
    //       skk = n + len( io2 )
    // for fresh io2, io4.
    Node rr = nm->mkNode(ITE, cond1, cc1, nm->mkNode(ITE, cond2, cc2, cc3));
    new_nodes.push_back( rr );

    // Thus, indexof( x, y, n ) = skk.
    retNode = skk;
  } else if( t.getKind() == kind::STRING_ITOS ) {
    //Node num = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::ITE,
    //        NodeManager::currentNM()->mkNode(kind::GEQ, t[0], d_zero),
    //        t[0], NodeManager::currentNM()->mkNode(kind::UMINUS, t[0])));
    Node num = t[0];
    Node pret = d_sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "itost");
    Node lenp = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, pret);

    Node nonneg = NodeManager::currentNM()->mkNode(kind::GEQ, t[0], d_zero);

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
  } else if( t.getKind() == kind::STRING_STOI ) {
    Node s = t[0];
    Node stoit = nm->mkSkolem("stoit", nm->integerType(), "created for stoi");
    Node lens = nm->mkNode(STRING_LENGTH, s);

    std::vector<Node> conc1;
    Node lem = stoit.eqNode(d_neg_one);
    conc1.push_back(lem);

    Node sEmpty = s.eqNode(d_empty_str);
    Node k = nm->mkSkolem("k", nm->integerType());
    Node kc1 = nm->mkNode(GEQ, k, d_zero);
    Node kc2 = nm->mkNode(LT, k, lens);
    Node codeSk = nm->mkNode(
        MINUS,
        nm->mkNode(STRING_CODE, nm->mkNode(STRING_SUBSTR, s, k, d_one)),
        nm->mkConst(Rational(48)));
    Node ten = nm->mkConst(Rational(10));
    Node kc3 = nm->mkNode(
        OR, nm->mkNode(LT, codeSk, d_zero), nm->mkNode(GEQ, codeSk, ten));
    conc1.push_back(nm->mkNode(OR, sEmpty, nm->mkNode(AND, kc1, kc2, kc3)));

    std::vector<Node> conc2;
    std::vector< TypeNode > argTypes;
    argTypes.push_back(nm->integerType());
    Node u = nm->mkSkolem("U", nm->mkFunctionType(argTypes, nm->integerType()));
    Node us =
        nm->mkSkolem("Us", nm->mkFunctionType(argTypes, nm->stringType()));
    Node ud =
        nm->mkSkolem("Ud", nm->mkFunctionType(argTypes, nm->stringType()));

    lem = stoit.eqNode(nm->mkNode(APPLY_UF, u, lens));
    conc2.push_back(lem);

    lem = d_zero.eqNode(nm->mkNode(APPLY_UF, u, d_zero));
    conc2.push_back(lem);

    lem = d_empty_str.eqNode(nm->mkNode(APPLY_UF, us, lens));
    conc2.push_back(lem);

    lem = s.eqNode(nm->mkNode(APPLY_UF, us, d_zero));
    conc2.push_back(lem);

    Node x = nm->mkBoundVar(nm->integerType());
    Node xbv = nm->mkNode(BOUND_VAR_LIST, x);
    Node g =
        nm->mkNode(AND, nm->mkNode(GEQ, x, d_zero), nm->mkNode(LT, x, lens));
    Node udx = nm->mkNode(APPLY_UF, ud, x);
    Node ux = nm->mkNode(APPLY_UF, u, x);
    Node ux1 = nm->mkNode(APPLY_UF, u, nm->mkNode(PLUS, x, d_one));
    Node c0 = nm->mkNode(STRING_CODE, nm->mkConst(String("0")));
    Node c = nm->mkNode(MINUS, nm->mkNode(STRING_CODE, udx), c0);
    Node usx = nm->mkNode(APPLY_UF, us, x);
    Node usx1 = nm->mkNode(APPLY_UF, us, nm->mkNode(PLUS, x, d_one));

    Node eqs = usx.eqNode(nm->mkNode(STRING_CONCAT, udx, usx1));
    Node eq = ux1.eqNode(nm->mkNode(PLUS, c, nm->mkNode(MULT, ten, ux)));
    Node cb =
        nm->mkNode(AND, nm->mkNode(GEQ, c, d_zero), nm->mkNode(LT, c, ten));

    lem = nm->mkNode(OR, g.negate(), nm->mkNode(AND, eqs, eq, cb));
    lem = nm->mkNode(FORALL, xbv, lem);
    conc2.push_back(lem);

    Node sneg = nm->mkNode(LT, stoit, d_zero);
    lem = nm->mkNode(ITE, sneg, nm->mkNode(AND, conc1), nm->mkNode(AND, conc2));
    new_nodes.push_back(lem);

    // assert:
    // IF stoit < 0
    // THEN:
    //   stoit = -1 ^
    //   ( s = "" OR
    //     ( k>=0 ^ k<len( s ) ^ ( str.code( str.substr( s, k, 1 ) ) < 48 OR
    //                             str.code( str.substr( s, k, 1 ) ) >= 58 )))
    // ELSE:
    //   stoit = U( len( s ) ) ^ U( 0 ) = 0 ^
    //   "" = Us( len( s ) ) ^ s = Us( 0 ) ^
    //   forall x. (x>=0 ^ x < str.len(s)) =>
    //     Us( x ) = Ud( x ) ++ Us( x+1 ) ^
    //     U( x+1 ) = ( str.code( Ud( x ) ) - 48 ) + 10*U( x )
    //     48 <= str.code( Ud( x ) ) < 58
    // Thus, str.to.int( s ) = stoit

    retNode = stoit;
  }
  else if (t.getKind() == kind::STRING_STRREPL)
  {
    // processing term: replace( x, y, z )
    Node x = t[0];
    Node y = t[1];
    Node z = t[2];
    TypeNode tn = t[0].getType();
    Node rp1 =
        d_sc->mkSkolemCached(x, y, SkolemCache::SK_FIRST_CTN_PRE, "rfcpre");
    Node rp2 =
        d_sc->mkSkolemCached(x, y, SkolemCache::SK_FIRST_CTN_POST, "rfcpost");
    Node rpw = d_sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "rpw");

    // y = ""
    Node cond1 = y.eqNode(nm->mkConst(CVC4::String("")));
    // rpw = str.++( z, x )
    Node c1 = rpw.eqNode(nm->mkNode(kind::STRING_CONCAT, z, x));

    // contains( x, y )
    Node cond2 = nm->mkNode(kind::STRING_STRCTN, x, y);
    // x = str.++( rp1, y, rp2 )
    Node c21 = x.eqNode(nm->mkNode(kind::STRING_CONCAT, rp1, y, rp2));
    // rpw = str.++( rp1, z, rp2 )
    Node c22 = rpw.eqNode(nm->mkNode(kind::STRING_CONCAT, rp1, z, rp2));
    // ~contains( str.++( rp1, substr( y, 0, len(y)-1 ) ), y )
    Node c23 =
        nm->mkNode(kind::STRING_STRCTN,
                   nm->mkNode(
                       kind::STRING_CONCAT,
                       rp1,
                       nm->mkNode(kind::STRING_SUBSTR,
                                  y,
                                  d_zero,
                                  nm->mkNode(kind::MINUS,
                                             nm->mkNode(kind::STRING_LENGTH, y),
                                             d_one))),
                   y)
            .negate();

    // assert:
    //   IF    y=""
    //   THEN: rpw = str.++( z, x )
    //   ELIF: contains( x, y )
    //   THEN: x = str.++( rp1, y, rp2 ) ^
    //         rpw = str.++( rp1, z, rp2 ) ^
    //         ~contains( str.++( rp1, substr( y, 0, len(y)-1 ) ), y ),
    //   ELSE: rpw = x
    // for fresh rp1, rp2, rpw
    Node rr = nm->mkNode(kind::ITE,
                         cond1,
                         c1,
                         nm->mkNode(kind::ITE,
                                    cond2,
                                    nm->mkNode(kind::AND, c21, c22, c23),
                                    rpw.eqNode(x)));
    new_nodes.push_back( rr );

    // Thus, replace( x, y, z ) = rpw.
    retNode = rpw;
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
  else if (t.getKind() == kind::STRING_LEQ)
  {
    Node ltp = nm->mkSkolem("ltp", nm->booleanType());
    Node k = nm->mkSkolem("k", nm->integerType());

    std::vector<Node> conj;
    conj.push_back(nm->mkNode(GEQ, k, d_zero));
    Node substr[2];
    Node code[2];
    for (unsigned r = 0; r < 2; r++)
    {
      Node ta = t[r];
      Node tb = t[1 - r];
      substr[r] = nm->mkNode(STRING_SUBSTR, ta, d_zero, k);
      code[r] =
          nm->mkNode(STRING_CODE, nm->mkNode(STRING_SUBSTR, ta, k, d_one));
      conj.push_back(nm->mkNode(LEQ, k, nm->mkNode(STRING_LENGTH, ta)));
    }
    conj.push_back(substr[0].eqNode(substr[1]));
    std::vector<Node> ite_ch;
    ite_ch.push_back(ltp);
    for (unsigned r = 0; r < 2; r++)
    {
      ite_ch.push_back(nm->mkNode(LT, code[r], code[1 - r]));
    }
    conj.push_back(nm->mkNode(ITE, ite_ch));

    // Intuitively, the reduction says either x and y are equal, or they have
    // some (maximal) common prefix after which their characters at position k
    // are distinct, and the comparison of their code matches the return value
    // of the overall term.
    // Notice the below reduction relies on the semantics of str.code being -1
    // for the empty string. In particular, say x = "a" and y = "ab", then the
    // reduction below is satisfied for k = 1, since
    //   str.code(substr( "a", 1, 1 )) = str.code( "" ) = -1 <
    //   str.code(substr( "ab", 1, 1 )) = str.code( "b" ) = 66

    // assert:
    //  IF x=y
    //  THEN: ltp
    //  ELSE: k >= 0 AND k <= len( x ) AND k <= len( y ) AND
    //        substr( x, 0, k ) = substr( y, 0, k ) AND
    //        IF    ltp
    //        THEN: str.code(substr( x, k, 1 )) < str.code(substr( y, k, 1 ))
    //        ELSE: str.code(substr( x, k, 1 )) > str.code(substr( y, k, 1 ))
    Node assert =
        nm->mkNode(ITE, t[0].eqNode(t[1]), ltp, nm->mkNode(AND, conj));
    new_nodes.push_back(assert);

    // Thus, str.<=( x, y ) = p_lt
    retNode = ltp;
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

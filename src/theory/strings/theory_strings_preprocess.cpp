/*********************                                                        */
/*! \file theory_strings_preprocess.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "proof/proof_manager.h"
#include "smt/logic_exception.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/sequences_rewriter.h"
#include "theory/strings/word.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

StringsPreprocess::StringsPreprocess(SkolemCache* sc,
                                     context::UserContext* u,
                                     SequencesStatistics& stats)
    : d_sc(sc), d_statistics(stats)
{
}

StringsPreprocess::~StringsPreprocess(){

}

Node StringsPreprocess::reduce(Node t,
                               std::vector<Node>& asserts,
                               SkolemCache* sc)
{
  Trace("strings-preprocess-debug")
      << "StringsPreprocess::reduce: " << t << std::endl;
  Node retNode = t;
  NodeManager* nm = NodeManager::currentNM();
  Node zero = nm->mkConst(Rational(0));
  Node one = nm->mkConst(Rational(1));
  Node negOne = nm->mkConst(Rational(-1));

  if( t.getKind() == kind::STRING_SUBSTR ) {
    // processing term:  substr( s, n, m )
    Node s = t[0];
    Node n = t[1];
    Node m = t[2];
    Node skt = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "sst");
    Node t12 = nm->mkNode(PLUS, n, m);
    t12 = Rewriter::rewrite(t12);
    Node lt0 = nm->mkNode(STRING_LENGTH, s);
    //start point is greater than or equal zero
    Node c1 = nm->mkNode(GEQ, n, zero);
    //start point is less than end of string
    Node c2 = nm->mkNode(GT, lt0, n);
    //length is positive
    Node c3 = nm->mkNode(GT, m, zero);
    Node cond = nm->mkNode(AND, c1, c2, c3);

    Node emp = Word::mkEmptyWord(t.getType());

    Node sk1 = sc->mkSkolemCached(s, n, SkolemCache::SK_PREFIX, "sspre");
    Node sk2 = sc->mkSkolemCached(s, t12, SkolemCache::SK_SUFFIX_REM, "sssufr");
    Node b11 = s.eqNode(nm->mkNode(STRING_CONCAT, sk1, skt, sk2));
    //length of first skolem is second argument
    Node b12 = nm->mkNode(STRING_LENGTH, sk1).eqNode(n);
    Node lsk2 = nm->mkNode(STRING_LENGTH, sk2);
    // Length of the suffix is either 0 (in the case where m + n > len(s)) or
    // len(s) - n -m
    Node b13 = nm->mkNode(
        OR,
        nm->mkNode(EQUAL, lsk2, nm->mkNode(MINUS, lt0, nm->mkNode(PLUS, n, m))),
        nm->mkNode(EQUAL, lsk2, zero));
    // Length of the result is at most m
    Node b14 = nm->mkNode(LEQ, nm->mkNode(STRING_LENGTH, skt), m);

    Node b1 = nm->mkNode(AND, b11, b12, b13, b14);
    Node b2 = skt.eqNode(emp);
    Node lemma = nm->mkNode(ITE, cond, b1, b2);

    // assert:
    // IF    n >=0 AND n < len( s ) AND m > 0
    // THEN: s = sk1 ++ skt ++ sk2 AND
    //       len( sk1 ) = n AND
    //       ( len( sk2 ) = len( s )-(n+m) OR len( sk2 ) = 0 ) AND
    //       len( skt ) <= m
    // ELSE: skt = ""
    //
    // Note: The length of sk2 is either 0 (if the n + m is greater or equal to
    // the length of s) or len(s) - (n + m) otherwise. If n + m is greater or
    // equal to the length of s, then len(s) - (n + m) is negative and in
    // conflict with lengths always being positive, so only len(sk2) = 0 may be
    // satisfied. If n + m is less than the length of s, then len(sk2) = 0
    // cannot be satisfied because we have the constraint that len(skt) <= m,
    // so sk2 must be greater than 0.
    asserts.push_back(lemma);

    // Thus, substr( s, n, m ) = skt
    retNode = skt;
  }
  else if (t.getKind() == kind::STRING_UPDATE)
  {
    // processing term:  update( s, n, r )
    Node s = t[0];
    Node n = t[1];
    Node r = t[2];
    Node skt = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "sst");
    Node ls = nm->mkNode(STRING_LENGTH, s);
    // start point is greater than or equal zero
    Node c1 = nm->mkNode(GEQ, n, zero);
    // start point is less than end of string
    Node c2 = nm->mkNode(GT, ls, n);
    Node cond = nm->mkNode(AND, c1, c2);

    // substr(r,0,|s|-n)
    Node lens = nm->mkNode(STRING_LENGTH, s);
    Node rs;
    if (r.isConst() && Word::getLength(r) == 1)
    {
      // optimization: don't need to take substring for single characters, due
      // to guard on where it is used in the reduction below.
      rs = r;
    }
    else
    {
      rs = nm->mkNode(STRING_SUBSTR, r, zero, nm->mkNode(MINUS, lens, n));
    }
    Node rslen = nm->mkNode(STRING_LENGTH, rs);
    Node nsuf = nm->mkNode(PLUS, n, rslen);
    // substr(s, n, len(substr(r,0,|s|-n))), which is used for formalizing the
    // purification variable sk3 below.
    Node ssubstr = nm->mkNode(STRING_SUBSTR, s, n, rslen);

    Node sk1 = sc->mkSkolemCached(s, n, SkolemCache::SK_PREFIX, "sspre");
    Node sk2 =
        sc->mkSkolemCached(s, nsuf, SkolemCache::SK_SUFFIX_REM, "sssufr");
    Node sk3 = sc->mkSkolemCached(ssubstr, SkolemCache::SK_PURIFY, "ssubstr");
    Node a1 = skt.eqNode(nm->mkNode(STRING_CONCAT, sk1, rs, sk2));
    Node a2 = s.eqNode(nm->mkNode(STRING_CONCAT, sk1, sk3, sk2));
    // length of first skolem is second argument
    Node a3 = nm->mkNode(STRING_LENGTH, sk1).eqNode(n);

    Node b1 = nm->mkNode(AND, a1, a2, a3);
    Node b2 = skt.eqNode(s);
    Node lemma = nm->mkNode(ITE, cond, b1, b2);

    // assert:
    // IF    n >=0 AND n < len( s )
    // THEN: skt = sk1 ++ substr(r,0,len(s)-n) ++ sk2 AND
    //       s = sk1 ++ sk3 ++ sk2 AND
    //       len( sk1 ) = n
    // ELSE: skt = s
    // We use an optimization where r is used instead of substr(r,0,len(s)-n)
    // if r is a constant of length one.
    asserts.push_back(lemma);

    // Thus, str.update( s, n, r ) = skt
    retNode = skt;
  }
  else if (t.getKind() == kind::STRING_STRIDOF)
  {
    // processing term:  indexof( x, y, n )
    Node x = t[0];
    Node y = t[1];
    Node n = t[2];
    Node skk = sc->mkTypedSkolemCached(
        nm->integerType(), t, SkolemCache::SK_PURIFY, "iok");

    Node negone = nm->mkConst(Rational(-1));
    Node krange = nm->mkNode(GEQ, skk, negone);
    // assert:   indexof( x, y, n ) >= -1
    asserts.push_back(krange);
    krange = nm->mkNode(GEQ, nm->mkNode(STRING_LENGTH, x), skk);
    // assert:   len( x ) >= indexof( x, y, z )
    asserts.push_back(krange);

    // substr( x, n, len( x ) - n )
    Node st = nm->mkNode(STRING_SUBSTR,
                         x,
                         n,
                         nm->mkNode(MINUS, nm->mkNode(STRING_LENGTH, x), n));
    Node io2 =
        sc->mkSkolemCached(st, y, SkolemCache::SK_FIRST_CTN_PRE, "iopre");
    Node io4 =
        sc->mkSkolemCached(st, y, SkolemCache::SK_FIRST_CTN_POST, "iopost");

    // ~contains( substr( x, n, len( x ) - n ), y )
    Node c11 = nm->mkNode(STRING_STRCTN, st, y).negate();
    // n > len( x )
    Node c12 = nm->mkNode(GT, n, nm->mkNode(STRING_LENGTH, x));
    // 0 > n
    Node c13 = nm->mkNode(GT, zero, n);
    Node cond1 = nm->mkNode(OR, c11, c12, c13);
    // skk = -1
    Node cc1 = skk.eqNode(negone);

    // y = ""
    Node emp = Word::mkEmptyWord(x.getType());
    Node cond2 = y.eqNode(emp);
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
                      zero,
                      nm->mkNode(MINUS, nm->mkNode(STRING_LENGTH, y), one))),
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
    asserts.push_back(rr);

    // Thus, indexof( x, y, n ) = skk.
    retNode = skk;
  }
  else if (t.getKind() == STRING_ITOS)
  {
    // processing term:  int.to.str( n )
    Node n = t[0];
    Node itost = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "itost");
    Node leni = nm->mkNode(STRING_LENGTH, itost);

    std::vector<Node> conc;
    std::vector< TypeNode > argTypes;
    argTypes.push_back(nm->integerType());
    Node u = nm->mkSkolem("U", nm->mkFunctionType(argTypes, nm->integerType()));

    Node lem = nm->mkNode(GEQ, leni, one);
    conc.push_back(lem);

    lem = n.eqNode(nm->mkNode(APPLY_UF, u, leni));
    conc.push_back(lem);

    lem = zero.eqNode(nm->mkNode(APPLY_UF, u, zero));
    conc.push_back(lem);

    Node x = SkolemCache::mkIndexVar(t);
    Node xPlusOne = nm->mkNode(PLUS, x, one);
    Node xbv = nm->mkNode(BOUND_VAR_LIST, x);
    Node g = nm->mkNode(AND, nm->mkNode(GEQ, x, zero), nm->mkNode(LT, x, leni));
    Node sx = nm->mkNode(STRING_SUBSTR, itost, x, one);
    Node ux = nm->mkNode(APPLY_UF, u, x);
    Node ux1 = nm->mkNode(APPLY_UF, u, xPlusOne);
    Node c0 = nm->mkNode(STRING_TO_CODE, nm->mkConst(String("0")));
    Node c = nm->mkNode(MINUS, nm->mkNode(STRING_TO_CODE, sx), c0);

    Node ten = nm->mkConst(Rational(10));
    Node eq = ux1.eqNode(nm->mkNode(PLUS, c, nm->mkNode(MULT, ten, ux)));
    Node leadingZeroPos =
        nm->mkNode(AND, x.eqNode(zero), nm->mkNode(GT, leni, one));
    Node cb = nm->mkNode(
        AND,
        nm->mkNode(GEQ, c, nm->mkNode(ITE, leadingZeroPos, one, zero)),
        nm->mkNode(LT, c, ten));

    Node ux1lem = nm->mkNode(GEQ, n, ux1);

    lem = nm->mkNode(OR, g.negate(), nm->mkNode(AND, eq, cb, ux1lem));
    lem = nm->mkNode(FORALL, xbv, lem);
    conc.push_back(lem);

    Node nonneg = nm->mkNode(GEQ, n, zero);

    Node emp = Word::mkEmptyWord(t.getType());
    lem = nm->mkNode(ITE, nonneg, nm->mkNode(AND, conc), itost.eqNode(emp));
    asserts.push_back(lem);
    // assert:
    // IF n>=0
    // THEN:
    //   len( itost ) >= 1 ^
    //   n = U( len( itost ) ) ^ U( 0 ) = 0 ^
    //   forall x. (x>=0 ^ x < str.len(itost)) =>
    //     U( x+1 ) = (str.code( str.at(itost, x) )-48) + 10*U( x ) ^
    //     ite( x=0 AND str.len(itost)>1, 49, 48 ) <=
    //       str.code( str.at(itost, x) ) < 58 ^
    //     n >= U(x + 1)
    // ELSE
    //   itost = ""
    // thus:
    //   int.to.str( n ) = itost
    //
    // Note: The conjunct `n >= U(x + 1)` is not needed for correctness but is
    // just an optimization.

    // The function U is an accumulator, where U( x ) for x>0 is the value of
    // str.to.int( str.substr( int.to.str( n ), 0, x ) ). For example, for
    // n=345, we have that U(1), U(2), U(3) = 3, 34, 345.
    // Above, we use str.code to map characters to their integer value, where
    // note that str.code( "0" ) = 48. Further notice that
    //   ite( x=0 AND str.len(itost)>1, 49, 48 )
    // enforces that int.to.str( n ) has no leading zeroes.
    retNode = itost;
  } else if( t.getKind() == kind::STRING_STOI ) {
    Node s = t[0];
    Node stoit = sc->mkTypedSkolemCached(
        nm->integerType(), t, SkolemCache::SK_PURIFY, "stoit");
    Node lens = nm->mkNode(STRING_LENGTH, s);

    std::vector<Node> conc1;
    Node lem = stoit.eqNode(negOne);
    conc1.push_back(lem);

    Node emp = Word::mkEmptyWord(s.getType());
    Node sEmpty = s.eqNode(emp);
    Node k = nm->mkSkolem("k", nm->integerType());
    Node kc1 = nm->mkNode(GEQ, k, zero);
    Node kc2 = nm->mkNode(LT, k, lens);
    Node c0 = nm->mkNode(STRING_TO_CODE, nm->mkConst(String("0")));
    Node codeSk = nm->mkNode(
        MINUS,
        nm->mkNode(STRING_TO_CODE, nm->mkNode(STRING_SUBSTR, s, k, one)),
        c0);
    Node ten = nm->mkConst(Rational(10));
    Node kc3 = nm->mkNode(
        OR, nm->mkNode(LT, codeSk, zero), nm->mkNode(GEQ, codeSk, ten));
    conc1.push_back(nm->mkNode(OR, sEmpty, nm->mkNode(AND, kc1, kc2, kc3)));

    std::vector<Node> conc2;
    std::vector< TypeNode > argTypes;
    argTypes.push_back(nm->integerType());
    Node u = nm->mkSkolem("U", nm->mkFunctionType(argTypes, nm->integerType()));

    lem = stoit.eqNode(nm->mkNode(APPLY_UF, u, lens));
    conc2.push_back(lem);

    lem = zero.eqNode(nm->mkNode(APPLY_UF, u, zero));
    conc2.push_back(lem);

    lem = nm->mkNode(GT, lens, zero);
    conc2.push_back(lem);

    Node x = SkolemCache::mkIndexVar(t);
    Node xbv = nm->mkNode(BOUND_VAR_LIST, x);
    Node g = nm->mkNode(AND, nm->mkNode(GEQ, x, zero), nm->mkNode(LT, x, lens));
    Node sx = nm->mkNode(STRING_SUBSTR, s, x, one);
    Node ux = nm->mkNode(APPLY_UF, u, x);
    Node ux1 = nm->mkNode(APPLY_UF, u, nm->mkNode(PLUS, x, one));
    Node c = nm->mkNode(MINUS, nm->mkNode(STRING_TO_CODE, sx), c0);

    Node eq = ux1.eqNode(nm->mkNode(PLUS, c, nm->mkNode(MULT, ten, ux)));
    Node cb = nm->mkNode(AND, nm->mkNode(GEQ, c, zero), nm->mkNode(LT, c, ten));

    Node ux1lem = nm->mkNode(GEQ, stoit, ux1);

    lem = nm->mkNode(OR, g.negate(), nm->mkNode(AND, eq, cb, ux1lem));
    lem = nm->mkNode(FORALL, xbv, lem);
    conc2.push_back(lem);

    Node sneg = nm->mkNode(LT, stoit, zero);
    lem = nm->mkNode(ITE, sneg, nm->mkNode(AND, conc1), nm->mkNode(AND, conc2));
    asserts.push_back(lem);

    // assert:
    // IF stoit < 0
    // THEN:
    //   stoit = -1 ^
    //   ( s = "" OR
    //     ( k>=0 ^ k<len( s ) ^ ( str.code( str.at(s, k) ) < 48 OR
    //                             str.code( str.at(s, k) ) >= 58 )))
    // ELSE:
    //   stoit = U( len( s ) ) ^ U( 0 ) = 0 ^
    //   str.len( s ) > 0 ^
    //   forall x. (x>=0 ^ x < str.len(s)) =>
    //     U( x+1 ) = ( str.code( str.at(s, x) ) - 48 ) + 10*U( x ) ^
    //     48 <= str.code( str.at(s, x) ) < 58 ^
    //     stoit >= U( x+1 )
    // Thus, str.to.int( s ) = stoit
    //
    // Note: The conjunct `stoit >= U( x+1 )` is not needed for correctness but
    // is just an optimization.

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
        sc->mkSkolemCached(x, y, SkolemCache::SK_FIRST_CTN_PRE, "rfcpre");
    Node rp2 =
        sc->mkSkolemCached(x, y, SkolemCache::SK_FIRST_CTN_POST, "rfcpost");
    Node rpw = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "rpw");

    // y = ""
    Node emp = Word::mkEmptyWord(tn);
    Node cond1 = y.eqNode(emp);
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
                                  zero,
                                  nm->mkNode(kind::MINUS,
                                             nm->mkNode(kind::STRING_LENGTH, y),
                                             one))),
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
    asserts.push_back(rr);

    // Thus, replace( x, y, z ) = rpw.
    retNode = rpw;
  }
  else if (t.getKind() == kind::STRING_STRREPLALL)
  {
    // processing term: replaceall( x, y, z )
    Node x = t[0];
    Node y = t[1];
    Node z = t[2];
    Node rpaw = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "rpaw");

    Node numOcc = sc->mkTypedSkolemCached(
        nm->integerType(), x, y, SkolemCache::SK_NUM_OCCUR, "numOcc");
    std::vector<TypeNode> argTypes;
    argTypes.push_back(nm->integerType());
    Node us =
        nm->mkSkolem("Us", nm->mkFunctionType(argTypes, nm->stringType()));
    TypeNode ufType = nm->mkFunctionType(argTypes, nm->integerType());
    Node uf = sc->mkTypedSkolemCached(
        ufType, x, y, SkolemCache::SK_OCCUR_INDEX, "Uf");

    Node ufno = nm->mkNode(APPLY_UF, uf, numOcc);
    Node usno = nm->mkNode(APPLY_UF, us, numOcc);
    Node rem = nm->mkNode(STRING_SUBSTR, x, ufno, nm->mkNode(STRING_LENGTH, x));

    std::vector<Node> lem;
    lem.push_back(nm->mkNode(GEQ, numOcc, zero));
    lem.push_back(rpaw.eqNode(nm->mkNode(APPLY_UF, us, zero)));
    lem.push_back(usno.eqNode(rem));
    lem.push_back(nm->mkNode(APPLY_UF, uf, zero).eqNode(zero));
    lem.push_back(nm->mkNode(STRING_STRIDOF, x, y, ufno).eqNode(negOne));

    Node i = SkolemCache::mkIndexVar(t);
    Node bvli = nm->mkNode(BOUND_VAR_LIST, i);
    Node bound =
        nm->mkNode(AND, nm->mkNode(GEQ, i, zero), nm->mkNode(LT, i, numOcc));
    Node ufi = nm->mkNode(APPLY_UF, uf, i);
    Node ufip1 = nm->mkNode(APPLY_UF, uf, nm->mkNode(PLUS, i, one));
    Node ii = nm->mkNode(STRING_STRIDOF, x, y, ufi);
    Node cc = nm->mkNode(
        STRING_CONCAT,
        nm->mkNode(STRING_SUBSTR, x, ufi, nm->mkNode(MINUS, ii, ufi)),
        z,
        nm->mkNode(APPLY_UF, us, nm->mkNode(PLUS, i, one)));

    std::vector<Node> flem;
    flem.push_back(ii.eqNode(negOne).negate());
    flem.push_back(nm->mkNode(APPLY_UF, us, i).eqNode(cc));
    flem.push_back(
        ufip1.eqNode(nm->mkNode(PLUS, ii, nm->mkNode(STRING_LENGTH, y))));

    Node q = nm->mkNode(
        FORALL, bvli, nm->mkNode(OR, bound.negate(), nm->mkNode(AND, flem)));
    lem.push_back(q);

    // assert:
    //   IF y=""
    //   THEN: rpaw = x
    //   ELSE:
    //     numOcc >= 0 ^
    //     rpaw = Us(0) ^ Us(numOcc) = substr(x, Uf(numOcc), len(x)) ^
    //     Uf(0) = 0 ^ indexof( x, y, Uf(numOcc) ) = -1 ^
    //     forall i. 0 <= i < numOcc =>
    //        ii != -1 ^
    //        Us( i ) = str.substr( x, Uf(i), ii - Uf(i) ) ++ z ++ Us(i+1) ^
    //        Uf( i+1 ) = ii + len(y)
    //        where ii == indexof( x, y, Uf(i) )

    // Conceptually, numOcc is the number of occurrences of y in x, Uf( i ) is
    // the index to begin searching in x for y after the i^th occurrence of y in
    // x, and Us( i ) is the result of processing the remainder after processing
    // the i^th occurrence of y in x.
    Node emp = Word::mkEmptyWord(t.getType());
    Node assert =
        nm->mkNode(ITE, y.eqNode(emp), rpaw.eqNode(x), nm->mkNode(AND, lem));
    asserts.push_back(assert);

    // Thus, replaceall( x, y, z ) = rpaw
    retNode = rpaw;
  }
  else if (t.getKind() == STRING_REPLACE_RE)
  {
    Node x = t[0];
    Node y = t[1];
    Node z = t[2];
    Node k = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "k");

    std::vector<Node> emptyVec;
    Node sigmaStar =
        nm->mkNode(REGEXP_STAR, nm->mkNode(REGEXP_SIGMA, emptyVec));
    Node re = nm->mkNode(REGEXP_CONCAT, sigmaStar, y, sigmaStar);
    // in_re(x, re.++(_*, y, _*))
    Node hasMatch = nm->mkNode(STRING_IN_REGEXP, x, re);

    // in_re("", y)
    Node matchesEmpty =
        nm->mkNode(STRING_IN_REGEXP, nm->mkConst(String("")), y);
    // k = z ++ x
    Node res1 = k.eqNode(nm->mkNode(STRING_CONCAT, z, x));

    Node k1 =
        sc->mkSkolemCached(x, y, SkolemCache::SK_FIRST_MATCH_PRE, "rre_pre");
    Node k2 =
        sc->mkSkolemCached(x, y, SkolemCache::SK_FIRST_MATCH, "rre_match");
    Node k3 =
        sc->mkSkolemCached(x, y, SkolemCache::SK_FIRST_MATCH_POST, "rre_post");
    // x = k1 ++ k2 ++ k3
    Node splitX = x.eqNode(nm->mkNode(STRING_CONCAT, k1, k2, k3));
    // ~in_re(k1 ++ str.substr(k2, 0, str.len(k2) - 1), re.++(_*, y, _*))
    Node k2len = nm->mkNode(STRING_LENGTH, k2);
    Node firstMatch =
        nm->mkNode(
              STRING_IN_REGEXP,
              nm->mkNode(
                  STRING_CONCAT,
                  k1,
                  nm->mkNode(
                      STRING_SUBSTR, k2, zero, nm->mkNode(MINUS, k2len, one))),
              re)
            .negate();
    // in_re(k2, y)
    Node k2Match = nm->mkNode(STRING_IN_REGEXP, k2, y);
    // k = k1 ++ z ++ k3
    Node res2 = k.eqNode(nm->mkNode(STRING_CONCAT, k1, z, k3));

    // IF in_re(x, re.++(_*, y, _*))
    // THEN:
    //   IF in_re("", y)
    //   THEN: k = z ++ x
    //   ELSE:
    //     x = k1 ++ k2 ++ k3 ^
    //     ~in_re(k1 ++ substr(k2, 0, str.len(k2) - 1), re.++(_*, y, _*)) ^
    //     in_re(k2, y) ^ k = k1 ++ z ++ k3
    // ELSE: k = x
    asserts.push_back(nm->mkNode(
        ITE,
        hasMatch,
        nm->mkNode(ITE,
                   matchesEmpty,
                   res1,
                   nm->mkNode(AND, splitX, firstMatch, k2Match, res2)),
        k.eqNode(x)));
    retNode = k;
  }
  else if (t.getKind() == STRING_REPLACE_RE_ALL)
  {
    Node x = t[0];
    Node y = t[1];
    Node z = t[2];
    Node k = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "k");

    Node numOcc = sc->mkTypedSkolemCached(
        nm->integerType(), x, y, SkolemCache::SK_NUM_OCCUR, "numOcc");
    std::vector<TypeNode> argTypes;
    argTypes.push_back(nm->integerType());
    Node us = nm->mkSkolem("Us", nm->mkFunctionType(argTypes, t.getType()));
    TypeNode ufType = nm->mkFunctionType(argTypes, nm->integerType());
    Node uf = sc->mkTypedSkolemCached(
        ufType, x, y, SkolemCache::SK_OCCUR_INDEX, "Uf");
    Node ul =
        sc->mkTypedSkolemCached(ufType, x, y, SkolemCache::SK_OCCUR_LEN, "Ul");

    Node emp = Word::mkEmptyWord(t.getType());

    std::vector<Node> emptyVec;
    Node sigmaStar =
        nm->mkNode(REGEXP_STAR, nm->mkNode(REGEXP_SIGMA, emptyVec));
    Node yp = nm->mkNode(REGEXP_DIFF, y, nm->mkNode(STRING_TO_REGEXP, emp));
    Node re = nm->mkNode(REGEXP_CONCAT, sigmaStar, yp, sigmaStar);
    // in_re(x, _* ++ y' ++ _*)
    Node hasMatch = nm->mkNode(STRING_IN_REGEXP, x, re);

    Node ufno = nm->mkNode(APPLY_UF, uf, numOcc);
    Node usno = nm->mkNode(APPLY_UF, us, numOcc);
    Node rem = nm->mkNode(STRING_SUBSTR, x, ufno, nm->mkNode(STRING_LENGTH, x));

    std::vector<Node> lemmas;
    // numOcc > 0
    lemmas.push_back(nm->mkNode(GT, numOcc, zero));
    // k = Us(0)
    lemmas.push_back(k.eqNode(nm->mkNode(APPLY_UF, us, zero)));
    // Us(numOcc) = substr(x, Uf(numOcc))
    lemmas.push_back(usno.eqNode(rem));
    // Uf(0) = 0
    lemmas.push_back(nm->mkNode(APPLY_UF, uf, zero).eqNode(zero));
    // not(in_re(substr(x, Uf(numOcc)), re.++(_*, y', _*)))
    lemmas.push_back(nm->mkNode(STRING_IN_REGEXP, rem, re).negate());

    Node i = SkolemCache::mkIndexVar(t);
    Node bvli = nm->mkNode(BOUND_VAR_LIST, i);
    Node bound =
        nm->mkNode(AND, nm->mkNode(GEQ, i, zero), nm->mkNode(LT, i, numOcc));
    Node ip1 = nm->mkNode(PLUS, i, one);
    Node ufi = nm->mkNode(APPLY_UF, uf, i);
    Node uli = nm->mkNode(APPLY_UF, ul, i);
    Node ufip1 = nm->mkNode(APPLY_UF, uf, ip1);
    Node ii = nm->mkNode(MINUS, ufip1, uli);
    Node match = nm->mkNode(STRING_SUBSTR, x, ii, uli);
    Node pfxMatch =
        nm->mkNode(STRING_SUBSTR, x, ufi, nm->mkNode(MINUS, ii, ufi));
    Node nonMatch =
        nm->mkNode(STRING_SUBSTR,
                   x,
                   ufi,
                   nm->mkNode(MINUS, nm->mkNode(MINUS, ufip1, one), ufi));

    std::vector<Node> flem;
    // Ul(i) > 0
    flem.push_back(nm->mkNode(GT, uli, zero));
    // Uf(i + 1) >= Uf(i) + Ul(i)
    flem.push_back(nm->mkNode(GEQ, ufip1, nm->mkNode(PLUS, ufi, uli)));
    // in_re(substr(x, ii, Ul(i)), y')
    flem.push_back(nm->mkNode(STRING_IN_REGEXP, match, yp));
    // ~in_re(substr(x, Uf(i), Uf(i + 1) - 1 - Uf(i)), re.++(_*, y', _*))
    flem.push_back(nm->mkNode(STRING_IN_REGEXP, nonMatch, re).negate());
    // Us(i) = substr(x, Uf(i), ii - Uf(i)) ++ z ++ Us(i + 1)
    flem.push_back(
        nm->mkNode(APPLY_UF, us, i)
            .eqNode(nm->mkNode(
                STRING_CONCAT, pfxMatch, z, nm->mkNode(APPLY_UF, us, ip1))));

    Node forall = nm->mkNode(
        FORALL, bvli, nm->mkNode(OR, bound.negate(), nm->mkNode(AND, flem)));
    lemmas.push_back(forall);

    // IF in_re(x, re.++(_*, y', _*))
    // THEN:
    //   numOcc > 0 ^
    //   k = Us(0) ^ Us(numOcc) = substr(x, Uf(numOcc)) ^
    //   Uf(0) = 0 ^ not(in_re(substr(x, Uf(numOcc)), re.++(_*, y', _*)))
    //   forall i. 0 <= i < nummOcc =>
    //     Ul(i) > 0 ^
    //     Uf(i + 1) >= Uf(i) + Ul(i) ^
    //     in_re(substr(x, ii, Ul(i)), y') ^
    //     ~in_re(substr(x, Uf(i), Uf(i + 1) - 1 - Uf(i)), re.++(_*, y', _*)) ^
    //     Us(i) = substr(x, Uf(i), ii - Uf(i)) ++ z ++ Us(i + 1)
    //     where ii = Uf(i + 1) - Ul(i)
    // ELSE: k = x
    // where y' = re.diff(y, "")
    //
    // Conceptually, y' is the regex y but excluding the empty string (because
    // we do not want to match empty strings), numOcc is the number of shortest
    // matches of y' in x, Uf(i) is the end position of the i-th match, Ul(i)
    // is the length of the i^th match, and Us(i) is the result of processing
    // the remainder after processing the i^th occurrence of y in x.
    asserts.push_back(
        nm->mkNode(ITE, hasMatch, nm->mkNode(AND, lemmas), k.eqNode(x)));
    retNode = k;
  }
  else if (t.getKind() == STRING_TOLOWER || t.getKind() == STRING_TOUPPER)
  {
    Node x = t[0];
    Node r = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "r");

    Node lenx = nm->mkNode(STRING_LENGTH, x);
    Node lenr = nm->mkNode(STRING_LENGTH, r);
    Node eqLenA = lenx.eqNode(lenr);

    Node i = SkolemCache::mkIndexVar(t);
    Node bvi = nm->mkNode(BOUND_VAR_LIST, i);

    Node ci = nm->mkNode(STRING_TO_CODE, nm->mkNode(STRING_SUBSTR, x, i, one));
    Node ri = nm->mkNode(STRING_TO_CODE, nm->mkNode(STRING_SUBSTR, r, i, one));

    Node lb = nm->mkConst(Rational(t.getKind() == STRING_TOUPPER ? 97 : 65));
    Node ub = nm->mkConst(Rational(t.getKind() == STRING_TOUPPER ? 122 : 90));
    Node offset =
        nm->mkConst(Rational(t.getKind() == STRING_TOUPPER ? -32 : 32));

    Node res = nm->mkNode(
        ITE,
        nm->mkNode(AND, nm->mkNode(LEQ, lb, ci), nm->mkNode(LEQ, ci, ub)),
        nm->mkNode(PLUS, ci, offset),
        ci);

    Node bound =
        nm->mkNode(AND, nm->mkNode(LEQ, zero, i), nm->mkNode(LT, i, lenr));
    Node rangeA =
        nm->mkNode(FORALL, bvi, nm->mkNode(OR, bound.negate(), ri.eqNode(res)));

    // upper 65 ... 90
    // lower 97 ... 122
    // assert:
    //   len(r) = len(x) ^
    //   forall i. 0 <= i < len(r) =>
    //     str.code( str.substr(r,i,1) ) = ite( 97 <= ci <= 122, ci-32, ci)
    // where ci = str.code( str.substr(x,i,1) )
    Node assert = nm->mkNode(AND, eqLenA, rangeA);
    asserts.push_back(assert);

    // Thus, toLower( x ) = r
    retNode = r;
  }
  else if (t.getKind() == STRING_REV)
  {
    Node x = t[0];
    Node r = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "r");

    Node lenx = nm->mkNode(STRING_LENGTH, x);
    Node lenr = nm->mkNode(STRING_LENGTH, r);
    Node eqLenA = lenx.eqNode(lenr);

    Node i = SkolemCache::mkIndexVar(t);
    Node bvi = nm->mkNode(BOUND_VAR_LIST, i);

    Node revi = nm->mkNode(
        MINUS, nm->mkNode(STRING_LENGTH, x), nm->mkNode(PLUS, i, one));
    Node ssr = nm->mkNode(STRING_SUBSTR, r, i, one);
    Node ssx = nm->mkNode(STRING_SUBSTR, x, revi, one);

    Node bound =
        nm->mkNode(AND, nm->mkNode(LEQ, zero, i), nm->mkNode(LT, i, lenr));
    Node rangeA = nm->mkNode(
        FORALL, bvi, nm->mkNode(OR, bound.negate(), ssr.eqNode(ssx)));
    // assert:
    //   len(r) = len(x) ^
    //   forall i. 0 <= i < len(r) =>
    //     substr(r,i,1) = substr(x,len(x)-(i+1),1)
    Node assert = nm->mkNode(AND, eqLenA, rangeA);
    asserts.push_back(assert);

    // Thus, (str.rev x) = r
    retNode = r;
  }
  else if (t.getKind() == kind::STRING_STRCTN)
  {
    Node x = t[0];
    Node s = t[1];
    //negative contains reduces to existential
    Node lenx = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, x);
    Node lens = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s);
    Node b1 = SkolemCache::mkIndexVar(t);
    Node b1v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b1);
    Node body = NodeManager::currentNM()->mkNode(
        kind::AND,
        NodeManager::currentNM()->mkNode(kind::LEQ, zero, b1),
        NodeManager::currentNM()->mkNode(
            kind::LEQ,
            b1,
            NodeManager::currentNM()->mkNode(kind::MINUS, lenx, lens)),
        NodeManager::currentNM()->mkNode(
            kind::EQUAL,
            NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, x, b1, lens),
            s));
    retNode = NodeManager::currentNM()->mkNode( kind::EXISTS, b1v, body );
  }
  else if (t.getKind() == kind::STRING_LEQ)
  {
    Node ltp = sc->mkTypedSkolemCached(
        nm->booleanType(), t, SkolemCache::SK_PURIFY, "ltp");
    Node k = nm->mkSkolem("k", nm->integerType());

    std::vector<Node> conj;
    conj.push_back(nm->mkNode(GEQ, k, zero));
    Node substr[2];
    Node code[2];
    for (unsigned r = 0; r < 2; r++)
    {
      Node ta = t[r];
      Node tb = t[1 - r];
      substr[r] = nm->mkNode(STRING_SUBSTR, ta, zero, k);
      code[r] =
          nm->mkNode(STRING_TO_CODE, nm->mkNode(STRING_SUBSTR, ta, k, one));
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
    asserts.push_back(assert);

    // Thus, str.<=( x, y ) = ltp
    retNode = ltp;
  }
  return retNode;
}

Node StringsPreprocess::simplify(Node t, std::vector<Node>& asserts)
{
  size_t prev_asserts = asserts.size();
  // call the static reduce routine
  Node retNode = reduce(t, asserts, d_sc);
  if( t!=retNode ){
    Trace("strings-preprocess") << "StringsPreprocess::simplify: " << t << " -> " << retNode << std::endl;
    if (!asserts.empty())
    {
      Trace("strings-preprocess")
          << " ... new nodes (" << (asserts.size() - prev_asserts)
          << "):" << std::endl;
      for (size_t i = prev_asserts; i < asserts.size(); ++i)
      {
        Trace("strings-preprocess") << "   " << asserts[i] << std::endl;
      }
    }
    d_statistics.d_reductions << t.getKind();
  }
  else
  {
    Trace("strings-preprocess-debug")
        << "Return " << retNode << " unchanged" << std::endl;
  }
  return retNode;
}

Node StringsPreprocess::simplifyRec(Node t,
                                    std::vector<Node>& asserts,
                                    std::map<Node, Node>& visited)
{
  std::map< Node, Node >::iterator it = visited.find(t);
  if( it!=visited.end() ){
    return it->second;
  }else{
    Node retNode = t;
    if( t.getNumChildren()==0 ){
      retNode = simplify(t, asserts);
    }else if( t.getKind()!=kind::FORALL ){
      bool changed = false;
      std::vector< Node > cc;
      if( t.getMetaKind() == kind::metakind::PARAMETERIZED ){
        cc.push_back( t.getOperator() );
      }
      for(unsigned i=0; i<t.getNumChildren(); i++) {
        Node s = simplifyRec(t[i], asserts, visited);
        cc.push_back( s );
        if( s!=t[i] ) {
          changed = true;
        }
      }
      Node tmp = t;
      if( changed ){
        tmp = NodeManager::currentNM()->mkNode( t.getKind(), cc );
      }
      retNode = simplify(tmp, asserts);
    }
    visited[t] = retNode;
    return retNode;
  }
}

Node StringsPreprocess::processAssertion(Node n, std::vector<Node>& asserts)
{
  std::map< Node, Node > visited;
  std::vector<Node> asserts_curr;
  Node ret = simplifyRec(n, asserts_curr, visited);
  while (!asserts_curr.empty())
  {
    Node curr = asserts_curr.back();
    asserts_curr.pop_back();
    std::vector<Node> asserts_tmp;
    curr = simplifyRec(curr, asserts_tmp, visited);
    asserts_curr.insert(
        asserts_curr.end(), asserts_tmp.begin(), asserts_tmp.end());
    asserts.push_back(curr);
  }
  return ret;
}

void StringsPreprocess::processAssertions( std::vector< Node > &vec_node ){
  std::map< Node, Node > visited;
  for( unsigned i=0; i<vec_node.size(); i++ ){
    Trace("strings-preprocess-debug") << "Preprocessing assertion " << vec_node[i] << std::endl;
    //preprocess until fixed point
    std::vector<Node> asserts;
    std::vector<Node> asserts_curr;
    asserts_curr.push_back(vec_node[i]);
    while (!asserts_curr.empty())
    {
      Node curr = asserts_curr.back();
      asserts_curr.pop_back();
      std::vector<Node> asserts_tmp;
      curr = simplifyRec(curr, asserts_tmp, visited);
      asserts_curr.insert(
          asserts_curr.end(), asserts_tmp.begin(), asserts_tmp.end());
      asserts.push_back(curr);
    }
    Node res = asserts.size() == 1
                   ? asserts[0]
                   : NodeManager::currentNM()->mkNode(kind::AND, asserts);
    if( res!=vec_node[i] ){
      res = Rewriter::rewrite( res );
      if (options::unsatCores())
      {
        ProofManager::currentPM()->addDependence(res, vec_node[i]);
      }
      vec_node[i] = res;
    }
  }
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Strings Preprocess.
 */

#include "theory/strings/theory_strings_preprocess.h"

#include "expr/kind.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "smt/logic_exception.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/sequences_rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"
#include "util/statistics_registry.h"
#include "util/string.h"

using namespace cvc5::internal;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

StringsPreprocess::StringsPreprocess(Env& env,
                                     SkolemCache* sc,
                                     HistogramStat<Kind>* statReductions)
    : EnvObj(env), d_sc(sc), d_statReductions(statReductions)
{
}

StringsPreprocess::~StringsPreprocess(){

}

Node StringsPreprocess::reduce(Node t,
                               std::vector<Node>& asserts,
                               SkolemCache* sc,
                               size_t alphaCard)
{
  Trace("strings-preprocess-debug")
      << "StringsPreprocess::reduce: " << t << std::endl;
  Node retNode = t;
  NodeManager* nm = NodeManager::currentNM();
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));
  Node negOne = nm->mkConstInt(Rational(-1));

  if( t.getKind() == kind::STRING_SUBSTR ) {
    // processing term:  substr( s, n, m )
    Node s = t[0];
    Node n = t[1];
    Node m = t[2];
    Node skt = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "sst");
    Node t12 = nm->mkNode(ADD, n, m);
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
        nm->mkNode(EQUAL, lsk2, nm->mkNode(SUB, lt0, nm->mkNode(ADD, n, m))),
        nm->mkNode(EQUAL, lsk2, zero));
    // Length of the result is at most m
    Node b14 = nm->mkNode(LEQ, nm->mkNode(STRING_LENGTH, skt), m);

    Node b1 = nm->mkNode(AND, {b11, b12, b13, b14});
    Node b2 = skt.eqNode(emp);
    Node lemma = nm->mkNode(ITE, cond, b1, b2);

    // assert:
    // IF    n >=0 AND len( s ) > n AND m > 0
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
      rs = nm->mkNode(STRING_SUBSTR, r, zero, nm->mkNode(SUB, lens, n));
    }
    Node rslen = nm->mkNode(STRING_LENGTH, rs);
    Node nsuf = nm->mkNode(ADD, n, rslen);
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
    Node a4 = nm->mkNode(STRING_LENGTH, rs).eqNode(nm->mkNode(STRING_LENGTH, sk3));

    Node b1 = nm->mkNode(AND, {a1, a2, a3, a4});
    Node b2 = skt.eqNode(s);
    Node lemma = nm->mkNode(ITE, cond, b1, b2);

    // assert:
    // IF    n >=0 AND n < len( s )
    // THEN: skt = sk1 ++ substr(r,0,len(s)-n) ++ sk2 AND
    //       s = sk1 ++ sk3 ++ sk2 AND
    //       len( sk1 ) = n AND
    //       len( substr(r,0,len(s)-n) ) = len( sk3 )
    // ELSE: skt = s
    // We use an optimization where r is used instead of substr(r,0,len(s)-n)
    // if r is a constant of length one.
    asserts.push_back(lemma);

    // Thus, str.update( s, n, r ) = skt
    retNode = skt;
  }
  else if (t.getKind() == kind::STRING_INDEXOF)
  {
    // processing term:  indexof( x, y, n )
    Node x = t[0];
    Node y = t[1];
    Node n = t[2];
    Node skk = sc->mkTypedSkolemCached(
        nm->integerType(), t, SkolemCache::SK_PURIFY, "iok");

    Node negone = nm->mkConstInt(Rational(-1));

    // substr( x, n, len( x ) - n )
    Node st = nm->mkNode(
        STRING_SUBSTR, x, n, nm->mkNode(SUB, nm->mkNode(STRING_LENGTH, x), n));
    Node io2 =
        sc->mkSkolemCached(st, y, SkolemCache::SK_FIRST_CTN_PRE, "iopre");
    Node io4 =
        sc->mkSkolemCached(st, y, SkolemCache::SK_FIRST_CTN_POST, "iopost");

    // ~contains( substr( x, n, len( x ) - n ), y )
    Node c11 = nm->mkNode(STRING_CONTAINS, st, y).negate();
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
        nm->mkNode(STRING_CONTAINS,
                   nm->mkNode(
                       STRING_CONCAT,
                       io2,
                       nm->mkNode(
                           STRING_SUBSTR,
                           y,
                           zero,
                           nm->mkNode(SUB, nm->mkNode(STRING_LENGTH, y), one))),
                   y)
            .negate();
    // skk = n + len( io2 )
    Node c33 = skk.eqNode(nm->mkNode(ADD, n, nm->mkNode(STRING_LENGTH, io2)));
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
  else if (t.getKind() == kind::STRING_INDEXOF_RE)
  {
    // processing term:  indexof_re(s, r, n)
    Node s = t[0];
    Node r = t[1];
    Node n = t[2];
    Node skk = sc->mkTypedSkolemCached(
        nm->integerType(), t, SkolemCache::SK_PURIFY, "iork");
    Node sLen = nm->mkNode(STRING_LENGTH, s);

    // n > len(x)
    Node ub = nm->mkNode(GT, n, sLen);
    // 0 > n
    Node lb = nm->mkNode(GT, zero, n);
    // n > len(x) OR 0 > n
    Node condNegOne = nm->mkNode(OR, ub, lb);
    // skk = -1
    Node retNegOne = skk.eqNode(negOne);

    Node emp = Word::mkEmptyWord(s.getType());
    // in_re("", r)
    Node matchEmptyStr = nm->mkNode(STRING_IN_REGEXP, emp, r);
    // skk = n
    Node retN = skk.eqNode(n);

    Node i = SkolemCache::mkIndexVar(t);
    Node l = SkolemCache::mkLengthVar(t);
    Node bvl = nm->mkNode(BOUND_VAR_LIST, i, l);
    Node bound =
        nm->mkNode(AND,
                   {
                       nm->mkNode(GEQ, i, n),
                       nm->mkNode(LT, i, nm->mkNode(ITE, retNegOne, sLen, skk)),
                       nm->mkNode(GT, l, zero),
                       nm->mkNode(LEQ, l, nm->mkNode(SUB, sLen, i)),
                   });
    Node body = nm->mkNode(
        OR,
        bound.negate(),
        nm->mkNode(STRING_IN_REGEXP, nm->mkNode(STRING_SUBSTR, s, i, l), r)
            .negate());
    // forall il.
    //   n <= i < ite(skk = -1, len(s), skk) ^ 0 < l <= len(s) - i =>
    //     ~in_re(substr(s, i, l), r)
    Node firstMatch = utils::mkForallInternal(bvl, body);
    Node bvll = nm->mkNode(BOUND_VAR_LIST, l);
    Node validLen = nm->mkNode(AND,
                               nm->mkNode(GEQ, l, zero),
                               nm->mkNode(LEQ, l, nm->mkNode(SUB, sLen, skk)));
    Node matchBody = nm->mkNode(
        AND,
        validLen,
        nm->mkNode(STRING_IN_REGEXP, nm->mkNode(STRING_SUBSTR, s, skk, l), r));
    // skk != -1 =>
    //   skk >= n ^ exists l. (0 <= l < len(s) - skk) ^ in_re(substr(s, skk, l),
    //   r))
    Node match = nm->mkNode(
        OR,
        retNegOne,
        nm->mkNode(AND,
                   nm->mkNode(GEQ, skk, n),
                   utils::mkForallInternal(bvll, matchBody.negate()).negate()));

    // assert:
    // IF:   n > len(s) OR 0 > n
    // THEN: skk = -1
    // ELIF: in_re("", r)
    // THEN: skk = n
    // ELSE: (forall il.
    //         n <= i < ite(skk = -1, len(s), skk) ^ 0 < l <= len(s) - i =>
    //           ~in_re(substr(s, i, l), r)) ^
    //       (skk != -1 =>
    //          skk >= n ^ exists l. 0 <= l <= len(s) - skk ^ in_re(substr(s,
    //          skk, l), r))
    //
    // Note that this reduction relies on eager reduction lemmas being sent to
    // properly limit the range of skk.
    Node rr = nm->mkNode(
        ITE,
        condNegOne,
        retNegOne,
        nm->mkNode(
            ITE, matchEmptyStr, retN, nm->mkNode(AND, firstMatch, match)));
    asserts.push_back(rr);

    // Thus, indexof_re(s, r, n) = skk.
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
    TypeNode itosResType = nm->mkFunctionType(argTypes, nm->integerType());
    Node u = sc->mkSkolemFun(SkolemFunId::STRINGS_ITOS_RESULT, itosResType, t);

    Node lem = nm->mkNode(GEQ, leni, one);
    conc.push_back(lem);

    lem = n.eqNode(nm->mkNode(APPLY_UF, u, leni));
    conc.push_back(lem);

    lem = zero.eqNode(nm->mkNode(APPLY_UF, u, zero));
    conc.push_back(lem);

    Node x = SkolemCache::mkIndexVar(t);
    Node xPlusOne = nm->mkNode(ADD, x, one);
    Node xbv = nm->mkNode(BOUND_VAR_LIST, x);
    Node g = nm->mkNode(AND, nm->mkNode(GEQ, x, zero), nm->mkNode(LT, x, leni));
    Node ux = nm->mkNode(APPLY_UF, u, x);
    Node ux1 = nm->mkNode(APPLY_UF, u, xPlusOne);
    Node c0 = nm->mkNode(STRING_TO_CODE, nm->mkConst(String("0")));
    Node c = nm->mkNode(SUB, mkCodePointAtIndex(itost, x), c0);

    Node ten = nm->mkConstInt(Rational(10));
    Node eq = ux1.eqNode(nm->mkNode(ADD, c, nm->mkNode(MULT, ten, ux)));
    Node leadingZeroPos =
        nm->mkNode(AND, x.eqNode(zero), nm->mkNode(GT, leni, one));
    Node cb = nm->mkNode(
        AND,
        nm->mkNode(GEQ, c, nm->mkNode(ITE, leadingZeroPos, one, zero)),
        nm->mkNode(LT, c, ten));

    Node ux1lem = nm->mkNode(GEQ, n, ux1);

    lem = nm->mkNode(OR, g.negate(), nm->mkNode(AND, eq, cb, ux1lem));
    lem = utils::mkForallInternal(xbv, lem);
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
    Node k = sc->mkSkolemFun(
        SkolemFunId::STRINGS_STOI_NON_DIGIT, nm->integerType(), t);
    Node kc1 = nm->mkNode(GEQ, k, zero);
    Node kc2 = nm->mkNode(LT, k, lens);
    Node c0 = nm->mkNode(STRING_TO_CODE, nm->mkConst(String("0")));
    Node codeSk = nm->mkNode(SUB, mkCodePointAtIndex(s, k), c0);
    Node ten = nm->mkConstInt(Rational(10));
    Node kc3 = nm->mkNode(
        OR, nm->mkNode(LT, codeSk, zero), nm->mkNode(GEQ, codeSk, ten));
    conc1.push_back(nm->mkNode(OR, sEmpty, nm->mkNode(AND, kc1, kc2, kc3)));

    std::vector<Node> conc2;
    std::vector< TypeNode > argTypes;
    argTypes.push_back(nm->integerType());
    TypeNode stoiResultType = nm->mkFunctionType(argTypes, nm->integerType());
    Node u =
        sc->mkSkolemFun(SkolemFunId::STRINGS_STOI_RESULT, stoiResultType, t);

    lem = stoit.eqNode(nm->mkNode(APPLY_UF, u, lens));
    conc2.push_back(lem);

    lem = zero.eqNode(nm->mkNode(APPLY_UF, u, zero));
    conc2.push_back(lem);

    lem = nm->mkNode(GT, lens, zero);
    conc2.push_back(lem);

    Node x = SkolemCache::mkIndexVar(t);
    Node xbv = nm->mkNode(BOUND_VAR_LIST, x);
    Node g = nm->mkNode(AND, nm->mkNode(GEQ, x, zero), nm->mkNode(LT, x, lens));
    Node ux = nm->mkNode(APPLY_UF, u, x);
    Node ux1 = nm->mkNode(APPLY_UF, u, nm->mkNode(ADD, x, one));
    Node c = nm->mkNode(SUB, mkCodePointAtIndex(s, x), c0);

    Node eq = ux1.eqNode(nm->mkNode(ADD, c, nm->mkNode(MULT, ten, ux)));
    Node cb = nm->mkNode(AND, nm->mkNode(GEQ, c, zero), nm->mkNode(LT, c, ten));

    Node ux1lem = nm->mkNode(GEQ, stoit, ux1);

    lem = nm->mkNode(OR, g.negate(), nm->mkNode(AND, eq, cb, ux1lem));
    lem = utils::mkForallInternal(xbv, lem);
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
  else if (t.getKind() == kind::SEQ_NTH)
  {
    // processing term:  str.nth( s, n)
    // similar to substr.
    Node s = t[0];
    Node n = t[1];
    Node skt = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "sst");
    Node t12 = nm->mkNode(ADD, n, one);
    Node lt0 = nm->mkNode(STRING_LENGTH, s);
    // start point is greater than or equal zero
    Node c1 = nm->mkNode(GEQ, n, zero);
    // start point is less than end of string
    Node c2 = nm->mkNode(GT, lt0, n);
    // check whether this application of seq.nth is defined.
    Node cond = nm->mkNode(AND, c1, c2);

    // nodes for the case where `seq.nth` is defined.
    Node sk1 = sc->mkSkolemCached(s, n, SkolemCache::SK_PREFIX, "sspre");
    Node sk2 = sc->mkSkolemCached(s, t12, SkolemCache::SK_SUFFIX_REM, "sssufr");
    Node unit = utils::mkUnit(s.getType(), skt);
    Node b11 = s.eqNode(nm->mkNode(STRING_CONCAT, sk1, unit, sk2));
    // length of first skolem is second argument
    Node b12 = nm->mkNode(STRING_LENGTH, sk1).eqNode(n);
    Node lsk2 = nm->mkNode(STRING_LENGTH, sk2);
    Node b13 = nm->mkNode(EQUAL, lsk2, nm->mkNode(SUB, lt0, t12));
    std::vector<Node> bchildren { b11, b12, b13 };
    if (s.getType().isString())
    {
      Node crange = utils::mkCodeRange(skt, alphaCard);
      bchildren.push_back(crange);
    }
    Node b1 = nm->mkNode(AND, bchildren);

    // the lemma for `seq.nth`
    Node lemma = nm->mkNode(IMPLIES, cond, b1);

    // assert:
    // n >=0 AND n < len( s )
    // IMPLIES: s = sk1 ++ unit(skt) ++ sk2 AND
    //          len( sk1 ) = n AND
    //          len( sk2 ) = len( s )- (n+1)
    // We also ensure skt is a valid code point if s is of type String
    asserts.push_back(lemma);
    retNode = skt;
  }
  else if (t.getKind() == kind::STRING_REPLACE)
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
    Node cond2 = nm->mkNode(kind::STRING_CONTAINS, x, y);
    // x = str.++( rp1, y, rp2 )
    Node c21 = x.eqNode(nm->mkNode(kind::STRING_CONCAT, rp1, y, rp2));
    // rpw = str.++( rp1, z, rp2 )
    Node c22 = rpw.eqNode(nm->mkNode(kind::STRING_CONCAT, rp1, z, rp2));
    // ~contains( str.++( rp1, substr( y, 0, len(y)-1 ) ), y )
    Node c23 =
        nm->mkNode(kind::STRING_CONTAINS,
                   nm->mkNode(
                       kind::STRING_CONCAT,
                       rp1,
                       nm->mkNode(kind::STRING_SUBSTR,
                                  y,
                                  zero,
                                  nm->mkNode(kind::SUB,
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
  else if (t.getKind() == kind::STRING_REPLACE_ALL)
  {
    // processing term: replaceall( x, y, z )
    Node x = t[0];
    Node y = t[1];
    Node z = t[2];
    Node rpaw = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "rpaw");

    Node numOcc = sc->mkSkolemFun(
        SkolemFunId::STRINGS_NUM_OCCUR, nm->integerType(), x, y);
    std::vector<TypeNode> argTypes;
    argTypes.push_back(nm->integerType());
    TypeNode raResultType = nm->mkFunctionType(argTypes, t.getType());
    Node us = sc->mkSkolemFun(
        SkolemFunId::STRINGS_REPLACE_ALL_RESULT, raResultType, t);
    TypeNode ufType = nm->mkFunctionType(argTypes, nm->integerType());
    Node uf = sc->mkSkolemFun(SkolemFunId::STRINGS_OCCUR_INDEX, ufType, x, y);

    Node ufno = nm->mkNode(APPLY_UF, uf, numOcc);
    Node usno = nm->mkNode(APPLY_UF, us, numOcc);
    Node rem = nm->mkNode(STRING_SUBSTR, x, ufno, nm->mkNode(STRING_LENGTH, x));

    std::vector<Node> lem;
    lem.push_back(nm->mkNode(GEQ, numOcc, zero));
    lem.push_back(rpaw.eqNode(nm->mkNode(APPLY_UF, us, zero)));
    lem.push_back(usno.eqNode(rem));
    lem.push_back(nm->mkNode(APPLY_UF, uf, zero).eqNode(zero));
    lem.push_back(nm->mkNode(STRING_INDEXOF, x, y, ufno).eqNode(negOne));

    Node i = SkolemCache::mkIndexVar(t);
    Node bvli = nm->mkNode(BOUND_VAR_LIST, i);
    Node bound =
        nm->mkNode(AND, nm->mkNode(GEQ, i, zero), nm->mkNode(LT, i, numOcc));
    Node ufi = nm->mkNode(APPLY_UF, uf, i);
    Node ufip1 = nm->mkNode(APPLY_UF, uf, nm->mkNode(ADD, i, one));
    Node ii = nm->mkNode(STRING_INDEXOF, x, y, ufi);
    Node cc =
        nm->mkNode(STRING_CONCAT,
                   nm->mkNode(STRING_SUBSTR, x, ufi, nm->mkNode(SUB, ii, ufi)),
                   z,
                   nm->mkNode(APPLY_UF, us, nm->mkNode(ADD, i, one)));

    std::vector<Node> flem;
    flem.push_back(ii.eqNode(negOne).negate());
    flem.push_back(nm->mkNode(APPLY_UF, us, i).eqNode(cc));
    flem.push_back(
        ufip1.eqNode(nm->mkNode(ADD, ii, nm->mkNode(STRING_LENGTH, y))));

    Node body = nm->mkNode(OR, bound.negate(), nm->mkNode(AND, flem));
    Node q = utils::mkForallInternal(bvli, body);
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
    // processing term: replace_re( x, y, z )
    Node x = t[0];
    Node y = t[1];
    Node z = t[2];
    Node k = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "k");

    // indexof_re(x, y, 0)
    Node idx = nm->mkNode(STRING_INDEXOF_RE, x, y, zero);

    // in_re("", y)
    Node matchesEmpty =
        nm->mkNode(STRING_IN_REGEXP, nm->mkConst(String("")), y);
    // k = z ++ x
    Node res1 = k.eqNode(nm->mkNode(STRING_CONCAT, z, x));

    TypeNode ktype = t.getType();
    Node k1 = sc->mkSkolemFun(SkolemFunId::SK_FIRST_MATCH_PRE, ktype, x, y);
    Node k2 = sc->mkSkolemFun(SkolemFunId::SK_FIRST_MATCH, ktype, x, y);
    Node k3 = sc->mkSkolemFun(SkolemFunId::SK_FIRST_MATCH_POST, ktype, x, y);
    Node k2Len = nm->mkNode(STRING_LENGTH, k2);
    // x = k1 ++ k2 ++ k3
    Node split = x.eqNode(nm->mkNode(STRING_CONCAT, k1, k2, k3));
    // len(k1) = indexof_re(x, y, 0)
    Node k1Len = nm->mkNode(STRING_LENGTH, k1).eqNode(idx);
    Node l = SkolemCache::mkLengthVar(t);
    Node bvll = nm->mkNode(BOUND_VAR_LIST, l);
    Node bound =
        nm->mkNode(AND, nm->mkNode(LEQ, zero, l), nm->mkNode(LT, l, k2Len));
    Node body = nm->mkNode(
        OR,
        bound.negate(),
        nm->mkNode(STRING_IN_REGEXP, nm->mkNode(STRING_SUBSTR, k2, zero, l), y)
            .negate());
    // forall l. 0 <= l < len(k2) => ~in_re(substr(k2, 0, l), r)
    Node shortestMatch = utils::mkForallInternal(bvll, body);
    // in_re(k2, y)
    Node match = nm->mkNode(STRING_IN_REGEXP, k2, y);
    // k = k1 ++ z ++ k3
    Node res = k.eqNode(nm->mkNode(STRING_CONCAT, k1, z, k3));

    // IF: indexof_re(x, y, 0) = -1
    // THEN: k = x
    // ELSE:
    //   x = k1 ++ k2 ++ k3 ^
    //   len(k1) = indexof_re(x, y, 0) ^
    //   (forall l. 0 <= l < len(k2) => ~in_re(substr(k2, 0, l), r)) ^
    //   in_re(k2, y) ^
    //   k = k1 ++ z ++ k3
    asserts.push_back(
        nm->mkNode(ITE,
                   idx.eqNode(negOne),
                   k.eqNode(x),
                   nm->mkNode(AND, {split, k1Len, shortestMatch, match, res})));
    retNode = k;
  }
  else if (t.getKind() == STRING_REPLACE_RE_ALL)
  {
    Node x = t[0];
    Node y = t[1];
    Node z = t[2];
    Node k = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "k");

    Node numOcc = sc->mkSkolemFun(
        SkolemFunId::STRINGS_NUM_OCCUR, nm->integerType(), x, y);
    std::vector<TypeNode> argTypes;
    argTypes.push_back(nm->integerType());
    TypeNode raResultType = nm->mkFunctionType(argTypes, t.getType());
    Node us = sc->mkSkolemFun(
        SkolemFunId::STRINGS_REPLACE_ALL_RESULT, raResultType, t);
    TypeNode ufType = nm->mkFunctionType(argTypes, nm->integerType());
    Node uf = sc->mkSkolemFun(SkolemFunId::STRINGS_OCCUR_INDEX, ufType, x, y);
    Node ul = sc->mkSkolemFun(SkolemFunId::STRINGS_OCCUR_LEN, ufType, x, y);

    Node emp = Word::mkEmptyWord(t.getType());

    Node yp = nm->mkNode(REGEXP_DIFF, y, nm->mkNode(STRING_TO_REGEXP, emp));
    // indexof_re(x, y', 0) = -1
    Node noMatch = nm->mkNode(STRING_INDEXOF_RE, x, yp, zero).eqNode(negOne);

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
    // indexof_re(substr(x, Uf(numOcc)), y', 0) = -1
    lemmas.push_back(
        nm->mkNode(STRING_INDEXOF_RE, rem, yp, zero).eqNode(negOne));

    Node i = SkolemCache::mkIndexVar(t);
    Node bvli = nm->mkNode(BOUND_VAR_LIST, i);
    Node bound =
        nm->mkNode(AND, nm->mkNode(GEQ, i, zero), nm->mkNode(LT, i, numOcc));
    Node ip1 = nm->mkNode(ADD, i, one);
    Node ufi = nm->mkNode(APPLY_UF, uf, i);
    Node ufip1 = nm->mkNode(APPLY_UF, uf, ip1);
    Node ulip1 = nm->mkNode(APPLY_UF, ul, ip1);
    // ii = Uf(i + 1) - Ul(i + 1)
    Node ii = nm->mkNode(SUB, ufip1, ulip1);

    std::vector<Node> flem;
    // Ul(i + 1) > 0
    flem.push_back(nm->mkNode(GT, ulip1, zero));
    // Uf(i + 1) = indexof_re(x, yp, Uf(i)) + Ul(i + 1)
    flem.push_back(ufip1.eqNode(
        nm->mkNode(ADD, nm->mkNode(STRING_INDEXOF_RE, x, yp, ufi), ulip1)));
    // in_re(substr(x, ii, Ul(i + 1)), y')
    flem.push_back(nm->mkNode(
        STRING_IN_REGEXP, nm->mkNode(STRING_SUBSTR, x, ii, ulip1), yp));
    Node l = SkolemCache::mkLengthVar(t);
    Node bvll = nm->mkNode(BOUND_VAR_LIST, l);
    Node lenBound =
        nm->mkNode(AND, nm->mkNode(LT, zero, l), nm->mkNode(LT, l, ulip1));
    Node shortestMatchBody = nm->mkNode(
        OR,
        lenBound.negate(),
        nm->mkNode(STRING_IN_REGEXP, nm->mkNode(STRING_SUBSTR, x, ii, l), y)
            .negate());
    // forall l. 0 < l < Ul(i + 1) =>
    //   ~in_re(substr(x, Uf(i + 1) - Ul(i + 1), l), y')
    flem.push_back(utils::mkForallInternal(bvll, shortestMatchBody));
    Node pfxMatch = nm->mkNode(STRING_SUBSTR, x, ufi, nm->mkNode(SUB, ii, ufi));
    // Us(i) = substr(x, Uf(i), ii - Uf(i)) ++ z ++ Us(i + 1)
    flem.push_back(
        nm->mkNode(APPLY_UF, us, i)
            .eqNode(nm->mkNode(
                STRING_CONCAT, pfxMatch, z, nm->mkNode(APPLY_UF, us, ip1))));
    Node body = nm->mkNode(OR, bound.negate(), nm->mkNode(AND, flem));
    Node forall = utils::mkForallInternal(bvli, body);
    lemmas.push_back(forall);

    // IF indexof(x, y', 0) = -1
    // THEN: k = x
    // ELSE:
    //   numOcc > 0 ^
    //   k = Us(0) ^ Us(numOcc) = substr(x, Uf(numOcc)) ^
    //   Uf(0) = 0 ^ indexof_re(substr(x, Uf(numOcc)), y', 0) = -1 ^
    //   forall i. 0 <= i < nummOcc =>
    //     Ul(i + 1) > 0 ^
    //     Uf(i + 1) = indexof_re(x, yp, Uf(i)) + Ul(i + 1) ^
    //     in_re(substr(x, ii, Ul(i + 1)), y') ^
    //     forall l. 0 < l < Ul(i + 1) =>
    //       ~in_re(substr(x, ii, l), y')
    //     Us(i) = substr(x, Uf(i), ii - Uf(i)) ++ z ++ Us(i + 1)
    //     where ii = Uf(i + 1) - Ul(i + 1)
    // where y' = re.diff(y, "")
    //
    // Conceptually, y' is the regex y but excluding the empty string (because
    // we do not want to match empty strings), numOcc is the number of shortest
    // matches of y' in x, Uf(i) is the end position of the i-th match, Ul(i)
    // is the length of the i^th match, and Us(i) is the result of processing
    // the remainder after processing the i^th occurrence of y in x.
    //
    // Visualization of Uf(i) and Ul(i):
    //
    // x = |------------| match 1 |-----------| match 2   |---|
    //     |                      |                       |
    //     Uf(0)                  Uf(1)                   Uf(2)
    //
    //                  |---------|           |-----------|
    //                    Ul(1)                 Ul(2)
    asserts.push_back(
        nm->mkNode(ITE, noMatch, k.eqNode(x), nm->mkNode(AND, lemmas)));
    retNode = k;
  }
  else if (t.getKind() == STRING_TO_LOWER || t.getKind() == STRING_TO_UPPER)
  {
    Node x = t[0];
    Node r = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "r");

    Node lenx = nm->mkNode(STRING_LENGTH, x);
    Node lenr = nm->mkNode(STRING_LENGTH, r);
    Node eqLenA = lenx.eqNode(lenr);

    Node i = SkolemCache::mkIndexVar(t);
    Node bvi = nm->mkNode(BOUND_VAR_LIST, i);

    Node ci = mkCodePointAtIndex(x, i);
    Node ri = mkCodePointAtIndex(r, i);

    Node lb =
        nm->mkConstInt(Rational(t.getKind() == STRING_TO_UPPER ? 97 : 65));
    Node ub =
        nm->mkConstInt(Rational(t.getKind() == STRING_TO_UPPER ? 122 : 90));
    Node offset =
        nm->mkConstInt(Rational(t.getKind() == STRING_TO_UPPER ? -32 : 32));

    Node res = nm->mkNode(
        ITE,
        nm->mkNode(AND, nm->mkNode(LEQ, lb, ci), nm->mkNode(LEQ, ci, ub)),
        nm->mkNode(ADD, ci, offset),
        ci);

    Node bound =
        nm->mkNode(AND, nm->mkNode(LEQ, zero, i), nm->mkNode(LT, i, lenr));
    Node body = nm->mkNode(OR, bound.negate(), ri.eqNode(res));
    Node rangeA = utils::mkForallInternal(bvi, body);

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

    Node revi =
        nm->mkNode(SUB, nm->mkNode(STRING_LENGTH, x), nm->mkNode(ADD, i, one));
    Node ssr = nm->mkNode(STRING_SUBSTR, r, i, one);
    Node ssx = nm->mkNode(STRING_SUBSTR, x, revi, one);

    Node bound =
        nm->mkNode(AND, nm->mkNode(LEQ, zero, i), nm->mkNode(LT, i, lenr));
    Node body = nm->mkNode(OR, bound.negate(), ssr.eqNode(ssx));
    Node rangeA = utils::mkForallInternal(bvi, body);
    // assert:
    //   len(r) = len(x) ^
    //   forall i. 0 <= i < len(r) =>
    //     substr(r,i,1) = substr(x,len(x)-(i+1),1)
    Node assert = nm->mkNode(AND, eqLenA, rangeA);
    asserts.push_back(assert);

    // Thus, (str.rev x) = r
    retNode = r;
  }
  else if (t.getKind() == kind::STRING_CONTAINS)
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
            NodeManager::currentNM()->mkNode(kind::SUB, lenx, lens)),
        NodeManager::currentNM()->mkNode(
            kind::EQUAL,
            NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, x, b1, lens),
            s));
    retNode = utils::mkForallInternal(b1v, body.negate()).negate();
  }
  else if (t.getKind() == kind::STRING_LEQ)
  {
    Node ltp = sc->mkTypedSkolemCached(
        nm->booleanType(), t, SkolemCache::SK_PURIFY, "ltp");
    Node k = SkolemCache::mkIndexVar(t);

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

    Node conjn = utils::mkForallInternal(nm->mkNode(BOUND_VAR_LIST, k),
                                         nm->mkNode(AND, conj).negate())
                     .negate();
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
    //  ELSE: exists k.
    //        k >= 0 AND k <= len( x ) AND k <= len( y ) AND
    //        substr( x, 0, k ) = substr( y, 0, k ) AND
    //        IF    ltp
    //        THEN: str.code(substr( x, k, 1 )) < str.code(substr( y, k, 1 ))
    //        ELSE: str.code(substr( x, k, 1 )) > str.code(substr( y, k, 1 ))
    Node assert = nm->mkNode(ITE, t[0].eqNode(t[1]), ltp, conjn);
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
  Node retNode = reduce(t, asserts, d_sc, options().strings.stringsAlphaCard);
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
    if (d_statReductions != nullptr)
    {
      (*d_statReductions) << t.getKind();
    }
  }
  else
  {
    Trace("strings-preprocess-debug")
        << "Return " << retNode << " unchanged" << std::endl;
  }
  return retNode;
}

Node StringsPreprocess::simplifyRec(Node t, std::vector<Node>& asserts)
{
  std::map<Node, Node>::iterator it = d_visited.find(t);
  if (it != d_visited.end())
  {
    return it->second;
  }else{
    Node retNode = t;
    if( t.getNumChildren()==0 ){
      retNode = simplify(t, asserts);
    }
    else if (!t.isClosure())
    {
      bool changed = false;
      std::vector< Node > cc;
      if( t.getMetaKind() == kind::metakind::PARAMETERIZED ){
        cc.push_back( t.getOperator() );
      }
      for(unsigned i=0; i<t.getNumChildren(); i++) {
        Node s = simplifyRec(t[i], asserts);
        cc.push_back( s );
        if( s!=t[i] ) {
          changed = true;
        }
      }
      Node tmp = t;
      if( changed ){
        tmp = NodeManager::currentNM()->mkNode( t.getKind(), cc );
      }
      // We cannot statically reduce seq.nth due to it being partial function.
      // Reducing it here would violate the functional property of seq.nth.
      if (tmp.getKind() != SEQ_NTH)
      {
        retNode = simplify(tmp, asserts);
      }
    }
    d_visited[t] = retNode;
    return retNode;
  }
}
Node StringsPreprocess::mkCodePointAtIndex(Node x, Node i)
{
  // We use (SEQ_NTH, x, i) instead of
  // (STRING_TO_CODE, (STRING_SUBSTR, x, i, 1)) here. The former may be
  // converted to the latter during preprocessing based on our options.
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(SEQ_NTH, x, i);
}

Node StringsPreprocess::processAssertion(Node n, std::vector<Node>& asserts)
{
  std::vector<Node> asserts_curr;
  Node ret = simplifyRec(n, asserts_curr);
  while (!asserts_curr.empty())
  {
    Node curr = asserts_curr.back();
    asserts_curr.pop_back();
    std::vector<Node> asserts_tmp;
    curr = simplifyRec(curr, asserts_tmp);
    asserts_curr.insert(
        asserts_curr.end(), asserts_tmp.begin(), asserts_tmp.end());
    asserts.push_back(curr);
  }
  return ret;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

/*********************                                                        */
/** expr_black.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Black box testing of CVC4::Expr.
 **/

#include <cxxtest/TestSuite.h>

#include <sstream>
#include <string>

#include "expr/expr_manager.h"
#include "expr/expr.h"
#include "util/Assert.h"
#include "util/exception.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

class ExprBlack : public CxxTest::TestSuite {
private:

  ExprManager* d_em;

  Expr* a;
  Expr* b;
  Expr* c;
  Expr* mult;
  Expr* plus;
  Expr* d;
  Expr* null;

  Expr* i1;
  Expr* i2;
  Expr* r1;
  Expr* r2;

public:

  void setUp() {
    try {
      d_em = new ExprManager;

      a = new Expr(d_em->mkVar(d_em->booleanType(), "a"));
      b = new Expr(d_em->mkVar(d_em->booleanType(), "b"));
      c = new Expr(d_em->mkExpr(MULT, *a, *b));
      mult = new Expr(d_em->mkConst(MULT));
      plus = new Expr(d_em->mkConst(PLUS));
      d = new Expr(d_em->mkExpr(APPLY_UF, *plus, *b, *c));
      null = new Expr;

      i1 = new Expr(d_em->mkConst(Integer("0")));
      i2 = new Expr(d_em->mkConst(Integer(23)));
      r1 = new Expr(d_em->mkConst(Rational(1, 5)));
      r2 = new Expr(d_em->mkConst(Rational("0")));
    } catch(Exception e) {
      cerr << "Exception during setUp():" << endl << e;
      throw;
    }
  }

  void tearDown() {
    try {
      delete r2;
      delete r1;
      delete i2;
      delete i1;

      delete null;
      delete d;
      delete plus;
      delete mult;
      delete c;
      delete b;
      delete a;

      delete d_em;
    } catch(Exception e) {
      cerr << "Exception during tearDown():" << endl << e;
      throw;
    }
  }

  void testDefaultCtor() {
    /* Expr(); */
    Expr e;
    TS_ASSERT(e.isNull());
  }

  void testCtors() {
    TS_ASSERT(!a->isNull());
    TS_ASSERT(!b->isNull());

    /* Expr(); */
    Expr e;
    TS_ASSERT(e.isNull());

    /* Expr(const Expr& e) */
    Expr e2(e);
    TS_ASSERT(e == e2);
    TS_ASSERT(e2 == e);
    TS_ASSERT(!(e2 < e));
    TS_ASSERT(!(e < e2));
    TS_ASSERT(e.isNull());
    TS_ASSERT(e2.isNull());
    Expr f = d_em->mkExpr(PLUS, *a, *b);
    Expr f2 = f;
    TS_ASSERT(!f.isNull());
    TS_ASSERT(!f2.isNull());
    TS_ASSERT(f == f2);
    TS_ASSERT(f2 == f);
    TS_ASSERT(!(f2 < f));
    TS_ASSERT(!(f < f2));
    TS_ASSERT(f == d_em->mkExpr(PLUS, *a, *b));
  }

  void testAssignment() {
    /* Expr& operator=(const Expr& e); */
    Expr e = d_em->mkExpr(PLUS, *a, *b);
    Expr f;
    TS_ASSERT(f.isNull());
    f = e;
    TS_ASSERT(!f.isNull());
    TS_ASSERT(e == f);
    TS_ASSERT(f == e);
    TS_ASSERT(!(f < e));
    TS_ASSERT(!(e < f));
    TS_ASSERT(f == d_em->mkExpr(PLUS, *a, *b));
  }

  void testEquality() {
    /* bool operator==(const Expr& e) const; */
    /* bool operator!=(const Expr& e) const; */

    TS_ASSERT(*a == *a);
    TS_ASSERT(*b == *b);
    TS_ASSERT(!(*a != *a));
    TS_ASSERT(!(*b != *b));

    TS_ASSERT(*a != *b);
    TS_ASSERT(*b != *a);
    TS_ASSERT(!(*a == *b));
    TS_ASSERT(!(*b == *a));
  }

  void testComparison() {
    /* bool operator<(const Expr& e) const; */

    TS_ASSERT(*null < *a);
    TS_ASSERT(*null < *b);
    TS_ASSERT(*null < *c);
    TS_ASSERT(*null < *d);
    TS_ASSERT(*null < *plus);
    TS_ASSERT(*null < *mult);
    TS_ASSERT(*null < *i1);
    TS_ASSERT(*null < *i2);
    TS_ASSERT(*null < *r1);
    TS_ASSERT(*null < *r2);

    TS_ASSERT(*a < *b);
    TS_ASSERT(*a < *c);
    TS_ASSERT(*a < *d);
    TS_ASSERT(!(*b < *a));
    TS_ASSERT(!(*c < *a));
    TS_ASSERT(!(*d < *a));

    TS_ASSERT(*b < *c);
    TS_ASSERT(*b < *d);
    TS_ASSERT(!(*c < *b));
    TS_ASSERT(!(*d < *b));

    TS_ASSERT(*c < *d);
    TS_ASSERT(!(*d < *c));

    TS_ASSERT(*mult < *c);
    TS_ASSERT(*mult < *d);
    TS_ASSERT(*plus < *d);
    TS_ASSERT(!(*c < *mult));
    TS_ASSERT(!(*d < *mult));
    TS_ASSERT(!(*d < *plus));

    TS_ASSERT(!(*null < *null));
    TS_ASSERT(!(*a < *a));
    TS_ASSERT(!(*b < *b));
    TS_ASSERT(!(*c < *c));
    TS_ASSERT(!(*plus < *plus));
    TS_ASSERT(!(*mult < *mult));
    TS_ASSERT(!(*d < *d));
  }

  void testGetKind() {
    /* Kind getKind() const; */

    TS_ASSERT(a->getKind() == VARIABLE);
    TS_ASSERT(b->getKind() == VARIABLE);
    TS_ASSERT(c->getKind() == MULT);
    TS_ASSERT(mult->getKind() == BUILTIN);
    TS_ASSERT(plus->getKind() == BUILTIN);
    TS_ASSERT(d->getKind() == APPLY_UF);
    TS_ASSERT(null->getKind() == NULL_EXPR);

    TS_ASSERT(i1->getKind() == CONST_INTEGER);
    TS_ASSERT(i2->getKind() == CONST_INTEGER);
    TS_ASSERT(r1->getKind() == CONST_RATIONAL);
    TS_ASSERT(r2->getKind() == CONST_RATIONAL);
  }

  void testGetNumChildren() {
    /* size_t getNumChildren() const; */

    TS_ASSERT(a->getNumChildren() == 0);
    TS_ASSERT(b->getNumChildren() == 0);
    TS_ASSERT(c->getNumChildren() == 2);
    TS_ASSERT(mult->getNumChildren() == 0);
    TS_ASSERT(plus->getNumChildren() == 0);
    TS_ASSERT(d->getNumChildren() == 2);
    TS_ASSERT(null->getNumChildren() == 0);

    TS_ASSERT(i1->getNumChildren() == 0);
    TS_ASSERT(i2->getNumChildren() == 0);
    TS_ASSERT(r1->getNumChildren() == 0);
    TS_ASSERT(r2->getNumChildren() == 0);
  }

  void testOperatorFunctions() {
    /* bool hasOperator() const; */
    /* Expr getOperator() const; */

    TS_ASSERT(!a->hasOperator());
    TS_ASSERT(!b->hasOperator());
    TS_ASSERT(c->hasOperator());
    TS_ASSERT(!mult->hasOperator());
    TS_ASSERT(!plus->hasOperator());
    TS_ASSERT(d->hasOperator());
    TS_ASSERT(!null->hasOperator());

    TS_ASSERT_THROWS(a->getOperator(), IllegalArgumentException);
    TS_ASSERT_THROWS(b->getOperator(), IllegalArgumentException);
    TS_ASSERT(c->getOperator() == *mult);
    TS_ASSERT_THROWS(plus->getOperator(), IllegalArgumentException);
    TS_ASSERT_THROWS(mult->getOperator(), IllegalArgumentException);
    TS_ASSERT(d->getOperator() == *plus);
    TS_ASSERT_THROWS(null->getOperator(), IllegalArgumentException);
  }

  void testGetType() {
    /* Type* getType() const; */

    TS_ASSERT(a->getType() == d_em->booleanType());
    TS_ASSERT(b->getType() == d_em->booleanType());
    TS_ASSERT(c->getType() == NULL);
    TS_ASSERT(mult->getType() == NULL);
    TS_ASSERT(plus->getType() == NULL);
    TS_ASSERT(d->getType() == NULL);
#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS(null->getType(), AssertionException);
#endif /* CVC4_ASSERTIONS */

    TS_ASSERT(i1->getType() == NULL);
    TS_ASSERT(i2->getType() == NULL);
    TS_ASSERT(r1->getType() == NULL);
    TS_ASSERT(r2->getType() == NULL);
  }

  void testToString() {
    /* std::string toString() const; */

    TS_ASSERT(a->toString() == "a");
    TS_ASSERT(b->toString() == "b");
    TS_ASSERT(c->toString() == "(MULT a b)");
    TS_ASSERT(mult->toString() == "(BUILTIN MULT)");
    TS_ASSERT(plus->toString() == "(BUILTIN PLUS)");
    TS_ASSERT(d->toString() == "(APPLY_UF (BUILTIN PLUS) b (MULT a b))");
    TS_ASSERT(null->toString() == "null");

    TS_ASSERT(i1->toString() == "(CONST_INTEGER 0)");
    TS_ASSERT(i2->toString() == "(CONST_INTEGER 23)");
    TS_ASSERT(r1->toString() == "(CONST_RATIONAL 1/5)");
    TS_ASSERT(r2->toString() == "(CONST_RATIONAL 0)");
  }

  void testToStream() {
    /* void toStream(std::ostream& out) const; */

    stringstream sa, sb, sc, smult, splus, sd, snull;
    stringstream si1, si2, sr1, sr2;
    a->toStream(sa);
    b->toStream(sb);
    c->toStream(sc);
    mult->toStream(smult);
    plus->toStream(splus);
    d->toStream(sd);
    null->toStream(snull);

    i1->toStream(si1);
    i2->toStream(si2);
    r1->toStream(sr1);
    r2->toStream(sr2);

    TS_ASSERT(sa.str() == "a");
    TS_ASSERT(sb.str() == "b");
    TS_ASSERT(sc.str() == "(MULT a b)");
    TS_ASSERT(smult.str() == "(BUILTIN MULT)");
    TS_ASSERT(splus.str() == "(BUILTIN PLUS)");
    TS_ASSERT(sd.str() == "(APPLY_UF (BUILTIN PLUS) b (MULT a b))");
    TS_ASSERT(snull.str() == "null");

    TS_ASSERT(si1.str() == "(CONST_INTEGER 0)");
    TS_ASSERT(si2.str() == "(CONST_INTEGER 23)");
    TS_ASSERT(sr1.str() == "(CONST_RATIONAL 1/5)");
    TS_ASSERT(sr2.str() == "(CONST_RATIONAL 0)");
  }

  void testIsNull() {
    /* bool isNull() const; */

    TS_ASSERT(!a->isNull());
    TS_ASSERT(!b->isNull());
    TS_ASSERT(!c->isNull());
    TS_ASSERT(!mult->isNull());
    TS_ASSERT(!plus->isNull());
    TS_ASSERT(!d->isNull());
    TS_ASSERT(null->isNull());
  }

  void testIsConst() {
    /* bool isConst() const; */

    TS_ASSERT(!a->isConst());
    TS_ASSERT(!b->isConst());
    TS_ASSERT(!c->isConst());
    TS_ASSERT(mult->isConst());
    TS_ASSERT(plus->isConst());
    TS_ASSERT(!d->isConst());
    TS_ASSERT(!null->isConst());
  }

  void testIsAtomic() {
    /* bool isAtomic() const; */

    TS_ASSERT(a->isAtomic());
    TS_ASSERT(b->isAtomic());
    TS_ASSERT(c->isAtomic());
    TS_ASSERT(mult->isAtomic());
    TS_ASSERT(plus->isAtomic());
    TS_ASSERT(d->isAtomic());
    TS_ASSERT(!null->isAtomic());

    TS_ASSERT(i1->isAtomic());
    TS_ASSERT(i2->isAtomic());
    TS_ASSERT(r1->isAtomic());
    TS_ASSERT(r2->isAtomic());

    Expr x = d_em->mkExpr(AND, *a, *b);
    Expr y = d_em->mkExpr(ITE, *a, *b, *c);
    Expr z = d_em->mkExpr(IFF, x, y);

    TS_ASSERT(!x.isAtomic());
    TS_ASSERT(!y.isAtomic());
    TS_ASSERT(!z.isAtomic());
  }

  void testGetConst() {
    /* template <class T>
       const T& getConst() const; */

    TS_ASSERT_THROWS(a->getConst<Kind>(), IllegalArgumentException);
    TS_ASSERT_THROWS(b->getConst<Kind>(), IllegalArgumentException);
    TS_ASSERT_THROWS(c->getConst<Kind>(), IllegalArgumentException);
    TS_ASSERT(mult->getConst<Kind>() == MULT);
    TS_ASSERT_THROWS(mult->getConst<Integer>(), IllegalArgumentException);
    TS_ASSERT(plus->getConst<Kind>() == PLUS);
    TS_ASSERT_THROWS(plus->getConst<Rational>(), IllegalArgumentException);
    TS_ASSERT_THROWS(d->getConst<Kind>(), IllegalArgumentException);
    TS_ASSERT_THROWS(null->getConst<Kind>(), IllegalArgumentException);

    TS_ASSERT(i1->getConst<Integer>() == 0);
    TS_ASSERT(i2->getConst<Integer>() == 23);
    TS_ASSERT(r1->getConst<Rational>() == Rational(1, 5));
    TS_ASSERT(r2->getConst<Rational>() == Rational("0"));

    TS_ASSERT_THROWS(i1->getConst<Kind>(), IllegalArgumentException);
    TS_ASSERT_THROWS(i2->getConst<Kind>(), IllegalArgumentException);
    TS_ASSERT_THROWS(r1->getConst<Kind>(), IllegalArgumentException);
    TS_ASSERT_THROWS(r2->getConst<Kind>(), IllegalArgumentException);
  }

  void testGetExprManager() {
    /* ExprManager* getExprManager() const; */

    TS_ASSERT(a->getExprManager() == d_em);
    TS_ASSERT(b->getExprManager() == d_em);
    TS_ASSERT(c->getExprManager() == d_em);
    TS_ASSERT(mult->getExprManager() == d_em);
    TS_ASSERT(plus->getExprManager() == d_em);
    TS_ASSERT(d->getExprManager() == d_em);
    TS_ASSERT(null->getExprManager() == NULL);

    TS_ASSERT(i1->getExprManager() == d_em);
    TS_ASSERT(i2->getExprManager() == d_em);
    TS_ASSERT(r1->getExprManager() == d_em);
    TS_ASSERT(r2->getExprManager() == d_em);
  }
};

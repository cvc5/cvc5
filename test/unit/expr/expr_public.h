/*********************                                                        */
/*! \file expr_public.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Public black-box testing of CVC4::Expr.
 **
 ** Public black-box testing of CVC4::Expr.
 **/

#include <cxxtest/TestSuite.h>

#include <sstream>
#include <string>

#include "api/cvc4cpp.h"
#include "base/exception.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "options/options.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

class ExprPublic : public CxxTest::TestSuite {
 public:
  void setUp() override
  {
    try
    {
      char* argv[2];
      argv[0] = strdup("");
      argv[1] = strdup("--output-lang=ast");
      Options::parseOptions(&opts, 2, argv);
      free(argv[0]);
      free(argv[1]);

      d_slv = new api::Solver(&opts);
      d_em = d_slv->getExprManager();

      a_bool = new Expr(d_em->mkVar("a", d_em->booleanType()));
      b_bool = new Expr(d_em->mkVar("b", d_em->booleanType()));
      c_bool_and = new Expr(d_em->mkExpr(AND, *a_bool, *b_bool));
      and_op = new Expr(d_em->mkConst(AND));
      plus_op = new Expr(d_em->mkConst(PLUS));
      fun_type = new Type(
          d_em->mkFunctionType(d_em->booleanType(), d_em->booleanType()));
      fun_op = new Expr(d_em->mkVar("f", *fun_type));
      d_apply_fun_bool = new Expr(d_em->mkExpr(APPLY_UF, *fun_op, *a_bool));
      null = new Expr();

      i1 = new Expr(d_em->mkConst(Rational("0")));
      i2 = new Expr(d_em->mkConst(Rational(23)));
      r1 = new Expr(d_em->mkConst(Rational(1, 5)));
      r2 = new Expr(d_em->mkConst(Rational("0")));
    }
    catch (Exception& e)
    {
      cerr << "Exception during setUp():" << endl << e;
      throw;
    }
  }

  void tearDown() override
  {
    try {
      delete r2;
      delete r1;
      delete i2;
      delete i1;

      delete null;
      delete d_apply_fun_bool;
      delete fun_type;
      delete fun_op;
      delete plus_op;
      delete and_op;
      delete c_bool_and;
      delete b_bool;
      delete a_bool;
      delete d_slv;
    }
    catch (Exception& e)
    {
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
    TS_ASSERT(!a_bool->isNull());
    TS_ASSERT(!b_bool->isNull());

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
    Expr f = d_em->mkExpr(OR, *a_bool, *b_bool);
    Expr f2 = f;
    TS_ASSERT(!f.isNull());
    TS_ASSERT(!f2.isNull());
    TS_ASSERT(f == f2);
    TS_ASSERT(f2 == f);
    TS_ASSERT(!(f2 < f));
    TS_ASSERT(!(f < f2));
    TS_ASSERT(f == d_em->mkExpr(OR, *a_bool, *b_bool));
  }

  void testAssignment() {
    /* Expr& operator=(const Expr& e); */
    Expr e = d_em->mkExpr(OR, *a_bool, *b_bool);
    Expr f;
    TS_ASSERT(f.isNull());
    f = e;
    TS_ASSERT(!f.isNull());
    TS_ASSERT(e == f);
    TS_ASSERT(f == e);
    TS_ASSERT(!(f < e));
    TS_ASSERT(!(e < f));
    TS_ASSERT(f == d_em->mkExpr(OR, *a_bool, *b_bool));
  }

  void testEquality() {
    /* bool operator==(const Expr& e) const; */
    /* bool operator!=(const Expr& e) const; */

    TS_ASSERT(*a_bool == *a_bool);
    TS_ASSERT(*b_bool == *b_bool);
    TS_ASSERT(!(*a_bool != *a_bool));
    TS_ASSERT(!(*b_bool != *b_bool));

    TS_ASSERT(*a_bool != *b_bool);
    TS_ASSERT(*b_bool != *a_bool);
    TS_ASSERT(!(*a_bool == *b_bool));
    TS_ASSERT(!(*b_bool == *a_bool));
  }

  void testComparison() {
    /* bool operator<(const Expr& e) const; */

    TS_ASSERT(*null < *a_bool);
    TS_ASSERT(*null < *b_bool);
    TS_ASSERT(*null < *c_bool_and);
    TS_ASSERT(*null < *d_apply_fun_bool);
    TS_ASSERT(*null < *plus_op);
    TS_ASSERT(*null < *and_op);
    TS_ASSERT(*null < *i1);
    TS_ASSERT(*null < *i2);
    TS_ASSERT(*null < *r1);
    TS_ASSERT(*null < *r2);

    TS_ASSERT(*a_bool < *b_bool);
    TS_ASSERT(*a_bool < *c_bool_and);
    TS_ASSERT(*a_bool < *d_apply_fun_bool);
    TS_ASSERT(!(*b_bool < *a_bool));
    TS_ASSERT(!(*c_bool_and < *a_bool));
    TS_ASSERT(!(*d_apply_fun_bool < *a_bool));

    TS_ASSERT(*b_bool < *c_bool_and);
    TS_ASSERT(*b_bool < *d_apply_fun_bool);
    TS_ASSERT(!(*c_bool_and < *b_bool));
    TS_ASSERT(!(*d_apply_fun_bool < *b_bool));

    TS_ASSERT(*c_bool_and < *d_apply_fun_bool);
    TS_ASSERT(!(*d_apply_fun_bool < *c_bool_and));

    TS_ASSERT(*and_op < *c_bool_and);
    TS_ASSERT(*and_op < *d_apply_fun_bool);
    TS_ASSERT(*plus_op < *d_apply_fun_bool);
    TS_ASSERT(!(*c_bool_and < *and_op));
    TS_ASSERT(!(*d_apply_fun_bool < *and_op));
    TS_ASSERT(!(*d_apply_fun_bool < *plus_op));

    TS_ASSERT(!(*null < *null));
    TS_ASSERT(!(*a_bool < *a_bool));
    TS_ASSERT(!(*b_bool < *b_bool));
    TS_ASSERT(!(*c_bool_and < *c_bool_and));
    TS_ASSERT(!(*plus_op < *plus_op));
    TS_ASSERT(!(*and_op < *and_op));
    TS_ASSERT(!(*d_apply_fun_bool < *d_apply_fun_bool));
  }

  void testGetKind() {
    /* Kind getKind() const; */

    TS_ASSERT(a_bool->getKind() == VARIABLE);
    TS_ASSERT(b_bool->getKind() == VARIABLE);
    TS_ASSERT(c_bool_and->getKind() == AND);
    TS_ASSERT(and_op->getKind() == BUILTIN);
    TS_ASSERT(plus_op->getKind() == BUILTIN);
    TS_ASSERT(d_apply_fun_bool->getKind() == APPLY_UF);
    TS_ASSERT(null->getKind() == NULL_EXPR);

    TS_ASSERT(i1->getKind() == CONST_RATIONAL);
    TS_ASSERT(i2->getKind() == CONST_RATIONAL);
    TS_ASSERT(r1->getKind() == CONST_RATIONAL);
    TS_ASSERT(r2->getKind() == CONST_RATIONAL);
  }

  void testGetNumChildren() {
    /* size_t getNumChildren() const; */

    TS_ASSERT(a_bool->getNumChildren() == 0);
    TS_ASSERT(b_bool->getNumChildren() == 0);
    TS_ASSERT(c_bool_and->getNumChildren() == 2);
    TS_ASSERT(and_op->getNumChildren() == 0);
    TS_ASSERT(plus_op->getNumChildren() == 0);
    TS_ASSERT(d_apply_fun_bool->getNumChildren() == 1);
    TS_ASSERT(null->getNumChildren() == 0);

    TS_ASSERT(i1->getNumChildren() == 0);
    TS_ASSERT(i2->getNumChildren() == 0);
    TS_ASSERT(r1->getNumChildren() == 0);
    TS_ASSERT(r2->getNumChildren() == 0);
  }

  void testOperatorFunctions() {
    /* bool hasOperator() const; */
    /* Expr getOperator() const; */

    TS_ASSERT(!a_bool->hasOperator());
    TS_ASSERT(!b_bool->hasOperator());
    TS_ASSERT(c_bool_and->hasOperator());
    TS_ASSERT(!and_op->hasOperator());
    TS_ASSERT(!plus_op->hasOperator());
    TS_ASSERT(d_apply_fun_bool->hasOperator());
    TS_ASSERT(!null->hasOperator());

    TS_ASSERT_THROWS(a_bool->getOperator(), IllegalArgumentException&);
    TS_ASSERT_THROWS(b_bool->getOperator(), IllegalArgumentException&);
    TS_ASSERT(c_bool_and->getOperator() == *and_op);
    TS_ASSERT_THROWS(plus_op->getOperator(), IllegalArgumentException&);
    TS_ASSERT_THROWS(and_op->getOperator(), IllegalArgumentException&);
    TS_ASSERT(d_apply_fun_bool->getOperator() == *fun_op);
    TS_ASSERT_THROWS(null->getOperator(), IllegalArgumentException&);
  }

  void testGetType() {
    /* Type getType(); */

    TS_ASSERT(a_bool->getType(false) == d_em->booleanType());
    TS_ASSERT(a_bool->getType(true) == d_em->booleanType());
    TS_ASSERT(b_bool->getType(false) == d_em->booleanType());
    TS_ASSERT(b_bool->getType(true) == d_em->booleanType());
    TS_ASSERT_THROWS(d_em->mkExpr(MULT, *a_bool, *b_bool).getType(true),
                     TypeCheckingException&);
    // These need better support for operators
    //    TS_ASSERT(and_op->getType().isNull());
    //    TS_ASSERT(plus_op->getType().isNull());
    TS_ASSERT(d_apply_fun_bool->getType() == d_em->booleanType());
    TS_ASSERT(i1->getType().isInteger());
    TS_ASSERT(i2->getType().isInteger());
    TS_ASSERT(r1->getType().isReal());
    TS_ASSERT(r2->getType().isReal());
  }

  void testToString() {
    /* std::string toString() const; */

    TS_ASSERT(a_bool->toString() == "a");
    TS_ASSERT(b_bool->toString() == "b");
    TS_ASSERT(c_bool_and->toString() == "(AND a b)");
    TS_ASSERT(and_op->toString() == "(BUILTIN AND)");
    TS_ASSERT(plus_op->toString() == "(BUILTIN PLUS)");
    TS_ASSERT(d_apply_fun_bool->toString() == "(APPLY_UF f a)");
    TS_ASSERT(null->toString() == "null");

    TS_ASSERT(i1->toString() == "(CONST_RATIONAL 0)");
    TS_ASSERT(i2->toString() == "(CONST_RATIONAL 23)");
    TS_ASSERT(r1->toString() == "(CONST_RATIONAL 1/5)");
    TS_ASSERT(r2->toString() == "(CONST_RATIONAL 0)");
  }

  void testToStream() {
    /* void toStream(std::ostream& out) const; */

    stringstream sa, sb, sc, smult, splus, sd, snull;
    stringstream si1, si2, sr1, sr2;
    a_bool->toStream(sa);
    b_bool->toStream(sb);
    c_bool_and->toStream(sc);
    and_op->toStream(smult);
    plus_op->toStream(splus);
    d_apply_fun_bool->toStream(sd);
    null->toStream(snull);

    i1->toStream(si1);
    i2->toStream(si2);
    r1->toStream(sr1);
    r2->toStream(sr2);

    TS_ASSERT(sa.str() == "a");
    TS_ASSERT(sb.str() == "b");
    TS_ASSERT(sc.str() == "(AND a b)");
    TS_ASSERT(smult.str() == "(BUILTIN AND)");
    TS_ASSERT(splus.str() == "(BUILTIN PLUS)");
    TS_ASSERT(sd.str() == "(APPLY_UF f a)");
    TS_ASSERT(snull.str() == "null");

    TS_ASSERT(si1.str() == "(CONST_RATIONAL 0)");
    TS_ASSERT(si2.str() == "(CONST_RATIONAL 23)");
    TS_ASSERT(sr1.str() == "(CONST_RATIONAL 1/5)");
    TS_ASSERT(sr2.str() == "(CONST_RATIONAL 0)");
  }

  void testIsNull() {
    /* bool isNull() const; */

    TS_ASSERT(!a_bool->isNull());
    TS_ASSERT(!b_bool->isNull());
    TS_ASSERT(!c_bool_and->isNull());
    TS_ASSERT(!and_op->isNull());
    TS_ASSERT(!plus_op->isNull());
    TS_ASSERT(!d_apply_fun_bool->isNull());
    TS_ASSERT(null->isNull());
  }

  void testIsConst() {
    /* bool isConst() const; */

    //Debug.on("isConst");

    TS_ASSERT(!a_bool->isConst());
    TS_ASSERT(!b_bool->isConst());
    TS_ASSERT(!c_bool_and->isConst());
    TS_ASSERT(and_op->isConst());
    TS_ASSERT(plus_op->isConst());
    TS_ASSERT(!d_apply_fun_bool->isConst());
    TS_ASSERT(!null->isConst());

    // more complicated "constants" exist in datatypes and arrays theories
    Datatype list(d_em, "list");
    DatatypeConstructor consC("cons");
    consC.addArg("car", d_em->integerType());
    consC.addArg("cdr", DatatypeSelfType());
    list.addConstructor(consC);
    list.addConstructor(DatatypeConstructor("nil"));
    DatatypeType listType = d_em->mkDatatypeType(list);
    Expr cons = listType.getDatatype().getConstructor("cons");
    Expr nil = listType.getDatatype().getConstructor("nil");
    Expr x = d_em->mkVar("x", d_em->integerType());
    Expr cons_x_nil = d_em->mkExpr(APPLY_CONSTRUCTOR, cons, x, d_em->mkExpr(APPLY_CONSTRUCTOR, nil));
    Expr cons_1_nil = d_em->mkExpr(APPLY_CONSTRUCTOR, cons, d_em->mkConst(Rational(1)), d_em->mkExpr(APPLY_CONSTRUCTOR, nil));
    Expr cons_1_cons_2_nil = d_em->mkExpr(APPLY_CONSTRUCTOR, cons, d_em->mkConst(Rational(1)), d_em->mkExpr(APPLY_CONSTRUCTOR, cons, d_em->mkConst(Rational(2)), d_em->mkExpr(APPLY_CONSTRUCTOR, nil)));
    TS_ASSERT(d_em->mkExpr(APPLY_CONSTRUCTOR, nil).isConst());
    TS_ASSERT(!cons_x_nil.isConst());
    TS_ASSERT(cons_1_nil.isConst());
    TS_ASSERT(cons_1_cons_2_nil.isConst());

    {
      ExprManagerScope ems(*d_em);
      ArrayType arrType =
          d_em->mkArrayType(d_em->integerType(), d_em->integerType());
      Expr zero = d_em->mkConst(Rational(0));
      Expr one = d_em->mkConst(Rational(1));
      Expr storeAll = d_em->mkConst(
          ArrayStoreAll(TypeNode::fromType(arrType), Node::fromExpr(zero)));
      TS_ASSERT(storeAll.isConst());

      Expr arr = d_em->mkExpr(STORE, storeAll, zero, zero);
      TS_ASSERT(!arr.isConst());
      arr = d_em->mkExpr(STORE, storeAll, zero, one);
      TS_ASSERT(arr.isConst());
      Expr arr2 = d_em->mkExpr(STORE, arr, one, zero);
      TS_ASSERT(!arr2.isConst());
      arr2 = d_em->mkExpr(STORE, arr, one, one);
      TS_ASSERT(arr2.isConst());
      arr2 = d_em->mkExpr(STORE, arr, zero, one);
      TS_ASSERT(!arr2.isConst());

      arrType =
          d_em->mkArrayType(d_em->mkBitVectorType(1), d_em->mkBitVectorType(1));
      zero = d_em->mkConst(BitVector(1, unsigned(0)));
      one = d_em->mkConst(BitVector(1, unsigned(1)));
      storeAll = d_em->mkConst(
          ArrayStoreAll(TypeNode::fromType(arrType), Node::fromExpr(zero)));
      TS_ASSERT(storeAll.isConst());

      arr = d_em->mkExpr(STORE, storeAll, zero, zero);
      TS_ASSERT(!arr.isConst());
      arr = d_em->mkExpr(STORE, storeAll, zero, one);
      TS_ASSERT(arr.isConst());
      arr2 = d_em->mkExpr(STORE, arr, one, zero);
      TS_ASSERT(!arr2.isConst());
      arr2 = d_em->mkExpr(STORE, arr, one, one);
      TS_ASSERT(!arr2.isConst());
      arr2 = d_em->mkExpr(STORE, arr, zero, one);
      TS_ASSERT(!arr2.isConst());
    }
  }

  void testGetConst() {
    /* template <class T>
       const T& getConst() const; */

    TS_ASSERT_THROWS(a_bool->getConst<Kind>(), IllegalArgumentException&);
    TS_ASSERT_THROWS(b_bool->getConst<Kind>(), IllegalArgumentException&);
    TS_ASSERT_THROWS(c_bool_and->getConst<Kind>(), IllegalArgumentException&);
    TS_ASSERT(and_op->getConst<Kind>() == AND);
    TS_ASSERT_THROWS(and_op->getConst<Rational>(), IllegalArgumentException&);
    TS_ASSERT(plus_op->getConst<Kind>() == PLUS);
    TS_ASSERT_THROWS(plus_op->getConst<Rational>(), IllegalArgumentException&);
    TS_ASSERT_THROWS(d_apply_fun_bool->getConst<Kind>(),
                     IllegalArgumentException&);
    TS_ASSERT_THROWS(null->getConst<Kind>(), IllegalArgumentException&);

    TS_ASSERT(i1->getConst<Rational>() == 0);
    TS_ASSERT(i2->getConst<Rational>() == 23);
    TS_ASSERT(r1->getConst<Rational>() == Rational(1, 5));
    TS_ASSERT(r2->getConst<Rational>() == Rational("0"));

    TS_ASSERT_THROWS(i1->getConst<Kind>(), IllegalArgumentException&);
    TS_ASSERT_THROWS(i2->getConst<Kind>(), IllegalArgumentException&);
    TS_ASSERT_THROWS(r1->getConst<Kind>(), IllegalArgumentException&);
    TS_ASSERT_THROWS(r2->getConst<Kind>(), IllegalArgumentException&);
  }

  void testGetExprManager() {
    /* ExprManager* getExprManager() const; */

    TS_ASSERT(a_bool->getExprManager() == d_em);
    TS_ASSERT(b_bool->getExprManager() == d_em);
    TS_ASSERT(c_bool_and->getExprManager() == d_em);
    TS_ASSERT(and_op->getExprManager() == d_em);
    TS_ASSERT(plus_op->getExprManager() == d_em);
    TS_ASSERT(d_apply_fun_bool->getExprManager() == d_em);
    TS_ASSERT(null->getExprManager() == NULL);

    TS_ASSERT(i1->getExprManager() == d_em);
    TS_ASSERT(i2->getExprManager() == d_em);
    TS_ASSERT(r1->getExprManager() == d_em);
    TS_ASSERT(r2->getExprManager() == d_em);
  }

 private:
  Options opts;

  api::Solver* d_slv;
  ExprManager* d_em;

  Expr* a_bool;
  Expr* b_bool;
  Expr* c_bool_and;
  Expr* and_op;
  Expr* plus_op;
  Type* fun_type;
  Expr* fun_op;
  Expr* d_apply_fun_bool;
  Expr* null;

  Expr* i1;
  Expr* i2;
  Expr* r1;
  Expr* r2;
};

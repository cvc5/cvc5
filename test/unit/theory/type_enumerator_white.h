/*********************                                                        */
/*! \file type_enumerator_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::theory::TypeEnumerator
 **
 ** White box testing of CVC4::theory::TypeEnumerator.  (These tests depends
 ** on the ordering that the TypeEnumerators use, so it's a white-box test.)
 **/

#include <cxxtest/TestSuite.h>

#include <unordered_set>

#include "expr/array_store_all.h"
#include "expr/expr_manager.h"
#include "expr/kind.h"
#include "expr/node_manager.h"
#include "expr/type_node.h"
#include "options/language.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/type_enumerator.h"

using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::theory;
using namespace CVC4::kind;

using namespace std;

class TypeEnumeratorWhite : public CxxTest::TestSuite {
 public:
  void setUp() override
  {
    d_em = new ExprManager();
    d_smt = new SmtEngine(d_em);
    d_nm = NodeManager::fromExprManager(d_em);
    d_scope = new SmtScope(d_smt);
    d_smt->finalOptionsAreSet();
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void testBooleans() {
    TypeEnumerator te(d_nm->booleanType());
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*te, d_nm->mkConst(false));
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(true));
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_THROWS(*++te, NoMoreValuesException&);
    TS_ASSERT( te.isFinished() );
    TS_ASSERT_THROWS(*++te, NoMoreValuesException&);
    TS_ASSERT( te.isFinished() );
    TS_ASSERT_THROWS(*++te, NoMoreValuesException&);
    TS_ASSERT( te.isFinished() );
  }

  void testUF() {
    TypeNode sortn = d_nm->mkSort("T");
    Type sort = sortn.toType();
    TypeNode sortn2 = d_nm->mkSort("U");
    Type sort2 = sortn2.toType();
    TypeEnumerator te(sortn);
    TS_ASSERT_EQUALS(*te, d_nm->mkConst(UninterpretedConstant(sort, 0)));
    for(size_t i = 1; i < 100; ++i) {
      TS_ASSERT_DIFFERS(*te, d_nm->mkConst(UninterpretedConstant(sort, i)));
      TS_ASSERT_DIFFERS(*te, d_nm->mkConst(UninterpretedConstant(sort2, i)));
      TS_ASSERT_EQUALS(*++te, d_nm->mkConst(UninterpretedConstant(sort, i)));
      TS_ASSERT_DIFFERS(*te, d_nm->mkConst(UninterpretedConstant(sort, i + 2)));
    }
  }

  void testArith() {
    TypeEnumerator te(d_nm->integerType());
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*te, d_nm->mkConst(Rational(0)));
    for(int i = 1; i <= 100; ++i) {
      TS_ASSERT( ! te.isFinished() );
      TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(i)));
      TS_ASSERT( ! te.isFinished() );
      TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-i)));
    }
    TS_ASSERT( ! te.isFinished() );

    te = TypeEnumerator(d_nm->realType());
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*te, d_nm->mkConst(Rational(0, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(1, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-1, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(2, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-2, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(1, 2)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-1, 2)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(3, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-3, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(1, 3)));
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-1, 3)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(4, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-4, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(3, 2)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-3, 2)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(2, 3)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-2, 3)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(1, 4)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-1, 4)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(5, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-5, 1)));
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(1, 5)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-1, 5)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(6, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-6, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(5, 2)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-5, 2)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(4, 3)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-4, 3)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(3, 4)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-3, 4)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(2, 5)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-2, 5)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(1, 6)));
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-1, 6)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(7, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-7, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(5, 3)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-5, 3)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(3, 5)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-3, 5)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(1, 7)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-1, 7)));
    TS_ASSERT( ! te.isFinished() );
  }

  void testDatatypesFinite() {
    Datatype dt(d_em, "Colors");
    dt.addConstructor(DatatypeConstructor("red"));
    dt.addConstructor(DatatypeConstructor("orange"));
    dt.addConstructor(DatatypeConstructor("yellow"));
    dt.addConstructor(DatatypeConstructor("green"));
    dt.addConstructor(DatatypeConstructor("blue"));
    dt.addConstructor(DatatypeConstructor("violet"));
    TypeNode datatype = TypeNode::fromType(d_em->mkDatatypeType(dt));
    TypeEnumerator te(datatype);
    TS_ASSERT_EQUALS(*te, d_nm->mkNode(APPLY_CONSTRUCTOR, DatatypeType(datatype.toType()).getDatatype().getConstructor("red")));
    TS_ASSERT_EQUALS(*++te, d_nm->mkNode(APPLY_CONSTRUCTOR, DatatypeType(datatype.toType()).getDatatype().getConstructor("orange")));
    TS_ASSERT_EQUALS(*++te, d_nm->mkNode(APPLY_CONSTRUCTOR, DatatypeType(datatype.toType()).getDatatype().getConstructor("yellow")));
    TS_ASSERT_EQUALS(*++te, d_nm->mkNode(APPLY_CONSTRUCTOR, DatatypeType(datatype.toType()).getDatatype().getConstructor("green")));
    TS_ASSERT_EQUALS(*++te, d_nm->mkNode(APPLY_CONSTRUCTOR, DatatypeType(datatype.toType()).getDatatype().getConstructor("blue")));
    TS_ASSERT_EQUALS(*++te, d_nm->mkNode(APPLY_CONSTRUCTOR, DatatypeType(datatype.toType()).getDatatype().getConstructor("violet")));
    TS_ASSERT_THROWS(*++te, NoMoreValuesException&);
    TS_ASSERT_THROWS(*++te, NoMoreValuesException&);
    TS_ASSERT_THROWS(*++te, NoMoreValuesException&);
  }

  void testDatatypesInfinite1() {
    Datatype colors(d_em, "Colors");
    colors.addConstructor(DatatypeConstructor("red"));
    colors.addConstructor(DatatypeConstructor("orange"));
    colors.addConstructor(DatatypeConstructor("yellow"));
    colors.addConstructor(DatatypeConstructor("green"));
    colors.addConstructor(DatatypeConstructor("blue"));
    colors.addConstructor(DatatypeConstructor("violet"));
    TypeNode colorsType = TypeNode::fromType(d_em->mkDatatypeType(colors));
    Datatype listColors(d_em, "ListColors");
    DatatypeConstructor consC("cons");
    consC.addArg("car", colorsType.toType());
    consC.addArg("cdr", DatatypeSelfType());
    listColors.addConstructor(consC);
    listColors.addConstructor(DatatypeConstructor("nil"));
    TypeNode listColorsType = TypeNode::fromType(d_em->mkDatatypeType(listColors));

    TypeEnumerator te(listColorsType);
    TS_ASSERT( ! te.isFinished() );
    Node cons = Node::fromExpr(DatatypeType(listColorsType.toType()).getDatatype().getConstructor("cons"));
    Node nil = d_nm->mkNode(APPLY_CONSTRUCTOR, DatatypeType(listColorsType.toType()).getDatatype().getConstructor("nil"));
    Node red = d_nm->mkNode(APPLY_CONSTRUCTOR, DatatypeType(colorsType.toType()).getDatatype().getConstructor("red"));
    Node orange = d_nm->mkNode(APPLY_CONSTRUCTOR, DatatypeType(colorsType.toType()).getDatatype().getConstructor("orange"));
    Node yellow = d_nm->mkNode(APPLY_CONSTRUCTOR, DatatypeType(colorsType.toType()).getDatatype().getConstructor("yellow"));
    TS_ASSERT_EQUALS(*te, nil);
    TS_ASSERT_EQUALS(*++te, d_nm->mkNode(APPLY_CONSTRUCTOR, cons, red, nil));
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*++te, d_nm->mkNode(APPLY_CONSTRUCTOR, cons, red,
                            d_nm->mkNode(APPLY_CONSTRUCTOR, cons, red, nil)));
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*++te, d_nm->mkNode(APPLY_CONSTRUCTOR, cons, orange, nil));
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*++te, d_nm->mkNode(APPLY_CONSTRUCTOR, cons, red,
                            d_nm->mkNode(APPLY_CONSTRUCTOR, cons, red,
                            d_nm->mkNode(APPLY_CONSTRUCTOR, cons, red, nil))));
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*++te, d_nm->mkNode(APPLY_CONSTRUCTOR, cons, orange,
                            d_nm->mkNode(APPLY_CONSTRUCTOR, cons, red, nil)));
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*++te, d_nm->mkNode(APPLY_CONSTRUCTOR, cons, yellow, nil));
    TS_ASSERT( ! te.isFinished() );
    TS_ASSERT_EQUALS(*++te, d_nm->mkNode(APPLY_CONSTRUCTOR, cons, red,
                            d_nm->mkNode(APPLY_CONSTRUCTOR, cons, orange, nil)));
    TS_ASSERT( ! te.isFinished() );
  }

  void NOTYETtestDatatypesInfinite2() {
    //TypeNode datatype;
    //TypeEnumerator te(datatype);
    //TS_ASSERT( ! te.isFinished() );
    TS_FAIL("unimplemented");
  }

  void testArraysInfinite() {
    TypeEnumerator te(d_nm->mkArrayType(d_nm->integerType(), d_nm->integerType()));
    unordered_set<Node, NodeHashFunction> elts;
    for(size_t i = 0; i < 1000; ++i) {
      TS_ASSERT( ! te.isFinished() );
      Node elt = *te++;
      // ensure no duplicates
      TS_ASSERT( elts.find(elt) == elts.end() );
      elts.insert(elt);
    }
    TS_ASSERT( ! te.isFinished() );

    // ensure that certain items were found
    ArrayType arrayType(d_em->mkArrayType(d_em->integerType(), d_em->integerType()));
    Node zeroes = d_nm->mkConst(ArrayStoreAll(arrayType, d_em->mkConst(Rational(0))));
    Node ones = d_nm->mkConst(ArrayStoreAll(arrayType, d_em->mkConst(Rational(1))));
    Node twos = d_nm->mkConst(ArrayStoreAll(arrayType, d_em->mkConst(Rational(2))));
    Node threes = d_nm->mkConst(ArrayStoreAll(arrayType, d_em->mkConst(Rational(3))));
    Node fours = d_nm->mkConst(ArrayStoreAll(arrayType, d_em->mkConst(Rational(4))));
    Node tens = d_nm->mkConst(ArrayStoreAll(arrayType, d_em->mkConst(Rational(10))));

    Node zero = d_nm->mkConst(Rational(0));
    Node one = d_nm->mkConst(Rational(1));
    Node two = d_nm->mkConst(Rational(2));
    Node three = d_nm->mkConst(Rational(3));
    Node four = d_nm->mkConst(Rational(4));
    Node five = d_nm->mkConst(Rational(5));
    Node eleven = d_nm->mkConst(Rational(11));

    // FIXME: the arrays enumerator isn't currently a fair enumerator,
    // so these will fail; disable them for now
    //TS_ASSERT( elts.find( d_nm->mkNode(STORE, ones, zero, zero) ) != elts.end() );
    //TS_ASSERT( elts.find( d_nm->mkNode(STORE, tens, four, five) ) != elts.end() );
    //TS_ASSERT( elts.find( d_nm->mkNode(STORE, d_nm->mkNode(STORE, d_nm->mkNode(STORE, fours, eleven, two), two, one), zero, two) ) != elts.end() );
    //TS_ASSERT( elts.find( threes ) != elts.end() );
    //TS_ASSERT( elts.find( d_nm->mkNode(STORE, d_nm->mkNode(STORE, d_nm->mkNode(STORE, d_nm->mkNode(STORE, twos, three, zero), two, zero), one, zero), zero, zero) ) != elts.end() );
  }

  void testBV() {
    TypeEnumerator te(d_nm->mkBitVectorType(3));
    TS_ASSERT_EQUALS(*te, d_nm->mkConst(BitVector(3u, 0u)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(BitVector(3u, 1u)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(BitVector(3u, 2u)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(BitVector(3u, 3u)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(BitVector(3u, 4u)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(BitVector(3u, 5u)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(BitVector(3u, 6u)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(BitVector(3u, 7u)));
    TS_ASSERT_THROWS(*++te, NoMoreValuesException&);
    TS_ASSERT_THROWS(*++te, NoMoreValuesException&);
    TS_ASSERT_THROWS(*++te, NoMoreValuesException&);
  }

 private:
  ExprManager* d_em;
  SmtEngine* d_smt;
  NodeManager* d_nm;
  SmtScope* d_scope;
};/* class TypeEnumeratorWhite */

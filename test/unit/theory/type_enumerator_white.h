/*********************                                                        */
/*! \file type_enumerator_white.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief White box testing of CVC4::theory::TypeEnumerator
 **
 ** White box testing of CVC4::theory::TypeEnumerator.  (These tests depends
 ** on the ordering that the TypeEnumerators use, so it's a white-box test.)
 **/

#include <cxxtest/TestSuite.h>

#include "expr/node_manager.h"
#include "expr/expr_manager.h"
#include "expr/type_node.h"
#include "expr/kind.h"
#include "theory/type_enumerator.h"
#include "util/language.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::kind;

using namespace std;

class TypeEnumeratorWhite : public CxxTest::TestSuite {
  ExprManager* d_em;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

public:

  void setUp() {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_scope = new NodeManagerScope(d_nm);
  }

  void tearDown() {
    delete d_scope;
    delete d_em;
  }

  void testBooleans() {
    TypeEnumerator te(d_nm->booleanType());
    TS_ASSERT_EQUALS(*te, d_nm->mkConst(false));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(true));
    TS_ASSERT_THROWS(*++te, NoMoreValuesException);
    TS_ASSERT_THROWS(*++te, NoMoreValuesException);
    TS_ASSERT_THROWS(*++te, NoMoreValuesException);
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
    TS_ASSERT_EQUALS(*te, d_nm->mkConst(Rational(0)));
    for(int i = 1; i <= 100; ++i) {
      TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(i)));
      TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-i)));
    }

    te = TypeEnumerator(d_nm->realType());
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
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-1, 6)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(7, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-7, 1)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(5, 3)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-5, 3)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(3, 5)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-3, 5)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(1, 7)));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(Rational(-1, 7)));
  }

  void testDatatypesFinite() {
    Datatype dt("Colors");
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
    TS_ASSERT_THROWS(*++te, NoMoreValuesException);
    TS_ASSERT_THROWS(*++te, NoMoreValuesException);
    TS_ASSERT_THROWS(*++te, NoMoreValuesException);
  }

  void NOtestDatatypesInfinite() {
    TypeNode datatype;
    TypeEnumerator te(datatype);
    TS_FAIL("unimplemented");
  }

  void NOtestArraysInfinite() {
    TypeEnumerator te(d_nm->mkArrayType(d_nm->integerType(), d_nm->integerType()));

    TS_FAIL("unimplemented");
  }

  // remove this when ArrayConst is available
  template <class T, class U> inline bool ArrayConst(const T&, const U&) { return false; }

  void NOtestArraysFinite() {
    TypeEnumerator te(d_nm->mkArrayType(d_nm->mkBitVectorType(2), d_nm->booleanType()));
    TS_ASSERT_EQUALS(*te, d_nm->mkConst(ArrayConst(d_nm->mkConst(BitVector(0)), d_nm->mkConst(false))));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(ArrayConst(d_nm->mkConst(BitVector(0)), d_nm->mkConst(true))));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(ArrayConst(d_nm->mkConst(BitVector(1)), d_nm->mkConst(false))));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(ArrayConst(d_nm->mkConst(BitVector(1)), d_nm->mkConst(true))));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(ArrayConst(d_nm->mkConst(BitVector(2)), d_nm->mkConst(false))));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(ArrayConst(d_nm->mkConst(BitVector(2)), d_nm->mkConst(true))));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(ArrayConst(d_nm->mkConst(BitVector(3)), d_nm->mkConst(false))));
    TS_ASSERT_EQUALS(*++te, d_nm->mkConst(ArrayConst(d_nm->mkConst(BitVector(3)), d_nm->mkConst(true))));
    TS_ASSERT_THROWS(*++te, NoMoreValuesException);
    TS_ASSERT_THROWS(*++te, NoMoreValuesException);
    TS_ASSERT_THROWS(*++te, NoMoreValuesException);
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
    TS_ASSERT_THROWS(*++te, NoMoreValuesException);
    TS_ASSERT_THROWS(*++te, NoMoreValuesException);
    TS_ASSERT_THROWS(*++te, NoMoreValuesException);
  }

};/* class TypeEnumeratorWhite */

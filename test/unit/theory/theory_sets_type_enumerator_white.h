/*********************                                                        */
/*! \file theory_sets_type_enumerator_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed, Andres Noetzli, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::theory::sets::SetEnumerator
 **
 ** White box testing of CVC4::theory::sets::SetEnumerator.  (These tests
 ** depends  on the ordering that the SetEnumerator use, so it's a white-box
 *  test.)
 **/

#include <cxxtest/TestSuite.h>

#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/sets/theory_sets_type_enumerator.h"

using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::theory;
using namespace CVC4::kind;
using namespace CVC4::theory::sets;
using namespace std;

class SetEnumeratorWhite : public CxxTest::TestSuite
{
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

  void testSetOfBooleans()
  {
    TypeNode boolType = d_nm->booleanType();
    SetEnumerator setEnumerator(d_nm->mkSetType(boolType));
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual0 = *setEnumerator;
    Node expected0 =
        d_nm->mkConst(EmptySet(d_nm->mkSetType(boolType)));
    TS_ASSERT_EQUALS(expected0, actual0);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual1 = *++setEnumerator;
    Node expected1 = d_nm->mkNode(Kind::SINGLETON, d_nm->mkConst(false));
    TS_ASSERT_EQUALS(expected1, actual1);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual2 = *++setEnumerator;
    Node expected2 = d_nm->mkNode(Kind::SINGLETON, d_nm->mkConst(true));
    TS_ASSERT_EQUALS(expected2, actual2);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual3 = Rewriter::rewrite(*++setEnumerator);
    Node expected3 =
        Rewriter::rewrite(d_nm->mkNode(Kind::UNION, expected1, expected2));
    TS_ASSERT_EQUALS(expected3, actual3);
    TS_ASSERT(!setEnumerator.isFinished());

    TS_ASSERT_THROWS(*++setEnumerator, NoMoreValuesException&);
    TS_ASSERT(setEnumerator.isFinished());
    TS_ASSERT_THROWS(*++setEnumerator, NoMoreValuesException&);
    TS_ASSERT(setEnumerator.isFinished());
    TS_ASSERT_THROWS(*++setEnumerator, NoMoreValuesException&);
    TS_ASSERT(setEnumerator.isFinished());
  }

  void testSetOfUF()
  {
    TypeNode sort = d_nm->mkSort("Atom");
    SetEnumerator setEnumerator(d_nm->mkSetType(sort));

    Node actual0 = *setEnumerator;
    Node expected0 = d_nm->mkConst(EmptySet(d_nm->mkSetType(sort)));
    TS_ASSERT_EQUALS(expected0, actual0);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual1 = *++setEnumerator;
    Node expected1 = d_nm->mkNode(
        Kind::SINGLETON, d_nm->mkConst(UninterpretedConstant(sort, 0)));
    TS_ASSERT_EQUALS(expected1, actual1);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual2 = *++setEnumerator;
    Node expected2 = d_nm->mkNode(
        Kind::SINGLETON, d_nm->mkConst(UninterpretedConstant(sort, 1)));
    TS_ASSERT_EQUALS(expected2, actual2);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual3 = *++setEnumerator;
    Node expected3 = d_nm->mkNode(Kind::UNION, expected1, expected2);
    TS_ASSERT_EQUALS(expected3, actual3);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual4 = *++setEnumerator;
    Node expected4 = d_nm->mkNode(
        Kind::SINGLETON, d_nm->mkConst(UninterpretedConstant(sort, 2)));
    TS_ASSERT_EQUALS(expected4, actual4);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual5 = *++setEnumerator;
    Node expected5 = d_nm->mkNode(Kind::UNION, expected1, expected4);
    TS_ASSERT_EQUALS(expected5, actual5);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual6 = *++setEnumerator;
    Node expected6 = d_nm->mkNode(Kind::UNION, expected2, expected4);
    TS_ASSERT_EQUALS(expected6, actual6);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual7 = *++setEnumerator;
    Node expected7 = d_nm->mkNode(Kind::UNION, expected3, expected4);
    TS_ASSERT_EQUALS(expected7, actual7);
    TS_ASSERT(!setEnumerator.isFinished());
  }

  void testSetOfFiniteDatatype()
  {
    Datatype dt(d_em, "Colors");
    dt.addConstructor(DatatypeConstructor("red"));
    dt.addConstructor(DatatypeConstructor("green"));
    dt.addConstructor(DatatypeConstructor("blue"));
    TypeNode datatype = TypeNode::fromType(d_em->mkDatatypeType(dt));
    SetEnumerator setEnumerator(d_nm->mkSetType(datatype));

    Node red = d_nm->mkNode(
        APPLY_CONSTRUCTOR,
        DatatypeType(datatype.toType()).getDatatype().getConstructor("red"));

    Node green = d_nm->mkNode(
        APPLY_CONSTRUCTOR,
        DatatypeType(datatype.toType()).getDatatype().getConstructor("green"));

    Node blue = d_nm->mkNode(
        APPLY_CONSTRUCTOR,
        DatatypeType(datatype.toType()).getDatatype().getConstructor("blue"));

    Node actual0 = *setEnumerator;
    Node expected0 =
        d_nm->mkConst(EmptySet(d_nm->mkSetType(datatype)));
    TS_ASSERT_EQUALS(expected0, actual0);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual1 = *++setEnumerator;
    Node expected1 = d_nm->mkNode(Kind::SINGLETON, red);
    TS_ASSERT_EQUALS(expected1, actual1);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual2 = *++setEnumerator;
    Node expected2 = d_nm->mkNode(Kind::SINGLETON, green);
    TS_ASSERT_EQUALS(expected2, actual2);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual3 = *++setEnumerator;
    Node expected3 = d_nm->mkNode(Kind::UNION, expected1, expected2);
    TS_ASSERT_EQUALS(expected3, actual3);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual4 = *++setEnumerator;
    Node expected4 = d_nm->mkNode(Kind::SINGLETON, blue);
    TS_ASSERT_EQUALS(expected4, actual4);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual5 = *++setEnumerator;
    Node expected5 = d_nm->mkNode(Kind::UNION, expected1, expected4);
    TS_ASSERT_EQUALS(expected5, actual5);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual6 = *++setEnumerator;
    Node expected6 = d_nm->mkNode(Kind::UNION, expected2, expected4);
    TS_ASSERT_EQUALS(expected6, actual6);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual7 = *++setEnumerator;
    Node expected7 = d_nm->mkNode(Kind::UNION, expected3, expected4);
    TS_ASSERT_EQUALS(expected7, actual7);
    TS_ASSERT(!setEnumerator.isFinished());

    TS_ASSERT_THROWS(*++setEnumerator, NoMoreValuesException&);
    TS_ASSERT(setEnumerator.isFinished());
    TS_ASSERT_THROWS(*++setEnumerator, NoMoreValuesException&);
    TS_ASSERT(setEnumerator.isFinished());
    TS_ASSERT_THROWS(*++setEnumerator, NoMoreValuesException&);
    TS_ASSERT(setEnumerator.isFinished());
  }

  void testBV()
  {
    TypeNode bitVector2 = d_nm->mkBitVectorType(2);
    SetEnumerator setEnumerator(d_nm->mkSetType(bitVector2));
    Node zero = d_nm->mkConst(BitVector(2u, 0u));
    Node one = d_nm->mkConst(BitVector(2u, 1u));
    Node two = d_nm->mkConst(BitVector(2u, 2u));
    Node three = d_nm->mkConst(BitVector(2u, 3u));
    Node four = d_nm->mkConst(BitVector(2u, 4u));

    Node actual0 = *setEnumerator;
    Node expected0 =
        d_nm->mkConst(EmptySet(d_nm->mkSetType(bitVector2)));
    TS_ASSERT_EQUALS(expected0, actual0);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual1 = *++setEnumerator;
    Node expected1 = d_nm->mkNode(Kind::SINGLETON, zero);
    TS_ASSERT_EQUALS(expected1, actual1);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual2 = *++setEnumerator;
    Node expected2 = d_nm->mkNode(Kind::SINGLETON, one);
    TS_ASSERT_EQUALS(expected2, actual2);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual3 = *++setEnumerator;
    Node expected3 = d_nm->mkNode(Kind::UNION, expected1, expected2);
    TS_ASSERT_EQUALS(expected3, actual3);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual4 = *++setEnumerator;
    Node expected4 = d_nm->mkNode(Kind::SINGLETON, two);
    TS_ASSERT_EQUALS(expected4, actual4);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual5 = *++setEnumerator;
    Node expected5 = d_nm->mkNode(Kind::UNION, expected1, expected4);
    TS_ASSERT_EQUALS(expected5, actual5);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual6 = *++setEnumerator;
    Node expected6 = d_nm->mkNode(Kind::UNION, expected2, expected4);
    TS_ASSERT_EQUALS(expected6, actual6);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual7 = *++setEnumerator;
    Node expected7 = d_nm->mkNode(Kind::UNION, expected3, expected4);
    TS_ASSERT_EQUALS(expected7, actual7);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual8 = *++setEnumerator;
    Node expected8 = d_nm->mkNode(Kind::SINGLETON, three);
    TS_ASSERT_EQUALS(expected8, actual8);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual9 = *++setEnumerator;
    Node expected9 = d_nm->mkNode(Kind::UNION, expected1, expected8);
    TS_ASSERT_EQUALS(expected9, actual9);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual10 = *++setEnumerator;
    Node expected10 = d_nm->mkNode(Kind::UNION, expected2, expected8);
    TS_ASSERT_EQUALS(expected10, actual10);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual11 = *++setEnumerator;
    Node expected11 = d_nm->mkNode(Kind::UNION, expected3, expected8);
    TS_ASSERT_EQUALS(expected11, actual11);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual12 = *++setEnumerator;
    Node expected12 = d_nm->mkNode(Kind::UNION, expected4, expected8);
    TS_ASSERT_EQUALS(expected12, actual12);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual13 = *++setEnumerator;
    Node expected13 = d_nm->mkNode(Kind::UNION, expected5, expected8);
    TS_ASSERT_EQUALS(expected13, actual13);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual14 = *++setEnumerator;
    Node expected14 = d_nm->mkNode(Kind::UNION, expected6, expected8);
    TS_ASSERT_EQUALS(expected14, actual14);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual15 = *++setEnumerator;
    Node expected15 = d_nm->mkNode(Kind::UNION, expected7, expected8);
    TS_ASSERT_EQUALS(expected15, actual15);
    TS_ASSERT(!setEnumerator.isFinished());

    TS_ASSERT_THROWS(*++setEnumerator, NoMoreValuesException&);
    TS_ASSERT(setEnumerator.isFinished());
    TS_ASSERT_THROWS(*++setEnumerator, NoMoreValuesException&);
    TS_ASSERT(setEnumerator.isFinished());
    TS_ASSERT_THROWS(*++setEnumerator, NoMoreValuesException&);
    TS_ASSERT(setEnumerator.isFinished());
  }

 private:
  ExprManager* d_em;
  SmtEngine* d_smt;
  NodeManager* d_nm;
  SmtScope* d_scope;
}; /* class SetEnumeratorWhite */

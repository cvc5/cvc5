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
  
  void addAndCheckUnique(Node n, std::vector<Node>& elems)
  {
    TS_ASSERT(n.isConst());
    TS_ASSERT(std::find(elems.begin(),elems.end(),n)==elems.end());
    elems.push_back(n);
  }

  void testSetOfBooleans()
  {
    TypeNode boolType = d_nm->booleanType();
    SetEnumerator setEnumerator(d_nm->mkSetType(boolType));
    TS_ASSERT(!setEnumerator.isFinished());

    std::vector<Node> elems;
    
    Node actual0 = *setEnumerator;
    addAndCheckUnique(actual0, elems);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual1 = *++setEnumerator;
    addAndCheckUnique(actual1, elems);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual2 = *++setEnumerator;
    addAndCheckUnique(actual2, elems);
    TS_ASSERT(!setEnumerator.isFinished());

    Node actual3 = Rewriter::rewrite(*++setEnumerator);
    addAndCheckUnique(actual3, elems);
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
    
    std::vector<Node> elems;
    for (unsigned i=0; i<7; i++)
    {
      Node actual = *setEnumerator;
      addAndCheckUnique(actual, elems);
      TS_ASSERT(!setEnumerator.isFinished());
      ++setEnumerator;
    }
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

    std::vector<Node> elems;
    for (unsigned i=0; i<8; i++)
    {
      Node actual = *setEnumerator;
      addAndCheckUnique(actual, elems);
      TS_ASSERT(!setEnumerator.isFinished());
      ++setEnumerator;
    }

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

    std::vector<Node> elems;
    for (unsigned i=0; i<16; i++)
    {
      Node actual = *setEnumerator;
      addAndCheckUnique(actual, elems);
      TS_ASSERT(!setEnumerator.isFinished());
      ++setEnumerator;
    }

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

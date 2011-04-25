/*********************                                                        */
/*! \file type_cardinality_public.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Public box testing of Type::getCardinality() for various Types
 **
 ** Public box testing of Type::getCardinality() for various Types.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <string>
#include <sstream>

#include "expr/kind.h"
#include "expr/type.h"
#include "expr/expr_manager.h"
#include "util/cardinality.h"
#include "util/Assert.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

class TypeCardinalityPublic : public CxxTest::TestSuite {
  ExprManager* d_em;

public:

  void setUp() {
    d_em = new ExprManager();
  }

  void tearDown() {
    delete d_em;
  }

  void testTheBasics() {
    TS_ASSERT( d_em->booleanType().getCardinality() == 2 );
    TS_ASSERT( d_em->integerType().getCardinality() == Cardinality::INTEGERS );
    TS_ASSERT( d_em->realType().getCardinality() == Cardinality::REALS );
  }

  void testArrays() {
    Type intToInt = d_em->mkArrayType(d_em->integerType(), d_em->integerType());
    Type realToReal = d_em->mkArrayType(d_em->realType(), d_em->realType());
    Type realToInt = d_em->mkArrayType(d_em->realType(), d_em->integerType());
    Type intToReal = d_em->mkArrayType(d_em->integerType(), d_em->realType());
    Type intToBool = d_em->mkArrayType(d_em->integerType(), d_em->booleanType());
    Type realToBool = d_em->mkArrayType(d_em->realType(), d_em->booleanType());
    Type boolToReal = d_em->mkArrayType(d_em->booleanType(), d_em->realType());
    Type boolToInt = d_em->mkArrayType(d_em->booleanType(), d_em->integerType());
    Type boolToBool = d_em->mkArrayType(d_em->booleanType(), d_em->booleanType());

    TS_ASSERT( intToInt.getCardinality() == Cardinality::REALS );
    TS_ASSERT( realToReal.getCardinality() > Cardinality::REALS );
    TS_ASSERT( realToInt.getCardinality() > Cardinality::REALS );
    TS_ASSERT( intToReal.getCardinality() == Cardinality::REALS );
    TS_ASSERT( intToBool.getCardinality() == Cardinality::REALS );
    TS_ASSERT( realToBool.getCardinality() > Cardinality::REALS );
    TS_ASSERT( boolToReal.getCardinality() == Cardinality::REALS );
    TS_ASSERT( boolToInt.getCardinality() == Cardinality::INTEGERS );
    TS_ASSERT( boolToBool.getCardinality() == 4 );
  }

  void testUnaryFunctions() {
    Type intToInt = d_em->mkFunctionType(d_em->integerType(), d_em->integerType());
    Type realToReal = d_em->mkFunctionType(d_em->realType(), d_em->realType());
    Type realToInt = d_em->mkFunctionType(d_em->realType(), d_em->integerType());
    Type intToReal = d_em->mkFunctionType(d_em->integerType(), d_em->realType());
    Type intToBool = d_em->mkFunctionType(d_em->integerType(), d_em->booleanType());
    Type realToBool = d_em->mkFunctionType(d_em->realType(), d_em->booleanType());
    Type boolToReal = d_em->mkFunctionType(d_em->booleanType(), d_em->realType());
    Type boolToInt = d_em->mkFunctionType(d_em->booleanType(), d_em->integerType());
    Type boolToBool = d_em->mkFunctionType(d_em->booleanType(), d_em->booleanType());

    TS_ASSERT( intToInt.getCardinality() == Cardinality::REALS );
    TS_ASSERT( realToReal.getCardinality() > Cardinality::REALS );
    TS_ASSERT( realToInt.getCardinality() > Cardinality::REALS );
    TS_ASSERT( intToReal.getCardinality() == Cardinality::REALS );
    TS_ASSERT( intToBool.getCardinality() == Cardinality::REALS );
    TS_ASSERT( realToBool.getCardinality() > Cardinality::REALS );
    TS_ASSERT( boolToReal.getCardinality() == Cardinality::REALS );
    TS_ASSERT( boolToInt.getCardinality() == Cardinality::INTEGERS );
    TS_ASSERT( boolToBool.getCardinality() == 4 );
  }

  void testBinaryFunctions() {
    vector<Type> boolbool; boolbool.push_back(d_em->booleanType()); boolbool.push_back(d_em->booleanType());
    vector<Type> boolint; boolint.push_back(d_em->booleanType()); boolint.push_back(d_em->integerType());
    vector<Type> intbool; intbool.push_back(d_em->integerType()); intbool.push_back(d_em->booleanType());
    vector<Type> intint; intint.push_back(d_em->integerType()); intint.push_back(d_em->integerType());
    vector<Type> intreal; intreal.push_back(d_em->integerType()); intreal.push_back(d_em->realType());
    vector<Type> realint; realint.push_back(d_em->realType()); realint.push_back(d_em->integerType());
    vector<Type> realreal; realreal.push_back(d_em->realType()); realreal.push_back(d_em->realType());
    vector<Type> realbool; realbool.push_back(d_em->realType()); realbool.push_back(d_em->booleanType());
    vector<Type> boolreal; boolreal.push_back(d_em->booleanType()); boolreal.push_back(d_em->realType());

    Type boolboolToBool = d_em->mkFunctionType(boolbool, d_em->booleanType());
    Type boolboolToInt = d_em->mkFunctionType(boolbool, d_em->integerType());
    Type boolboolToReal = d_em->mkFunctionType(boolbool, d_em->realType());

    Type boolintToBool = d_em->mkFunctionType(boolint, d_em->booleanType());
    Type boolintToInt = d_em->mkFunctionType(boolint, d_em->integerType());
    Type boolintToReal = d_em->mkFunctionType(boolint, d_em->realType());

    Type intboolToBool = d_em->mkFunctionType(intbool, d_em->booleanType());
    Type intboolToInt = d_em->mkFunctionType(intbool, d_em->integerType());
    Type intboolToReal = d_em->mkFunctionType(intbool, d_em->realType());

    Type intintToBool = d_em->mkFunctionType(intint, d_em->booleanType());
    Type intintToInt = d_em->mkFunctionType(intint, d_em->integerType());
    Type intintToReal = d_em->mkFunctionType(intint, d_em->realType());

    Type intrealToBool = d_em->mkFunctionType(intreal, d_em->booleanType());
    Type intrealToInt = d_em->mkFunctionType(intreal, d_em->integerType());
    Type intrealToReal = d_em->mkFunctionType(intreal, d_em->realType());

    Type realintToBool = d_em->mkFunctionType(realint, d_em->booleanType());
    Type realintToInt = d_em->mkFunctionType(realint, d_em->integerType());
    Type realintToReal = d_em->mkFunctionType(realint, d_em->realType());

    Type realrealToBool = d_em->mkFunctionType(realreal, d_em->booleanType());
    Type realrealToInt = d_em->mkFunctionType(realreal, d_em->integerType());
    Type realrealToReal = d_em->mkFunctionType(realreal, d_em->realType());

    Type realboolToBool = d_em->mkFunctionType(realbool, d_em->booleanType());
    Type realboolToInt = d_em->mkFunctionType(realbool, d_em->integerType());
    Type realboolToReal = d_em->mkFunctionType(realbool, d_em->realType());

    Type boolrealToBool = d_em->mkFunctionType(boolreal, d_em->booleanType());
    Type boolrealToInt = d_em->mkFunctionType(boolreal, d_em->integerType());
    Type boolrealToReal = d_em->mkFunctionType(boolreal, d_em->realType());

    TS_ASSERT( boolboolToBool.getCardinality() == 16 );
    TS_ASSERT( boolboolToInt.getCardinality() == Cardinality::INTEGERS );
    TS_ASSERT( boolboolToReal.getCardinality() == Cardinality::REALS );

    TS_ASSERT( boolintToBool.getCardinality() == Cardinality::REALS );
    TS_ASSERT( boolintToInt.getCardinality() == Cardinality::REALS );
    TS_ASSERT( boolintToReal.getCardinality() == Cardinality::REALS );

    TS_ASSERT( intboolToBool.getCardinality() == Cardinality::REALS );
    TS_ASSERT( intboolToInt.getCardinality() == Cardinality::REALS );
    TS_ASSERT( intboolToReal.getCardinality() == Cardinality::REALS );

    TS_ASSERT( intintToBool.getCardinality() == Cardinality::REALS );
    TS_ASSERT( intintToInt.getCardinality() == Cardinality::REALS );
    TS_ASSERT( intintToReal.getCardinality() == Cardinality::REALS );

    TS_ASSERT( intrealToBool.getCardinality() > Cardinality::REALS );
    TS_ASSERT( intrealToInt.getCardinality() > Cardinality::REALS );
    TS_ASSERT( intrealToReal.getCardinality() > Cardinality::REALS );

    TS_ASSERT( realintToBool.getCardinality() > Cardinality::REALS );
    TS_ASSERT( realintToInt.getCardinality() > Cardinality::REALS );
    TS_ASSERT( realintToReal.getCardinality() > Cardinality::REALS );

    TS_ASSERT( realrealToBool.getCardinality() > Cardinality::REALS );
    TS_ASSERT( realrealToInt.getCardinality() > Cardinality::REALS );
    TS_ASSERT( realrealToReal.getCardinality() > Cardinality::REALS );

    TS_ASSERT( realboolToBool.getCardinality() > Cardinality::REALS );
    TS_ASSERT( realboolToInt.getCardinality() > Cardinality::REALS );
    TS_ASSERT( realboolToReal.getCardinality() > Cardinality::REALS );

    TS_ASSERT( boolrealToBool.getCardinality() > Cardinality::REALS );
    TS_ASSERT( boolrealToInt.getCardinality() > Cardinality::REALS );
    TS_ASSERT( boolrealToReal.getCardinality() > Cardinality::REALS );
  }

  void testTernaryFunctions() {
    vector<Type> boolbool; boolbool.push_back(d_em->booleanType()); boolbool.push_back(d_em->booleanType());
    vector<Type> boolboolbool = boolbool; boolboolbool.push_back(d_em->booleanType());

    Type boolboolTuple = d_em->mkTupleType(boolbool);
    Type boolboolboolTuple = d_em->mkTupleType(boolboolbool);

    Type boolboolboolToBool = d_em->mkFunctionType(boolboolbool, d_em->booleanType());
    Type boolboolToBoolbool = d_em->mkFunctionType(boolbool, boolboolTuple);
    Type boolToBoolboolbool = d_em->mkFunctionType(d_em->booleanType(), boolboolboolTuple);

    TS_ASSERT( boolboolboolToBool.getCardinality() == /* 2 ^ 8 */ 1 << 8 );
    TS_ASSERT( boolboolToBoolbool.getCardinality() == /* 4 ^ 4 */ 4 * 4 * 4 * 4 );
    TS_ASSERT( boolToBoolboolbool.getCardinality() == /* 8 ^ 2 */ 8 * 8 );
  }

  void testUndefinedSorts() {
    Type foo = d_em->mkSort("foo");
    // We've currently assigned them a specific Beth number, which
    // isn't really correct, but...
    TS_ASSERT( !foo.getCardinality().isFinite() );
  }

  void testBitvectors() {
    Debug.on("bvcard");
    TS_ASSERT( d_em->mkBitVectorType(0).getCardinality() == 0 );
    for(unsigned i = 1; i < 128; ++i) {
      try {
        Cardinality card = Cardinality(2) ^ i;
        if( d_em->mkBitVectorType(i).getCardinality() != card ) {
          stringstream ss;
          ss << "test failed for bitvector(" << i << ")";
          TS_FAIL(ss.str().c_str());
        }
      } catch(Exception& e) {
        cout << endl << e << endl;
        throw;
      }
    }
  }

};/* TypeCardinalityPublic */

/*********************                                                        */
/*! \file type_node_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of TypeNode
 **
 ** White box testing of TypeNode.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <string>
#include <sstream>

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/node_manager.h"
#include "expr/type_node.h"
#include "util/subrange_bound.h"
#include "smt/smt_engine.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace std;

class TypeNodeWhite : public CxxTest::TestSuite {
  ExprManager* d_em;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;
  SmtEngine* d_smt;

public:

  void setUp() {
    d_em = new ExprManager();
    d_nm = d_em->getNodeManager();
    d_smt = new SmtEngine(d_em);
    d_scope = new NodeManagerScope(d_nm);
  }

  void tearDown() {
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void testSubtypes() {
    TypeNode realType = d_nm->realType();
    TypeNode integerType = d_nm->realType();
    TypeNode booleanType = d_nm->booleanType();
    TypeNode arrayType = d_nm->mkArrayType(realType, integerType);
    TypeNode bvType = d_nm->mkBitVectorType(32);
    TypeNode subrangeType = d_nm->mkSubrangeType(SubrangeBounds(Integer(1), Integer(10)));

    Node x = d_nm->mkBoundVar("x", realType);
    Node xPos = d_nm->mkNode(GT, x, d_nm->mkConst(Rational(0)));
    TypeNode funtype = d_nm->mkFunctionType(integerType, booleanType);
    Node lambda = d_nm->mkVar("lambda", funtype);
    vector<Expr> formals;
    formals.push_back(x.toExpr());
    d_smt->defineFunction(lambda.toExpr(), formals, xPos.toExpr());
    TypeNode predicateSubtype = d_nm->mkPredicateSubtype(lambda.toExpr());

    TS_ASSERT( not realType.isComparableTo(booleanType) );
    TS_ASSERT( realType.isComparableTo(integerType) );
    TS_ASSERT( realType.isComparableTo(realType) );
    TS_ASSERT( not realType.isComparableTo(arrayType) );
    TS_ASSERT( not realType.isComparableTo(bvType) );
    TS_ASSERT( realType.isComparableTo(subrangeType) );
    TS_ASSERT( realType.isComparableTo(predicateSubtype) );

    TS_ASSERT( not booleanType.isComparableTo(integerType) );
    TS_ASSERT( not booleanType.isComparableTo(realType) );
    TS_ASSERT( booleanType.isComparableTo(booleanType) );
    TS_ASSERT( not booleanType.isComparableTo(arrayType) );
    TS_ASSERT( not booleanType.isComparableTo(bvType) );
    TS_ASSERT( not booleanType.isComparableTo(subrangeType) );
    TS_ASSERT( not booleanType.isComparableTo(predicateSubtype) );

    TS_ASSERT( integerType.isComparableTo(realType) );
    TS_ASSERT( integerType.isComparableTo(integerType) );
    TS_ASSERT( not integerType.isComparableTo(booleanType) );
    TS_ASSERT( not integerType.isComparableTo(arrayType) );
    TS_ASSERT( not integerType.isComparableTo(bvType) );
    TS_ASSERT( integerType.isComparableTo(subrangeType) );
    TS_ASSERT( integerType.isComparableTo(predicateSubtype) );

    TS_ASSERT( not arrayType.isComparableTo(booleanType) );
    TS_ASSERT( not arrayType.isComparableTo(integerType) );
    TS_ASSERT( not arrayType.isComparableTo(realType) );
    TS_ASSERT( arrayType.isComparableTo(arrayType) );
    TS_ASSERT( not arrayType.isComparableTo(bvType) );
    TS_ASSERT( not arrayType.isComparableTo(subrangeType) );
    TS_ASSERT( not arrayType.isComparableTo(predicateSubtype) );

    TS_ASSERT( not bvType.isComparableTo(booleanType) );
    TS_ASSERT( not bvType.isComparableTo(integerType) );
    TS_ASSERT( not bvType.isComparableTo(realType) );
    TS_ASSERT( not bvType.isComparableTo(arrayType) );
    TS_ASSERT( bvType.isComparableTo(bvType) );
    TS_ASSERT( not bvType.isComparableTo(subrangeType) );
    TS_ASSERT( not bvType.isComparableTo(predicateSubtype) );

    TS_ASSERT( not subrangeType.isComparableTo(booleanType) );
    TS_ASSERT( subrangeType.isComparableTo(integerType) );
    TS_ASSERT( subrangeType.isComparableTo(realType) );
    TS_ASSERT( not subrangeType.isComparableTo(arrayType) );
    TS_ASSERT( not subrangeType.isComparableTo(bvType) );
    TS_ASSERT( subrangeType.isComparableTo(subrangeType) );
    TS_ASSERT( subrangeType.isComparableTo(predicateSubtype) );

    TS_ASSERT( not predicateSubtype.isComparableTo(booleanType) );
    TS_ASSERT( predicateSubtype.isComparableTo(integerType) );
    TS_ASSERT( predicateSubtype.isComparableTo(realType) );
    TS_ASSERT( not predicateSubtype.isComparableTo(arrayType) );
    TS_ASSERT( not predicateSubtype.isComparableTo(bvType) );
    TS_ASSERT( predicateSubtype.isComparableTo(subrangeType) );
    TS_ASSERT( predicateSubtype.isComparableTo(predicateSubtype) );

    TS_ASSERT(realType.getBaseType() == realType);
    TS_ASSERT(integerType.getBaseType() == realType);
    TS_ASSERT(booleanType.getBaseType() == booleanType);
    TS_ASSERT(arrayType.getBaseType() == arrayType);
    TS_ASSERT(bvType.getBaseType() == bvType);
    TS_ASSERT(subrangeType.getBaseType() == realType);
    TS_ASSERT(predicateSubtype.getBaseType() == realType);

    TS_ASSERT(predicateSubtype.getSubtypeParentType() == integerType);
  }

};/* TypeNodeWhite */


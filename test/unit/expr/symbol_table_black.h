/*********************                                                        */
/*! \file symbol_table_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::SymbolTable
 **
 ** Black box testing of CVC4::SymbolTable.
 **/

#include <cxxtest/TestSuite.h>

#include <sstream>
#include <string>

#include "api/cvc4cpp.h"
#include "base/check.h"
#include "base/exception.h"
#include "context/context.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/symbol_table.h"
#include "expr/type.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace std;

class SymbolTableBlack : public CxxTest::TestSuite {
 public:
  void setUp() override
  {
    try
    {
      d_slv = new api::Solver();
      d_exprManager = d_slv->getExprManager();
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
      delete d_slv;
    }
    catch (Exception& e)
    {
      cerr << "Exception during tearDown():" << endl << e;
      throw;
    }
  }

  void testBind() {
    SymbolTable symtab;
    Type booleanType = d_exprManager->booleanType();
    Expr x = d_exprManager->mkVar(booleanType);
    symtab.bind("x",x);
    TS_ASSERT( symtab.isBound("x") );
    TS_ASSERT_EQUALS( symtab.lookup("x"), x );
  }

  void testBind2() {
    SymbolTable symtab;
    Type booleanType = d_exprManager->booleanType();
    // var name attribute shouldn't matter
    Expr y = d_exprManager->mkVar("y", booleanType);
    symtab.bind("x",y);
    TS_ASSERT( symtab.isBound("x") );
    TS_ASSERT_EQUALS( symtab.lookup("x"), y );
  }

  void testBind3() {
    SymbolTable symtab;
    Type booleanType = d_exprManager->booleanType();
    Expr x = d_exprManager->mkVar(booleanType);
    symtab.bind("x",x);
    Expr y = d_exprManager->mkVar(booleanType);
    // new binding covers old
    symtab.bind("x",y);
    TS_ASSERT( symtab.isBound("x") );
    TS_ASSERT_EQUALS( symtab.lookup("x"), y );
  }

  void testBind4() {
    SymbolTable symtab;
    Type booleanType = d_exprManager->booleanType();
    Expr x = d_exprManager->mkVar(booleanType);
    symtab.bind("x",x);

    Type t = d_exprManager->mkSort("T");
    // duplicate binding for type is OK
    symtab.bindType("x",t);

    TS_ASSERT( symtab.isBound("x") );
    TS_ASSERT_EQUALS( symtab.lookup("x"), x );
    TS_ASSERT( symtab.isBoundType("x") );
    TS_ASSERT_EQUALS( symtab.lookupType("x"), t );
  }

  void testBindType() {
    SymbolTable symtab;
    Type s = d_exprManager->mkSort("S");
    symtab.bindType("S",s);
    TS_ASSERT( symtab.isBoundType("S") );
    TS_ASSERT_EQUALS( symtab.lookupType("S"), s );
  }

  void testBindType2() {
    SymbolTable symtab;
    // type name attribute shouldn't matter
    Type s = d_exprManager->mkSort("S");
    symtab.bindType("T",s);
    TS_ASSERT( symtab.isBoundType("T") );
    TS_ASSERT_EQUALS( symtab.lookupType("T"), s );
  }

  void testBindType3() {
    SymbolTable symtab;
    Type s = d_exprManager->mkSort("S");
    symtab.bindType("S",s);
    Type t = d_exprManager->mkSort("T");
    // new binding covers old
    symtab.bindType("S",t);
    TS_ASSERT( symtab.isBoundType("S") );
    TS_ASSERT_EQUALS( symtab.lookupType("S"), t );
  }

  void testPushScope() {
    SymbolTable symtab;
    Type booleanType = d_exprManager->booleanType();
    Expr x = d_exprManager->mkVar(booleanType);
    symtab.bind("x",x);
    symtab.pushScope();

    TS_ASSERT( symtab.isBound("x") );
    TS_ASSERT_EQUALS( symtab.lookup("x"), x );

    Expr y = d_exprManager->mkVar(booleanType);
    symtab.bind("x",y);

    TS_ASSERT( symtab.isBound("x") );
    TS_ASSERT_EQUALS( symtab.lookup("x"), y );

    symtab.popScope();
    TS_ASSERT( symtab.isBound("x") );
    TS_ASSERT_EQUALS( symtab.lookup("x"), x );
  }

  void testBadPop() {
    SymbolTable symtab;
    // TODO: What kind of exception gets thrown here?
    TS_ASSERT_THROWS(symtab.popScope(), ScopeException&);
  }

 private:
  api::Solver* d_slv;
  ExprManager* d_exprManager;
};/* class SymbolTableBlack */

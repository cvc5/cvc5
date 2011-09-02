/*********************                                                        */
/*! \file declaration_scope_black.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::DeclarationScope.
 **
 ** Black box testing of CVC4::DeclarationScope.
 **/

#include <cxxtest/TestSuite.h>

#include <sstream>
#include <string>

#include "context/context.h"
#include "expr/declaration_scope.h"
#include "expr/expr_manager.h"
#include "expr/expr.h"
#include "expr/type.h"
#include "util/Assert.h"
#include "util/exception.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace std;

class DeclarationScopeBlack : public CxxTest::TestSuite {
private:

  ExprManager* d_exprManager;

public:

  void setUp() {
    try {
      d_exprManager = new ExprManager;
    } catch(Exception e) {
      cerr << "Exception during setUp():" << endl << e;
      throw;
    }
  }

  void tearDown() {
    try {
      delete d_exprManager;
    } catch(Exception e) {
      cerr << "Exception during tearDown():" << endl << e;
      throw;
    }
  }

  void testBind() {
    DeclarationScope declScope;
    Type booleanType = d_exprManager->booleanType();
    Expr x = d_exprManager->mkVar(booleanType);
    declScope.bind("x",x);
    TS_ASSERT( declScope.isBound("x") );
    TS_ASSERT_EQUALS( declScope.lookup("x"), x );
  }

  void testBind2() {
    DeclarationScope declScope;
    Type booleanType = d_exprManager->booleanType();
    // var name attribute shouldn't matter
    Expr y = d_exprManager->mkVar("y", booleanType);
    declScope.bind("x",y);
    TS_ASSERT( declScope.isBound("x") );
    TS_ASSERT_EQUALS( declScope.lookup("x"), y );
  }

  void testBind3() {
    DeclarationScope declScope;
    Type booleanType = d_exprManager->booleanType();
    Expr x = d_exprManager->mkVar(booleanType);
    declScope.bind("x",x);
    Expr y = d_exprManager->mkVar(booleanType);
    // new binding covers old
    declScope.bind("x",y);
    TS_ASSERT( declScope.isBound("x") );
    TS_ASSERT_EQUALS( declScope.lookup("x"), y );
  }

  void testBind4() {
    DeclarationScope declScope;
    Type booleanType = d_exprManager->booleanType();
    Expr x = d_exprManager->mkVar(booleanType);
    declScope.bind("x",x);

    Type t = d_exprManager->mkSort("T");
    // duplicate binding for type is OK
    declScope.bindType("x",t);

    TS_ASSERT( declScope.isBound("x") );
    TS_ASSERT_EQUALS( declScope.lookup("x"), x );
    TS_ASSERT( declScope.isBoundType("x") );
    TS_ASSERT_EQUALS( declScope.lookupType("x"), t );
  }

  void testBindType() {
    DeclarationScope declScope;
    Type s = d_exprManager->mkSort("S");
    declScope.bindType("S",s);
    TS_ASSERT( declScope.isBoundType("S") );
    TS_ASSERT_EQUALS( declScope.lookupType("S"), s );
  }

  void testBindType2() {
    DeclarationScope declScope;
    // type name attribute shouldn't matter
    Type s = d_exprManager->mkSort("S");
    declScope.bindType("T",s);
    TS_ASSERT( declScope.isBoundType("T") );
    TS_ASSERT_EQUALS( declScope.lookupType("T"), s );
  }

  void testBindType3() {
    DeclarationScope declScope;
    Type s = d_exprManager->mkSort("S");
    declScope.bindType("S",s);
    Type t = d_exprManager->mkSort("T");
    // new binding covers old
    declScope.bindType("S",t);
    TS_ASSERT( declScope.isBoundType("S") );
    TS_ASSERT_EQUALS( declScope.lookupType("S"), t );
  }

  void testPushScope() {
    DeclarationScope declScope;
    Type booleanType = d_exprManager->booleanType();
    Expr x = d_exprManager->mkVar(booleanType);
    declScope.bind("x",x);
    declScope.pushScope();

    TS_ASSERT( declScope.isBound("x") );
    TS_ASSERT_EQUALS( declScope.lookup("x"), x );

    Expr y = d_exprManager->mkVar(booleanType);
    declScope.bind("x",y);

    TS_ASSERT( declScope.isBound("x") );
    TS_ASSERT_EQUALS( declScope.lookup("x"), y );

    declScope.popScope();
    TS_ASSERT( declScope.isBound("x") );
    TS_ASSERT_EQUALS( declScope.lookup("x"), x );
  }

  void testBadPop() {
    DeclarationScope declScope;
    // TODO: What kind of exception gets thrown here?
    TS_ASSERT_THROWS( declScope.popScope(), ScopeException );
  }
};

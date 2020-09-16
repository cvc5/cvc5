/*********************                                                        */
/*! \file expr_manager_public.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Andres Noetzli, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Public black-box testing of CVC4::ExprManager.
 **
 ** Public black-box testing of CVC4::ExprManager.
 **/

#include <cxxtest/TestSuite.h>

#include <sstream>
#include <string>

#include "api/cvc4cpp.h"
#include "base/exception.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

class ExprManagerPublic : public CxxTest::TestSuite {
 public:
  void setUp() override
  {
    d_slv = new api::Solver();
    d_exprManager = d_slv->getExprManager();
  }

  void tearDown() override
  {
    try
    {
      delete d_slv;
    }
    catch (Exception& e)
    {
      cerr << "Exception during tearDown():" << endl << e;
      throw;
    }
  }

  void testMkAssociative() {
    try {
      std::vector<Expr> vars = mkVars(d_exprManager->booleanType(), 294821);
      Expr n = d_exprManager->mkAssociative(AND,vars);
      checkAssociative(n,AND,vars.size());

      vars = mkVars(d_exprManager->booleanType(), 2);
      n = d_exprManager->mkAssociative(OR,vars);
      checkAssociative(n,OR,2);
    } catch( Exception& e ) {
      cerr << "Exception in testMkAssociative(): " << endl << e;
      throw;
    }
  }

  void testMkAssociative2() {
    try {
      std::vector<Expr> vars = mkVars(d_exprManager->booleanType(), 2);
      Expr n = d_exprManager->mkAssociative(OR,vars);
      checkAssociative(n,OR,2);
    } catch( Exception& e ) {
      cerr << "Exception in testMkAssociative2(): " << endl << e;
      throw;
    }
  }

  void testMkAssociative3() {
    try {
      //unsigned int numVars = d_exprManager->maxArity(AND) + 1;
      unsigned int numVars = (1<<16) + 1;
      std::vector<Expr> vars = mkVars(d_exprManager->booleanType(), numVars);
      Expr n = d_exprManager->mkAssociative(AND,vars);
      checkAssociative(n,AND,numVars);
    } catch( Exception& e ) {
      cerr << "Exception in testMkAssociative3(): " << endl << e;
      throw;
    }
  }

  void testMkAssociativeTooFew() {
    std::vector<Expr> vars = mkVars(d_exprManager->booleanType(), 1);
    TS_ASSERT_THROWS(d_exprManager->mkAssociative(AND, vars),
                     IllegalArgumentException&);
  }

  void testMkAssociativeBadKind() {
    std::vector<Expr> vars = mkVars(d_exprManager->integerType(), 10);
    TS_ASSERT_THROWS(d_exprManager->mkAssociative(LEQ, vars),
                     IllegalArgumentException&);
  }

 private:
  void checkAssociative(Expr expr, Kind kind, unsigned int numChildren)
  {
    std::vector<Expr> worklist;
    worklist.push_back(expr);

    unsigned int childrenFound = 0;

    while (!worklist.empty())
    {
      Expr current = worklist.back();
      worklist.pop_back();
      if (current.getKind() == kind)
      {
        for (unsigned int i = 0; i < current.getNumChildren(); ++i)
        {
          worklist.push_back(current[i]);
        }
      }
      else
      {
        childrenFound++;
      }
    }

    TS_ASSERT_EQUALS(childrenFound, numChildren);
  }

  std::vector<Expr> mkVars(Type type, unsigned int n)
  {
    std::vector<Expr> vars;
    for (unsigned int i = 0; i < n; ++i)
    {
      vars.push_back(d_exprManager->mkVar(type));
    }
    return vars;
  }

  api::Solver* d_slv;
  ExprManager* d_exprManager;
};

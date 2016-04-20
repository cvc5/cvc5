/*********************                                                        */
/*! \file cvc3_main.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Test of CVC3 compatibility interface
 **
 ** This is part of a test of the CVC3 compatibility interface present in
 ** CVC4.  It is a test copied from CVC3's "test" directory.  Only #includes
 ** were changed to support this test in CVC4.
 **
 ** The original file comment is preserved in the source.
 **/

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// File: main.cpp                                                            //
// Author: Clark Barrett                                                     //
// Created: Sat Apr 19 01:47:47 2003                                         //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
 

#include "compat/cvc3_compat.h"
//#include "vc.h"
//#include "theory_arith.h" // for arith kinds and expressions
//#include "theory_array.h"
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <deque>
//#include "exception.h"
//#include "typecheck_exception.h"
//#include "command_line_flags.h"
//#include "debug.h"
#include "cvc3_george.h"


using namespace std;
using namespace CVC3;

int exitStatus;

inline void __expect__(const std::string& file,
                       int line,
                       bool cond,
                       const std::string& cond_s,
                       const std::string& msg) {
  if(!cond) {
    std::cerr << file << ":" << line
              << ": Expected: (" << cond_s << "). "
              << msg << std::endl;
    exitStatus = 1;
  }
}

#define EXPECT(cond, msg) __expect__(__FILE__, __LINE__, (cond), #cond, (msg))

// Check whether e is valid
bool check(ValidityChecker* vc, Expr e, bool verbose=true)
{
  if(verbose) {
    cout << "Query: ";
    vc->printExpr(e);
  }
  bool res = vc->query(e);
  if (res) {
    if(verbose) cout << "Valid" << endl << endl;
  } else {
    if(verbose) cout << "Invalid" << endl << endl;
  }
  return res;
}


// Make a new assertion
void newAssertion(ValidityChecker* vc, Expr e)
{
  cout << "Assert: ";
  vc->printExpr(e);
  vc->assertFormula(e);
}

int eqExprVecs(const vector<Expr>& v1,
                const vector<Expr>& v2) {
    if( v1.size() != v2.size() ) {
        return 0;
    }

    for( unsigned int i=0; i < v1.size(); ++i ) {
        if( v1[i] != v2[i] ) {
            return 0;
        }
    }

    return 1;
}

int eqExprVecVecs(const vector<vector<Expr> > vv1,
                   const vector<vector<Expr> > vv2) {
    if( vv1.size() != vv2.size() ) {
        return 0;
    }

    for( unsigned int i=0; i < vv1.size(); ++i ) {
        if( !eqExprVecs(vv1[i],vv2[i]) ) {
            return 0;
        }
    }

    return 1;
}


void test ()
{
   CLFlags flags = ValidityChecker::createFlags();
   ValidityChecker* vc = ValidityChecker::create(flags);

   try {
     Type it (vc->intType ());                //int
     Op f = vc->createOp("f",vc->funType(it,it));
     Expr z = vc->varExpr("z",it);
     Expr e = vc->funExpr(f, vc->funExpr(f, z));
     e = e[0];
     Expr f2 = vc->funExpr(f, e);
     Expr f3 = vc->funExpr(f, f2);

     EXPECT(e != f2 && e != f3, "Refcount problems");

     Expr x (vc->boundVarExpr ("x", "0", it));//x0:int
     vector<Expr> xs;
     xs.push_back (x);                        //<x0:int>
     Op lxsx (vc->lambdaExpr (xs,x));       //\<x0:int>. x0:int
     Expr y (vc->ratExpr (1,1));              //1
     vector<Expr> ys;
     ys.push_back (y);                        //<1>
     Expr lxsxy = vc->funExpr (lxsx, y);      //(\<x0:int>. x0:int)1
     Expr lxsxys = vc->funExpr (lxsx, ys);  //(\<x0:int>. x0:int)<1>
     cout << "Lambda application: " << lxsxy << endl;
     cout << "Simplified: " << vc->simplify(lxsxy) << endl;
   } catch(const Exception& e) {
     exitStatus = 1;
     cout << "*** Exception caught in test (): \n" << e << endl;
   }
   delete vc;
}

void test1()
{
  CLFlags flags = ValidityChecker::createFlags();
  flags.setFlag("dagify-exprs",false);
  flags.setFlag("dump-log", ".test1.cvc");
  ValidityChecker* vc = ValidityChecker::create(flags);
  
  // It is important that all Expr objects are deleted before vc is
  // deleted.  Therefore, we enclose them in a scope of try{ }catch
  // block.
  //
  // Also, vc methods may throw an Exception, and we want to delete vc
  // even in those exceptional cases.
  try {

    bool b = check(vc, vc->trueExpr());
    EXPECT(b, "Should be valid");

    vc->push();
    b = check(vc, vc->falseExpr());
    EXPECT(!b, "Should be invalid");
    vc->pop();          

    // Check p OR ~p

    Expr p = vc->varExpr("p", vc->boolType());
    Expr e = vc->orExpr(p, vc->notExpr(p));

    b = check(vc, e);
    EXPECT(b, "Should be valid");

    // Check x = y -> f(x) = f(y)

    Expr x = vc->varExpr("x", vc->realType());
    Expr y = vc->varExpr("y", vc->realType());

    Type real2real = vc->funType(vc->realType(), vc->realType());
    Op f = vc->createOp("f", real2real);
    Expr fx = vc->funExpr(f, x);
    Expr fy = vc->funExpr(f, y);

    e = vc->impliesExpr(vc->eqExpr(x,y),vc->eqExpr(fx, fy));
    b = check(vc, e);
    EXPECT(b, "Should be valid");

    // Check f(x) = f(y) -> x = y

    e = vc->impliesExpr(vc->eqExpr(fx,fy),vc->eqExpr(x, y));
    int scopeLevel = vc->scopeLevel();
    vc->push();
    b = check(vc, e);
    EXPECT(!b, "Should be invalid");

    // Get counter-example
    
    vector<Expr> assertions;
    cout << "Scope level: " << vc->scopeLevel() << endl;
    cout << "Counter-example:" << endl;
    //vc->getCounterExample(assertions);
    for (unsigned i = 0; i < assertions.size(); ++i) {
      vc->printExpr(assertions[i]);
    }
    cout << "End of counter-example" << endl << endl;

    // Reset to initial scope
    cout << "Resetting" << endl;
    vc->pop();
    EXPECT(scopeLevel == vc->scopeLevel(), "scope error");
    cout << "Scope level: " << vc->scopeLevel() << endl << endl;

    // Check w = x & x = y & y = z & f(x) = f(y) & x = 1 & z = 2
    
    Expr w = vc->varExpr("w", vc->realType());
    Expr z = vc->varExpr("z", vc->realType());

    cout << "Push Scope" << endl << endl;
    vc->push();

    newAssertion(vc, vc->eqExpr(w, x));
    newAssertion(vc, vc->eqExpr(x, y));
    newAssertion(vc, vc->eqExpr(y, z));
    newAssertion(vc, vc->eqExpr(fx, fy));
    newAssertion(vc, vc->eqExpr(x, vc->ratExpr(1)));

    cout << endl << "simplify(w) = ";
    vc->printExpr(vc->simplify(w));
    cout << endl;
    EXPECT(vc->simplify(w)==vc->ratExpr(1), "Expected simplify(w) = 1");

    newAssertion(vc, vc->eqExpr(z, vc->ratExpr(2)));
    assertions.clear();
    cout << "Inconsistent?: " << vc->inconsistent(assertions) << endl;

    cout << "Assumptions Used:" << endl;
    for (unsigned i = 0; i < assertions.size(); ++i) {
      vc->printExpr(assertions[i]);
    }

    cout << endl << "Pop Scope" << endl << endl;
    vc->pop();
    
    cout << "simplify(w) = ";
    vc->printExpr(vc->simplify(w));
    EXPECT(vc->simplify(w)==w, "Expected simplify(w) = w");
    cout << endl;
    
    assertions.clear();
    cout << "Inconsistent?: " << vc->inconsistent(assertions) << endl;
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test1(): \n" << e << endl;
  }
  delete vc;
}


void test2()
{
  CLFlags flags = ValidityChecker::createFlags();
  flags.setFlag("dagify-exprs",false);
  ValidityChecker* vc = ValidityChecker::create(flags);

  try {

    Expr bexpr = vc->varExpr("b", vc->intType());
    vc->assertFormula(vc->ltExpr(bexpr, vc->ratExpr(10)));

    Expr c = vc->varExpr("c", vc->intType());
    vc->assertFormula(c.eqExpr(vc->ratExpr(0)) || c.eqExpr(vc->ratExpr(1)));

    bool b = check(vc, vc->leExpr(bexpr, vc->ratExpr(10)));
    EXPECT(b, "Should be valid");

    b = check(vc, vc->falseExpr());
    EXPECT(!b, "Should be invalid");
    vc->returnFromCheck();

    // Check x = y -> g(x,y) = g(y,x)

    Expr x = vc->varExpr("x", vc->realType());
    Expr y = vc->varExpr("y", vc->realType());

    Type real = vc->realType();
    vector<Type> RxR;
    RxR.push_back(real);
    RxR.push_back(real);

    Type realxreal2real = vc->funType(RxR, real);
    Op g = vc->createOp("g", realxreal2real);

    Expr gxy = vc->funExpr(g, x, y);
    Expr gyx = vc->funExpr(g, y, x);

    Expr e = vc->impliesExpr(vc->eqExpr(x,y),vc->eqExpr(gxy, gyx));
    b = check(vc, e);
    EXPECT(b, "Should be valid");

    Op h = vc->createOp("h", realxreal2real);

    Expr hxy = vc->funExpr(h, x, y);
    Expr hyx = vc->funExpr(h, y, x);

    e = vc->impliesExpr(vc->eqExpr(x,y),vc->eqExpr(hxy, hyx));
    b = check(vc, e);
    EXPECT(b, "Should be valid");

  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test2(): \n" << e << endl;
  }

  delete vc;
}


Expr ltLex(ValidityChecker* vc, Expr i1, Expr i2, Expr j1, Expr j2)
{
  Expr res = vc->ltExpr(i1, j1);
  return vc->orExpr(res, vc->andExpr(vc->eqExpr(i1, j1), vc->ltExpr(i2, j2)));
}


Expr createTestFormula(ValidityChecker* vc, Expr i1, Expr i2, Expr r1, Expr r2)
{
  Expr lt1 = ltLex(vc, r1, r2, i1, i2);
  Expr lt2 = ltLex(vc, i2, i1, r2, r1);
  return vc->andExpr(lt1, lt2);
}


void test3()
{
  CLFlags flags = ValidityChecker::createFlags();
  flags.setFlag("dagify-exprs",false);
  ValidityChecker* vc = ValidityChecker::create(flags);

  try {
    Expr i = vc->varExpr("i", vc->realType());
    Expr j = vc->varExpr("j", vc->realType());
    Expr k = vc->varExpr("k", vc->realType());
    
    Expr one = vc->ratExpr(1);
    
    cout << "i: " << i.getIndex() << endl;
    
    Expr test = createTestFormula(vc, i, j,
				  vc->minusExpr(i, one), vc->minusExpr(j, k));
    
    cout << "Trying test: ";
    vc->printExpr(test);
    cout << endl;
    
    vc->push();
    bool result = vc->query(test);
    if (result) {
      cout << "Test Valid" << endl;
      vc->pop();
    }
    else {
      Expr condition;
      vector<Expr> assertions;
      unsigned index;
      
      //vc->getCounterExample(assertions);
      
      cout << "Test Invalid Under Conditions:" << endl;
      for (index = 0; index < assertions.size(); ++index) {
	vc->printExpr(assertions[index]);
      }
      
      // Try assertions one by one
      for (index = 0; index < assertions.size(); ++index) {
	condition = vc->notExpr(assertions[index]);
	cout << "Trying test under condition: ";
	vc->printExpr(condition);
	cout << endl;
	vc->pop();
        vc->push();
	result = vc->query(vc->impliesExpr(condition, test));
	if (result) {
	  cout << "Result Valid" << endl;
	  break;
	}
	else {
	  cout << "Result Invalid" << endl;
	}
      }
    }
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test3(): \n" << e << endl;
  }
  delete vc;
}


void test4()
{
  CLFlags flags = ValidityChecker::createFlags();
  flags.setFlag("dagify-exprs",false);
  ValidityChecker* vc = ValidityChecker::create(flags);
  
  try {
  Expr i = vc->varExpr("i", vc->realType());
  Expr j = vc->varExpr("j", vc->realType());
  Expr k = vc->varExpr("k", vc->realType());

  Expr one = vc->ratExpr(1);

  cout << "i: " << i.getIndex() << endl;

  Expr test = createTestFormula(vc, i, j,
				vc->minusExpr(i, one), vc->minusExpr(j, k));

  cout << "Trying test: ";
  vc->printExpr(test);
  cout << endl;

  vc->push();
  bool result = vc->query(test);
  if (result) {
    cout << "Test Valid" << endl;
  }
  else {
    Expr condition;
    vector<Expr> assertions;
    unsigned index;

    //vc->getCounterExample(assertions);

    cout << "Test Invalid Under Conditions:" << endl;
    for (index = 0; index < assertions.size(); ++index) {
      vc->printExpr(assertions[index]);
    }

    // Try assertions one by one
    for (index = 0; index < assertions.size(); ++index) {
      condition = vc->notExpr(assertions[index]);
      cout << "Trying test under condition: ";
      vc->printExpr(condition);
      cout << endl;
      vc->pop();
      vc->push();
      result = vc->query(vc->impliesExpr(condition, test));
      if (result) {
	cout << "Result Valid" << endl;
	break;
      }
      else {
	cout << "Result Invalid" << endl;
      }
    }
  }
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test4(): \n" << e << endl;
  }
  delete vc;
}


void findLeaves(Expr e, vector<Expr>& l)
{
  int ar = e.arity();
  if (ar > 0) {
    for (int i = 0; i < ar; ++i)
      findLeaves(e[i], l);
    return;
  }
  l.push_back(e);
}


bool hasij(Expr e, Expr i, Expr j)
{
  int ar = e.arity();
  if (ar > 0) {
    for (int k = 0; k < ar; ++k)
      if (hasij(e[k], i, j)) return true;
    return false;
  }
  if (e == i || e == j) return true;
  return false;
}


Expr plusExpr(ValidityChecker* vc, vector<Expr>& kids)
{
  if (kids.size() == 0) return vc->ratExpr(0);
  else if (kids.size() == 1) return kids[0];
  else if (kids.size() == 2) return vc->plusExpr(kids[0], kids[1]);
  else {
    Expr r = kids.back();
    kids.pop_back();
    return vc->plusExpr(plusExpr(vc, kids), r);
  }
}


void test5()
{
  CLFlags flags = ValidityChecker::createFlags();
  flags.setFlag("dagify-exprs",false);
  flags.setFlag("dump-log", ".test5.cvc");
  ValidityChecker* vc = ValidityChecker::create(flags);

  try {
  Expr i = vc->varExpr("i1", vc->realType());
  Expr j = vc->varExpr("i2", vc->realType());
  Expr p = vc->varExpr("p", vc->realType());
  Expr q = vc->varExpr("q", vc->realType());
  Expr r = vc->varExpr("r", vc->realType());
  Expr a = vc->varExpr("arb_addr", vc->realType());
  Expr N = vc->varExpr("N", vc->realType());

  Expr M = vc->varExpr("M", vc->arrayType(vc->realType(), vc->realType()));

  Expr M2 = vc->writeExpr(M, vc->plusExpr(q, i), vc->readExpr(M, vc->plusExpr(r, i)));

  Expr M1 = vc->writeExpr(M, vc->plusExpr(p, j), vc->readExpr(M, vc->plusExpr(r, j)));

  Expr e = vc->eqExpr(vc->readExpr(vc->writeExpr(M2, vc->plusExpr(p, j), vc->readExpr(M2, vc->plusExpr(r, j))), a),
		      vc->readExpr(vc->writeExpr(M1, vc->plusExpr(q, i), vc->readExpr(M1, vc->plusExpr(r, i))), a));

  Expr one = vc->ratExpr(1);
  Expr zero = vc->ratExpr(0);

  Expr qmp = vc->minusExpr(q, p);
  Expr qmr = vc->minusExpr(q, r);

  vector<Expr> hyp;
  hyp.push_back(vc->ltExpr(i, j));
//   hyp.push_back(vc->orExpr(vc->geExpr(qmp, N), vc->leExpr(qmp, zero)));
//   hyp.push_back(vc->orExpr(vc->geExpr(qmr, N), vc->leExpr(qmr, zero)));

  Expr test = vc->impliesExpr(vc->andExpr(hyp), e);
  Expr query;

  cout << "Checking verification condition:" << endl;
  vc->printExpr(test);
  cout << endl;

  vc->push();
  bool result = vc->query(test);
  if (result) {
    cout << "Valid" << endl;
  }
  else {
    vector<Expr> conditions;
    vector<Expr> assertions;
    unsigned index, index2;
    int req;
    vector<Expr> leaves;

    //vc->getCounterExample(assertions);

    cout << "Invalid Under Conditions:" << endl;
    for (index = 0; index < assertions.size(); ++index) {
      if (assertions[index] == (!test)) {
	for (; index < assertions.size()-1; ++index) {
	  assertions[index] = assertions[index+1];
	}
	assertions.pop_back();
	break;
      }
    }
    for (index = 0; index < assertions.size(); ++index) {
      vc->printExpr(assertions[index]);
    }

    cout << endl;

    // Try assertions one by one
    for (index = 0; index < assertions.size(); ++index) {
      e = assertions[index];
      
      // Check condition for eligibility
      if (e.isNot()) {
	cout << "Condition ineligible: negation" << endl;
	vc->printExpr(e);
	cout << endl;
	continue;
      }
      if (e.isEq()) {
	req = 2;
      }
      else req = 1;

      leaves.clear();
      findLeaves(e, leaves);
      for (index2 = 0; index2 < leaves.size(); ++index2) {
	if (!leaves[index2].isVar() ||
	    leaves[index2] == i ||
	    leaves[index2] == j ||
	    leaves[index2] == a)
	  continue;
	req--;
      }
      if (req > 0) {
	cout << "Condition ineligible: not enough non-loop variables" << endl;
	vc->printExpr(e);
	cout << endl;
	continue;
      }

      cout << "Condition selected:" << endl;
      vc->printExpr(e);
      cout << endl << endl;

      conditions.push_back(vc->notExpr(e));
      cout << "Trying verification condition with hypothesis:" << endl;
      vc->printExpr(vc->andExpr(conditions));
      cout << endl;
      vc->pop();
      vc->push();
      query = vc->impliesExpr(vc->andExpr(conditions), test);
      result = vc->query(query);
      if (result) {
	cout << "Result Valid" << endl;
	break;
      }
      else {
	assertions.clear();
	vc->getCounterExample(assertions);

	cout << "Invalid Under Conditions:" << endl;
	for (index2 = 0; index2 < assertions.size(); ++index2) {
	  if (assertions[index2] == (!query)) {
	    for (; index2 < assertions.size()-1; ++index2) {
	      assertions[index2] = assertions[index2+1];
	    }
	    assertions.pop_back();
	    break;
	  }
	}

	for (index2 = 0; index2 < assertions.size(); ++index2) {
	  vc->printExpr(assertions[index2]);
	}
	cout << endl;
	index = (unsigned)-1;
      }
    }

    cout << endl << "Attempting to remove loop variables" << endl;
    // replace loop variables in conditions
    vector<Expr> newConditions;
    vector<Expr> newPlus;
    bool foundi, foundj, negi, negj;
    Expr minusone = vc->ratExpr(-1);
    for (index = 0; index < conditions.size(); ++index) {
      if (conditions[index][0].isEq()) {
	e = vc->simplify(vc->minusExpr(conditions[index][0][0], conditions[index][0][1]));
	if (hasij(e, i, j)) {
	  if (e.getKind() == CVC3::PLUS) {
	    newPlus.clear();
	    newPlus.push_back(e[0]);
	    foundi = foundj = negi = negj = false;
	    for (index2 = 1; index2 < (unsigned)e.arity(); index2++) {
	      Expr term = e[index2];
	      if (term == i && !foundi) foundi = true;
	      else if (term == j && !foundj) {
                foundj = true;
		negj = true;
	      }
	      else if (term.getKind() == CVC3::MULT && term[0] == minusone && term[1] == i && !foundi) {
		foundi = true;
		negi = true;
	      }
	      else if (term.getKind() == CVC3::MULT && term[0] == minusone && term[1] == j && !foundj) foundj = true;
	      else newPlus.push_back(term);
	    }
	    if (foundi && foundj && ((negi && negj) || (!negi && !negj))) {
	      e = plusExpr(vc, newPlus);
	      if (negi && negj) e = vc->uminusExpr(e);
	      e = vc->simplify(e);
	      if (!hasij(e, i, j)) {
		newConditions.push_back(vc->orExpr(vc->geExpr(e, N), vc->leExpr(e, zero)));
		continue;
	      }
	    }
	  }
	  cout << "Unable to remove loop variables:" << endl;
	  vc->printExpr(e);
	  break;
	}
      }
      newConditions.push_back(conditions[index]);
    }
    if (index == conditions.size()) {
      cout << "Loop variables successfully removed:" << endl;
      Expr cond = (newConditions.size()>0)?
	vc->andExpr(newConditions) : vc->trueExpr();
      vc->printExpr(cond);
      cout << endl;

      vector<Expr> loopConditions;
      loopConditions.push_back(cond);
      loopConditions.push_back(vc->geExpr(i, one));
      loopConditions.push_back(vc->geExpr(j, one));
      loopConditions.push_back(vc->leExpr(i, N));
      loopConditions.push_back(vc->leExpr(j, N));
      vc->pop();
      vc->push();
      cout << "Final query" << endl;
      result = vc->query(vc->impliesExpr(vc->andExpr(loopConditions), test));
      if (result) {
	cout << "Result Valid" << endl;
      }
      else {
	cout << "Result Invalid" << endl;
      }
    }
  }
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test5(): \n" << e << endl;
  }
  delete vc;
}

//#include "debug.h"

// Test importing of Exprs from a different validity checker
void test6() {
  ValidityChecker* vc1 = ValidityChecker::create();
  ValidityChecker* vc2 = ValidityChecker::create();

  try {
    Type real1 = vc1->realType();

    Expr x1 = vc1->varExpr("x", real1);
    Expr y1 = vc1->boundVarExpr("y", "0", real1);
    
    cout << "vc1 variables: " << x1 << ", " << y1 << endl;
    
    Expr x2 = vc2->varExpr("x", vc2->importType(real1));
    Expr y2 = vc2->boundVarExpr("y", "0", vc2->realType());
    
    cout << "vc2 variables: " << x2 << ", " << y2 << endl;
    cout << "vars imported to vc2 from vc1: "
	 << vc2->importExpr(x1) << ", " << vc2->importExpr(y1) << endl;
    Expr t1 = vc1->trueExpr();
    Expr and1 = vc1->andExpr(t1, vc1->falseExpr());
    Op f1 = vc1->createOp("f", vc1->funType(real1, real1));
    Expr fx1 = vc1->funExpr(f1, x1);
    Expr f5_1 = vc1->funExpr(f1, vc1->ratExpr(5,1));
    Type rt1 = vc1->recordType("foo", real1, "bar", real1);
    Expr r1 = vc1->recordExpr("foo", fx1, "bar", f5_1);
    Expr r1_eq = vc1->eqExpr(r1, vc1->recUpdateExpr(r1, "foo", f5_1));
    Type art1 = vc1->arrayType(real1, rt1);
    Expr ar1 = vc1->varExpr("ar", art1);
    Expr ar_eq1 = vc1->eqExpr(vc1->writeExpr(ar1, x1, r1), ar1);
    Expr query1 = vc1->eqExpr(vc1->recSelectExpr(vc1->readExpr(ar1, x1), "foo"),
			      vc1->recSelectExpr(r1, "bar"));
    
    cout << "*** VC #1:" << endl;
    newAssertion(vc1, r1_eq);
    newAssertion(vc1, ar_eq1);
    check(vc1, query1);
    
    //cout << "*** VC #2:" << endl;
    //newAssertion(vc2, vc2->importExpr(r1_eq));
    //newAssertion(vc2, vc2->importExpr(ar_eq1));
    //check(vc2, vc2->importExpr(query1));
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test6(): \n" << e << endl;
  }
  delete vc1;
  delete vc2;
}


void test7() {
  ValidityChecker* vc1 = ValidityChecker::create();
  ValidityChecker* vc2 = ValidityChecker::create();
  try {
    Expr e1 = vc1->varExpr("e1", vc1->realType());
    Expr e2 = vc2->varExpr("e2", vc2->realType());
    newAssertion(vc2, vc2->eqExpr(vc2->importExpr(e1), e2));
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test7(): \n" << e << endl;
  }
  delete vc1;
  delete vc2;
}


void test8() {
  ValidityChecker* vc = ValidityChecker::create();
  try {
    vector<Expr> vec;
    vec.push_back(vc->boundVarExpr("x", "x", vc->realType()));
    Expr lambda = vc->lambdaExpr(vec, vc->falseExpr()).getExpr();
    Expr witness;
    try {
      Type t = vc->subtypeType(lambda, witness);
      EXPECT(false, "Typechecking exception expected");
    } catch(const TypecheckException&) {
      // fall through
    }
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test8(): \n" << e << endl;
  }
  delete vc;
}


Expr adder(ValidityChecker* vc, const Expr& a, const Expr& b, const Expr& c)
{
  return vc->notExpr(vc->iffExpr(vc->notExpr(vc->iffExpr(a,b)),c));
}


Expr carry(ValidityChecker* vc, const Expr& a, const Expr& b, const Expr& c)
{
  return vc->orExpr(vc->andExpr(a,b), vc->orExpr(vc->andExpr(b,c),vc->andExpr(a,c)));
}


void add(ValidityChecker* vc, vector<Expr> a, vector<Expr> b, vector<Expr>& sum)
{
  int i,N=a.size();
  Expr c = vc->falseExpr();

  for (i=0; i < N; i++)
  {
    sum.push_back(adder(vc,a[i],b[i],c));
    c = carry(vc,a[i],b[i],c);
  }
}


Expr vectorEq(ValidityChecker* vc, vector<Expr> a, vector<Expr> b)
{
  int i, N=a.size();
  Expr result = vc->trueExpr();

  for (i=0; i < N; i++) {
    result = result && a[i].iffExpr(b[i]);
  }
  return result;
}


void test9(int N) {
  CLFlags flags = ValidityChecker::createFlags();
  //  flags.setFlag("proofs",true);
  ValidityChecker* vc = ValidityChecker::create(flags);

  try {
  int i;
  vector<Expr> a,b,sum1,sum2;

  for (i=0; i < N; i++) {
    a.push_back(vc->varExpr("a" + int2string(i), vc->boolType()));
    b.push_back(vc->varExpr("b" + int2string(i), vc->boolType()));
  }

  add(vc,a,b,sum1);
  add(vc,b,a,sum2);

  Expr q = vectorEq(vc,sum1,sum2);

  check(vc, q);

  //  Proof p = vc->getProof();

  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test9(): \n" << e << endl;
  }
  delete vc;
}


Expr bvadder(ValidityChecker* vc, const Expr& a, const Expr& b, const Expr& c)
{
  return vc->newBVXorExpr(a, vc->newBVXorExpr(b, c));
}


Expr bvcarry(ValidityChecker* vc, const Expr& a, const Expr& b, const Expr& c)
{
  return vc->newBVOrExpr(vc->newBVAndExpr(a,b), vc->newBVOrExpr(vc->newBVAndExpr(b,c),vc->newBVAndExpr(a,c)));
}


void bvadd(ValidityChecker* vc, vector<Expr> a, vector<Expr> b, vector<Expr>& sum)
{
  int i,N=a.size();
  Expr c = vc->newBVConstExpr(Rational(0), 1);

  for (i=0; i < N; i++)
  {
    sum.push_back(bvadder(vc,a[i],b[i],c));
    c = bvcarry(vc,a[i],b[i],c);
  }
}


Expr bvvectorEq(ValidityChecker* vc, vector<Expr> a, vector<Expr> b)
{
  int i, N=a.size();
  Expr result = vc->newBVConstExpr(string("1"));

  for (i=0; i < N; i++) {
    result = vc->newBVAndExpr(result, vc->newBVXnorExpr(a[i], b[i]));
  }
  return result;
}


void bvtest9(int N) {
  CLFlags flags = ValidityChecker::createFlags();
  ValidityChecker* vc = ValidityChecker::create(flags);

  try {
  int i;
  vector<Expr> avec,bvec,sum1vec,sum2;

  Expr a, b, sum1;
  a = vc->varExpr("a", vc->bitvecType(N));
  b = vc->varExpr("b", vc->bitvecType(N));
  vector<Expr> kids;
  kids.push_back(a);
  kids.push_back(b);
  sum1 = vc->newBVPlusExpr(N, kids);

  for (i=0; i < N; i++) {
    avec.push_back(vc->newBVExtractExpr(a, i, i));
    bvec.push_back(vc->newBVExtractExpr(b, i, i));
    sum1vec.push_back(vc->newBVExtractExpr(sum1, i, i));
  }

  bvadd(vc,avec,bvec,sum2);

  Expr q = bvvectorEq(vc,sum1vec,sum2);

  check(vc, vc->eqExpr(q,vc->newBVConstExpr(string("1"))));

  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in bvtest9(): \n" << e << endl;
  }
  delete vc;
}


// Test for memory leaks (run silently)
void test10()
{
  CLFlags flags = ValidityChecker::createFlags();
  ValidityChecker* vc = ValidityChecker::create(flags);

  // Create all expressions in a separate scope, so that they are
  // destroyed before vc is deleted.

  try {
    //  Check x = y -> g(x,y) = g(y,x)

    Expr x = vc->varExpr("x", vc->realType());
    Expr y = vc->varExpr("y", vc->realType());

    Type real = vc->realType();
    vector<Type> RxR;
    RxR.push_back(real);
    RxR.push_back(real);

    Type realxreal2real = vc->funType(RxR, real);
    Op g = vc->createOp("g", realxreal2real);

    Expr gxy = vc->funExpr(g, x, y);
    Expr gyx = vc->funExpr(g, y, x);

    Expr e = vc->impliesExpr(vc->eqExpr(x,y),vc->eqExpr(gxy, gyx));
    check(vc, e, false);

    Op h = vc->createOp("h", realxreal2real);

    Expr hxy = vc->funExpr(h, x, y);
    Expr hyx = vc->funExpr(h, y, x);

    e = vc->impliesExpr(vc->eqExpr(x,y),vc->eqExpr(hxy, hyx));
    check(vc, e, false);

  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test10(): \n" << e << endl;
  }
  // Make sure all Expr's are deleted first
  delete vc;
}

unsigned int printImpliedLiterals(ValidityChecker* vc)
{
  unsigned int count = 0;
  cout << "Implied Literals:" << endl;
  Expr impLit = vc->getImpliedLiteral();
  while (!impLit.isNull()) {
    ++count;
    vc->printExpr(impLit);
    impLit = vc->getImpliedLiteral();
  }
  return count;
}


void test11()
{
  CLFlags flags = ValidityChecker::createFlags();
  ValidityChecker* vc = ValidityChecker::create(flags);

  try {
    Expr x = vc->varExpr("x", vc->realType());
    Expr y = vc->varExpr("y", vc->realType());
    Expr z = vc->varExpr("z", vc->realType());

    Type real = vc->realType();
    Type real2real = vc->funType(real, real);
    Type real2bool = vc->funType(real, vc->boolType());
    Op f = vc->createOp("f", real2real);
    Op p = vc->createOp("p", real2bool);

    Expr fx = vc->funExpr(f, x);
    Expr fy = vc->funExpr(f, y);

    Expr px = vc->funExpr(p, x);
    Expr py = vc->funExpr(p, y);

    Expr xeqy = vc->eqExpr(x, y);
    Expr yeqx = vc->eqExpr(y, x);
    Expr xeqz = vc->eqExpr(x, z);
    Expr zeqx = vc->eqExpr(z, x);
    Expr yeqz = vc->eqExpr(y, z);
    Expr zeqy = vc->eqExpr(z, y);

    unsigned int c;

    vc->registerAtom(vc->eqExpr(x,vc->ratExpr(0,1)));
    vc->registerAtom(xeqy);
    vc->registerAtom(yeqx);
    vc->registerAtom(xeqz);
    vc->registerAtom(zeqx);
    vc->registerAtom(yeqz);
    vc->registerAtom(zeqy);
    vc->registerAtom(px);
    vc->registerAtom(py);
    vc->registerAtom(vc->eqExpr(fx, fy));

    cout << "Push" << endl;
    vc->push();

    cout << "Assert x = y" << endl;
    vc->assertFormula(xeqy);
    c = printImpliedLiterals(vc);
    EXPECT(c==3,"Implied literal error 0");

    cout << "Push" << endl;
    vc->push();
    cout << "Assert x /= z" << endl;
    vc->assertFormula(!xeqz);
    c = printImpliedLiterals(vc);
    EXPECT(c==4,"Implied literal error 1");
    cout << "Pop" << endl;
    vc->pop();

    cout << "Push" << endl;
    vc->push();
    cout << "Assert y /= z" << endl;
    vc->assertFormula(!yeqz);
    c = printImpliedLiterals(vc);
    EXPECT(c==4,"Implied literal error 2");
    cout << "Pop" << endl;
    vc->pop();

    cout << "Push" << endl;
    vc->push();
    cout << "Assert p(x)" << endl;
    vc->assertFormula(px);
    c = printImpliedLiterals(vc);
    EXPECT(c==2,"Implied literal error 3");
    cout << "Pop" << endl;
    vc->pop();

    cout << "Push" << endl;
    vc->push();
    cout << "Assert p(y)" << endl;
    vc->assertFormula(py);
    c = printImpliedLiterals(vc);
    EXPECT(c==2,"Implied literal error 4");
    cout << "Pop" << endl;
    vc->pop();

    cout << "Pop" << endl;
    vc->pop();

    cout << "Push" << endl;
    vc->push();
    cout << "Assert y = x" << endl;
    vc->assertFormula(yeqx);
    c = printImpliedLiterals(vc);
    EXPECT(c==3,"Implied literal error 5");
    cout << "Pop" << endl;
    vc->pop();

    cout << "Push" << endl;
    vc->push();
    cout << "Assert p(x)" << endl;
    vc->assertFormula(px);
    c = printImpliedLiterals(vc);
    EXPECT(c==1,"Implied literal error 6");
    cout << "Assert x = y" << endl;
    vc->assertFormula(xeqy);
    c = printImpliedLiterals(vc);
    EXPECT(c==4,"Implied literal error 7");
    cout << "Pop" << endl;
    vc->pop();

    cout << "Push" << endl;
    vc->push();
    cout << "Assert NOT p(x)" << endl;
    vc->assertFormula(!px);
    c = printImpliedLiterals(vc);
    EXPECT(c==1,"Implied literal error 8");
    cout << "Assert x = y" << endl;
    vc->assertFormula(xeqy);
    c = printImpliedLiterals(vc);
    EXPECT(c==4,"Implied literal error 9");
    cout << "Pop" << endl;
    vc->pop();

  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test11(): \n" << e << endl;
  }
  delete vc;
}


void test12()
{
  ValidityChecker * vc = ValidityChecker::create( );
  try {
    Type realType = vc->realType();
    Type intType = vc->intType();
    Type boolType = vc->boolType();
    vc -> push();
    int initial_layer = vc->stackLevel();
    int initial_scope = vc->scopeLevel();
    Expr exprObj_trueID = vc->trueExpr();
    Expr exprObj_falseID = vc->notExpr(vc->trueExpr());
    vc->popto(initial_layer);
    EXPECT(vc->scopeLevel() == initial_scope, "Expected no change");
    EXPECT(vc->stackLevel() == initial_layer, "Expected no change");
    // TODO: what happens if we push and then popscope?
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test12(): \n" << e << endl;
  }
  delete vc;
}


void test13()
{
  CLFlags flags = ValidityChecker::createFlags();
  flags.setFlag("dagify-exprs", false);
  flags.setFlag("dump-log", ".test13.cvc");
  ValidityChecker* vc = ValidityChecker::create(flags);
  try {
    Expr rat_one = vc->ratExpr(1);
    Expr rat_two = vc->ratExpr(2);
    Expr rat_minus_one = vc->ratExpr(-1);

    bool query_result;
    query_result = vc->query(vc->eqExpr(rat_two,rat_one));
    cout << "2=1 " << query_result << endl;
    query_result = vc->query(vc->eqExpr(rat_two,rat_minus_one));
    cout << "2=-1 " << query_result << endl;
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test13(): \n" << e << endl;
  }
  delete vc;
}


Expr func1(ValidityChecker *vc)  {
 // local Expr 'tmp'
 Expr tmp = vc->varExpr("tmp", vc->boolType());
 return vc->trueExpr();
}


void test14()  {
  ValidityChecker *vc = ValidityChecker::create();
  try {
    // func call: ok
    Expr test1 = func1(vc);

    // func call: fail
    Expr test2 = func1(vc);
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test14(): \n" << e << endl;
  }
  delete vc;
}


void test15() {
  CLFlags flags = ValidityChecker::createFlags();
  flags.setFlag("dagify-exprs", false);
  ValidityChecker *vc = ValidityChecker::create(flags);
  try {

  /*****************************************************
   *          array declaration                        *
   *****************************************************/

  // array: index type
  Type index_type = vc->subrangeType(vc->ratExpr(0), 
				     vc->ratExpr(3));
  // array: data type
  Type data_type = vc->subrangeType(vc->ratExpr(0), 
				    vc->ratExpr(3));
  // array type: [0 .. 3] of 0 .. 3
  Type array_type = vc->arrayType(index_type, data_type);
  Expr arr = vc->varExpr("array", array_type);

  // array: [1,1,0,0]
  arr = vc->writeExpr(arr, vc->ratExpr(0), vc->ratExpr(1));
  arr = vc->writeExpr(arr, vc->ratExpr(1), vc->ratExpr(1));
  arr = vc->writeExpr(arr, vc->ratExpr(2), vc->ratExpr(0));
  arr = vc->writeExpr(arr, vc->ratExpr(3), vc->ratExpr(0));



  /*****************************************************
   *             forall Expr                           *
   *****************************************************/

  // for loop: index
  Expr id = vc->boundVarExpr("id", "0", vc->subrangeType(vc->ratExpr(0),
                                                         vc->ratExpr(2)));
  vector<Expr> vars;
  vars.push_back(id);

  // for loop: body
  Expr for_body = vc->leExpr(vc->readExpr(arr, id),
			     vc->readExpr(arr, vc->plusExpr(id, vc->ratExpr(1))));
  // forall expr
  Expr forall_expr = vc->forallExpr(vars, for_body);
  
  vc->push();
  check(vc, forall_expr);

  vector<Expr> assertions;
  cout << "Scope level: " << vc->scopeLevel() << endl;
  cout << "Counter-example:" << endl;
  //vc->getCounterExample(assertions);
  for (unsigned i = 0; i < assertions.size(); ++i) {
    vc->printExpr(assertions[i]);
  }
  cout << "End of counter-example" << endl << endl;
  vc->pop();
  
  /*****************************************************
   *            manual expansion                       *
   *****************************************************/

  Expr e1 = vc->leExpr(vc->readExpr(arr, vc->ratExpr(0)),
		       vc->readExpr(arr, vc->ratExpr(1)));
  Expr e2 = vc->leExpr(vc->readExpr(arr, vc->ratExpr(1)),
		       vc->readExpr(arr, vc->ratExpr(2)));
  Expr e3 = vc->leExpr(vc->readExpr(arr, vc->ratExpr(2)),
		       vc->readExpr(arr, vc->ratExpr(3)));
  Expr manual_expr = vc->andExpr(e1, vc->andExpr(e2, e3));



  /*****************************************************
   *            exists Expr                            *
   *****************************************************/

  // exists: index
  Expr id_ex = vc->varExpr("id_ex", vc->subrangeType(vc->ratExpr(0),
						     vc->ratExpr(2)));
  vector<Expr> vars_ex;
  vars_ex.push_back(id_ex);

  // exists: body
  Expr ex_body = vc->gtExpr(vc->readExpr(arr, id_ex),
			    vc->readExpr(arr, vc->plusExpr(id_ex, vc->ratExpr(1))));
  // exists expr
  Expr ex_expr = vc->existsExpr(vars_ex, ex_body);




  /*****************************************************
   *            ???     forall <==> manual expansion   *
   *****************************************************/
  
  cout << endl << "Checking forallExpr <==> manual expansion ..." << endl;
  if (vc->query(vc->iffExpr(forall_expr, manual_expr)))
    cout << "   -- yes." << endl;
  else {
    cout << "   -- no, with counter examples as " << endl;
    
    vector<Expr> assert1;
    vc->getCounterExample(assert1);
    for (unsigned int i = 0; i < assert1.size(); i ++)
      vc->printExpr(assert1[i]);
    
  }
  cout << endl;

  

  /*****************************************************
   *            ???     !forall <==> existsExpr        *
   *****************************************************/
  cout << endl << "Checking !forallExpr <==> existsExpr ..." << endl;
  if (vc->query(vc->iffExpr(vc->notExpr(forall_expr), ex_expr)))
    cout << "   -- yes." << endl;
  else if (vc->incomplete()) {
    cout << "   -- incomplete:" << endl;
    vector<string> reasons;
    vc->incomplete(reasons);
    for (unsigned int i = 0; i < reasons.size(); ++i)
      cout << reasons[i] << endl;
  }
  else {
    cout << "   -- no, with counter examples as " << endl;
 
    vector<Expr> assert2;
    //vc->getCounterExample(assert2);
    for (unsigned int i = 0; i < assert2.size(); i ++)
      vc->printExpr(assert2[i]);
  }
    
  cout << endl << "End of testcases." << endl << endl; 


  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test15(): \n" << e << endl;
  }
  delete vc;
}


void test16()  {
  ValidityChecker *vc = ValidityChecker::create();
  try {
    Type zto100 = vc->subrangeType(vc->ratExpr(0), vc->ratExpr(100));
    Expr mem = vc->varExpr("mem", vc->arrayType(zto100, vc->intType()));
    Expr a = vc->varExpr("a", zto100);
    Expr b = vc->varExpr("b", zto100);

    Expr lhs = vc->readExpr(vc->writeExpr(mem, a, vc->ratExpr(30)), b);
    Expr rhs = vc->readExpr(vc->writeExpr(mem, b, vc->ratExpr(40)), a);

    Expr q = vc->impliesExpr(vc->notExpr(vc->eqExpr(a, b)), vc->eqExpr(lhs, rhs));

    check(vc, q);

    vector<Expr> assertions;
    cout << "Scope level: " << vc->scopeLevel() << endl;
    cout << "Counter-example:" << endl;
    vc->getCounterExample(assertions);
    EXPECT(assertions.size() > 0, "Expected non-empty counter-example");
    for (unsigned i = 0; i < assertions.size(); ++i) {
      vc->printExpr(assertions[i]);
    }
    cout << "End of counter-example" << endl << endl;

    ExprMap<Expr> m;
    vc->getConcreteModel(m);
    ExprMap<Expr>::iterator it = m.begin(), end = m.end();
    if(it == end)
      cout << " Did not find concrete model for any vars" << endl;
    else {
      cout << "%Satisfiable  Variable Assignment: % \n";
      for(; it!= end; it++) {
	Expr eq;
	if(it->first.getType().isBool()) {
	  EXPECT((it->second).isBoolConst(),
		      "Bad variable assignement: e = "+(it->first).toString()
		      +"\n\n val = "+(it->second).toString());
	  if((it->second).isTrue())
	    eq = it->first;
	  else
	    eq = !(it->first);
	}
	else
	  eq = (it->first).eqExpr(it->second);
	//cout << Expr(ASSERT,  eq) << "\n";
      }
    }

  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test16(): \n" << e << endl;
  }
  delete vc;
}


void test17()  {
  ValidityChecker *vc = ValidityChecker::create();
  try {
    try {
      vector<string> selectors;
      vector<Expr> types;

      selectors.push_back("car");
      types.push_back(vc->intType().getExpr());
      selectors.push_back("cdr");
      types.push_back(vc->stringExpr("list"));

      Type badList = vc->dataType("list", "cons", selectors, types);
      EXPECT(false, "Typechecking exception expected");
    } catch(const TypecheckException&) {
      // fall through
    }
    delete vc;
    vc = ValidityChecker::create();
    {
      vector<string> constructors;
      vector<vector<string> > selectors(2);
      vector<vector<Expr> > types(2);

      constructors.push_back("cons");
      selectors[0].push_back("car");
      types[0].push_back(vc->intType().getExpr());
      selectors[0].push_back("cdr");
      types[0].push_back(vc->stringExpr("list"));
      constructors.push_back("null");

      Type list = vc->dataType("list", constructors, selectors, types);

      Expr x = vc->varExpr("x", vc->intType());
      Expr y = vc->varExpr("y", list);

      vector<Expr> args;
      args.push_back(x);
      args.push_back(y);
      Expr cons = vc->datatypeConsExpr("cons", args);

      Expr sel = vc->datatypeSelExpr("car", cons);
      bool b = check(vc, vc->eqExpr(sel, x));
      EXPECT(b, "Should be valid");

    }
    delete vc;
    vc = ValidityChecker::create();
    try {
      vector<string> names;
      vector<vector<string> > constructors(2);
      vector<vector<vector<string> > > selectors(2);
      vector<vector<vector<Expr> > > types(2);
      vector<Type> returnTypes;

      names.push_back("list1");

      selectors[0].resize(1);
      types[0].resize(1);
      constructors[0].push_back("cons1");
      selectors[0][0].push_back("car1");
      types[0][0].push_back(vc->intType().getExpr());
      selectors[0][0].push_back("cdr1");
      types[0][0].push_back(vc->stringExpr("list2"));

      names.push_back("list2");

      selectors[1].resize(1);
      types[1].resize(1);
      constructors[1].push_back("cons2");
      selectors[0][0].push_back("car2");
      types[0][0].push_back(vc->intType().getExpr());
      selectors[0][0].push_back("cdr2");
      types[0][0].push_back(vc->stringExpr("list1"));

      vc->dataType(names, constructors, selectors, types, returnTypes);
      EXPECT(false, "Typechecking exception expected");
    } catch(const TypecheckException&) {
      // fall through
    }
    delete vc;
    vc = ValidityChecker::create();
    {
      vector<string> names;
      vector<vector<string> > constructors(2);
      vector<vector<vector<string> > > selectors(2);
      vector<vector<vector<Expr> > > types(2);
      vector<Type> returnTypes;

      names.push_back("list1");

      selectors[0].resize(1);
      types[0].resize(1);
      constructors[0].push_back("cons1");
      selectors[0][0].push_back("car1");
      types[0][0].push_back(vc->intType().getExpr());
      selectors[0][0].push_back("cdr1");
      types[0][0].push_back(vc->stringExpr("list2"));

      names.push_back("list2");

      selectors[1].resize(2);
      types[1].resize(2);
      constructors[1].push_back("cons2");
      selectors[1][0].push_back("car2");
      types[1][0].push_back(vc->intType().getExpr());
      selectors[1][0].push_back("cdr2");
      types[1][0].push_back(vc->stringExpr("list1"));
      constructors[1].push_back("null");

      vc->dataType(names, constructors, selectors, types, returnTypes);

      Type list1 = returnTypes[0];
      Type list2 = returnTypes[1];

      Expr x = vc->varExpr("x", vc->intType());
      Expr y = vc->varExpr("y", list2);
      Expr z = vc->varExpr("z", list1);

      vector<Expr> args;
      args.push_back(x);
      args.push_back(y);
      Expr cons1 = vc->datatypeConsExpr("cons1", args);

      Expr isnull = vc->datatypeTestExpr("null", y);
      Expr hyp = vc->andExpr(vc->eqExpr(z, cons1), isnull);

      args.clear();
      Expr null = vc->datatypeConsExpr("null", args);

      args.push_back(x);
      args.push_back(null);
      Expr cons1_2 = vc->datatypeConsExpr("cons1", args);

      bool b = check(vc, vc->impliesExpr(hyp, vc->eqExpr(z, cons1_2)));
      EXPECT(b, "Should be valid");

    }
    delete vc;
    vc = ValidityChecker::create();
    {
      vector<string> constructors;
      vector<vector<string> > selectors(2);
      vector<vector<Expr> > types(2);

      constructors.push_back("A");
      constructors.push_back("B");

      Type two = vc->dataType("two", constructors, selectors, types);

      Expr x = vc->varExpr("x", two);
      Expr y = vc->varExpr("y", two);
      Expr z = vc->varExpr("z", two);

      vector<Expr> args;
      args.push_back(!vc->eqExpr(x,y));
      args.push_back(!vc->eqExpr(y,z));
      args.push_back(!vc->eqExpr(x,z));

      bool b = check(vc, !vc->andExpr(args));
      EXPECT(b, "Should be valid");

    }
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test17(): \n" << e << endl;
  }
  delete vc;
}


void test18()
{
  CLFlags flags = ValidityChecker::createFlags();
  flags.setFlag("tcc", true);
  ValidityChecker *vc = ValidityChecker::create(flags);
  try {
    vector<string> names;
    vector<vector<string> > constructors(3);
    vector<vector<vector<string> > > selectors(3);
    vector<vector<vector<Expr> > > types(3);
    vector<Type> returnTypes;

    names.push_back("nat");

    selectors[0].resize(2);
    types[0].resize(2);
    constructors[0].push_back("zero");
    constructors[0].push_back("succ");
    selectors[0][1].push_back("pred");
    types[0][1].push_back(vc->stringExpr("nat"));

    names.push_back("list");

    selectors[1].resize(2);
    types[1].resize(2);
    constructors[1].push_back("cons");
    selectors[1][0].push_back("car");
    types[1][0].push_back(vc->stringExpr("tree"));
    selectors[1][0].push_back("cdr");
    types[1][0].push_back(vc->stringExpr("list"));
    constructors[1].push_back("null");

    names.push_back("tree");

    selectors[2].resize(2);
    types[2].resize(2);
    constructors[2].push_back("leaf");
    constructors[2].push_back("node");
    selectors[2][1].push_back("data");
    types[2][1].push_back(vc->stringExpr("nat"));
    selectors[2][1].push_back("children");
    types[2][1].push_back(vc->stringExpr("list"));

    vc->dataType(names, constructors, selectors, types, returnTypes);

    Type nat = returnTypes[0];
    Type listType = returnTypes[1];
    Type tree = returnTypes[2];

    Expr x = vc->varExpr("x", nat);

    vector<Expr> args;
    Expr zero = vc->datatypeConsExpr("zero", args);
    Expr null = vc->datatypeConsExpr("null", args);
    Expr leaf = vc->datatypeConsExpr("leaf", args);

    vc->push();
    try {
      check(vc, vc->notExpr(vc->eqExpr(zero, null)));
      // TCCs not supported by CVC4 yet
      //EXPECT(false, "Should have caught tcc exception");
    } catch(const TypecheckException&) { }

    vc->pop();
    args.push_back(vc->datatypeSelExpr("pred",x));
    Expr spx = vc->datatypeConsExpr("succ", args);
    Expr spxeqx = vc->eqExpr(spx, x);
    vc->push();
    try {
      check(vc, spxeqx);
      // TCCs not supported by CVC4 yet
      //EXPECT(false, "Should have caught tcc exception");
    } catch(const TypecheckException&) { }

    vc->pop();
    bool b = check(vc, vc->impliesExpr(vc->datatypeTestExpr("succ", x), spxeqx));
    EXPECT(b, "Should be valid");

    b = check(vc, vc->orExpr(vc->datatypeTestExpr("zero", x),
                             vc->datatypeTestExpr("succ", x)));
    EXPECT(b, "Should be valid");

    Expr y = vc->varExpr("y", nat);
    Expr xeqy = vc->eqExpr(x, y);
    args.clear();
    args.push_back(x);
    Expr sx = vc->datatypeConsExpr("succ", args);
    args.clear();
    args.push_back(y);
    Expr sy = vc->datatypeConsExpr("succ", args);
    Expr sxeqsy = vc->eqExpr(sx,sy);
    b = check(vc, vc->impliesExpr(xeqy, sxeqsy));
    EXPECT(b, "Should be valid");

    b = check(vc, vc->notExpr(vc->eqExpr(sx, zero)));
    EXPECT(b, "Should be valid");

    b = check(vc, vc->impliesExpr(sxeqsy, xeqy));
    EXPECT(b, "Should be valid");

    b = check(vc, vc->notExpr(vc->eqExpr(sx, x)));
    EXPECT(b, "Should be valid");

  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test18(): \n" << e << endl;
  }
  delete vc;
}

void test19()
{
  CVC3::CLFlags flags = CVC3::ValidityChecker::createFlags();
  flags.setFlag("dagify-exprs", false);
  CVC3::ValidityChecker* vc = CVC3::ValidityChecker::create(flags);
  try {      
    CVC3::Type RealType=(vc->realType());
    CVC3::Type IntType=(vc->intType());
    CVC3::Type BoolType=(vc->boolType());
    CVC3::Type PtrType=(RealType);
    CVC3::Type HeapType=(vc->arrayType(PtrType, RealType));
         
    // -----------------
    //ASSERT(FORALL (CVCi: REAL): (Hs[CVCi] = Ht[CVCi]));
    //QUERY(Hs[(t6 + (3 * 1))] = Ht[(t6 + (3 * 1))]);
    CVC3::Expr Ad = vc->boundVarExpr("CVCi", "CVCi", RealType);
    CVC3::Expr Hs = vc->varExpr("Hs", HeapType);
    CVC3::Expr Ht = vc->varExpr("Ht", HeapType);
    CVC3::Expr t6 = vc->varExpr("t6", RealType);
  
    vector<CVC3::Expr> Vars;
    Vars.push_back(Ad);
    // Body= (Hs[Ad] = Ht[Ad])
    CVC3::Expr Body = vc->eqExpr(vc->readExpr(Hs, Ad), vc->readExpr(Ht, Ad));
      
    //A = forall (~i:REAL): Body
    CVC3::Expr A = vc->forallExpr(Vars, Body); 
        
    // Q = (Hs[t6] = Ht[t6])          
    CVC3::Expr Q = vc->eqExpr(vc->readExpr(Hs, t6), vc->readExpr(Ht, t6));
  
    // ----------- CHECK A -> Q
    vc->push();

    vc->assertFormula(A);

    cout<<"Checking formula "<<Q<<"\n in context "<<A<<"\n";
  
    bool Succ = vc->query(Q);

    EXPECT(Succ, "Expected valid formula");

  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test19(): \n" << e << endl;
  }
  delete vc;
}


void test20()  {
  ValidityChecker *vc = ValidityChecker::create();
  try {
    vector<string> names;
    vector<vector<string> > constructors(3);
    vector<vector<vector<string> > > selectors(3);
    vector<vector<vector<Expr> > > types(3);
    vector<Type> returnTypes;

    names.push_back("pair");

    selectors[0].resize(1);
    types[0].resize(1);
    constructors[0].push_back("p");
    selectors[0][0].push_back("p1");
    types[0][0].push_back(vc->stringExpr("t1"));
    selectors[0][0].push_back("p2");
    types[0][0].push_back(vc->stringExpr("t2"));

    names.push_back("t1");

    selectors[1].resize(5);
    types[1].resize(5);
    constructors[1].push_back("a");
    constructors[1].push_back("b");
    constructors[1].push_back("c");
    constructors[1].push_back("d");
    constructors[1].push_back("e");

    names.push_back("t2");

    selectors[2].resize(1);
    types[2].resize(1);
    constructors[2].push_back("cons");
    selectors[2][0].push_back("s0");
    types[2][0].push_back(vc->bitvecType(2).getExpr());
    selectors[2][0].push_back("s1");
    types[2][0].push_back(vc->arrayType(vc->intType(), vc->subrangeType(vc->ratExpr(0), vc->ratExpr(0))).getExpr());

    vc->dataType(names, constructors, selectors, types, returnTypes);

    EXPECT(returnTypes[0].card() == CARD_FINITE, "Expected finite");
    Unsigned size = returnTypes[0].sizeFinite();
    Unsigned i = 0;
    for (; i < size; ++i) {
      cout << i << ": ";
      vc->printExpr(returnTypes[0].enumerateFinite(i));
    }

  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test20(): \n" << e << endl;
  }
  delete vc;
}

void test21()  {
  ValidityChecker *vc = ValidityChecker::create();

  try {
    Type t = vc->realType();

    Expr x1 = vc->varExpr("x",t);

    Expr x2 = vc->exprFromString("x");
    cout << "x1: " << x1;
    cout << "\nx2: " << x2;
    EXPECT(x1 == x2, "Expected x1 == x2");

    Expr x3 = vc->exprFromString("x", SMTLIB_V2_LANG);
    cout << "\nx3: " << x3;
    EXPECT(x1 == x3, "Expected x1 == x3");

    Expr y1 = vc->varExpr("y",t);
    Expr y2 = vc->exprFromString("y");
    cout << "\ny1: " << y1;
    cout << "\ny2: " << y2;
    EXPECT(y1 == y2, "Expected y1 == y2");

    Expr y3 = vc->exprFromString("y", SMTLIB_V2_LANG);
    cout << "\ny3: " << y3;
    EXPECT(y1 == y3, "Expected y1 == y3");

    Expr a1 = vc->gtExpr(x1,vc->ratExpr(0,1));
    Expr a2 = vc->exprFromString("x > 0");
    cout << "\na1: " << a1;
    cout << "\na2: " << a2;
    EXPECT(a1 == a2, "Expected a1 == a2");

    Expr a3 = vc->exprFromString("(> x 0)", SMTLIB_V2_LANG);
    cout << "\na3: " << a3;
    EXPECT(a1 == a3, "Expected a1 == a3");

    Expr b1 = vc->ltExpr(x1,y1);
    Expr b2 = vc->exprFromString ("x < y");
    cout << "\nb1: " << b1;
    cout << "\nb2: " << b2;
    EXPECT(b1 == b2, "Expected b1 == b2");

    Expr b3 = vc->exprFromString ("(< x y)", SMTLIB_V2_LANG);
    cout << "\nb3: " << b3;
    EXPECT(b1 == b3, "Expected b1 == b3");

    Expr e1 = a1 && b1;
    Expr e2 = vc->exprFromString("x > 0 AND x < y");
    cout << "\ne1: " << e1;
    cout << "\ne2: " << e2;
    EXPECT(e1 == e2, "Expected e1 == e2");

    Expr e3 = vc->exprFromString("(and (> x 0) (< x y))", SMTLIB_V2_LANG);
    cout << "\ne3: " << e3;
    EXPECT(e1 == e3, "Expected e1 == e3");
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test21(): \n" << e << endl;
  }
  delete vc;
}

void test22() {
  CLFlags flags = ValidityChecker::createFlags();
  ValidityChecker* vc = ValidityChecker::create(flags);

  try {
    Type intType(vc->intType());
    Type fType(vc->funType(intType,intType));

    Op f(vc->createOp("f",fType));
    Expr x(vc->varExpr("x",intType));
    Expr fx(vc->exprFromString("f(x)"));

    Expr p(vc->exprFromString("FORALL (x:INT) : x < f(x)"));

    vector<vector<Expr> > patternvv;
    vector<Expr> patternv;
    patternv.push_back(fx);
    patternvv.push_back(patternv);

    vc->setTriggers(p,patternv);
    EXPECT( eqExprVecVecs(p.getTriggers(), patternvv),
                 "Expected p.getTriggers() == patternvv: " + p.toString() );

    vc->setTriggers(p,patternvv);

    EXPECT( eqExprVecVecs(p.getTriggers(), patternvv),
                 "Expected p.getTriggers() == patternvv: " + p.toString() );

    // [chris 10/4/2009] Not sure why, but this fails

    // Expr q(vc->exprFromString("FORALL (x:INT) : PATTERN (f(x)) : x < f(x)"));

    // EXPECT( eqExprVecVecs(q.getTriggers(), patternvv),
    //              "Expected q.getTriggers() == patternvv"  + q.toString());

    vector<Expr> vars;
    vars.push_back(x);
    Expr r(vc->forallExpr( vars, vc->ltExpr(x,fx), patternvv ));

    EXPECT( eqExprVecVecs(r.getTriggers(), patternvv),
                 "Expected r.getTriggers() == patternvv: " + r.toString() );

    Expr s(vc->exprFromString("FORALL (x:INT) : x > f(x)"));
    vc->setTrigger(s,fx);

    std::ostringstream stringHolder("");
    std::vector<std::vector<Expr> > trigsvv = s.getTriggers();
    stringHolder << trigsvv.size();
    EXPECT( trigsvv.size() == 1, 
                 "Expected s.getTriggers().size() == 1: " + stringHolder.str() );

    stringHolder.str("");
    std::vector<Expr> trigsv = trigsvv[0];
    stringHolder << trigsv.size();

    EXPECT( trigsv.size() == 1, 
                 "Expected s.getTriggers()[0].size() == 1: "
                 + stringHolder.str() );

    EXPECT( trigsv[0] == fx, 
                 "Expected s.getTriggers()[0][0] == fx: "
                 + (trigsv[0].toString()) );

    stringHolder.str("");
    Expr t(vc->exprFromString("FORALL (x:INT) : x > f(x)"));
    vc->setMultiTrigger(t,patternv);
    trigsvv = t.getTriggers();
    stringHolder << trigsvv.size();
    EXPECT( trigsvv.size() == 1,
                 "Expected t.getTriggers().size() == 1: " + stringHolder.str() );

    stringHolder.str("");
    trigsv = trigsvv[0];
    stringHolder << trigsv.size();
    EXPECT( trigsv.size() == 1,
                 "Expected t.getTriggers()[0].size() == 1: "
                 + stringHolder.str() );

    EXPECT( trigsv[0] == fx,
                 "Expected t.getTriggers()[0][0] == fx: "
                 + (trigsv[0].toString()) );
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test22(): \n" << e << endl;
  }
  delete vc;
}

void test23() {
  CLFlags flags = ValidityChecker::createFlags();
  ValidityChecker* vc = ValidityChecker::create(flags);

  try {
    Type intType(vc->intType());
    Type fType(vc->funType(intType,intType));

    Expr x(vc->varExpr("x",intType));
    Expr y(vc->varExpr("y",intType));
    Expr a(vc->varExpr("a",intType));
    Expr b(vc->varExpr("b",intType));

    Expr s(vc->exprFromString("x < y"));
    Expr t(vc->exprFromString("a < b"));

    cout << "s=" << s << "\nt=" << t << "\n";

    std::vector<Expr> oldExprs, newExprs;
    oldExprs.push_back(x);
    oldExprs.push_back(y);
    newExprs.push_back(a);
    newExprs.push_back(b);

    Expr u(s.substExpr(oldExprs,newExprs));
    cout << "u=" << u << "\n";

    EXPECT( t == u, "Expected t==u" );
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test23(): \n" << e << endl;
  }
  delete vc;
}

void test24() {
  CLFlags flags = ValidityChecker::createFlags();
  ValidityChecker* vc = ValidityChecker::create(flags);

  try {
    Type intType(vc->intType());
    Type aType(vc->arrayType(intType,intType));

    Expr a(vc->varExpr("a",aType));
    Expr x(vc->varExpr("x",intType));
    Expr ax(vc->exprFromString("a[x]"));

    Expr p(vc->exprFromString("FORALL (x:INT) : PATTERN (a[x]) : x < a[x]"));

    cout << p  << "\n";

    vector<vector<Expr> > pTriggers(p.getTriggers());
    EXPECT( pTriggers.size() == 1, 
            "Actual: " + int2string(pTriggers.size()));
    EXPECT( pTriggers[0].size() == 1, 
            "Actual: " + int2string( pTriggers[0].size()));
    /* We can't check that the trigger == ax, because x will have
     * been replaced with a bvar
     */
    EXPECT( pTriggers[0][0].getKind() == READ,
            "Actual: " + int2string(pTriggers[0][0].getKind()));
    EXPECT( pTriggers[0][0][0] == a,
            "Actual: " + pTriggers[0][0][0].toString() );

    Expr aPrime(vc->varExpr("a'",aType));
    Expr axPrime(vc->exprFromString("a'[x]"));

    ExprHashMap<Expr> substMap;
    substMap.insert(a,aPrime);

    Expr q(p.substExpr(substMap));

    cout << q << "\n";

    vector<vector<Expr> > qTriggers(q.getTriggers());
    EXPECT( qTriggers.size() == 1, 
            "Actual: " + 
            int2string(qTriggers.size()));
    EXPECT( qTriggers[0].size() == 1, 
            "Actual: " +
            int2string(qTriggers[0].size()));
    EXPECT( qTriggers[0][0].getKind() == READ,
            "Actual: " +
            int2string(qTriggers[0][0].getKind()));
    EXPECT( qTriggers[0][0][0] == aPrime,
            "Actual: " + qTriggers[0][0][0].toString() );
  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test24(): \n" << e << endl;
  }
  delete vc;
}


void test25() {
  CLFlags flags = ValidityChecker::createFlags();
  ValidityChecker* vc = ValidityChecker::create(flags);

  try {
    Type realType(vc->realType());

    Expr x = vc->ratExpr("-0.1");
    cout << "-0.1: " << x << endl;
    Expr y = vc->ratExpr("-1/10");
    cout << "-1/10: " << y << endl;
    Expr z = vc->ratExpr("-1","10",10);
    cout << "-1 over 10: " << z << endl;
    Expr w = vc->ratExpr(-1,10);
    cout << "-1 over 10 (ints): " << w << endl;

    EXPECT(x == y && y == z && z == w, "Error in rational constants");

  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test25(): \n" << e << endl;
  }
  delete vc;
}


void test26() {
  CLFlags flags = ValidityChecker::createFlags();
  ValidityChecker* vc = ValidityChecker::create(flags);

  try {
    Type bvType(vc->bitvecType(32));

    Expr x = vc->varExpr("x", bvType);
    Expr e1 = vc->newFixedConstWidthLeftShiftExpr(x, 16);
    Expr e2 = vc->newBVSHL(x, vc->newBVConstExpr(16, 32));

    bool b = check(vc, vc->eqExpr(e1, e2));
    EXPECT(b, "Should be valid");

    e1 = vc->newFixedRightShiftExpr(x, 16);
    e2 = vc->newBVLSHR(x, vc->newBVConstExpr(16, 32));

    b = check(vc, vc->eqExpr(e1, e2));
    EXPECT(b, "Should be valid");

    e2 = vc->newBVASHR(x, vc->newBVConstExpr(16, 32));
    b = check(vc, vc->eqExpr(e1, e2));
    EXPECT(!b, "Should be invalid");

  } catch(const Exception& e) {
    exitStatus = 1;
    cout << "*** Exception caught in test26(): \n" << e << endl;
  }
  delete vc;
}


int main(int argc, char** argv)
{
  int regressLevel = 3;
  if (argc > 1) regressLevel = atoi(argv[1]);
  cout << "Running API test, regress level = " << regressLevel << endl;
  exitStatus = 0;

  try {
    // [MGD for CVC4] This is a CVC3 test, and many tests had to be commented
    // out for CVC4 since the functionality is either unsupported or
    // as-yet-unimplemented in CVC4's compatibility layer.  For example,
    // subranges, predicate subtyping, quantifiers, and string expressions
    // are unavailable.  Also, Exprs and Types are distinct in CVC4 and it's
    // not clear how to implement Type::getExpr(), and Exprs and Ops are
    // indistinguishable, so getOp() and getOpExpr() have the same result.

    cout << "\n}\ntest26(): {" << endl;
    test26();
    //cout << "\ntest(): {" << endl;
    //test();
    cout << "\n}\ntest1(): {" << endl;
    test1();
    cout << "\n}\n\ntest2(): {" << endl;
    test2();
    cout << "\n}\n\ntest3(): {" << endl;
    test3();
    cout << "\n}\n\ntest4(): {" << endl;
    test4();
    if (regressLevel > 0) {
      cout << "\n}\n\ntest5(): {" << endl;
      test5();
    }
    cout << "\n}\n\ntest6(): {" << endl;
    test6();
    cout << "\n}\n\ntest7(): {" << endl;
    test7();
    //cout << "\n}\n\ntest8(): {" << endl;
    //test8();
    cout << "\n}\n\ntest9(" << 10*regressLevel+10 << "): {" << endl;
    test9(10*regressLevel+10);
    cout << "\nbvtest9(): {" << endl;
    bvtest9(regressLevel*3+2);
    cout << "\n}" << endl;

    // Test for obvious memory leaks
    int limit = 100 * regressLevel+10;
    for(int i=0; i<limit; ++i) {
      if(i % 100 == 0)	cout << "test10[" << i << "]" << endl;
      test10();
    }

    //cout << "\ntest11(): {" << endl;
    //test11();
    cout << "\n}\ntest12(): {" << endl;
    test12();
    cout << "\n}\ntest13(): {" << endl;
    test13();
    cout << "\n}\ntest14(): {" << endl;
    test14();
    //cout << "\n}\ntest15(): {" << endl;
    //test15();
    //cout << "\n}\ntest16(): {" << endl;
    //test16();
    cout << "\n}\ntest17(): {" << endl;
    test17();
    cout << "\n}\ntest18(): {" << endl;
    test18();
    cout << "\n}\ntest19(): {" << endl;
    test19();
    cout << "\ntest20(): {" << endl;
    test20();
    cout << "\n}\ntest21(): {" << endl;
    test21();
    //cout << "\n}\ntest22(): {" << endl;
    //test22();
    cout << "\n}\ntest23(): {" << endl;
    test23();
    cout << "\n}\ntest24(): {" << endl;
    test24();
    cout << "\n}\ntest25(): {" << endl;
    test25();

    /*
    if (regressLevel > 1) {
      cout << "\n}\ntestgeorge1(): {" << endl;
      testgeorge1();
      cout << "\n}\ntestgeorge2(): {" << endl;
      testgeorge2();
      cout << "\n}\ntestgeorge3(): {" << endl;
      testgeorge3();
      cout << "\n}\ntestgeorge4(): {" << endl;
      testgeorge4();
      cout << "\n}\ntestgeorge5(): {" << endl;
      testgeorge5();
    }
    */
    cout << "\n}" << endl;

  } catch(const Exception& e) {
    cout << "*** Exception caught: \n" << e << endl;
    exitStatus = 1;
  }
  if(exitStatus == 0)
    cout << "Program exits successfully." << endl;
  else
    cout << "Program exits with error status = " << exitStatus << "." << endl;
  return exitStatus;
}

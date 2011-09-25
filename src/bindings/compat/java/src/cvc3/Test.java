package cvc3;

import java.util.*;

class Test {

    public static void main(String args[]) {
      int regressLevel = 3;
      if (args.length > 1) {
         regressLevel = Integer.parseInt(args[0]);
      }
      
      boolean allPassed = true;
      System.out.println("Running API test, regress level = " + regressLevel);
      try {
	  System.out.println("\ntest():");
	  allPassed = test() && allPassed;
	  System.out.println("\n}\ntest1():");
	  allPassed = test1() && allPassed;
	  System.out.println("\n}\ntest2():");
	  allPassed = test2() && allPassed;
	  System.out.println("\n}\ntest3():");
	  allPassed = test3() && allPassed;
	  System.out.println("\n}\ntest4():");
	  allPassed = test4() && allPassed;
	  if (regressLevel > 0) {
	      System.out.println("\n}\n\ntest5():");
	      allPassed = test5() && allPassed;
	  }
	  System.out.println("\n}\ntest6():");
	  allPassed = test6() && allPassed;
	  System.out.println("\n}\ntest7():");
	  allPassed = test7() && allPassed;
	  System.out.println("\n}\ntest8():");
	  allPassed = test8() && allPassed;
	  System.out.println("\n}\ntest9():");
	  allPassed = test9(10 * regressLevel + 10) && allPassed;
	  System.out.println("\n}\nbvtest9():");
	  allPassed = bvtest9(regressLevel*3+2) && allPassed;

	  // Test for obvious memory leaks
	  int limit = 100 * regressLevel + 10;
	  for (int i = 0; i < limit; ++i) {
	      if (i % 100 == 0) System.out.println("test10[" + i + "]");
	      allPassed = test10() && allPassed;
	  }

	  System.out.println("\n}\ntest11():");
	  allPassed = test11() && allPassed;
	  System.out.println("\n}\ntest12():");
	  allPassed = test12() && allPassed;
	  System.out.println("\n}\ntest13():");
	  allPassed = test13() && allPassed;
	  System.out.println("\n}\ntest14():");
	  allPassed = test14() && allPassed;
	  System.out.println("\n}\ntest15():");
	  allPassed = test15() && allPassed;
	  System.out.println("\n}\ntest16():");
	  allPassed = test16() && allPassed;
	  System.out.println("\n}\ntest17():");
	  allPassed = test17() && allPassed;
	  System.out.println("\n}\ntest18():");
	  allPassed = test18() && allPassed;
	  System.out.println("\n}\ntest19():");
	  allPassed = test19() && allPassed;
      System.out.println("\n}\ntest22():");
      allPassed = test22() && allPassed;
      System.out.println("\n}\ntest23():");
      allPassed = test23() && allPassed;
	  /* :TODO:
	  if (regressLevel > 1) {
	      System.out.println("\n}\ntestgeorge1():");
	      George.testgeorge1();
	      System.out.println("\n}\ntestgeorge2():");
	      George.testgeorge2();
	      System.out.println("\n}\ntestgeorge3():");
	      George.testgeorge3();
	      System.out.println("\n}\ntestgeorge4():");
	      George.testgeorge4();
	      System.out.println("\n}\ntestgeorge5():");
	      George.testgeorge5();
	  }
	  */
	  System.out.println("\n}\ntestNonlinearBV():");
	  allPassed = testNonlinearBV() && allPassed;
	  System.out.println("\n}\ntestDistinct():");
	  allPassed = testDistinct() && allPassed;	  
	  System.out.println("\n}");
      } catch (Exception e) {
	  System.out.println("*** Exception caught: \n" + e);
	  e.printStackTrace(System.out);
	  allPassed = false;
      }
      
      if (allPassed) {
	  System.out.println("Program exits successfully.");
      }
      else {
	  System.out.println("Program exits with error status = " + allPassed + ".");
      }
      System.exit(allPassed ? 0 : 1);
    }


    public static void DebugAssert(boolean condition, String message) throws Cvc3Exception {
      if (!condition) {
        throw new DebugException(message);
      }
    }
    
    // Check whether e is valid
    public static boolean check(ValidityChecker vc, Expr e) throws Cvc3Exception {
	return check(vc, e, true);
    }
    
    public static boolean check(ValidityChecker vc, Expr e, boolean verbose) throws Cvc3Exception {
	if(verbose) {
	    System.out.println("Query: " + e.toString());
	}
	QueryResult result = vc.query(e);
	if (result == QueryResult.VALID) {
	    if (verbose) System.out.println("Valid\n");
	    return true;
	}
	else if (result == QueryResult.INVALID) {
	    if (verbose) System.out.println("Invalid\n");
	    return false;
	}
	if (verbose) System.out.println("Returned neither valid nor invalid\n");
	return false;
    }

    public static void printResult(QueryResult result) throws Cvc3Exception {
	if (result == QueryResult.VALID) {
	    System.out.println("Result Valid");
	}
	else if (result == QueryResult.INVALID) {
	    System.out.println("Result Invalid");
	}
	else if (result == QueryResult.UNKNOWN) {
	    System.out.println("Result Unknown");
	}
	else if (result == QueryResult.ABORT) {
	    System.out.println("Aborted");
	} else {
	    assert(false);
	}
    }

    // Make a new assertion - disposes expression
    public static void newAssertion(ValidityChecker vc, Expr e) throws Cvc3Exception {
      System.out.println("Assert: " + e);
      vc.assertFormula(e);
    }



    public static boolean test() throws Cvc3Exception {
	ValidityChecker vc = null;
	try {
	    vc = ValidityChecker.create();
	    
	    Type it = vc.intType();               //int
	    Op f = vc.createOp("f", vc.funType(it, it));
	    Expr z = vc.varExpr("z", it);
	    Expr e = vc.funExpr(f, vc.funExpr(f, z));
	    e = e.getChild(0);
	    Expr f2 = vc.funExpr(f, e);
	    Expr f3 = vc.funExpr(f, f2);
	    
	    DebugAssert(!e.equals(f2) && !e.equals(f3), "Refcount problems");
	    
	    Expr x = vc.boundVarExpr("x", "0", it);        //x0:int
	    List xs = new ArrayList();
	    xs.add(x);                                     //<x0:int>
	    Op lxsx = vc.lambdaExpr(xs, x);                //\<x0:int>. x0:int
	    Expr y = vc.ratExpr(1, 1);                     //1
	    List ys = new ArrayList();
	    ys.add(y);                                     //<1>
	    Expr lxsxy = vc.funExpr(lxsx, y);           //(\<x0:int>. x0:int)1
	    Expr lxsxys = vc.funExpr(lxsx, ys);         //(\<x0:int>. x0:int)<1>
	    System.out.println("Lambda application: " + lxsxy);
	    System.out.println("Simplified: " + vc.simplify(lxsxy));
	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	}
    }

    public static boolean test1() throws Cvc3Exception {
	// It is important that all Expr objects are deleted before vc is
	// deleted.  Therefore, we enclose them in a scope of try{ }catch
	// block.
	//
	// Also, vc methods may throw an Exception, and we want to delete vc
	// even in those exceptional cases.
	ValidityChecker vc = null;
	FlagsMut flags = null;
	try {
	    flags = ValidityChecker.createFlags(null);
	    flags.setFlag("dagify-exprs",false);
	    flags.setFlag("dump-log", ".test1.cvc");
	    vc = ValidityChecker.create(flags);
	    
	    boolean b = check(vc, vc.trueExpr());
	    DebugAssert(b, "Should be valid");

	    vc.push();
	    b = check(vc, vc.falseExpr());
	    DebugAssert(!b, "Should be invalid");
	    vc.pop();

	    // Check p OR ~p
	    
	    Expr p = vc.varExpr("p", vc.boolType());
	    Expr e = vc.orExpr(p, vc.notExpr(p));
	    
	    b = check(vc, e);
	    DebugAssert(b, "Should be valid");

	    // Check x = y . f(x) = f(y)

	    Expr x = vc.varExpr("x", vc.realType());
	    Expr y = vc.varExpr("y", vc.realType());

	    Type real2real = vc.funType(vc.realType(), vc.realType());
	    Op f = vc.createOp("f", real2real);
	    Expr fx = vc.funExpr(f, x);
	    Expr fy = vc.funExpr(f, y);

	    e = vc.impliesExpr(vc.eqExpr(x,y),vc.eqExpr(fx, fy));
	    b = check(vc, e);
	    DebugAssert(b, "Should be valid");

	    // Check f(x) = f(y) . x = y
	    
	    e = vc.impliesExpr(vc.eqExpr(fx,fy),vc.eqExpr(x, y));
	    int scopeLevel = vc.scopeLevel();
	    vc.push();
	    b = check(vc, e);
	    DebugAssert(!b, "Should be invalid");

	    // Get counter-example
	    
	    System.out.println("Scope level: " + vc.scopeLevel());
	    System.out.println("Counter-example:");
	    List assertions = vc.getCounterExample();
	    for (int i = 0; i < assertions.size(); ++i) {
		System.out.println((Expr)assertions.get(i));
	    }
	    System.out.println("End of counter-example");
	    System.out.println();

	    // Reset to initial scope
	    System.out.println("Resetting");
	    vc.pop();
	    DebugAssert(scopeLevel == vc.scopeLevel(), "scope error");
	    System.out.println("Scope level: " + vc.scopeLevel());
	    System.out.println();

	    // Check w = x & x = y & y = z & f(x) = f(y) & x = 1 & z = 2
	    
	    Expr w = vc.varExpr("w", vc.realType());
	    Expr z = vc.varExpr("z", vc.realType());

	    System.out.println("Push Scope");
	    System.out.println();
	    vc.push();

	    newAssertion(vc, vc.eqExpr(w, x));
	    newAssertion(vc, vc.eqExpr(x, y));
	    newAssertion(vc, vc.eqExpr(y, z));
	    newAssertion(vc, vc.eqExpr(fx, fy));
	    newAssertion(vc, vc.eqExpr(x, vc.ratExpr(1)));

	    System.out.println("simplify(w) = " + vc.simplify(w));
	    DebugAssert(vc.simplify(w).equals(vc.ratExpr(1)), "Expected simplify(w) = 1");
	    
	    newAssertion(vc, vc.eqExpr(z, vc.ratExpr(2)));
	    System.out.println("Inconsistent?: " + vc.inconsistent());
	    
	    System.out.println("Assumptions Used:");
	    assertions = vc.inconsistentReasons();
	    for (int i = 0; i < assertions.size(); ++i) {
		System.out.println((Expr)assertions.get(i));
	    }

	    System.out.println("Pop Scope");
	    System.out.println();
	    vc.pop();
    
	    System.out.println("simplify(w) = " + vc.simplify(w));
	    DebugAssert(vc.simplify(w).equals(w), "Expected simplify(w) = w");
    
	    System.out.println("Inconsistent?: " + vc.inconsistent());

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test1(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	    if (flags != null) flags.delete();
	}
    }


    public static boolean test2() throws Cvc3Exception {
	ValidityChecker vc = null;
	FlagsMut flags = null;
	try {
	    flags = ValidityChecker.createFlags(null);
	    flags.setFlag("dagify-exprs",false);
	    vc = ValidityChecker.create(flags);

	    Expr bexpr = vc.varExpr("b", vc.intType());
	    vc.assertFormula(vc.ltExpr(bexpr, vc.ratExpr(10)));

	    Expr c = vc.varExpr("c", vc.intType());
	    vc.assertFormula(vc.orExpr(vc.eqExpr(c, vc.ratExpr(0)), vc.eqExpr(c, vc.ratExpr(1))));

	    boolean b = check(vc, vc.leExpr(bexpr, vc.ratExpr(10)));
	    DebugAssert(b, "Should be valid");

	    b = check(vc, vc.falseExpr());
	    DebugAssert(!b, "Should be invalid");
	    vc.returnFromCheck();

	    // Check x = y . g(x,y) = g(y,x)
	    
	    Expr x = vc.varExpr("x", vc.realType());
	    Expr y = vc.varExpr("y", vc.realType());

	    Type real = vc.realType();
	    List RxR = new ArrayList();
	    RxR.add(real);
	    RxR.add(real);

	    Type realxreal2real = vc.funType(RxR, real);
	    Op g = vc.createOp("g", realxreal2real);

	    Expr gxy = vc.funExpr(g, x, y);
	    Expr gyx = vc.funExpr(g, y, x);

	    Expr e = vc.impliesExpr(vc.eqExpr(x,y),vc.eqExpr(gxy, gyx));
	    b = check(vc, e);
	    DebugAssert(b, "Should be valid");
	    
	    Op h = vc.createOp("h", realxreal2real);

	    Expr hxy = vc.funExpr(h, x, y);
	    Expr hyx = vc.funExpr(h, y, x);

	    e = vc.impliesExpr(vc.eqExpr(x,y),vc.eqExpr(hxy, hyx));
	    b = check(vc, e);
	    DebugAssert(b, "Should be valid");

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test2(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	    if (flags != null) flags.delete();
	}
    }


    public static ExprMut ltLex(ValidityChecker vc, Expr i1, Expr i2, Expr j1, Expr j2) throws Cvc3Exception {
	Expr res = vc.ltExpr(i1, j1);
	return vc.orExpr(res, vc.andExpr(vc.eqExpr(i1, j1), vc.ltExpr(i2, j2)));
    }

    public static ExprMut createTestFormula(ValidityChecker vc, Expr i1, Expr i2, Expr r1, Expr r2)
	throws Cvc3Exception {
	Expr lt1 = ltLex(vc, r1, r2, i1, i2);
	Expr lt2 = ltLex(vc, i2, i1, r2, r1);
	return vc.andExpr(lt1, lt2);
    }

    public static boolean test3() throws Cvc3Exception {
	ValidityChecker vc = null;
	FlagsMut flags = null;
	try {
	    flags = ValidityChecker.createFlags(null);
	    flags.setFlag("dagify-exprs",false);
	    vc = ValidityChecker.create(flags);
	    
	    Expr i = vc.varExpr("i", vc.realType());
	    Expr j = vc.varExpr("j", vc.realType());
	    Expr k = vc.varExpr("k", vc.realType());
	    
	    Expr one = vc.ratExpr(1);
	    
	    Expr test = createTestFormula(vc, i, j,
					  vc.minusExpr(i, one), vc.minusExpr(j, k));
	    
	    System.out.println("Trying test: " + test);
	    
	    vc.push();
	    QueryResult result = vc.query(test);
	    if (result == QueryResult.VALID) {
		System.out.println("Test Valid");
		vc.pop();
	    }
	    else {
		List assertions = vc.getCounterExample();
		System.out.println("Test Invalid Under Conditions:");
		for (int index = 0; index < assertions.size(); ++index) {
		    System.out.println(assertions.get(index));
		}
		
		// Try assertions one by one
		for (int index = 0; index < assertions.size(); ++index) {
		    Expr condition = vc.notExpr((Expr)assertions.get(index));
		    System.out.println("Trying test under condition: " + condition);
		    vc.pop();
		    vc.push();
		    printResult(vc.query(vc.impliesExpr(condition, test)));
		}
	    }
   
	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test3(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	    if (flags != null) flags.delete();
	}
    }


    public static boolean test4() throws Cvc3Exception {
	ValidityChecker vc = null;
	FlagsMut flags = null;
	try {
	    flags = ValidityChecker.createFlags(null);
	    flags.setFlag("dagify-exprs",false);
	    vc = ValidityChecker.create(flags);

	    Expr i = vc.varExpr("i", vc.realType());
	    Expr j = vc.varExpr("j", vc.realType());
	    Expr k = vc.varExpr("k", vc.realType());
	    
	    Expr one = vc.ratExpr(1);

	    Expr test = createTestFormula(vc, i, j,
					  vc.minusExpr(i, one), vc.minusExpr(j, k));

	    System.out.println("Trying test: " + test);

	    vc.push();
	    QueryResult result = vc.query(test);
	    if (result == QueryResult.VALID) {
		System.out.println("Test Valid");
	    }
	    else {
		List assertions = vc.getCounterExample();
		System.out.println("Test Invalid Under Conditions:");
		for (int index = 0; index < assertions.size(); ++index) {
		    System.out.println(assertions.get(index));
		}

		// Try assertions one by one
		for (int index = 0; index < assertions.size(); ++index) {
		    Expr condition = vc.notExpr((Expr)assertions.get(index));
		    System.out.println("Trying test under condition: " + condition);
		    vc.pop();
		    vc.push();
		    printResult(vc.query(vc.impliesExpr(condition, test)));
		}
	    }

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test4(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	    if (flags != null) flags.delete();
	}
    }


    public static void findLeaves(Expr e, List l) throws Cvc3Exception {
	int ar = e.arity();
	if (ar > 0) {
	    for (int i = 0; i < ar; ++i) {
		findLeaves(e.getChild(i), l);
	    }
	    return;
	}
	l.add(e);
    }

    public static boolean hasij(Expr e, Expr i, Expr j) throws Cvc3Exception {
	int ar = e.arity();
	if (ar > 0) {
	    for (int k = 0; k < ar; ++k)
		if (hasij(e.getChild(k), i, j)) return true;
	    return false;
	}
	if (e.equals(i) || e.equals(j)) return true;
	return false;
    }

    public static Expr plusExpr(ValidityChecker vc, List kids) throws Cvc3Exception {
	if (kids.size() == 0) return vc.ratExpr(0);
	else if (kids.size() == 1) return (Expr)kids.get(0);
	else if (kids.size() == 2) return vc.plusExpr((Expr)kids.get(0), (Expr)kids.get(1));
	else {
	    Expr r = (Expr)kids.get(kids.size() - 1);
	    kids.remove(kids.size() - 1);
	    return vc.plusExpr(plusExpr(vc, kids), r);
	}
    }

    public static boolean test5() throws Cvc3Exception {
	ValidityChecker vc = null;
	FlagsMut flags = null;
	try {
	    flags = ValidityChecker.createFlags(null);
	    flags.setFlag("dagify-exprs",false);
	    vc = ValidityChecker.create(flags);

	    Expr i = vc.varExpr("i1", vc.realType());
	    Expr j = vc.varExpr("i2", vc.realType());
	    Expr p = vc.varExpr("p", vc.realType());
	    Expr q = vc.varExpr("q", vc.realType());
	    Expr r = vc.varExpr("r", vc.realType());
	    Expr a = vc.varExpr("arb_addr", vc.realType());
	    Expr N = vc.varExpr("N", vc.realType());

	    Expr M = vc.varExpr("M", vc.arrayType(vc.realType(), vc.realType()));

	    Expr M2 = vc.writeExpr(M, vc.plusExpr(q, i), vc.readExpr(M, vc.plusExpr(r, i)));
	    
	    Expr M1 = vc.writeExpr(M, vc.plusExpr(p, j), vc.readExpr(M, vc.plusExpr(r, j)));

	    Expr e = vc.eqExpr(vc.readExpr(vc.writeExpr(M2, vc.plusExpr(p, j),
							vc.readExpr(M2, vc.plusExpr(r, j))), a),
			       vc.readExpr(vc.writeExpr(M1, vc.plusExpr(q, i),
							vc.readExpr(M1, vc.plusExpr(r, i))), a));

	    Expr one = vc.ratExpr(1);
	    Expr zero = vc.ratExpr(0);

	    Expr qmp = vc.minusExpr(q, p);
	    Expr qmr = vc.minusExpr(q, r);

	    List hyp = new ArrayList();
	    hyp.add(vc.ltExpr(i, j));
	    //   hyp.add(vc.orExpr(vc.geExpr(qmp, N), vc.leExpr(qmp, zero)));
	    //   hyp.add(vc.orExpr(vc.geExpr(qmr, N), vc.leExpr(qmr, zero)));

	    Expr test = vc.impliesExpr(vc.andExpr(hyp), e);
	    Expr query;

	    System.out.println("Checking verification condition:" + test);

	    vc.push();
	    QueryResult result = vc.query(test);
	    if (result == QueryResult.VALID) {
		System.out.println("Test Valid");
	    }
	    else {
		List conditions = new ArrayList();
		int req;
		
		List assertions = vc.getCounterExample();
		
		System.out.println("Invalid Under Conditions:");
		for (int index = 0; index < assertions.size(); ++index) {
		    if (((Expr)assertions.get(index)).equals(vc.notExpr(test))) {
			for (; index < assertions.size()-1; ++index) {
			    assertions.set(index, assertions.get(index+1));
			}
			assertions.remove(assertions.size() - 1);
			break;
		    }
		}
		for (int index = 0; index < assertions.size(); ++index) {
		    System.out.println(assertions.get(index));
		}

		System.out.println();
		
		// Try assertions one by one
		for (int index = 0; index < assertions.size(); ++index) {
		    e = (Expr)assertions.get(index);
      
		    // Check condition for eligibility
		    if (e.isNot()) {
			System.out.println("Condition ineligible: negation: " + e);
			System.out.println();
			continue;
		    }
		    if (e.isEq()) {
			req = 2;
		    }
		    else req = 1;
		    
		    List leaves = new ArrayList();
		    findLeaves(e, leaves);
		    for (int index2 = 0; index2 < leaves.size(); ++index2) {
			if (!((Expr)leaves.get(index2)).isVar() ||
			    ((Expr)leaves.get(index2)).equals(i) ||
			    ((Expr)leaves.get(index2)).equals(j) ||
			    ((Expr)leaves.get(index2)).equals(a))
			    continue;
			req--;
		    }
		    if (req > 0) {
			System.out.println("Condition ineligible: not enough non-loop variables: " + e);
			System.out.println();
			continue;
		    }

		    System.out.println("Condition selected: " + e);
		    System.out.println();

		    conditions.add(vc.notExpr(e));
		    System.out.println("Trying verification condition with hypothesis: "
				       + vc.andExpr(conditions));
		    vc.pop();
		    vc.push();
		    query = vc.impliesExpr(vc.andExpr(conditions), test);
		    result = vc.query(test);
		    if (result == QueryResult.VALID) {
			System.out.println("Result Valid");
			break;
		    }
		    else {
			assertions = vc.getCounterExample();

			System.out.println("Invalid Under Conditions:");
			for (int index2 = 0; index2 < assertions.size(); ++index2) {
			    if (((Expr)assertions.get(index2)).equals(vc.notExpr(query))) {
				for (; index2 < assertions.size()-1; ++index2) {
				    assertions.set(index2, assertions.get(index2+1));
				}
				assertions.remove(assertions.size() - 1);
				break;
			    }
			}

			for (int index2 = 0; index2 < assertions.size(); ++index2) {
			    System.out.println(assertions.get(index2));
			}
			System.out.println();
			index = assertions.size();
		    }
		}
		
		System.out.println();
		System.out.println("Attempting to remove loop variables");
		// replace loop variables in conditions
		List newConditions = new ArrayList();
		List newPlus = new ArrayList();
		boolean foundi, foundj, negi, negj;
		Expr minusone = vc.ratExpr(-1);
		int index;
		for (index = 0; index < conditions.size(); ++index) {
		    if (((Expr)conditions.get(index)).getChild(0).isEq()) {
			e = vc.simplify(
					vc.minusExpr(((Expr)conditions.get(index)).getChild(0).getChild(0),
						     ((Expr)conditions.get(index)).getChild(0).getChild(1)));
			if (hasij(e, i, j)) {
			    if (e.isPlus()) {
				newPlus.clear();
				newPlus.add(e.getChild(0));
				foundi = foundj = negi = negj = false;
				for (int index2 = 1; index2 < e.arity(); index2++) {
				    Expr term = e.getChild(index2);
				    if (term.equals(i) && !foundi) foundi = true;
				    else if (term.equals(j) && !foundj) {
					foundj = true;
					negj = true;
				    }
				    else if (term.isMult()
					     && term.getChild(0).equals(minusone)
					     && term.getChild(1).equals(i)
					     && !foundi) {
					foundi = true;
					negi = true;
				    }
				    else if (term.isMult()
					     && term.getChild(0).equals(minusone)
					     && term.getChild(1).equals(j)
					     && !foundj)
					foundj = true;
				    else newPlus.add(term);
				}
				if (foundi && foundj && (negi && negj || (!negi && !negj))) {
				    e = plusExpr(vc, newPlus);
				    if (negi && negj) e = vc.uminusExpr(e);
				    e = vc.simplify(e);
				    if (!hasij(e, i, j)) {
					newConditions.add(vc.orExpr(vc.geExpr(e, N), vc.leExpr(e, zero)));
					continue;
				    }
				}
			    }
			    System.out.println("Unable to remove loop variables:" + e);
			    break;
			}
		    }
		    newConditions.add(conditions.get(index));
		}
		if (index == conditions.size()) {
		    System.out.println("Loop variables successfully removed:");
		    Expr cond = (newConditions.size()>0)?
			vc.andExpr(newConditions) : vc.trueExpr();
		    System.out.println(cond);
		    
		    List loopConditions = new ArrayList();
		    loopConditions.add(cond);
		    loopConditions.add(vc.geExpr(i, one));
		    loopConditions.add(vc.geExpr(j, one));
		    loopConditions.add(vc.leExpr(i, N));
		    loopConditions.add(vc.leExpr(j, N));
		    vc.pop();
		    vc.push();
		    System.out.println("Final query");
		    printResult(vc.query(vc.impliesExpr(vc.andExpr(loopConditions), test)));
		}
	    }
	    
	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test5(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	    if (flags != null) flags.delete();
	}
    }



    public static boolean test6() throws Cvc3Exception {
	ValidityChecker vc1 = null;
	ValidityChecker vc2 = null;
	try {
	    vc1 = ValidityChecker.create();
	    vc2 = ValidityChecker.create();

	    Type real1 = vc1.realType();
	    
	    Expr x1 = vc1.varExpr("x", real1);
	    Expr y1 = vc1.boundVarExpr("y", "0", real1);
	    
	    System.out.println("vc1 variables: " + x1 + ", " + y1);
	    
	    Expr x2 = vc2.varExpr("x", vc2.importType(real1));
	    Expr y2 = vc2.boundVarExpr("y", "0", vc2.realType());
	    
	    System.out.println("vc2 variables: " + x2 + ", " + y2);
	    System.out.println("vars imported to vc2 from vc1: "
			       + vc2.importExpr(x1) + ", " + vc2.importExpr(y1));
	    Expr t1 = vc1.trueExpr();
	    Expr and1 = vc1.andExpr(t1, vc1.falseExpr());
	    Op f1 = vc1.createOp("f", vc1.funType(real1, real1));
	    Expr fx1 = vc1.funExpr(f1, x1);
	    Expr f5_1 = vc1.funExpr(f1, vc1.ratExpr(5,1));
	    Type rt1 = vc1.recordType("foo", real1, "bar", real1);
	    Expr r1 = vc1.recordExpr("foo", fx1, "bar", f5_1);
	    Expr r1_eq = vc1.eqExpr(r1, vc1.recUpdateExpr(r1, "foo", f5_1));
	    Type art1 = vc1.arrayType(real1, rt1);
	    Expr ar1 = vc1.varExpr("ar", art1);
	    Expr ar_eq1 = vc1.eqExpr(vc1.writeExpr(ar1, x1, r1), ar1);
	    Expr query1 = vc1.eqExpr(vc1.recSelectExpr(vc1.readExpr(ar1, x1), "foo"),
				     vc1.recSelectExpr(r1, "bar"));
	    
	    System.out.println("*** VC #1:");
	    newAssertion(vc1, r1_eq);
	    newAssertion(vc1, ar_eq1);
	    check(vc1, query1);
	    
	    System.out.println("*** VC #2:");
	    newAssertion(vc2, vc2.importExpr(r1_eq));
	    newAssertion(vc2, vc2.importExpr(ar_eq1));
	    check(vc2, vc2.importExpr(query1));
	    
	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test6(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc1 != null) vc1.delete();
	    if (vc2 != null) vc2.delete();
	}
    }



    public static boolean test7() throws Cvc3Exception {
	ValidityChecker vc1 = null;
	ValidityChecker vc2 = null;
	try {
	    vc1 = ValidityChecker.create();
	    vc2 = ValidityChecker.create();

	    Expr e1 = vc1.varExpr("e1", vc1.realType());
	    Expr e2 = vc2.varExpr("e2", vc2.realType());
	    newAssertion(vc2, vc2.eqExpr(vc2.importExpr(e1), e2));

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test7(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc1 != null) vc1.delete();
	    if (vc2 != null) vc2.delete();
	}
    }



    public static boolean test8() throws Cvc3Exception {
	ValidityChecker vc = null;
	try {
	    vc = ValidityChecker.create();

	    List vec = new ArrayList();
	    vec.add(vc.boundVarExpr("x", "x", vc.realType()));
	    Expr lambda = vc.lambdaExpr(vec, vc.falseExpr()).getExpr();
	    try {
		Type t = vc.subtypeType(lambda, vc.nullExpr());
		DebugAssert(false, "Typechecking exception expected");
	    } catch(TypecheckException e) {
		// fall through
	    }
	    
	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test5(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	}
    }



    public static ExprMut adder(ValidityChecker vc, Expr a, Expr b, Expr c) throws Cvc3Exception {
	return vc.notExpr(vc.iffExpr(vc.notExpr(vc.iffExpr(a,b)),c));
    }

    public static ExprMut carry(ValidityChecker vc, Expr a, Expr b, Expr c) throws Cvc3Exception {
	return vc.orExpr(vc.andExpr(a,b), vc.orExpr(vc.andExpr(b,c),vc.andExpr(a,c)));
    }

    public static List add(ValidityChecker vc, List a, List b) throws Cvc3Exception {
	int N = a.size();
	Expr c = vc.falseExpr();
	
	List sum = new ArrayList();
	for (int i = 0; i < N; i++) {
	    sum.add(adder(vc,(Expr)a.get(i),(Expr)b.get(i),c));
	    c = carry(vc,(Expr)a.get(i),(Expr)b.get(i),c);
	}
	return sum;
    }

    public static ExprMut vectorEq(ValidityChecker vc, List a, List b) throws Cvc3Exception {
	int N = a.size();
	ExprMut result = vc.trueExpr();
	
	for (int i = 0; i < N; i++) {
	    result = vc.andExpr(result, vc.iffExpr((Expr)a.get(i), (Expr)b.get(i)));
	}
	return result;
    }


    public static boolean test9(int N) throws Cvc3Exception {
	ValidityChecker vc = null;
	try {
	    vc = ValidityChecker.create();

	    int i;
	    List a = new ArrayList();
	    List b = new ArrayList();
	    
	    for (i=0; i < N; i++) {
		a.add(vc.varExpr("a" + Integer.toString(i), vc.boolType()));
		b.add(vc.varExpr("b" + Integer.toString(i), vc.boolType()));
	    }
	    
	    List sum1 = add(vc,a,b);
	    List sum2 = add(vc,b,a);
	    
	    Expr q = vectorEq(vc,sum1,sum2);
	    
	    check(vc, q);
	    
	    //  Proof p = vc.getProof();

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test9(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	}
    }


  public static boolean test22() throws Cvc3Exception {
    ValidityChecker vc = null;

    try {
      vc = ValidityChecker.create();
      Type intType = vc.intType();
      Type fType = vc.funType(intType, intType);

      Op f = vc.createOp("f", fType);
      Expr x = vc.varExpr("x", intType);
      Expr fx = vc.exprFromString("f(x)");

      Expr p = vc.exprFromString("FORALL (x:INT) : x < f(x)");

      List patternvv = new ArrayList();
      List patternv = new ArrayList();
      patternv.add(fx);
      patternvv.add(patternv);

      vc.setTriggers(p, patternv);
      DebugAssert(patternvv.equals(p.getTriggers()),
          "Expected p.getTriggers() == patternvv: " + p.toString());

      vc.setMultiTriggers(p, patternvv);

      DebugAssert(patternvv.equals(p.getTriggers()),
          "Expected p.getTriggers() == patternvv: " + p.toString());

      List vars = new ArrayList();
      vars.add(x);
      Expr r = vc.forallExpr(vars, vc.ltExpr(x, fx), patternv);

      DebugAssert(patternvv.equals(r.getTriggers()),
          "Expected r.getTriggers() == patternvv: " + r.toString());

      Expr s = vc.exprFromString("FORALL (x:INT) : x > f(x)");
      vc.setTrigger(s, fx);

      List trigsvv = s.getTriggers();
      DebugAssert(trigsvv.size() == 1, "Expected s.getTriggers().size() == 1: "
          + trigsvv.size());

      List trigsv = (List)trigsvv.get(0);
      DebugAssert(trigsv.size() == 1, "Expected s.getTriggers()[0].size() == 1: "
          + trigsv.size());

      DebugAssert(fx.equals(trigsv.get(0)),
          "Expected s.getTriggers()[0][0] == fx: " + (trigsv.get(0)));

      Expr t = vc.exprFromString("FORALL (x:INT) : x > f(x)");
      vc.setMultiTrigger(t, patternv);
      trigsvv = t.getTriggers();
      DebugAssert(trigsvv.size() == 1, "Expected t.getTriggers().size() == 1: "
          + trigsvv.size());

      trigsv = (List)trigsvv.get(0);
      DebugAssert(trigsv.size() == 1, "Expected t.getTriggers()[0].size() == 1: "
          + trigsv.size());

      DebugAssert(fx.equals(trigsv.get(0)),
          "Expected t.getTriggers()[0][0] == fx: " + (trigsv.get(0)));

      Expr u = vc.forallExprMultiTriggers(vars, vc.ltExpr(x, fx), patternvv);

      DebugAssert(patternvv.equals(u.getTriggers()),
          "Expected u.getTriggers() == patternvv: " + u.toString());
    
    } catch (Exception e) {
      System.out.println("*** Exception caught in test22(): \n" + e);
      e.printStackTrace(System.out);
      return false;
    } finally {
      if (vc != null)
        vc.delete();
    }
    return true;
  }
    
  private static boolean test23() throws Cvc3Exception {
    ValidityChecker vc = null;

    try {
      vc = ValidityChecker.create();
      Type intType = vc.intType();

      Expr x = vc.varExpr("x",intType);
      Expr y= vc.varExpr("y",intType);
      Expr a = vc.varExpr("a",intType);
      Expr b = vc.varExpr("b",intType);

      Expr s = vc.exprFromString("x < y");
      Expr t = vc.exprFromString("a < b");

      System.out.println( "s=" + s + "\nt=" + t );

      List oldExprs = new ArrayList(), newExprs = new ArrayList();
      oldExprs.add(x);
      oldExprs.add(y);
      newExprs.add(a);
      newExprs.add(b);

      Expr u = s.subst(oldExprs,newExprs);
      System.out.println( "u=" + u );

      DebugAssert( t.equals(u), "Expected t==u" );
    } catch(Throwable e) {
      System.out.println( "*** Exception caught in test23(): ");
      e.printStackTrace(System.out);
      return false;
    } finally {
      if (vc != null)
        vc.delete();
    }
    return true;
  }

    public static ExprMut bvadder(ValidityChecker vc, Expr a, Expr b, Expr c) throws Cvc3Exception {
	return vc.newBVXorExpr(a, vc.newBVXorExpr(b, c));
    }


    public static ExprMut bvcarry(ValidityChecker vc, Expr a, Expr b, Expr c) throws Cvc3Exception {
	return vc.newBVOrExpr(vc.newBVAndExpr(a,b), vc.newBVOrExpr(vc.newBVAndExpr(b,c),vc.newBVAndExpr(a,c)));
    }

    public static List bvadd(ValidityChecker vc, List a, List b) throws Cvc3Exception {
	int N=a.size();
	Expr c = vc.newBVConstExpr(new Rational(0, vc.embeddedManager()), 1);
	
	List sum = new ArrayList();
	for (int i = 0; i < N; i++) {
	    sum.add(bvadder(vc,(Expr)a.get(i),(Expr)b.get(i),c));
	    c = bvcarry(vc,(Expr)a.get(i),(Expr)b.get(i),c);
	}
	return sum;
    }


    public static ExprMut bvvectorEq(ValidityChecker vc, List a, List b) throws Cvc3Exception {
	int N = a.size();
	ExprMut result = vc.newBVConstExpr("1");
	
	for (int i = 0; i < N; i++) {
	    result = vc.newBVAndExpr(result, vc.newBVXnorExpr((Expr)a.get(i), (Expr)b.get(i)));
	}
	return result;
    }


    public static boolean bvtest9(int N) throws Cvc3Exception {
	ValidityChecker vc = null;
	try {
	    vc = ValidityChecker.create();
	    
	    Expr a, b, sum1;
	    a = vc.varExpr("a", vc.bitvecType(N));
	    b = vc.varExpr("b", vc.bitvecType(N));
	    List kids = new ArrayList();
	    kids.add(a);
	    kids.add(b);
	    sum1 = vc.newBVPlusExpr(N, kids);
	    
	    List avec = new ArrayList();
	    List bvec = new ArrayList();
	    List sum1vec = new ArrayList();
	    for (int i = 0; i < N; i++) {
		avec.add(vc.newBVExtractExpr(a, i, i));
		bvec.add(vc.newBVExtractExpr(b, i, i));
		sum1vec.add(vc.newBVExtractExpr(sum1, i, i));
	    }
	    
	    List sum2 = bvadd(vc,avec,bvec);
	    
	    Expr q = bvvectorEq(vc,sum1vec,sum2);
	    
	    check(vc, vc.eqExpr(q,vc.newBVConstExpr("1")));

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in bvtest9(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	}
    }


    public static boolean test10() throws Cvc3Exception {
	ValidityChecker vc = null;
	try {
	    vc = ValidityChecker.create();
	    
	    Expr x = vc.varExpr("x", vc.realType());
	    Expr y = vc.varExpr("y", vc.realType());
	    
	    Type real = vc.realType();
	    List RxR = new ArrayList();
	    RxR.add(real);
	    RxR.add(real);

	    Type realxreal2real = vc.funType(RxR, real);
	    Op g = vc.createOp("g", realxreal2real);
	    
	    Expr gxy = vc.funExpr(g, x, y);
	    Expr gyx = vc.funExpr(g, y, x);

	    Expr ia = vc.eqExpr(x,y);
	    Expr ib = vc.eqExpr(gxy, gyx);

	    Expr e = vc.impliesExpr(vc.eqExpr(x,y),vc.eqExpr(gxy, gyx));
	    check(vc, e, false);

	    Op h = vc.createOp("h", realxreal2real);
	    
	    Expr hxy = vc.funExpr(h, x, y);
	    Expr hyx = vc.funExpr(h, y, x);
	    
	    e = vc.impliesExpr(vc.eqExpr(x,y),vc.eqExpr(hxy, hyx));
	    check(vc, e, false);

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test10(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	}
    }



    public static int printImpliedLiterals(ValidityChecker vc) throws Cvc3Exception {
	int count = 0;
	System.out.println("Implied Literals:");
	Expr impLit = vc.getImpliedLiteral();
	while (!impLit.isNull()) {
	    ++count;
	    System.out.println(impLit);
	    impLit = vc.getImpliedLiteral();
	}
	return count;
    }

    public static boolean test11() throws Cvc3Exception {
	ValidityChecker vc = null;
	try {
	    vc = ValidityChecker.create();
	    
	    Expr x = vc.varExpr("x", vc.realType());
	    Expr y = vc.varExpr("y", vc.realType());
	    Expr z = vc.varExpr("z", vc.realType());
	    
	    Type real = vc.realType();
	    Type real2real = vc.funType(real, real);
	    Type real2bool = vc.funType(real, vc.boolType());
	    Op f = vc.createOp("f", real2real);
	    Op p = vc.createOp("p", real2bool);

	    Expr fx = vc.funExpr(f, x);
	    Expr fy = vc.funExpr(f, y);
	    
	    Expr px = vc.funExpr(p, x);
	    Expr py = vc.funExpr(p, y);
	    
	    Expr xeqy = vc.eqExpr(x, y);
	    Expr yeqx = vc.eqExpr(y, x);
	    Expr xeqz = vc.eqExpr(x, z);
	    Expr zeqx = vc.eqExpr(z, x);
	    Expr yeqz = vc.eqExpr(y, z);
	    Expr zeqy = vc.eqExpr(z, y);
	    
	    int c;

	    vc.registerAtom(vc.eqExpr(x,vc.ratExpr(0,1)));
	    vc.registerAtom(xeqy);
	    vc.registerAtom(yeqx);
	    vc.registerAtom(xeqz);
	    vc.registerAtom(zeqx);
	    vc.registerAtom(yeqz);
	    vc.registerAtom(zeqy);
	    vc.registerAtom(px);
	    vc.registerAtom(py);
	    vc.registerAtom(vc.eqExpr(fx, fy));

	    System.out.println("Push");
	    vc.push();

	    System.out.println("Assert x = y");
	    vc.assertFormula(xeqy);
	    c = printImpliedLiterals(vc);
	    DebugAssert(c==3,"Implied literal error 0");

	    System.out.println("Push");
	    vc.push();
	    System.out.println("Assert x /= z");
	    vc.assertFormula(vc.notExpr(xeqz));
	    c = printImpliedLiterals(vc);
	    DebugAssert(c==4,"Implied literal error 1");
	    System.out.println("Pop");
	    vc.pop();
	    
	    System.out.println("Push");
	    vc.push();
	    System.out.println("Assert y /= z");
	    vc.assertFormula(vc.notExpr(yeqz));
	    c = printImpliedLiterals(vc);
	    DebugAssert(c==4,"Implied literal error 2");
	    System.out.println("Pop");
	    vc.pop();
	    
	    System.out.println("Push");
	    vc.push();
	    System.out.println("Assert p(x)");
	    vc.assertFormula(px);
	    c = printImpliedLiterals(vc);
	    DebugAssert(c==2,"Implied literal error 3");
	    System.out.println("Pop");
	    vc.pop();

	    System.out.println("Push");
	    vc.push();
	    System.out.println("Assert p(y)");
	    vc.assertFormula(py);
	    c = printImpliedLiterals(vc);
	    DebugAssert(c==2,"Implied literal error 4");
	    System.out.println("Pop");
	    vc.pop();

	    System.out.println("Pop");
	    vc.pop();
	    
	    System.out.println("Push");
	    vc.push();
	    System.out.println("Assert y = x");
	    vc.assertFormula(yeqx);
	    c = printImpliedLiterals(vc);
	    DebugAssert(c==3,"Implied literal error 5");
	    System.out.println("Pop");
	    vc.pop();

	    System.out.println("Push");
	    vc.push();
	    System.out.println("Assert p(x)");
	    vc.assertFormula(px);
	    c = printImpliedLiterals(vc);
	    DebugAssert(c==1,"Implied literal error 6");
	    System.out.println("Assert x = y");
	    vc.assertFormula(xeqy);
	    c = printImpliedLiterals(vc);
	    DebugAssert(c==4,"Implied literal error 7");
	    System.out.println("Pop");
	    vc.pop();

	    System.out.println("Push");
	    vc.push();
	    System.out.println("Assert NOT p(x)");
	    vc.assertFormula(vc.notExpr(px));
	    c = printImpliedLiterals(vc);
	    DebugAssert(c==1,"Implied literal error 8");
	    System.out.println("Assert x = y");
	    vc.assertFormula(xeqy);
	    c = printImpliedLiterals(vc);
	    DebugAssert(c==4,"Implied literal error 9");
	    System.out.println("Pop");
	    vc.pop();

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test11(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	}
    }


    public static boolean test12() throws Cvc3Exception {
	ValidityChecker vc = null;
	try {
	    vc = ValidityChecker.create();

	    Type realType = vc.realType();
	    Type intType = vc.intType();
	    Type boolType = vc.boolType();
	    vc.push();
	    int initial_layer = vc.stackLevel();
	    int initial_scope = vc.scopeLevel();
	    Expr exprObj_trueID = vc.trueExpr();
	    Expr exprObj_falseID = vc.notExpr(vc.trueExpr());
	    vc.popTo(initial_layer);
	    DebugAssert(vc.scopeLevel() == initial_scope, "Expected no change");
	    DebugAssert(vc.stackLevel() == initial_layer, "Expected no change");
	    // TODO: what happens if we push and then popscope?

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test12(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	}
    }


    public static boolean test13() throws Cvc3Exception {
	ValidityChecker vc = null;
	FlagsMut flags = null;
	try {
	    flags = ValidityChecker.createFlags(null);
	    flags.setFlag("dagify-exprs",false);
	    flags.setFlag("dump-log", ".test13.cvc");
	    vc = ValidityChecker.create(flags);

	    Expr rat_one = vc.ratExpr(1);
	    Expr rat_two = vc.ratExpr(2);
	    Expr rat_minus_one = vc.ratExpr(-1);
	    
	    QueryResult query_result;
	    query_result = vc.query(vc.eqExpr(rat_two,rat_one));
	    System.out.println("2=1 " + query_result);
	    query_result = vc.query(vc.eqExpr(rat_two,rat_minus_one));
	    System.out.println("2=-1 " + query_result);

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test13(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	    if (flags != null) flags.delete();
	}
    }


    public static Expr func1(ValidityChecker vc) throws Cvc3Exception {
	// local Expr 'tmp'
	Expr tmp = vc.varExpr("tmp", vc.boolType());
	return vc.trueExpr();
    }


    public static boolean test14() throws Cvc3Exception {
	ValidityChecker vc = null;
	try {
	    vc = ValidityChecker.create();
	    
	    // func call: ok
	    Expr test1 = func1(vc);
	    
	    // func call: fail
	    Expr test2 = func1(vc);

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test13(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	}
    }


    public static boolean test15() throws Cvc3Exception {
	ValidityChecker vc = null;
	FlagsMut flags = null;
	try {
	    flags = ValidityChecker.createFlags(null);
	    flags.setFlag("dagify-exprs",false);
	    vc = ValidityChecker.create(flags);

	    /*****************************************************
	     *          array declaration                        *
	     *****************************************************/
	    
	    // array: index type
	    Type index_type = vc.subrangeType(vc.ratExpr(0), 
					      vc.ratExpr(3));
	    // array: data type
	    Type data_type = vc.subrangeType(vc.ratExpr(0), 
					     vc.ratExpr(3));
	    // array type: [0 .. 3] of 0 .. 3
	    Type array_type = vc.arrayType(index_type, data_type);
	    Expr arr = vc.varExpr("array", array_type);
	    
	    // array: [1,1,0,0]
	    arr = vc.writeExpr(arr, vc.ratExpr(0), vc.ratExpr(1));
	    arr = vc.writeExpr(arr, vc.ratExpr(1), vc.ratExpr(1));
	    arr = vc.writeExpr(arr, vc.ratExpr(2), vc.ratExpr(0));
	    arr = vc.writeExpr(arr, vc.ratExpr(3), vc.ratExpr(0));
	    
	    
	    
	    /*****************************************************
	     *             forall Expr                           *
	     *****************************************************/
	    
	    // for loop: index
	    Expr id = vc.boundVarExpr("id", "0", vc.subrangeType(vc.ratExpr(0),
								 vc.ratExpr(2)));
	    List vars = new ArrayList();
	    vars.add(id);
	    
	    // for loop: body
	    Expr for_body = vc.leExpr(vc.readExpr(arr, id),
				      vc.readExpr(arr, vc.plusExpr(id, vc.ratExpr(1))));
	    // forall expr
	    Expr forall_expr = vc.forallExpr(vars, for_body);
	    
	    vc.push();
	    check(vc, forall_expr);
	    
	    System.out.println("Scope level: " + vc.scopeLevel());
	    System.out.println("Counter-example:");
	    List assertions = vc.getCounterExample();
	    for (int i = 0; i < assertions.size(); ++i) {
		System.out.println(assertions.get(i));
	    }
	    System.out.println("End of counter-example");
	    System.out.println("");
	    vc.pop();
	    
	    /*****************************************************
	     *            manual expansion                       *
	     *****************************************************/
	    
	    Expr e1 = vc.leExpr(vc.readExpr(arr, vc.ratExpr(0)),
				vc.readExpr(arr, vc.ratExpr(1)));
	    Expr e2 = vc.leExpr(vc.readExpr(arr, vc.ratExpr(1)),
				vc.readExpr(arr, vc.ratExpr(2)));
	    Expr e3 = vc.leExpr(vc.readExpr(arr, vc.ratExpr(2)),
				vc.readExpr(arr, vc.ratExpr(3)));
	    Expr manual_expr = vc.andExpr(e1, vc.andExpr(e2, e3));

	    

	    /*****************************************************
	     *            exists Expr                            *
	     *****************************************************/
	    
	    // exists: index
	    Expr id_ex = vc.varExpr("id_ex", vc.subrangeType(vc.ratExpr(0),
							     vc.ratExpr(2)));
	    List vars_ex = new ArrayList();
	    vars_ex.add(id_ex);
	    
	    // exists: body
	    Expr ex_body = vc.gtExpr(vc.readExpr(arr, id_ex),
				     vc.readExpr(arr, vc.plusExpr(id_ex, vc.ratExpr(1))));
	    // exists expr
	    Expr ex_expr = vc.existsExpr(vars_ex, ex_body);




	    /*****************************************************
	     *            ???     forall <==> manual expansion   *
	     *****************************************************/
	    System.out.println("Checking forallExpr <==> manual expansion ...");
	    if (vc.query(vc.iffExpr(forall_expr, manual_expr)) == QueryResult.VALID)
		System.out.println("   -- yes.");
	    else {
		System.out.println("   -- no, with counter examples as ");
		
		List assert1 = vc.getCounterExample();
		for (int i = 0; i < assert1.size(); i ++)
		    System.out.println(assert1.get(i));
	    }
	    System.out.println();



	    /*****************************************************
	     *            ???     !forall <==> existsExpr        *
	     *****************************************************/
	    System.out.println();
	    System.out.println("Checking !forallExpr <==> existsExpr ...");
	    if (vc.query(vc.iffExpr(vc.notExpr(forall_expr), ex_expr)) == QueryResult.VALID)
		System.out.println("   -- yes.");
	    else if (vc.incomplete()) {
		System.out.println("   -- incomplete:");
		List reasons = vc.incompleteReasons();
		for (int i = 0; i < reasons.size(); ++i)
		    System.out.println(reasons.get(i));
	    }
	    else {
		System.out.println("   -- no, with counter examples as ");
		
		List assert2 = vc.getCounterExample();
		for (int i = 0; i < assert2.size(); i ++)
		    System.out.println(assert2.get(i));
	    }
	    
	    System.out.println();
	    System.out.println("End of testcases.");
	    System.out.println();
	    
	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test15(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	    if (flags != null) flags.delete();
	}
    }


    public static boolean test16() throws Cvc3Exception {
	ValidityChecker vc = null;
	try {
	    vc = ValidityChecker.create();

	    Type zto100 = vc.subrangeType(vc.ratExpr(0), vc.ratExpr(100));
	    Expr mem = vc.varExpr("mem", vc.arrayType(zto100, vc.intType()));
	    Expr a = vc.varExpr("a", zto100);
	    Expr b = vc.varExpr("b", zto100);
	    
	    Expr lhs = vc.readExpr(vc.writeExpr(mem, a, vc.ratExpr(30)), b);
	    Expr rhs = vc.readExpr(vc.writeExpr(mem, b, vc.ratExpr(40)), a);
	    
	    Expr q = vc.impliesExpr(vc.notExpr(vc.eqExpr(a, b)), vc.eqExpr(lhs, rhs));
	    
	    check(vc, q);
	    
	    System.out.println("Scope level: " + vc.scopeLevel());
	    System.out.println("Counter-example:");
	    List assertions = vc.getCounterExample();
	    DebugAssert(assertions.size() > 0, "Expected non-empty counter-example");
	    for (int i = 0; i < assertions.size(); ++i) {
		System.out.println(assertions.get(i));
	    }
	    System.out.println("End of counter-example");
	    System.out.println();
	    
	    HashMap m = vc.getConcreteModel();
	    if(m.isEmpty())
		System.out.println(" Did not find concrete model for any vars");
	    else {
		System.out.println("%Satisfiable  Variable Assignment: %");
		Iterator it = m.entrySet().iterator();
		while(it.hasNext()) {
		    Map.Entry next = (Map.Entry)it.next();
		    Expr eq;
		    Expr key = (Expr)next.getKey();
		    Expr value = (Expr)next.getValue();
		    if (key.getType().isBoolean()) {
			DebugAssert(value.isBooleanConst(),
				    "Bad variable assignement: e = "+ key
				    +"\n\n val = "+ value);
			if(value.isTrue())
			    eq = key;
			else
			    eq = vc.notExpr(key);
		    }
		    else
			eq = vc.eqExpr(key, value);
		    //:TODO:System.out.println(Expr(ASSERT, eq));
		    System.out.println(eq);
		}
	    }

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test16(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	}
    }


    public static boolean test17() throws Cvc3Exception {
	ValidityChecker vc = null;
	try {
	    vc = ValidityChecker.create();
	    try {
		List selectors = new ArrayList();
		List types = new ArrayList();
		
		selectors.add("car");
		types.add(vc.intType().getExpr());
		selectors.add("cdr");
		types.add(vc.stringExpr("list"));
		
		Type badList = vc.dataType("list", "cons", selectors, types);
		DebugAssert(false, "Typechecking exception expected");
	    } catch(TypecheckException e) {
		// fall through
	    }

	    vc.delete();

	    vc = ValidityChecker.create();
	    {
		List constructors = new ArrayList();
		List selectors = new ArrayList();
		List selectors0 = new ArrayList();
		List selectors1 = new ArrayList();
		selectors.add(selectors0);
		selectors.add(selectors1);
		List types = new ArrayList();
		List types0 = new ArrayList();
		List types1 = new ArrayList();
		types.add(types0);
		types.add(types1);
		
		constructors.add("cons");
		selectors0.add("car");
		types0.add(vc.intType().getExpr());
		selectors0.add("cdr");
		types0.add(vc.stringExpr("list"));
		constructors.add("null");
		
		Type list = vc.dataType("list", constructors, selectors, types);
		
		Expr x = vc.varExpr("x", vc.intType());
		Expr y = vc.varExpr("y", list);
		
		List args = new ArrayList();
		args.add(x);
		args.add(y);
		Expr cons = vc.datatypeConsExpr("cons", args);
		
		Expr sel = vc.datatypeSelExpr("car", cons);
		boolean b = check(vc, vc.eqExpr(sel, x));
		DebugAssert(b, "Should be valid");
	    }
	    vc.delete();

	    vc = ValidityChecker.create();
	    try {
		List names = new ArrayList();
		List constructors = new ArrayList();
		List constructors0 = new ArrayList();
		List constructors1 = new ArrayList();
		constructors.add(constructors0);
		constructors.add(constructors1);
		List selectors = new ArrayList();
		List selectors0 = new ArrayList();
		List selectors1 = new ArrayList();
		List selectors00 = new ArrayList();
		List selectors10 = new ArrayList();
		selectors.add(selectors0);
		selectors0.add(selectors00);
		selectors.add(selectors1);
		selectors1.add(selectors10);
		List types = new ArrayList();
		List types0 = new ArrayList();
		List types1 = new ArrayList();
		List types00 = new ArrayList();
		List types10 = new ArrayList();
		types.add(types0);
		types0.add(types00);
		types.add(types1);
		types1.add(types10);

		names.add("list1");
		
		constructors0.add("cons1");
		selectors00.add("car1");
		types00.add(vc.intType().getExpr());
		selectors00.add("cdr1");
		types00.add(vc.stringExpr("list2"));
		
		names.add("list2");
		
		constructors1.add("cons2");
		selectors10.add("car2");
		types10.add(vc.intType().getExpr());
		selectors10.add("cdr2");
		types10.add(vc.stringExpr("list1"));
		constructors1.add("null");
		
		List returnTypes = vc.dataType(names, constructors, selectors, types);
		
		Type list1 = (Type)returnTypes.get(0);
		Type list2 = (Type)returnTypes.get(1);
		
		Expr x = vc.varExpr("x", vc.intType());
		Expr y = vc.varExpr("y", list2);
		Expr z = vc.varExpr("z", list1);
		
		List args = new ArrayList();
		args.add(x);
		args.add(y);
		Expr cons1 = vc.datatypeConsExpr("cons1", args);
		
		Expr isnull = vc.datatypeTestExpr("null", y);
		Expr hyp = vc.andExpr(vc.eqExpr(z, cons1), isnull);
		
		Expr nullE = vc.datatypeConsExpr("null", new ArrayList());
		
		args = new ArrayList();
		args.add(x);
		args.add(nullE);
		Expr cons1_2 = vc.datatypeConsExpr("cons1", args);
		
		boolean b = check(vc, vc.impliesExpr(hyp, vc.eqExpr(z, cons1_2)));
		DebugAssert(b, "Should be valid");
	    } catch(TypecheckException e) {
		// fall through
	    }

	    vc.delete();

	    vc = ValidityChecker.create();
	    {
		List constructors = new ArrayList();
		List selectors = new ArrayList();
		selectors.add(new ArrayList());
		selectors.add(new ArrayList());
		List types = new ArrayList();
		types.add(new ArrayList());
		types.add(new ArrayList());
		
		constructors.add("A");
		constructors.add("B");
		
		Type two = vc.dataType("two", constructors, selectors, types);
		
		Expr x = vc.varExpr("x", two);
		Expr y = vc.varExpr("y", two);
		Expr z = vc.varExpr("z", two);
		
		List args = new ArrayList();
		args.add(vc.notExpr(vc.eqExpr(x,y)));
		args.add(vc.notExpr(vc.eqExpr(y,z)));
		args.add(vc.notExpr(vc.eqExpr(x,z)));
		
		boolean b = check(vc, vc.notExpr(vc.andExpr(args)));
		DebugAssert(b, "Should be valid");
	    }
	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test17(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	}
    }


    public static boolean test18() throws Cvc3Exception {
	ValidityChecker vc = null;
	FlagsMut flags = null;
	try {
	    flags = ValidityChecker.createFlags(null);
	    flags.setFlag("tcc", true);
	    vc = ValidityChecker.create(flags);

	    List names = new ArrayList();
	    List constructors = new ArrayList();
	    List constructors0 = new ArrayList();
	    List constructors1 = new ArrayList();
	    List constructors2 = new ArrayList();
	    constructors.add(constructors0);
	    constructors.add(constructors1);
	    constructors.add(constructors2);
	    List selectors = new ArrayList();
	    List selectors0 = new ArrayList();
	    List selectors1 = new ArrayList();
	    List selectors2 = new ArrayList();
	    List selectors00 = new ArrayList();
	    List selectors01 = new ArrayList();
	    List selectors10 = new ArrayList();
	    List selectors11 = new ArrayList();
	    List selectors20 = new ArrayList();
	    List selectors21 = new ArrayList();
	    selectors.add(selectors0);
	    selectors0.add(selectors00);
	    selectors0.add(selectors01);
	    selectors.add(selectors1);
	    selectors1.add(selectors10);
	    selectors1.add(selectors11);
	    selectors.add(selectors2);
	    selectors2.add(selectors20);
	    selectors2.add(selectors21);
	    List types = new ArrayList();
	    List types0 = new ArrayList();
	    List types1 = new ArrayList();
	    List types2 = new ArrayList();
	    List types00 = new ArrayList();
	    List types01 = new ArrayList();
	    List types10 = new ArrayList();
	    List types11 = new ArrayList();
	    List types20 = new ArrayList();
	    List types21 = new ArrayList();
	    types.add(types0);
	    types0.add(types00);
	    types0.add(types01);
	    types.add(types1);
	    types1.add(types10);
	    types1.add(types11);
	    types.add(types2);
	    types2.add(types20);
	    types2.add(types21);
	    
	    names.add("nat");
	    
	    constructors0.add("zero");
	    constructors0.add("succ");
	    selectors01.add("pred");
	    types01.add(vc.stringExpr("nat"));
	    
	    names.add("list");
	    
	    constructors1.add("cons");
	    selectors10.add("car");
	    types10.add(vc.stringExpr("tree"));
	    selectors10.add("cdr");
	    types10.add(vc.stringExpr("list"));
	    constructors1.add("null");

	    names.add("tree");
	    
	    constructors2.add("leaf");
	    constructors2.add("node");
	    selectors21.add("data");
	    types21.add(vc.stringExpr("nat"));
	    selectors21.add("children");
	    types21.add(vc.stringExpr("list"));
	    
	    List returnTypes = vc.dataType(names, constructors, selectors, types);
	    
	    Type nat = (Type)returnTypes.get(0);
	    Type listType = (Type)returnTypes.get(1);
	    Type tree = (Type)returnTypes.get(2);
	    
	    Expr x = vc.varExpr("x", nat);
	    
	    List args = new ArrayList();
	    Expr zero = vc.datatypeConsExpr("zero", args);
	    Expr nullE = vc.datatypeConsExpr("null", args);
	    Expr leaf = vc.datatypeConsExpr("leaf", args);
	    
	    vc.push();
	    try {
		check(vc, vc.notExpr(vc.eqExpr(zero, nullE)));
		DebugAssert(false, "Should have caught tcc exception");
	    } catch (TypecheckException e) { }

	    vc.pop();
	    args.add(vc.datatypeSelExpr("pred",x));
	    Expr spx = vc.datatypeConsExpr("succ", args);
	    Expr spxeqx = vc.eqExpr(spx, x);
	    vc.push();
	    try {
		check(vc, spxeqx);
		DebugAssert(false, "Should have caught tcc exception");
	    } catch(TypecheckException e) { }
	    
	    vc.pop();
	    boolean b = check(vc, vc.impliesExpr(vc.datatypeTestExpr("succ", x), spxeqx));
	    DebugAssert(b, "Should be valid");
	    
	    b = check(vc, vc.orExpr(vc.datatypeTestExpr("zero", x),
				     vc.datatypeTestExpr("succ", x)));
	    DebugAssert(b, "Should be valid");
	    
	    Expr y = vc.varExpr("y", nat);
	    Expr xeqy = vc.eqExpr(x, y);
	    args.clear();
	    args.add(x);
	    Expr sx = vc.datatypeConsExpr("succ", args);
	    args.clear();
	    args.add(y);
	    Expr sy = vc.datatypeConsExpr("succ", args);
	    Expr sxeqsy = vc.eqExpr(sx,sy);
	    b = check(vc, vc.impliesExpr(xeqy, sxeqsy));
	    DebugAssert(b, "Should be valid");
	    
	    b = check(vc, vc.notExpr(vc.eqExpr(sx, zero)));
	    DebugAssert(b, "Should be valid");
	    
	    b = check(vc, vc.impliesExpr(sxeqsy, xeqy));
	    DebugAssert(b, "Should be valid");
	    
	    b = check(vc, vc.notExpr(vc.eqExpr(sx, x)));
	    DebugAssert(b, "Should be valid");

	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test18(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	    if (flags != null) flags.delete();
	}
    }


    public static boolean test19() throws Cvc3Exception {
	ValidityChecker vc = null;
	FlagsMut flags = null;
	try {
	    flags = ValidityChecker.createFlags(null);
	    flags.setFlag("dagify-exprs",false);
	    vc = ValidityChecker.create(flags);

	    Type RealType= vc.realType();
	    Type IntType= vc.intType();
	    Type BoolType= vc.boolType();
	    Type PtrType = RealType;
	    Type HeapType = vc.arrayType(PtrType, RealType);
	    
	    // -----------------
	    //ASSERT(FORALL (CVCi: REAL): (Hs[CVCi] = Ht[CVCi]));
	    //QUERY(Hs[(t6 + (3 * 1))] = Ht[(t6 + (3 * 1))]);
	    Expr Ad = vc.boundVarExpr("CVCi", "CVCi", RealType);
	    Expr Hs = vc.varExpr("Hs", HeapType);
	    Expr Ht = vc.varExpr("Ht", HeapType);
	    Expr t6 = vc.varExpr("t6", RealType);
	    
	    List Vars = new ArrayList();
	    Vars.add(Ad);
	    // Body = (Hs[Ad] = Ht[Ad])
	    Expr Body = vc.eqExpr(vc.readExpr(Hs, Ad), vc.readExpr(Ht, Ad));
	    
	    //A = forall (~i:REAL): Body
	    Expr A = vc.forallExpr(Vars, Body); 
	    
	    // Q = (Hs[t6] = Ht[t6])          
	    Expr Q = vc.eqExpr(vc.readExpr(Hs, t6), vc.readExpr(Ht, t6));
	    
	    // ----------- CHECK A . Q
	    vc.push();
	    
	    vc.assertFormula(A);
	    
	    System.out.println("Checking formula " + Q);
	    System.out.println(" in context " + A);
	    
	    QueryResult Succ = vc.query(Q);
	    
	    DebugAssert(Succ == QueryResult.VALID, "Expected valid formula");
	    
	    return true;
	} catch (Exception e) {
	    System.out.println("*** Exception caught in test19(): \n" + e);
	    e.printStackTrace(System.out);
	    return false;
	} finally {
	    if (vc != null) vc.delete();
	    if (flags != null) flags.delete();
	}
    }

    public static boolean testNonlinearBV() throws Cvc3Exception {
    	ValidityChecker vc = null;
    	FlagsMut flags = null;
    	try {
    	    flags = ValidityChecker.createFlags(null);
    	    flags.setFlag("dagify-exprs",false);   	        	    
    	    vc = ValidityChecker.create(flags);    	    	    
    	
    	    int bvLength = 8;
    	    
    	    Rational zero = new Rational(0, vc.embeddedManager());
    	    
    	    Expr x   = vc.varExpr("x", vc.bitvecType(bvLength));
    	    Expr y   = vc.varExpr("y", vc.bitvecType(bvLength));
    	    Expr bv0 = vc.newBVConstExpr(zero, bvLength); 

    	    // BVUDIV
    	    vc.push();
    	    System.out.println("Checking BVUDIV:");
    	    Expr udiv = vc.newBVUDivExpr(x, y);
    	    Expr umult = vc.newBVMultExpr(bvLength, udiv, y);
    	    Expr test = vc.eqExpr(bv0, y);
    	    boolean result = check(vc, vc.impliesExpr(vc.notExpr(test), vc.newBVLEExpr(umult, x)), true);    	    
    	    DebugAssert(result, "Expected valid formula");
    	    vc.pop();

    	    // BVUREM
    	    vc.push();
    	    System.out.println("Checking BVUREM:");
    	    Expr urem = vc.newBVURemExpr(x, y);
    	    result = check(vc, vc.impliesExpr(vc.notExpr(test), vc.newBVLTExpr(urem, y)), true);    	    
    	    DebugAssert(result, "Expected valid formula");
    	    vc.pop();

    	    // BVSDIV
    	    vc.push();
    	    System.out.println("Checking BVSDIV:");
    	    Expr sdiv = vc.newBVSDivExpr(x, y);
    	    Expr smult = vc.newBVMultExpr(bvLength, sdiv, y);
    	    Expr signed_test = vc.newBVSLEExpr(bv0, x);
    	    signed_test = vc.andExpr(signed_test, vc.newBVSLTExpr(bv0, y));
    	    result = check(vc, vc.impliesExpr(signed_test, vc.newBVSLEExpr(smult, x)), true);    	    
    	    DebugAssert(result, "Expected valid formula");
    	    vc.pop();

    	    // BVSREM
    	    vc.push();
    	    System.out.println("Checking BVSREM:");
    	    Expr srem = vc.newBVSRemExpr(x, y);
    	    result = check(vc, vc.impliesExpr(signed_test, vc.newBVLTExpr(srem, y)), true);    	    
    	    DebugAssert(result, "Expected valid formula");
    	    vc.pop();

    	    // BVSMOD
    	    vc.push();
    	    System.out.println("Checking BVSMOD:");
    	    Expr smod = vc.newBVSModExpr(x, y);
    	    result = check(vc, vc.impliesExpr(signed_test, vc.newBVLTExpr(smod, y)), true);    	    
    	    DebugAssert(result, "Expected valid formula");
    	    vc.pop();

    	    return true;
    	} catch (Exception e) {
    	    System.out.println("*** Exception caught in test19(): \n" + e);
    	    e.printStackTrace(System.out);
    	    return false;
    	} finally {
    	    if (vc != null) vc.delete();
    	    if (flags != null) flags.delete();
    	}
    }

    public static boolean testDistinct() throws Cvc3Exception {
    	ValidityChecker vc = null;
    	FlagsMut flags = null;
    	try {
    	    flags = ValidityChecker.createFlags(null);
    	    vc = ValidityChecker.create(flags);    	    	    
    	
    	    int bvLength = 2;
    	    int elements_count = bvLength*bvLength + 1;
    	    
    	    List elements = new ArrayList();
    	    for (int i = 0; i < elements_count; i ++)
    	    	elements.add(vc.varExpr("x" + i, vc.bitvecType(bvLength)));
    	    Expr distinct = vc.distinctExpr(elements);
    	    boolean result = check(vc, vc.notExpr(distinct), true);    	    
    	    DebugAssert(result, "Expected valid formula");

    	    return true;
    	} catch (Exception e) {
    	    System.out.println("*** Exception caught in test19(): \n" + e);
    	    e.printStackTrace(System.out);
    	    return false;
    	} finally {
    	    if (vc != null) vc.delete();
    	    if (flags != null) flags.delete();
    	}
    }

}


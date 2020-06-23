/*********************                                                        */
/*! \file sep_log_api.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew V. Jones
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Two tests to validate the use of the separation logic API.
 **
 ** First test validates that we cannot use the API if not using separation
 ** logic.
 **
 ** Second test validates that the expressions returned from the API are
 ** correct and can be interrogated.
 **
 *****************************************************************************/

#include <iostream>
#include <sstream>

#include "expr/expr.h"
#include "smt/smt_engine.h"

using namespace CVC4;
using namespace std;

/**
 * Test function to validate that we *cannot* obtain the heap/nil expressions
 * when *not* using the separation logic theory
 */
int validate_exception(void)
{
  ExprManager em;
  Options opts;
  SmtEngine smt(&em);

  /*
   * Setup some options for CVC4 -- we explictly want to use a simplistic
   * theory (e.g., QF_IDL)
   */
  smt.setLogic("QF_IDL");
  smt.setOption("produce-models", SExpr("true"));
  smt.setOption("incremental", SExpr("false"));

  /* Our integer type */
  Type integer(em.integerType());

  /* Our SMT constants */
  Expr x(em.mkVar("x", integer));
  Expr y(em.mkVar("y", integer));

  /* y > x */
  Expr y_gt_x(em.mkExpr(kind::GT, y, x));

  /* assert it */
  smt.assertFormula(y_gt_x);

  /* check */
  Result r(smt.checkSat());

  /* If this is UNSAT, we have an issue; so bail-out */
  if (!r.isSat())
  {
    return -1;
  }

  /*
   * We now try to obtain our separation logic expressions from the solver --
   * we want to validate that we get our expected exceptions.
   */
  bool caught_on_heap(false);
  bool caught_on_nil(false);

  /* The exception message we expect to obtain */
  std::string expected(
      "Cannot obtain separation logic expressions if not using the separation "
      "logic theory.");

  /* test the heap expression */
  try
  {
    Expr heap_expr(smt.getSepHeapExpr());
  }
  catch (const CVC4::RecoverableModalException& e)
  {
    caught_on_heap = true;

    /* Check we get the correct exception string */
    if (e.what() != expected)
    {
      return -1;
    }
  }

  /* test the nil expression */
  try
  {
    Expr nil_expr(smt.getSepNilExpr());
  }
  catch (const CVC4::RecoverableModalException& e)
  {
    caught_on_nil = true;

    /* Check we get the correct exception string */
    if (e.what() != expected)
    {
      return -1;
    }
  }

  if (!caught_on_heap || !caught_on_nil)
  {
    return -1;
  }

  /* All tests pass! */
  return 0;
}

/**
 * Test function to demonstrate the use of, and validate the capability, of
 * obtaining the heap/nil expressions when using separation logic.
 */
int validate_getters(void)
{
  ExprManager em;
  Options opts;
  SmtEngine smt(&em);

  /* Setup some options for CVC4 */
  smt.setLogic("QF_ALL_SUPPORTED");
  smt.setOption("produce-models", SExpr("true"));
  smt.setOption("incremental", SExpr("false"));

  /* Our integer type */
  Type integer(em.integerType());

  /* A "random" constant */
  Rational val_for_random_constant(Rational(0xDEADBEEF));
  Expr random_constant(em.mkConst(val_for_random_constant));

  /* Another random constant */
  Rational val_for_expr_nil_val(Rational(0xFBADBEEF));
  Expr expr_nil_val(em.mkConst(val_for_expr_nil_val));

  /* Our nil term */
  Expr nil(em.mkNullaryOperator(integer, kind::SEP_NIL));

  /* Our SMT constants */
  Expr x(em.mkVar("x", integer));
  Expr y(em.mkVar("y", integer));
  Expr p1(em.mkVar("p1", integer));
  Expr p2(em.mkVar("p2", integer));

  /* Constraints on x and y */
  Expr x_equal_const(em.mkExpr(kind::EQUAL, x, random_constant));
  Expr y_gt_x(em.mkExpr(kind::GT, y, x));

  /* Points-to expressions */
  Expr p1_to_x(em.mkExpr(kind::SEP_PTO, p1, x));
  Expr p2_to_y(em.mkExpr(kind::SEP_PTO, p2, y));

  /* Heap -- the points-to have to be "starred"! */
  Expr heap(em.mkExpr(kind::SEP_STAR, p1_to_x, p2_to_y));

  /* Constain "nil" to be something random */
  Expr fix_nil(em.mkExpr(kind::EQUAL, nil, expr_nil_val));

  /* Add it all to the solver! */
  smt.assertFormula(x_equal_const);
  smt.assertFormula(y_gt_x);
  smt.assertFormula(heap);
  smt.assertFormula(fix_nil);

  /*
   * Incremental is disabled due to using separation logic, so don't query
   * twice!
   */
  Result r(smt.checkSat());

  /* If this is UNSAT, we have an issue; so bail-out */
  if (!r.isSat())
  {
    return -1;
  }

  /* Obtain our separation logic terms from the solver */
  Expr heap_expr(smt.getSepHeapExpr());
  Expr nil_expr(smt.getSepNilExpr());

  /* If the heap is not a separating conjunction, bail-out */
  if (heap_expr.getKind() != kind::SEP_STAR)
  {
    return -1;
  }

  /* If nil is not a direct equality, bail-out */
  if (nil_expr.getKind() != kind::EQUAL)
  {
    return -1;
  }

  /* Obtain the values for our "pointers" */
  Rational val_for_p1(smt.getValue(p1).getConst<CVC4::Rational>());
  Rational val_for_p2(smt.getValue(p2).getConst<CVC4::Rational>());

  /* We need to make sure we find both pointers in the heap */
  bool checked_p1(false);
  bool checked_p2(false);

  /* Walk all the children */
  for (Expr child : heap_expr.getChildren())
  {
    /* If we don't have a PTO operator, bail-out */
    if (child.getKind() != kind::SEP_PTO)
    {
      return -1;
    }

    /* Find both sides of the PTO operator */
    Rational addr(
        smt.getValue(child.getChildren().at(0)).getConst<CVC4::Rational>());
    Rational value(
        smt.getValue(child.getChildren().at(1)).getConst<CVC4::Rational>());

    /* If the current address is the value for p1 */
    if (addr == val_for_p1)
    {
      checked_p1 = true;

      /* If it doesn't match the random constant, we have a problem */
      if (value != val_for_random_constant)
      {
        return -1;
      }
      continue;
    }

    /* If the current address is the value for p2 */
    if (addr == val_for_p2)
    {
      checked_p2 = true;

      /*
       * Our earlier constraint was that what p2 points to must be *greater*
       * than the random constant -- if we get a value that is LTE, then
       * something has gone wrong!
       */
      if (value <= val_for_random_constant)
      {
        return -1;
      }
      continue;
    }

    /*
     * We should only have two addresses in heap, so if we haven't hit the
     * "continue" for p1 or p2, then bail-out
     */
    return -1;
  }

  /*
   * If we complete the loop and we haven't validated both p1 and p2, then we
   * have a problem
   */
  if (!checked_p1 || !checked_p2)
  {
    return -1;
  }

  /* We now get our value for what nil is */
  Rational value_for_nil =
      smt.getValue(nil_expr.getChildren().at(1)).getConst<CVC4::Rational>();

  /*
   * The value for nil from the solver should be the value we originally tied
   * nil to
   */
  if (value_for_nil != val_for_expr_nil_val)
  {
    return -1;
  }

  /* All tests pass! */
  return 0;
}

int main(void)
{
  /* check that we get an exception when we should */
  int check_exception(validate_exception());

  if (check_exception)
  {
    return check_exception;
  }

  /* check the getters */
  int check_getters(validate_getters());

  if (check_getters)
  {
    return check_getters;
  }

  return 0;
}

package cvc5;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class ResultTest
{
  private Solver d_solver;

    @BeforeEach void setUp()
    {
        d_solver = new Solver();
    }

    @AfterEach void tearDown()
    {
        d_solver.deletePointer();
    }

  @Test void isNull()
{
  cvc5::api::Result res_null;
  ASSERT_TRUE(res_null.isNull());
  ASSERT_FALSE(res_null.isSat());
  ASSERT_FALSE(res_null.isUnsat());
  ASSERT_FALSE(res_null.isSatUnknown());
  ASSERT_FALSE(res_null.isEntailed());
  ASSERT_FALSE(res_null.isNotEntailed());
  ASSERT_FALSE(res_null.isEntailmentUnknown());
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkVar(u_sort, "x");
  d_solver.assertFormula(x.eqTerm(x));
  cvc5::api::Result res = d_solver.checkSat();
  ASSERT_FALSE(res.isNull());
}

  @Test void eq)
{
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkVar(u_sort, "x");
  d_solver.assertFormula(x.eqTerm(x));
  cvc5::api::Result res;
  cvc5::api::Result res2 = d_solver.checkSat();
  cvc5::api::Result res3 = d_solver.checkSat();
  res = res2;
  ASSERT_EQ(res, res2);
  ASSERT_EQ(res3, res2);
}

  @Test void isSat)
{
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkVar(u_sort, "x");
  d_solver.assertFormula(x.eqTerm(x));
  cvc5::api::Result res = d_solver.checkSat();
  ASSERT_TRUE(res.isSat());
  ASSERT_FALSE(res.isSatUnknown());
}

  @Test void isUnsat)
{
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkVar(u_sort, "x");
  d_solver.assertFormula(x.eqTerm(x).notTerm());
  cvc5::api::Result res = d_solver.checkSat();
  ASSERT_TRUE(res.isUnsat());
  ASSERT_FALSE(res.isSatUnknown());
}

  @Test void isSatUnknown)
{
  d_solver.setLogic("QF_NIA");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("solve-int-as-bv", "32");
  Sort int_sort = d_solver.getIntegerSort();
  Term x = d_solver.mkVar(int_sort, "x");
  d_solver.assertFormula(x.eqTerm(x).notTerm());
  cvc5::api::Result res = d_solver.checkSat();
  ASSERT_FALSE(res.isSat());
  ASSERT_TRUE(res.isSatUnknown());
}

  @Test void isEntailed)
{
  d_solver.setOption("incremental", "true");
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkConst(u_sort, "x");
  Term y = d_solver.mkConst(u_sort, "y");
  Term a = x.eqTerm(y).notTerm();
  Term b = x.eqTerm(y);
  d_solver.assertFormula(a);
  cvc5::api::Result entailed = d_solver.checkEntailed(a);
  ASSERT_TRUE(entailed.isEntailed());
  ASSERT_FALSE(entailed.isEntailmentUnknown());
  cvc5::api::Result not_entailed = d_solver.checkEntailed(b);
  ASSERT_TRUE(not_entailed.isNotEntailed());
  ASSERT_FALSE(not_entailed.isEntailmentUnknown());
}

  @Test void isEntailmentUnknown)
{
  d_solver.setLogic("QF_NIA");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("solve-int-as-bv", "32");
  Sort int_sort = d_solver.getIntegerSort();
  Term x = d_solver.mkVar(int_sort, "x");
  d_solver.assertFormula(x.eqTerm(x).notTerm());
  cvc5::api::Result res = d_solver.checkEntailed(x.eqTerm(x));
  ASSERT_FALSE(res.isEntailed());
  ASSERT_TRUE(res.isEntailmentUnknown());
  ASSERT_EQ(res.getUnknownExplanation(), api::Result::UNKNOWN_REASON);
}
}  // namespace test
}  // namespace cvc5

/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Liana Hadarean, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the solving capabilities of the cvc5
 * bit-vector solver.
 *
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace std;
using namespace cvc5;

int main()
{
  TermManager tm;
  Solver slv(tm);
  slv.setLogic("QF_BV");  // Set the logic

  // The following example has been adapted from the book A Hacker's Delight by
  // Henry S. Warren.
  //
  // Given a variable x that can only have two values, a or b. We want to
  // assign to x a value other than the current one. The straightforward code
  // to do that is:
  //
  //(0) if (x == a ) x = b;
  //    else x = a;
  //
  // Two more efficient yet equivalent methods are:
  //
  //(1) x = a ⊕ b ⊕ x;
  //
  //(2) x = a + b - x;
  //
  // We will use cvc5 to prove that the three pieces of code above are all
  // equivalent by encoding the problem in the bit-vector theory.

  // Creating a bit-vector type of width 32
  Sort bv32 = tm.mkBitVectorSort(32);

  // Variables
  Term x = tm.mkConst(bv32, "x");
  Term a = tm.mkConst(bv32, "a");
  Term b = tm.mkConst(bv32, "b");

  // First encode the assumption that x must be equal to a or b
  Term x_eq_a = tm.mkTerm(Kind::EQUAL, {x, a});
  Term x_eq_b = tm.mkTerm(Kind::EQUAL, {x, b});
  Term assumption = tm.mkTerm(Kind::OR, {x_eq_a, x_eq_b});

  // Assert the assumption
  slv.assertFormula(assumption);

  // Introduce a new variable for the new value of x after assignment.
  Term new_x = tm.mkConst(bv32, "new_x");  // x after executing code (0)
  Term new_x_ =
      tm.mkConst(bv32, "new_x_");  // x after executing code (1) or (2)

  // Encoding code (0)
  // new_x = x == a ? b : a;
  Term ite = tm.mkTerm(Kind::ITE, {x_eq_a, b, a});
  Term assignment0 = tm.mkTerm(Kind::EQUAL, {new_x, ite});

  // Assert the encoding of code (0)
  cout << "Asserting " << assignment0 << " to cvc5" << endl;
  slv.assertFormula(assignment0);
  cout << "Pushing a new context." << endl;
  slv.push();

  // Encoding code (1)
  // new_x_ = a xor b xor x
  Term a_xor_b_xor_x = tm.mkTerm(Kind::BITVECTOR_XOR, {a, b, x});
  Term assignment1 = tm.mkTerm(Kind::EQUAL, {new_x_, a_xor_b_xor_x});

  // Assert encoding to cvc5 in current context;
  cout << "Asserting " << assignment1 << " to cvc5" << endl;
  slv.assertFormula(assignment1);
  Term new_x_eq_new_x_ = tm.mkTerm(Kind::EQUAL, {new_x, new_x_});

  cout << " Check sat assuming: " << new_x_eq_new_x_.notTerm() << endl;
  cout << " Expect UNSAT." << endl;
  cout << " cvc5: " << slv.checkSatAssuming(new_x_eq_new_x_.notTerm()) << endl;
  cout << " Popping context." << endl;
  slv.pop();

  // Encoding code (2)
  // new_x_ = a + b - x
  Term a_plus_b = tm.mkTerm(Kind::BITVECTOR_ADD, {a, b});
  Term a_plus_b_minus_x = tm.mkTerm(Kind::BITVECTOR_SUB, {a_plus_b, x});
  Term assignment2 = tm.mkTerm(Kind::EQUAL, {new_x_, a_plus_b_minus_x});

  // Assert encoding to cvc5 in current context;
  cout << "Asserting " << assignment2 << " to cvc5" << endl;
  slv.assertFormula(assignment2);

  cout << " Check sat assuming: " << new_x_eq_new_x_.notTerm() << endl;
  cout << " Expect UNSAT." << endl;
  cout << " cvc5: " << slv.checkSatAssuming(new_x_eq_new_x_.notTerm()) << endl;

  Term x_neq_x = tm.mkTerm(Kind::DISTINCT, {x, x});
  std::vector<Term> v{new_x_eq_new_x_, x_neq_x};
  Term query = tm.mkTerm(Kind::AND, {v});
  cout << " Check sat assuming: " << query.notTerm() << endl;
  cout << " Expect SAT." << endl;
  cout << " cvc5: " << slv.checkSatAssuming(query.notTerm()) << endl;

  // Assert that a is odd
  Op extract_op = tm.mkOp(Kind::BITVECTOR_EXTRACT, {0, 0});
  Term lsb_of_a = tm.mkTerm(extract_op, {a});
  cout << "Sort of " << lsb_of_a << " is " << lsb_of_a.getSort() << endl;
  Term a_odd = tm.mkTerm(Kind::EQUAL, {lsb_of_a, tm.mkBitVector(1u, 1u)});
  cout << "Assert " << a_odd << endl;
  cout << "Check satisfiability." << endl;
  slv.assertFormula(a_odd);
  cout << " Expect sat." << endl;
  cout << " cvc5: " << slv.checkSat() << endl;
  return 0;
}

/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
  Solver slv;
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
  Sort bitvector32 = slv.mkBitVectorSort(32);

  // Variables
  Term x = slv.mkConst(bitvector32, "x");
  Term a = slv.mkConst(bitvector32, "a");
  Term b = slv.mkConst(bitvector32, "b");

  // First encode the assumption that x must be equal to a or b
  Term x_eq_a = slv.mkTerm(EQUAL, {x, a});
  Term x_eq_b = slv.mkTerm(EQUAL, {x, b});
  Term assumption = slv.mkTerm(OR, {x_eq_a, x_eq_b});

  // Assert the assumption
  slv.assertFormula(assumption);

  // Introduce a new variable for the new value of x after assignment.
  Term new_x = slv.mkConst(bitvector32, "new_x");  // x after executing code (0)
  Term new_x_ =
      slv.mkConst(bitvector32, "new_x_");  // x after executing code (1) or (2)

  // Encoding code (0)
  // new_x = x == a ? b : a;
  Term ite = slv.mkTerm(ITE, {x_eq_a, b, a});
  Term assignment0 = slv.mkTerm(EQUAL, {new_x, ite});

  // Assert the encoding of code (0)
  cout << "Asserting " << assignment0 << " to cvc5 " << endl;
  slv.assertFormula(assignment0);
  cout << "Pushing a new context." << endl;
  slv.push();

  // Encoding code (1)
  // new_x_ = a xor b xor x
  Term a_xor_b_xor_x = slv.mkTerm(BITVECTOR_XOR, {a, b, x});
  Term assignment1 = slv.mkTerm(EQUAL, {new_x_, a_xor_b_xor_x});

  // Assert encoding to cvc5 in current context;
  cout << "Asserting " << assignment1 << " to cvc5 " << endl;
  slv.assertFormula(assignment1);
  Term new_x_eq_new_x_ = slv.mkTerm(EQUAL, {new_x, new_x_});

  cout << " Check sat assuming: " << new_x_eq_new_x_.notTerm() << endl;
  cout << " Expect UNSAT. " << endl;
  cout << " cvc5: " << slv.checkSatAssuming(new_x_eq_new_x_.notTerm()) << endl;
  cout << " Popping context. " << endl;
  slv.pop();

  // Encoding code (2)
  // new_x_ = a + b - x
  Term a_plus_b = slv.mkTerm(BITVECTOR_ADD, {a, b});
  Term a_plus_b_minus_x = slv.mkTerm(BITVECTOR_SUB, {a_plus_b, x});
  Term assignment2 = slv.mkTerm(EQUAL, {new_x_, a_plus_b_minus_x});

  // Assert encoding to cvc5 in current context;
  cout << "Asserting " << assignment2 << " to cvc5 " << endl;
  slv.assertFormula(assignment2);

  cout << " Check sat assuming: " << new_x_eq_new_x_.notTerm() << endl;
  cout << " Expect UNSAT. " << endl;
  cout << " cvc5: " << slv.checkSatAssuming(new_x_eq_new_x_.notTerm()) << endl;

  Term x_neq_x = slv.mkTerm(EQUAL, {x, x}).notTerm();
  std::vector<Term> v{new_x_eq_new_x_, x_neq_x};
  Term query = slv.mkTerm(AND, {v});
  cout << " Check sat assuming: " << query.notTerm() << endl;
  cout << " Expect SAT. " << endl;
  cout << " cvc5: " << slv.checkSatAssuming(query.notTerm()) << endl;

  // Assert that a is odd
  Op extract_op = slv.mkOp(BITVECTOR_EXTRACT, {0, 0});
  Term lsb_of_a = slv.mkTerm(extract_op, {a});
  cout << "Sort of " << lsb_of_a << " is " << lsb_of_a.getSort() << endl;
  Term a_odd = slv.mkTerm(EQUAL, {lsb_of_a, slv.mkBitVector(1u, 1u)});
  cout << "Assert " << a_odd << endl;
  cout << "Check satisfiability." << endl;
  slv.assertFormula(a_odd);
  cout << " Expect sat. " << endl;
  cout << " cvc5: " << slv.checkSat() << endl;
  return 0;
}

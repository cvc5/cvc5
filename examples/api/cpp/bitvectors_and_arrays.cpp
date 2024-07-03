/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Liana Hadarean, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the solving capabilities of the cvc5
 * bit-vector and array solvers.
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
  slv.setOption("produce-models", "true");    // Produce Models
  slv.setLogic("QF_ABV");                     // Set the logic

  // Consider the following code (where size is some previously defined constant):
  //
  //
  //   Assert (current_array[0] > 0);
  //   for (unsigned i = 1; i < k; ++i) {
  //     current_array[i] = 2 * current_array[i - 1];
  //     Assert (current_array[i-1] < current_array[i]);
  //     }
  //
  // We want to check whether the assertion in the body of the for loop holds
  // throughout the loop.

  // Setting up the problem parameters
  uint32_t k = 4;           // number of unrollings (should be a power of 2)
  uint32_t index_size = 2;  // size of the index, must be log2(k)

  // Sorts
  Sort elementSort = tm.mkBitVectorSort(32);
  Sort indexSort = tm.mkBitVectorSort(index_size);
  Sort arraySort = tm.mkArraySort(indexSort, elementSort);

  // Variables
  Term current_array = tm.mkConst(arraySort, "current_array");

  // Making a bit-vector constant
  Term zero = tm.mkBitVector(index_size, 0u);

  // Asserting that current_array[0] > 0
  Term current_array0 = tm.mkTerm(Kind::SELECT, {current_array, zero});
  Term current_array0_gt_0 = tm.mkTerm(
      Kind::BITVECTOR_SGT, {current_array0, tm.mkBitVector(32, 0u)});
  slv.assertFormula(current_array0_gt_0);

  // Building the assertions in the loop unrolling
  Term index = tm.mkBitVector(index_size, 0u);
  Term old_current = tm.mkTerm(Kind::SELECT, {current_array, index});
  Term two = tm.mkBitVector(32, 2u);

  std::vector<Term> assertions;
  for (uint32_t i = 1; i < k; ++i)
  {
    index = tm.mkBitVector(index_size, i);
    Term new_current = tm.mkTerm(Kind::BITVECTOR_MULT, {two, old_current});
    // current[i] = 2 * current[i-1]
    current_array =
        tm.mkTerm(Kind::STORE, {current_array, index, new_current});
    // current[i-1] < current [i]
    Term current_slt_new_current =
        tm.mkTerm(Kind::BITVECTOR_SLT, {old_current, new_current});
    assertions.push_back(current_slt_new_current);

    old_current = tm.mkTerm(Kind::SELECT, {current_array, index});
  }

  Term query = tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::AND, assertions)});

  cout << "Asserting " << query << " to cvc5" << endl;
  slv.assertFormula(query);
  cout << "Expect sat." << endl;
  cout << "cvc5: " << slv.checkSat() << endl;

  // Getting the model
  cout << "The satisfying model is:" << endl;
  cout << "  current_array = " << slv.getValue(current_array) << endl;
  cout << "  current_array[0] = " << slv.getValue(current_array0) << endl;
  return 0;
}

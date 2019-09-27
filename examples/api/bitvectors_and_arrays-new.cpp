/*********************                                                        */
/*! \file bitvectors_and_arrays-new.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Makai Mann
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the solving capabilities of the CVC4
 ** bit-vector and array solvers.
 **
 **/

#include <iostream>
#include <cmath>

#include <cvc4/api/cvc4cpp.h>

using namespace std;
using namespace CVC4::api;

int main()
{
  Solver slv;
  slv.setOption("produce-models", "true");      // Produce Models
  slv.setOption("output-language", "smtlib"); // output-language
  slv.setLogic("QF_AUFBV");                   // Set the logic

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
  unsigned k = 4;                // number of unrollings (should be a power of 2)
  unsigned index_size = log2(k); // size of the index


  // Sorts
  Sort elementSort = slv.mkBitVectorSort(32);
  Sort indexSort = slv.mkBitVectorSort(index_size);
  Sort arraySort = slv.mkArraySort(indexSort, elementSort);

  // Variables
  Term current_array = slv.mkConst(arraySort, "current_array");

  // Making a bit-vector constant
  Term zero = slv.mkBitVector(index_size, 0u);

  // Asserting that current_array[0] > 0
  Term current_array0 = slv.mkTerm(SELECT, current_array, zero);
  Term current_array0_gt_0 = slv.mkTerm(
      BITVECTOR_SGT, current_array0, slv.mkBitVector(32, 0u));
  slv.assertFormula(current_array0_gt_0);

  // Building the assertions in the loop unrolling
  Term index = slv.mkBitVector(index_size, 0u);
  Term old_current = slv.mkTerm(SELECT, current_array, index);
  Term two = slv.mkBitVector(32, 2u);

  std::vector<Term> assertions;
  for (unsigned i = 1; i < k; ++i) {
    index = slv.mkBitVector(index_size, i);
    Term new_current = slv.mkTerm(BITVECTOR_MULT, two, old_current);
    // current[i] = 2 * current[i-1]
    current_array = slv.mkTerm(STORE, current_array, index, new_current);
    // current[i-1] < current [i]
    Term current_slt_new_current = slv.mkTerm(BITVECTOR_SLT, old_current, new_current);
    assertions.push_back(current_slt_new_current);

    old_current = slv.mkTerm(SELECT, current_array, index);
  }

  Term query = slv.mkTerm(NOT, slv.mkTerm(AND, assertions));

  cout << "Asserting " << query << " to CVC4 " << endl;
  slv.assertFormula(query);
  cout << "Expect sat. " << endl;
  cout << "CVC4: " << slv.checkSatAssuming(slv.mkTrue()) << endl;

  // Getting the model
  cout << "The satisfying model is: " << endl;
  cout << "  current_array = " << slv.getValue(current_array) << endl;
  cout << "  current_array[0] = " << slv.getValue(current_array0) << endl;
  return 0;
}

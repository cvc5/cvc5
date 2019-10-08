/*********************                                                        */
/*! \file bitvectors_and_arrays.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean
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

#include <cvc4/cvc4.h>

using namespace std;
using namespace CVC4;

int main() {
  ExprManager em;
  SmtEngine smt(&em);
  smt.setOption("produce-models", true);      // Produce Models
  smt.setOption("output-language", "smtlib"); // output-language
  smt.setLogic("QF_AUFBV");                   // Set the logic

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


  // Types
  Type elementType = em.mkBitVectorType(32);
  Type indexType = em.mkBitVectorType(index_size);
  Type arrayType = em.mkArrayType(indexType, elementType);

  // Variables
  Expr current_array = em.mkVar("current_array", arrayType);

  // Making a bit-vector constant
  Expr zero = em.mkConst(BitVector(index_size, 0u));

  // Asserting that current_array[0] > 0
  Expr current_array0 = em.mkExpr(kind::SELECT, current_array, zero);
  Expr current_array0_gt_0 = em.mkExpr(kind::BITVECTOR_SGT, current_array0, em.mkConst(BitVector(32, 0u)));
  smt.assertFormula(current_array0_gt_0);

  // Building the assertions in the loop unrolling
  Expr index = em.mkConst(BitVector(index_size, 0u));
  Expr old_current = em.mkExpr(kind::SELECT, current_array, index);
  Expr two = em.mkConst(BitVector(32, 2u));

  std::vector<Expr> assertions;
  for (unsigned i = 1; i < k; ++i) {
    index = em.mkConst(BitVector(index_size, Integer(i)));
    Expr new_current = em.mkExpr(kind::BITVECTOR_MULT, two, old_current);
    // current[i] = 2 * current[i-1]
    current_array = em.mkExpr(kind::STORE, current_array, index, new_current);
    // current[i-1] < current [i]
    Expr current_slt_new_current = em.mkExpr(kind::BITVECTOR_SLT, old_current, new_current);
    assertions.push_back(current_slt_new_current);

    old_current = em.mkExpr(kind::SELECT, current_array, index);
  }

  Expr query = em.mkExpr(kind::NOT, em.mkExpr(kind::AND, assertions));

  cout << "Asserting " << query << " to CVC4 " << endl;
  smt.assertFormula(query);
  cout << "Expect sat. " << endl;
  cout << "CVC4: " << smt.checkSat(em.mkConst(true)) << endl;

  // Getting the model
  cout << "The satisfying model is: " << endl;
  cout << "  current_array = " << smt.getValue(current_array) << endl;
  cout << "  current_array[0] = " << smt.getValue(current_array0) << endl;
  return 0;
}

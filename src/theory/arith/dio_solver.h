/*********************                                                        */
/*! \file dio_solver.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Diophantine equation solver
 **
 ** A Diophantine equation solver for the theory of arithmetic.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__DIO_SOLVER_H
#define __CVC4__THEORY__ARITH__DIO_SOLVER_H

#include "context/context.h"

#include "theory/arith/tableau.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/arith_utilities.h"
#include "util/rational.h"

#include <vector>
#include <utility>

namespace CVC4 {
namespace theory {
namespace arith {

class DioSolver {
  context::Context* d_context;
  const Tableau& d_tableau;
  ArithPartialModel& d_partialModel;

public:

  /** Construct a Diophantine equation solver with the given context. */
  DioSolver(context::Context* ctxt, const Tableau& tab, ArithPartialModel& pmod) :
    d_context(ctxt),
    d_tableau(tab),
    d_partialModel(pmod) {
  }

  /**
   * Solve the set of Diophantine equations in the tableau.
   *
   * @return true if the set of equations was solved; false if no
   * solution
   */
  bool solve();

  /**
   * Get the parameterized solution to this set of Diophantine
   * equations.  Must be preceded by a call to solve() that returned
   * true. */
  void getSolution();

};/* class DioSolver */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__DIO_SOLVER_H */

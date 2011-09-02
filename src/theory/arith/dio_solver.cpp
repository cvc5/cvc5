/*********************                                                        */
/*! \file dio_solver.cpp
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

#include "theory/arith/dio_solver.h"

#include <iostream>

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

/*
static void printEquation(vector<Rational>& coeffs,
                          vector<ArithVar>& variables,
                          ostream& out) {
  Assert(coeffs.size() == variables.size());
  vector<Rational>::const_iterator i = coeffs.begin();
  vector<ArithVar>::const_iterator j = variables.begin();
  while(i != coeffs.end()) {
    out << *i << "*" << *j;
    ++i;
    ++j;
    if(i != coeffs.end()) {
      out << " + ";
    }
  }
  out << " = 0";
}
*/

bool DioSolver::solve() {
  Trace("integers") << "DioSolver::solve()" << endl;
  if(Debug.isOn("integers")) {
    ScopedDebug dtab("tableau");
    d_tableau.printTableau();
  }
  for(ArithVarSet::const_iterator i = d_tableau.beginBasic();
      i != d_tableau.endBasic();
      ++i) {
    Debug("integers") << "going through row " << *i << endl;

    Integer m = 1;
    for(Tableau::RowIterator j = d_tableau.rowIterator(*i); !j.atEnd(); ++j) {
      Debug("integers") << "  column " << (*j).getCoefficient() << " * " << (*j).getColVar() << endl;
      m *= (*j).getCoefficient().getDenominator();
    }
    Assert(m >= 1);
    Debug("integers") << "final multiplier is " << m << endl;

    Integer gcd = 0;
    Rational c = 0;
    Debug("integers") << "going throw row " << *i << " to find gcd" << endl;
    for(Tableau::RowIterator j = d_tableau.rowIterator(*i); !j.atEnd(); ++j) {
      Rational r = (*j).getCoefficient();
      ArithVar v = (*j).getColVar();
      r *= m;
      Debug("integers") << "  column " << r << " * " << v << endl;
      Assert(r.getDenominator() == 1);
      bool foundConstant = false;
      // The tableau doesn't store constants.  Constants int he input
      // are mapped to slack variables that are constrained with
      // bounds in the partial model.  So we detect and accumulate all
      // variables whose upper bound equals their lower bound, which
      // catches these input constants as well as any (contextually)
      // eliminated variables.
      if(d_partialModel.hasUpperBound(v) && d_partialModel.hasLowerBound(v)) {
        DeltaRational b = d_partialModel.getLowerBound(v);
        if(b.getInfinitesimalPart() == 0 && b == d_partialModel.getUpperBound(v)) {
          r *= b.getNoninfinitesimalPart();
          Debug("integers") << "    var " << v << " == [" << b << "], so found a constant part " << r << endl;
          c += r;
          foundConstant = true;
        }
      }
      if(!foundConstant) {
        // calculate gcd of all (NON-constant) coefficients
        gcd = (gcd == 0) ? r.getNumerator().abs() : gcd.gcd(r.getNumerator());
        Debug("integers") << "    gcd now " << gcd << endl;
      }
    }
    Debug("integers") << "addEquation: gcd is " << gcd << ", c is " << c << endl;
    // The gcd must divide c for this equation to be satisfiable.
    // If c is not an integer, there's no way it can.
    if(c.getDenominator() == 1 && gcd == gcd.gcd(c.getNumerator())) {
      Trace("integers") << "addEquation: this eqn is fine" << endl;
    } else {
      Trace("integers") << "addEquation: eqn not satisfiable, returning false" << endl;
      return false;
    }
  }

  return true;
}

void DioSolver::getSolution() {
  Unimplemented();
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

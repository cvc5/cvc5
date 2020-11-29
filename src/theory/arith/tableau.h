/*********************                                                        */
/*! \file tableau.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include <vector>

#include "theory/arith/arithvar.h"
#include "theory/arith/matrix.h"
#include "util/dense_map.h"
#include "util/rational.h"

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * A Tableau is a Rational matrix that keeps its rows in solved form.
 * Each row has a basic variable with coefficient -1 that is solved.
 * Tableau is optimized for pivoting.
 * The tableau should only be updated via pivot calls.
 */
class Tableau : public Matrix<Rational> {
public:
private:
  typedef DenseMap<RowIndex> BasicToRowMap;
  // Set of all of the basic variables in the tableau.
  // ArithVarMap<RowIndex> : ArithVar |-> RowIndex
  BasicToRowMap d_basic2RowIndex;

  // RowIndex |-> Basic Variable
  typedef DenseMap<ArithVar> RowIndexToBasicMap;
  RowIndexToBasicMap d_rowIndex2basic;

public:

  Tableau() : Matrix<Rational>(Rational(0)) {}

  typedef Matrix<Rational>::ColIterator ColIterator;
  typedef Matrix<Rational>::RowIterator RowIterator;
  typedef BasicToRowMap::const_iterator BasicIterator;

  typedef MatrixEntry<Rational> Entry;

  bool isBasic(ArithVar v) const{
    return d_basic2RowIndex.isKey(v);
  }

  void debugPrintIsBasic(ArithVar v) const {
    if(isBasic(v)){
      Warning() << v << " is basic." << std::endl;
    }else{
      Warning() << v << " is non-basic." << std::endl;
    }
  }

  BasicIterator beginBasic() const {
    return d_basic2RowIndex.begin();
  }
  BasicIterator endBasic() const {
    return d_basic2RowIndex.end();
  }

  RowIndex basicToRowIndex(ArithVar x) const {
    return d_basic2RowIndex[x];
  }

  ArithVar rowIndexToBasic(RowIndex rid) const {
    Assert(d_rowIndex2basic.isKey(rid));
    return d_rowIndex2basic[rid];
  }

  ColIterator colIterator(ArithVar x) const {
    return getColumn(x).begin();
  }

  RowIterator ridRowIterator(RowIndex rid) const {
    return getRow(rid).begin();
  }

  RowIterator basicRowIterator(ArithVar basic) const {
    return ridRowIterator(basicToRowIndex(basic));
  }

  const Entry& basicFindEntry(ArithVar basic, ArithVar col) const {
    return findEntry(basicToRowIndex(basic), col);
  }

  /**
   * Adds a row to the tableau.
   * The new row is equivalent to:
   *   basicVar = \f$\sum_i\f$ coeffs[i] * variables[i]
   * preconditions:
   *   basicVar is already declared to be basic
   *   basicVar does not have a row associated with it in the tableau.
   *
   * Note: each variables[i] does not have to be non-basic.
   * Pivoting will be mimicked if it is basic.
   */
  void addRow(ArithVar basicVar,
              const std::vector<Rational>& coeffs,
              const std::vector<ArithVar>& variables);

  /**
   * preconditions:
   *   x_r is basic,
   *   x_s is non-basic, and
   *   a_rs != 0.
   */
  void pivot(ArithVar basicOld, ArithVar basicNew, CoefficientChangeCallback& cb);

  void removeBasicRow(ArithVar basic);

  uint32_t basicRowLength(ArithVar basic) const{
    RowIndex ridx = basicToRowIndex(basic);
    return getRowLength(ridx);
  }

  /**
   *  to += mult * from
   * replacing from with its row.
   */
  void substitutePlusTimesConstant(ArithVar to, ArithVar from, const Rational& mult,  CoefficientChangeCallback& cb);

  void directlyAddToCoefficient(ArithVar rowVar, ArithVar col, const Rational& mult,  CoefficientChangeCallback& cb){
    RowIndex ridx = basicToRowIndex(rowVar);
    manipulateRowEntry(ridx, col, mult, cb);
  }

  /* Returns the complexity of a row in the tableau. */
  uint32_t rowComplexity(ArithVar basic) const;

  /* Returns the average complexity of the rows in the tableau. */
  double avgRowComplexity() const;

  void printBasicRow(ArithVar basic, std::ostream& out);

private:
  /* Changes the basic variable on the row for basicOld to basicNew. */
  void rowPivot(ArithVar basicOld, ArithVar basicNew, CoefficientChangeCallback& cb);

};/* class Tableau */



}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

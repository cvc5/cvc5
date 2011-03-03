/*********************                                                        */
/*! \file tableau.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "expr/node.h"
#include "expr/attribute.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar_set.h"
#include "theory/arith/normal_form.h"

#include "theory/arith/row_vector.h"

#include <ext/hash_map>
#include <set>

#ifndef __CVC4__THEORY__ARITH__TABLEAU_H
#define __CVC4__THEORY__ARITH__TABLEAU_H

namespace CVC4 {
namespace theory {
namespace arith {

typedef ArithVarSet Column;

typedef std::vector<Column> ColumnMatrix;

class Tableau {
private:

  typedef std::vector< ReducedRowVector* > RowsTable;

  RowsTable d_rowsTable;

  ArithVarSet d_basicVariables;

  std::vector<uint32_t> d_rowCount;
  ColumnMatrix d_columnMatrix;

public:
  /**
   * Constructs an empty tableau.
   */
  Tableau() :
    d_rowsTable(),
    d_basicVariables(),
    d_rowCount(),
    d_columnMatrix()
  {}

  /** Copy constructor. */
  Tableau(const Tableau& tab);
  ~Tableau();

  Tableau& operator=(const Tableau& tab);

  size_t getNumRows() const {
    return d_basicVariables.size();
  }

  void increaseSize(){
    d_basicVariables.increaseSize();
    d_rowsTable.push_back(NULL);
    d_rowCount.push_back(0);

    d_columnMatrix.push_back(ArithVarSet());

    //TODO replace with version of ArithVarSet that handles misses as non-entries
    // not as buffer overflows
    ColumnMatrix::iterator i = d_columnMatrix.begin(), end = d_columnMatrix.end();
    for(; i != end; ++i){
      Column& col = *i;
      col.increaseSize(d_columnMatrix.size());
    }
  }

  bool isBasic(ArithVar v) const {
    return d_basicVariables.isMember(v);
  }

  ArithVarSet::iterator begin(){
    return d_basicVariables.begin();
  }

  ArithVarSet::iterator end(){
    return d_basicVariables.end();
  }

  const Column& getColumn(ArithVar v){
    Assert(v < d_columnMatrix.size());
    return d_columnMatrix[v];
  }

  Column::iterator beginColumn(ArithVar v){
    return getColumn(v).begin();
  }
  Column::iterator endColumn(ArithVar v){
    return getColumn(v).end();
  }


  ReducedRowVector& lookup(ArithVar var){
    Assert(d_basicVariables.isMember(var));
    Assert(d_rowsTable[var] != NULL);
    return *(d_rowsTable[var]);
  }

  uint32_t getRowCount(ArithVar x){
    Assert(x < d_rowCount.size());
    AlwaysAssert(d_rowCount[x] == getColumn(x).size());

    return d_rowCount[x];
  }

  /**
   * Adds a row to the tableau.
   * The new row is equivalent to:
   *   basicVar = \sum_i coeffs[i] * variables[i]
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
  void pivot(ArithVar x_r, ArithVar x_s);

  void printTableau();

  ReducedRowVector* removeRow(ArithVar basic);


private:
  /** Copies the datastructures in tab to this.*/
  void internalCopy(const Tableau& tab);

  /** Clears the structures in the tableau. */
  void clear();
};

}; /* namespace arith  */
}; /* namespace theory */
}; /* namespace CVC4   */

#endif /* __CVC4__THEORY__ARITH__TABLEAU_H */

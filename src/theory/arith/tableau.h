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

class Tableau {
private:

  typedef std::vector< ReducedRowVector* > RowsTable;

  ArithVarSet d_activeBasicVars;
  RowsTable d_rowsTable;


  ActivityMonitor& d_activityMonitor;
  ArithVarSet& d_basicManager;

  std::vector<uint32_t> d_rowCount;

public:
  /**
   * Constructs an empty tableau.
   */
  Tableau(ActivityMonitor &am, ArithVarSet& bm) :
    d_activeBasicVars(),
    d_rowsTable(),
    d_activityMonitor(am),
    d_basicManager(bm)
  {}

  void increaseSize(){
    d_activeBasicVars.increaseSize();
    d_rowsTable.push_back(NULL);
    d_rowCount.push_back(0);
  }

  ArithVarSet::iterator begin(){
    return d_activeBasicVars.begin();
  }

  ArithVarSet::iterator end(){
    return d_activeBasicVars.end();
  }

  ReducedRowVector* lookup(ArithVar var){
    Assert(isActiveBasicVariable(var));
    return d_rowsTable[var];
  }

private:
  ReducedRowVector* lookupEjected(ArithVar var){
    Assert(isEjected(var));
    return d_rowsTable[var];
  }
public:

  uint32_t getRowCount(ArithVar x){
    Assert(x < d_rowCount.size());
    return d_rowCount[x];
  }

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

  bool isEjected(ArithVar var){
    return d_basicManager.isMember(var) && !isActiveBasicVariable(var);
  }

  void ejectBasic(ArithVar basic){
    Assert(d_basicManager.isMember(basic));
    Assert(isActiveBasicVariable(basic));

    d_activeBasicVars.remove(basic);
  }

  void reinjectBasic(ArithVar basic){
    AlwaysAssert(false);

    Assert(d_basicManager.isMember(basic));
    Assert(isEjected(basic));

    ReducedRowVector* row = lookupEjected(basic);
    d_activeBasicVars.add(basic);
    updateRow(row);
  }
private:
  inline bool isActiveBasicVariable(ArithVar var){
    return d_activeBasicVars.isMember(var);
  }

  void updateRow(ReducedRowVector* row);
};

}; /* namespace arith  */
}; /* namespace theory */
}; /* namespace CVC4   */

#endif /* __CVC4__THEORY__ARITH__TABLEAU_H */

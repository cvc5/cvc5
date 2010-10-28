/*********************                                                        */
/*! \file tableau.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
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


#include "theory/arith/tableau.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

void Tableau::addRow(ArithVar basicVar,
                     const std::vector<Rational>& coeffs,
                     const std::vector<ArithVar>& variables){

  Assert(coeffs.size() == variables.size());
  Assert(d_basicManager.isMember(basicVar));

  //The new basic variable cannot already be a basic variable
  Assert(!isActiveBasicVariable(basicVar));
  d_activeBasicVars.insert(basicVar);
  ReducedRowVector* row_current = new ReducedRowVector(basicVar,variables, coeffs);
  d_rowsTable[basicVar] = row_current;

  //A variable in the row may have been made non-basic already.
  //If this is the case we fake pivoting this variable
  vector<Rational>::const_iterator coeffsIter = coeffs.begin();
  vector<Rational>::const_iterator coeffsEnd = coeffs.end();

  vector<ArithVar>::const_iterator varsIter = variables.begin();

  for( ; coeffsIter != coeffsEnd; ++coeffsIter, ++ varsIter){
    ArithVar var = *varsIter;

    if(d_basicManager.isMember(var)){
      if(!isActiveBasicVariable(var)){
        reinjectBasic(var);
      }
      Assert(isActiveBasicVariable(var));

      ReducedRowVector* row_var = lookup(var);
      row_current->substitute(*row_var);
    }
  }
}

void Tableau::pivot(ArithVar x_r, ArithVar x_s){
  Assert(d_basicManager.isMember(x_r));
  Assert(!d_basicManager.isMember(x_s));

  ReducedRowVector* row_s = lookup(x_r);
  Assert(row_s->has(x_s));

  //Swap x_r and x_s in d_activeRows
  d_rowsTable[x_s] = row_s;
  d_rowsTable[x_r] = NULL;

  d_activeBasicVars.erase(x_r);
  d_basicManager.remove(x_r);

  d_activeBasicVars.insert(x_s);
  d_basicManager.add(x_s);

  row_s->pivot(x_s);

  for(ArithVarSet::iterator basicIter = begin(), endIter = end();
      basicIter != endIter; ++basicIter){
    ArithVar basic = *basicIter;
    if(basic == x_s) continue;

    ReducedRowVector* row_k = lookup(basic);
    if(row_k->has(x_s)){
      d_activityMonitor[basic] += 30;
      row_k->substitute(*row_s);
    }
  }
}
void Tableau::printTableau(){
  Debug("tableau") << "Tableau::d_activeRows"  << endl;

  typedef RowsTable::iterator table_iter;
  for(table_iter rowIter = d_rowsTable.begin(), end = d_rowsTable.end();
      rowIter != end; ++rowIter){
    ReducedRowVector* row_k = *rowIter;
    if(row_k != NULL){
      row_k->printRow();
    }
  }
}


void Tableau::updateRow(ReducedRowVector* row){
  ArithVar basic = row->basic();
  for(ReducedRowVector::NonZeroIterator i=row->beginNonZero(), endIter = row->endNonZero(); i != endIter; ){
    ArithVar var = i->first;
    ++i;
    if(var != basic && d_basicManager.isMember(var)){
      ReducedRowVector* row_var = isActiveBasicVariable(var) ? lookup(var) : lookupEjected(var);

      Assert(row_var != row);
      row->substitute(*row_var);

      i = row->beginNonZero();
      endIter = row->endNonZero();
    }
  }
}

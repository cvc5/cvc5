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

using namespace std;

Tableau::~Tableau(){
  while(!d_basicVariables.empty()){
    ArithVar curr = *(d_basicVariables.begin());
    ReducedRowVector* vec = removeRow(curr);
    delete vec;
  }
}

void Tableau::addRow(ArithVar basicVar,
                     const std::vector<Rational>& coeffs,
                     const std::vector<ArithVar>& variables){

  Assert(coeffs.size() == variables.size());

  //The new basic variable cannot already be a basic variable
  Assert(!d_basicVariables.isMember(basicVar));
  d_basicVariables.add(basicVar);
  ReducedRowVector* row_current = new ReducedRowVector(basicVar,variables, coeffs,d_rowCount, d_columnMatrix);
  d_rowsTable[basicVar] = row_current;

  //A variable in the row may have been made non-basic already.
  //If this is the case we fake pivoting this variable
  vector<ArithVar>::const_iterator varsIter = variables.begin();
  vector<ArithVar>::const_iterator varsEnd = variables.end();

  for( ; varsIter != varsEnd; ++varsIter){
    ArithVar var = *varsIter;

    if(d_basicVariables.isMember(var)){
      ReducedRowVector& row_var = lookup(var);
      row_current->substitute(row_var);
    }
  }
}

ReducedRowVector* Tableau::removeRow(ArithVar basic){
  Assert(d_basicVariables.isMember(basic));

  ReducedRowVector* row = d_rowsTable[basic];

  d_basicVariables.remove(basic);
  d_rowsTable[basic] = NULL;

  return row;
}

void Tableau::pivot(ArithVar x_r, ArithVar x_s){
  Assert(d_basicVariables.isMember(x_r));
  Assert(!d_basicVariables.isMember(x_s));

  Debug("tableau") << "Tableau::pivot(" <<  x_r <<", " <<x_s <<")"  << endl;

  ReducedRowVector* row_s = d_rowsTable[x_r];
  Assert(row_s != NULL);
  Assert(row_s->has(x_s));

  //Swap x_r and x_s in d_activeRows
  d_rowsTable[x_s] = row_s;
  d_rowsTable[x_r] = NULL;

  d_basicVariables.remove(x_r);

  d_basicVariables.add(x_s);

  row_s->pivot(x_s);

  ArithVarSet::VarList copy(getColumn(x_s).getList());
  vector<ArithVar>::iterator basicIter = copy.begin(), endIter = copy.end();

  for(; basicIter != endIter; ++basicIter){
    ArithVar basic = *basicIter;
    if(basic == x_s) continue;

    ReducedRowVector& row_k = lookup(basic);
    Assert(row_k.has(x_s));

    row_k.substitute(*row_s);
  }
  Assert(getColumn(x_s).size() == 1);
  Assert(getRowCount(x_s) == 1);
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

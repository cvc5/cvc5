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

Row::Row(ArithVar basic,
         const std::vector< Rational >& coefficients,
         const std::vector< ArithVar >& variables):
  d_x_i(basic),
  d_coeffs(){

  Assert(coefficients.size() == variables.size() );

  std::vector<Rational>::const_iterator coeffIter = coefficients.begin();
  std::vector<Rational>::const_iterator coeffEnd = coefficients.end();
  std::vector<ArithVar>::const_iterator varIter = variables.begin();

  for(; coeffIter != coeffEnd; ++coeffIter, ++varIter){
    const Rational& coeff = *coeffIter;
    ArithVar var_i = *varIter;

    Assert(var_i != d_x_i);
    Assert(!has(var_i));
    Assert(coeff != Rational(0,1));

    d_coeffs[var_i] = coeff;
    Assert(d_coeffs[var_i] != Rational(0,1));
  }
}
void Row::subsitute(Row& row_s){
  ArithVar x_s = row_s.basicVar();

  Assert(has(x_s));
  Assert(x_s != d_x_i);

  Rational zero(0,1);

  Rational a_rs = lookup(x_s);
  Assert(a_rs != zero);
  d_coeffs.erase(x_s);

  for(iterator iter = row_s.begin(), iter_end = row_s.end();
      iter != iter_end; ++iter){
    ArithVar x_j = iter->first;
    Rational a_sj = iter->second;
    a_sj *= a_rs;
    CoefficientTable::iterator coeff_iter = d_coeffs.find(x_j);

    if(coeff_iter != d_coeffs.end()){
      coeff_iter->second += a_sj;
      if(coeff_iter->second == zero){
        d_coeffs.erase(coeff_iter);
      }
    }else{
      d_coeffs.insert(std::make_pair(x_j,a_sj));
    }
  }
}

void Row::pivot(ArithVar x_j){
  Rational negInverseA_rs = -(lookup(x_j).inverse());
  d_coeffs[d_x_i] = Rational(Integer(-1));
  d_coeffs.erase(x_j);

  d_x_i = x_j;

  for(iterator nonbasicIter = begin(), nonbasicIter_end = end();
      nonbasicIter != nonbasicIter_end; ++nonbasicIter){
    nonbasicIter->second *= negInverseA_rs;
  }

}

void Row::printRow(){
  Debug("tableau") << d_x_i << " ";
  for(iterator nonbasicIter = d_coeffs.begin();
      nonbasicIter != d_coeffs.end();
      ++nonbasicIter){
    ArithVar nb = nonbasicIter->first;
    Debug("tableau") << "{" << nb << "," << d_coeffs[nb] << "}";
  }
  Debug("tableau") << std::endl;
}

void Tableau::addRow(ArithVar basicVar,
                     const std::vector<Rational>& coeffs,
                     const std::vector<ArithVar>& variables){

  Assert(coeffs.size() == variables.size());
  Assert(d_basicManager.isBasic(basicVar));

  //The new basic variable cannot already be a basic variable
  Assert(!isActiveBasicVariable(basicVar));
  d_activeBasicVars.insert(basicVar);
  Row* row_current = new Row(basicVar,coeffs,variables);
  d_rowsTable[basicVar] = row_current;

  //A variable in the row may have been made non-basic already.
  //If this is the case we fake pivoting this variable
  std::vector<Rational>::const_iterator coeffsIter = coeffs.begin();
  std::vector<Rational>::const_iterator coeffsEnd = coeffs.end();

  std::vector<ArithVar>::const_iterator varsIter = variables.begin();

  for( ; coeffsIter != coeffsEnd; ++coeffsIter, ++ varsIter){
    ArithVar var = *varsIter;

    if(d_basicManager.isBasic(var)){
      if(!isActiveBasicVariable(var)){
        reinjectBasic(var);
      }
      Assert(isActiveBasicVariable(var));

      Row* row_var = lookup(var);
      row_current->subsitute(*row_var);
    }
  }
}

void Tableau::pivot(ArithVar x_r, ArithVar x_s){
  Assert(d_basicManager.isBasic(x_r));
  Assert(!d_basicManager.isBasic(x_s));

  Row* row_s = lookup(x_r);
  Assert(row_s->has(x_s));

  //Swap x_r and x_s in d_activeRows
  d_rowsTable[x_s] = row_s;
  d_rowsTable[x_r] = NULL;

  d_activeBasicVars.erase(x_r);
  d_basicManager.makeNonbasic(x_r);

  d_activeBasicVars.insert(x_s);
  d_basicManager.makeBasic(x_s);

  row_s->pivot(x_s);

  for(ArithVarSet::iterator basicIter = begin(), endIter = end();
      basicIter != endIter; ++basicIter){
    ArithVar basic = *basicIter;
    Row* row_k = lookup(basic);
    if(row_k->has(x_s)){
      d_activityMonitor.increaseActivity(basic, 30);
      row_k->subsitute(*row_s);
    }
  }
}
void Tableau::printTableau(){
  Debug("tableau") << "Tableau::d_activeRows"  << endl;

  typedef RowsTable::iterator table_iter;
  for(table_iter rowIter = d_rowsTable.begin(), end = d_rowsTable.end();
      rowIter != end; ++rowIter){
    Row* row_k = *rowIter;
    if(row_k != NULL){
      row_k->printRow();
    }
  }
}


void Tableau::updateRow(Row* row){
  for(Row::iterator i=row->begin(), endIter = row->end(); i != endIter; ){
    ArithVar var = i->first;
    ++i;
    if(d_basicManager.isBasic(var)){
      Row* row_var = isActiveBasicVariable(var) ? lookup(var) : lookupEjected(var);

      Assert(row_var != row);
      row->subsitute(*row_var);

      i = row->begin();
      endIter = row->end();
    }
  }
}

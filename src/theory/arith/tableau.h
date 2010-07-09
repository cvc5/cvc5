/*********************                                                        */
/*! \file tableau.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
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

#include "theory/arith/basic.h"
#include "theory/arith/arith_activity.h"


#include <ext/hash_map>
#include <map>
#include <set>

#ifndef __CVC4__THEORY__ARITH__TABLEAU_H
#define __CVC4__THEORY__ARITH__TABLEAU_H

namespace CVC4 {
namespace theory {
namespace arith {


class Row {
  TNode d_x_i;

  typedef std::map<TNode, Rational> CoefficientTable;

  CoefficientTable d_coeffs;

public:

  typedef CoefficientTable::iterator iterator;

  /**
   * Construct a row equal to:
   *   basic = \sum_{x_i} c_i * x_i
   */
  Row(TNode basic, TNode sum):
    d_x_i(basic),
    d_coeffs(){

    Assert(d_x_i.getMetaKind() == kind::metakind::VARIABLE);
    Assert(sum.getKind() == kind::PLUS);

    for(TNode::iterator iter=sum.begin(); iter != sum.end(); ++iter){
      TNode pair = *iter;
      Assert(pair.getKind() == kind::MULT);
      Assert(pair.getNumChildren() == 2);
      TNode coeff = pair[0];
      TNode var_i = pair[1];
      Assert(coeff.getKind() == kind::CONST_RATIONAL);
      Assert(var_i.getKind() == kind::VARIABLE);

      Assert(!has(var_i));
      d_coeffs[var_i] = coeff.getConst<Rational>();
      Assert(coeff.getConst<Rational>() != Rational(0,1));
      Assert(d_coeffs[var_i] != Rational(0,1));
    }
  }

  iterator begin(){
    return d_coeffs.begin();
  }

  iterator end(){
    return d_coeffs.end();
  }

  TNode basicVar(){
    return d_x_i;
  }

  bool has(TNode x_j){
    CoefficientTable::iterator x_jPos = d_coeffs.find(x_j);
    return x_jPos != d_coeffs.end();
  }

  const Rational& lookup(TNode x_j){
    CoefficientTable::iterator x_jPos = d_coeffs.find(x_j);
    Assert(x_jPos !=  d_coeffs.end());
    return (*x_jPos).second;
  }

  void pivot(TNode x_j){
    Rational negInverseA_rs = -(lookup(x_j).inverse());
    d_coeffs[d_x_i] = Rational(Integer(-1));
    d_coeffs.erase(x_j);

    d_x_i = x_j;

    for(iterator nonbasicIter = begin(), nonbasicIter_end = end();
        nonbasicIter != nonbasicIter_end; ++nonbasicIter){
      nonbasicIter->second *= negInverseA_rs;
    }

  }

  void subsitute(Row& row_s){
    TNode x_s = row_s.basicVar();

    Assert(has(x_s));
    Assert(x_s != d_x_i);

    Rational zero(0,1);

    Rational a_rs = lookup(x_s);
    Assert(a_rs != zero);
    d_coeffs.erase(x_s);

    for(iterator iter = row_s.begin(), iter_end = row_s.end();
        iter != iter_end; ++iter){
      TNode x_j = iter->first;
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

  void printRow(){
    Debug("tableau") << d_x_i << " ";
    for(iterator nonbasicIter = d_coeffs.begin();
        nonbasicIter != d_coeffs.end();
        ++nonbasicIter){
      TNode nb = nonbasicIter->first;
      Debug("tableau") << "{" << nb << "," << d_coeffs[nb] << "}";
    }
    Debug("tableau") << std::endl;
  }
};

class Tableau {
public:
  typedef std::set<TNode> VarSet;

private:
  typedef __gnu_cxx::hash_map<TNode, Row*, NodeHashFunction> RowsTable;

  VarSet d_activeBasicVars;
  RowsTable d_activeRows, d_inactiveRows;


public:
  /**
   * Constructs an empty tableau.
   */
  Tableau() : d_activeBasicVars(), d_activeRows(), d_inactiveRows() {}

  VarSet::iterator begin(){
    return d_activeBasicVars.begin();
  }

  VarSet::iterator end(){
    return d_activeBasicVars.end();
  }

  Row* lookup(TNode var){
    Assert(isActiveBasicVariable(var));
    return d_activeRows[var];
  }

private:
  Row* lookupEjected(TNode var){
    Assert(isEjected(var));
    return d_inactiveRows[var];
  }
public:

  void addRow(TNode eq){
    Assert(eq.getKind() == kind::EQUAL);
    Assert(eq.getNumChildren() == 2);

    TNode var = eq[0];
    TNode sum = eq[1];

    Assert(var.getAttribute(IsBasic()));

    //The new basic variable cannot already be a basic variable
    Assert(!isActiveBasicVariable(var));
    d_activeBasicVars.insert(var);
    Row* row_var = new Row(var,sum);
    d_activeRows[var] = row_var;

    //A variable in the row may have been made non-basic already.
    //If this is the case we fake pivoting this variable
    for(TNode::iterator sumIter = sum.begin(); sumIter!=sum.end(); ++sumIter){
      TNode child = *sumIter;
      Assert(child.getKind() == kind::MULT);
      Assert(child.getNumChildren() == 2);
      Assert(child[0].getKind() == kind::CONST_RATIONAL);
      TNode c = child[1];
      Assert(var.getMetaKind() == kind::metakind::VARIABLE);
      if(isActiveBasicVariable(c)){
        Row* row_c = lookup(c);
        row_var->subsitute(*row_c);
      }
    }
  }

  /**
   * preconditions:
   *   x_r is basic,
   *   x_s is non-basic, and
   *   a_rs != 0.
   */
  void pivot(TNode x_r, TNode x_s){
    RowsTable::iterator ptrRow_r = d_activeRows.find(x_r);
    Assert(ptrRow_r != d_activeRows.end());

    Row* row_s = (*ptrRow_r).second;

    Assert(row_s->has(x_s));
    row_s->pivot(x_s);

    d_activeRows.erase(ptrRow_r);
    d_activeBasicVars.erase(x_r);
    makeNonbasic(x_r);

    d_activeRows.insert(std::make_pair(x_s,row_s));
    d_activeBasicVars.insert(x_s);
    makeBasic(x_s);

    for(VarSet::iterator basicIter = begin(), endIter = end();
        basicIter != endIter; ++basicIter){
      TNode basic = *basicIter;
      Row* row_k = lookup(basic);
      if(row_k->has(x_s)){
         increaseActivity(basic, 30);
        row_k->subsitute(*row_s);
      }
    }
  }
  void printTableau(){
    for(VarSet::iterator basicIter = begin(), endIter = end();
        basicIter != endIter; ++basicIter){
      TNode basic = *basicIter;
      Row* row_k = lookup(basic);
      row_k->printRow();
    }
  }

  bool isEjected(TNode var){
    return d_inactiveRows.find(var) != d_inactiveRows.end();
  }

  void ejectBasic(TNode basic){
    Assert(isActiveBasicVariable(basic));

    Row* row = lookup(basic);
    d_activeRows.erase(basic);
    d_activeBasicVars.erase(basic);

    d_inactiveRows.insert(std::make_pair(basic, row));
  }

  void reinjectBasic(TNode basic){
    Assert(isEjected(basic));

    Row* row = lookupEjected(basic);

    d_inactiveRows.erase(basic);
    d_activeBasicVars.insert(basic);
    d_activeRows.insert(std::make_pair(basic, row));

    updateRow(row);
  }
private:
  inline bool isActiveBasicVariable(TNode var){
    return d_activeBasicVars.find(var) != d_activeBasicVars.end();
  }

  void updateRow(Row* row){
    for(Row::iterator i=row->begin(), endIter = row->end(); i != endIter; ){
      TNode var = i->first;
      ++i;
      if(isBasic(var)){
        Row* row_var = isActiveBasicVariable(var) ? lookup(var) : lookupEjected(var);

        Assert(row_var != row);
        row->subsitute(*row_var);

        i = row->begin();
        endIter = row->end();
      }
    }
  }
};

}; /* namespace arith  */
}; /* namespace theory */
}; /* namespace CVC4   */

#endif /* __CVC4__THEORY__ARITH__TABLEAU_H */

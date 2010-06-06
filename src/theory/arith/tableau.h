/*********************                                                        */
/*! \file tableau.h
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


#include "expr/node.h"
#include "expr/attribute.h"

#include "theory/arith/basic.h"

#include <ext/hash_map>
#include <set>

#ifndef __CVC4__THEORY__ARITH__TABLEAU_H
#define __CVC4__THEORY__ARITH__TABLEAU_H

namespace CVC4 {
namespace theory {
namespace arith {


class Row {
  TNode d_x_i;

  typedef __gnu_cxx::hash_map<TNode, Rational, NodeHashFunction> CoefficientTable;

  std::set<TNode> d_nonbasic;
  CoefficientTable d_coeffs;

public:

  /**
   * Construct a row equal to:
   *   basic = \sum_{x_i} c_i * x_i
   */
  Row(TNode basic, TNode sum): d_x_i(basic),d_nonbasic(), d_coeffs(){
    using namespace CVC4::kind;

    Assert(d_x_i.getMetaKind() == CVC4::kind::metakind::VARIABLE);

    //TODO Assert(d_x_i.getType() == REAL);
    Assert(sum.getKind() == PLUS);

    for(TNode::iterator iter=sum.begin(); iter != sum.end(); ++iter){
      TNode pair = *iter;
      Assert(pair.getKind() == MULT);
      Assert(pair.getNumChildren() == 2);
      TNode coeff = pair[0];
      TNode var_i = pair[1];
      Assert(coeff.getKind() == CONST_RATIONAL);
      Assert(var_i.getKind() == VARIABLE);
      //TODO Assert(var_i.getKind() == REAL);
      Assert(!has(var_i));
      d_nonbasic.insert(var_i);
      d_coeffs[var_i] = coeff.getConst<Rational>();
      Assert(coeff.getConst<Rational>() != Rational(0,1));
      Assert(d_coeffs[var_i] != Rational(0,1));
    }
  }

  std::set<TNode>::iterator begin(){
    return d_nonbasic.begin();
  }

  std::set<TNode>::iterator end(){
    return d_nonbasic.end();
  }

  TNode basicVar(){
    return d_x_i;
  }

  bool has(TNode x_j){
    CoefficientTable::iterator x_jPos = d_coeffs.find(x_j);
    return x_jPos != d_coeffs.end();
  }

  Rational& lookup(TNode x_j){
    CoefficientTable::iterator x_jPos = d_coeffs.find(x_j);
    Assert(x_jPos !=  d_coeffs.end());
    return (*x_jPos).second;
  }

  void pivot(TNode x_j){
    Rational negInverseA_rs = -(lookup(x_j).inverse());
    d_coeffs[d_x_i] = Rational(Integer(-1));
    d_coeffs.erase(x_j);

    d_nonbasic.erase(x_j);
    d_nonbasic.insert(d_x_i);
    d_x_i = x_j;

    for(std::set<TNode>::iterator nonbasicIter = d_nonbasic.begin();
        nonbasicIter != d_nonbasic.end();
        ++nonbasicIter){
      TNode nb = *nonbasicIter;
      d_coeffs[nb] = d_coeffs[nb] * negInverseA_rs;
    }

  }

  void subsitute(Row& row_s){
    TNode x_s = row_s.basicVar();

    Assert(has(x_s));
    Assert(d_nonbasic.find(x_s) != d_nonbasic.end());
    Assert(x_s != d_x_i);

    Rational zero(0,1);

    Rational a_rs = lookup(x_s);
    Assert(a_rs != zero);
    d_coeffs.erase(x_s);
    d_nonbasic.erase(x_s);

    for(std::set<TNode>::iterator iter = row_s.d_nonbasic.begin();
        iter != row_s.d_nonbasic.end();
        ++iter){
      TNode x_j = *iter;
      Rational a_sj = row_s.lookup(x_j);
      a_sj *= a_rs;
      CoefficientTable::iterator coeff_iter = d_coeffs.find(x_j);

      if(coeff_iter != d_coeffs.end()){
        coeff_iter->second += a_sj;
        if(coeff_iter->second == zero){
          d_coeffs.erase(coeff_iter);
          d_nonbasic.erase(x_j);
        }
      }else{
        d_nonbasic.insert(x_j);
        d_coeffs.insert(make_pair(x_j,a_sj));
      }
      /*
      if(has(x_j)){
        d_coeffs[x_j] = d_coeffs[x_j] + a_sj;
        if(d_coeffs[x_j] == zero){
          d_coeffs.erase(x_j);
          d_nonbasic.erase(x_j);
        }
      }else{
        d_nonbasic.insert(x_j);
        d_coeffs[x_j] = a_sj;
      }
      */
    }
  }

  void printRow(){
    Debug("tableau") << d_x_i << " ";
    for(std::set<TNode>::iterator nonbasicIter = d_nonbasic.begin();
        nonbasicIter != d_nonbasic.end();
        ++nonbasicIter){
      TNode nb = *nonbasicIter;
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

  VarSet d_basicVars;
  RowsTable d_rows;

  inline bool contains(TNode var){
    return d_basicVars.find(var) != d_basicVars.end();
  }

public:
  /**
   * Constructs an empty tableau.
   */
  Tableau() : d_basicVars(), d_rows() {}

  VarSet::iterator begin(){
    return d_basicVars.begin();
  }

  VarSet::iterator end(){
    return d_basicVars.end();
  }

  Row* lookup(TNode var){
    Assert(contains(var));
    return d_rows[var];
  }

  /**
   * Iterator for the tableau. Iterates over rows.
   */
  /* TODO add back in =(
  class iterator {
  private:
    const Tableau*  table_ref;
    VarSet::iterator variableIter;

    iterator(const Tableau* tr, VarSet::iterator& i) :
      table_ref(tr), variableIter(i){}

  public:
    void operator++(){
      ++variableIter;
    }

    bool operator==(iterator& other){
      return variableIter == other.variableIter;
    }
    bool operator!=(iterator& other){
      return variableIter != other.variableIter;
    }

    Row& operator*() const{
      TNode var = *variableIter;
      RowsTable::iterator iter = table_ref->d_rows.find(var);
      return *iter;
    }
  };
  iterator begin(){
    return iterator(this, d_basicVars.begin());
  }
  iterator end(){
    return iterator(this, d_basicVars.end());
  }*/

  void addRow(TNode eq){
    Assert(eq.getKind() == kind::EQUAL);
    Assert(eq.getNumChildren() == 2);

    TNode var = eq[0];
    TNode sum = eq[1];

    //Assert(isAdmissableVariable(var));
    Assert(var.getAttribute(IsBasic()));

    //The new basic variable cannot already be a basic variable
    Assert(d_basicVars.find(var) == d_basicVars.end());
    d_basicVars.insert(var);
    Row* row_var = new Row(var,sum);
    d_rows[var] = row_var;

    //A variable in the row may have been made non-basic already.
    //fake the pivot of this variable
    for(TNode::iterator sumIter = sum.begin(); sumIter!=sum.end(); ++sumIter){
      TNode child = *sumIter; //(MULT (CONST_RATIONAL 1998/1001) x_5)
      Assert(child.getKind() == kind::MULT);
      Assert(child.getNumChildren() == 2);
      Assert(child[0].getKind() == kind::CONST_RATIONAL);
      TNode c = child[1];
      Assert(var.getMetaKind() == kind::metakind::VARIABLE);
      if(contains(c)){
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
    RowsTable::iterator ptrRow_r = d_rows.find(x_r);
    Assert(ptrRow_r != d_rows.end());

    Row* row_s = (*ptrRow_r).second;

    Assert(row_s->has(x_s));
    row_s->pivot(x_s);

    d_rows.erase(ptrRow_r);
    d_basicVars.erase(x_r);
    makeNonbasic(x_r);

    d_rows.insert(std::make_pair(x_s,row_s));
    d_basicVars.insert(x_s);
    makeBasic(x_s);

    for(VarSet::iterator basicIter = begin(); basicIter != end(); ++basicIter){
      TNode basic = *basicIter;
      Row* row_k = lookup(basic);
      if(row_k->basicVar() != x_s){
        if(row_k->has(x_s)){
          row_k->subsitute(*row_s);
        }
      }
    }
  }
  void printTableau(){
    for(VarSet::iterator basicIter = begin(); basicIter != end(); ++basicIter){
      TNode basic = *basicIter;
      Row* row_k = lookup(basic);
      row_k->printRow();
    }
  }
};

}; /* namespace arith  */
}; /* namespace theory */
}; /* namespace CVC4   */

#endif /* __CVC4__THEORY__ARITH__TABLEAU_H */

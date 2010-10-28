
#include "theory/arith/row_vector.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith ;

void RowVector::zip(const vector< ArithVar >& variables,
                    const vector< Rational >& coefficients,
                    VarCoeffArray& output){

  Assert(coefficients.size() == variables.size() );

  vector<Rational>::const_iterator coeffIter = coefficients.begin();
  vector<Rational>::const_iterator coeffEnd = coefficients.end();
  vector<ArithVar>::const_iterator varIter = variables.begin();

  for(; coeffIter != coeffEnd; ++coeffIter, ++varIter){
    const Rational& coeff = *coeffIter;
    ArithVar var_i = *varIter;

    output.push_back(make_pair(var_i, coeff));
  }
}

RowVector::RowVector(const vector< ArithVar >& variables,
                     const vector< Rational >& coefficients){
  zip(variables, coefficients, d_entries);

  std::sort(d_entries.begin(), d_entries.end(), cmp);

  Assert(isSorted(d_entries, true));
  Assert(noZeroCoefficients(d_entries));
}

void RowVector::merge(VarCoeffArray& arr, const VarCoeffArray& other, const Rational& c){
  VarCoeffArray copy = arr;
  arr.clear();

  iterator curr1 = copy.begin();
  iterator end1 = copy.end();

  NonZeroIterator curr2 = other.begin();
  NonZeroIterator end2 = other.end();

  while(curr1 != end1 && curr2 != end2){
    if(getArithVar(*curr1) < getArithVar(*curr2)){
      arr.push_back(*curr1);
      ++curr1;
    }else if(getArithVar(*curr1) > getArithVar(*curr2)){
      arr.push_back( make_pair(getArithVar(*curr2), c * getCoefficient(*curr2)));
      ++curr2;
    }else{
      Rational res = getCoefficient(*curr1) + c * getCoefficient(*curr2);
      if(res != 0){
        arr.push_back(make_pair(getArithVar(*curr1), res));
      }
      ++curr1;
      ++curr2;
    }
  }
  while(curr1 != end1){
    arr.push_back(*curr1);
    ++curr1;
  }
  while(curr2 != end2){
    arr.push_back(make_pair(getArithVar(*curr2), c * getCoefficient(*curr2)));
    ++curr2;
  }
}

void RowVector::multiply(const Rational& c){
  Assert(c != 0);

  for(iterator i = d_entries.begin(), end = d_entries.end(); i != end; ++i){
    getCoefficient(*i) *= c;
  }
}

void RowVector::addRowTimesConstant(const Rational& c, const RowVector& other){
  Assert(c != 0);

  merge(d_entries, other.d_entries, c);
}

void RowVector::printRow(){
  for(NonZeroIterator i = beginNonZero(); i != endNonZero(); ++i){
    ArithVar nb = getArithVar(*i);
    Debug("tableau") << "{" << nb << "," << getCoefficient(*i) << "}";
  }
  Debug("tableau") << std::endl;
}

ReducedRowVector::ReducedRowVector(ArithVar basic,
                                   const vector<ArithVar>& variables,
                                   const vector<Rational>& coefficients):
  RowVector(variables, coefficients), d_basic(basic){


  VarCoeffArray justBasic;
  justBasic.push_back(make_pair(basic, Rational(-1)));

  merge(d_entries,justBasic, Rational(1));

  Assert(wellFormed());
}

void ReducedRowVector::substitute(const ReducedRowVector& row_s){
  ArithVar x_s = row_s.basic();

  Assert(has(x_s));
  Assert(x_s != basic());

  Rational a_rs = lookup(x_s);
  Assert(a_rs != 0);

  addRowTimesConstant(a_rs, row_s);

  Assert(!has(x_s));
  Assert(wellFormed());
}

void ReducedRowVector::pivot(ArithVar x_j){
  Assert(has(x_j));
  Assert(basic() != x_j);
  Rational negInverseA_rs = -(lookup(x_j).inverse());
  multiply(negInverseA_rs);
  d_basic = x_j;

  Assert(wellFormed());
}

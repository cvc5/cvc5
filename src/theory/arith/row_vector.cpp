
#include "theory/arith/row_vector.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith ;

bool RowVector::isSorted(const VarCoeffArray& arr, bool strictlySorted) {
  if(arr.size() >= 2){
    NonZeroIterator curr = arr.begin();
    NonZeroIterator end = arr.end();
    ArithVar prev = getArithVar(*curr);
    ++curr;
    for(;curr != end; ++curr){
      ArithVar v = getArithVar(*curr);
      if(strictlySorted && prev > v) return false;
      if(!strictlySorted && prev >= v) return false;
      prev = v;
    }
  }
  return true;
}

RowVector::~RowVector(){
  NonZeroIterator curr = beginNonZero();
  NonZeroIterator end = endNonZero();
  for(;curr != end; ++curr){
    ArithVar v = getArithVar(*curr);
    Assert(d_rowCount[v] >= 1);
    --(d_rowCount[v]);
  }
}

bool RowVector::noZeroCoefficients(const VarCoeffArray& arr){
  for(NonZeroIterator curr = arr.begin(), end = arr.end();
      curr != end; ++curr){
    const Rational& coeff = getCoefficient(*curr);
    if(coeff == 0) return false;
  }
  return true;
}

void RowVector::zip(const std::vector< ArithVar >& variables,
                    const std::vector< Rational >& coefficients,
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


RowVector::RowVector(const std::vector< ArithVar >& variables,
                     const std::vector< Rational >& coefficients,
                     std::vector<uint32_t>& counts):
  d_rowCount(counts)
{
  zip(variables, coefficients, d_entries);

  std::sort(d_entries.begin(), d_entries.end(), cmp);

  for(NonZeroIterator i=beginNonZero(), end=endNonZero(); i != end; ++i){
    ++d_rowCount[getArithVar(*i)];
    addArithVar(d_contains, getArithVar(*i));
  }

  Assert(isSorted(d_entries, true));
  Assert(noZeroCoefficients(d_entries));
}

void RowVector::addArithVar(ArithVarContainsSet& contains, ArithVar v){
  if(v >= contains.size()){
    contains.resize(v+1, false);
  }
  contains[v] = true;
}

void RowVector::removeArithVar(ArithVarContainsSet& contains, ArithVar v){
  Assert(v < contains.size());
  Assert(contains[v]);
  contains[v] = false;
}

void RowVector::merge(VarCoeffArray& arr,
                      ArithVarContainsSet& contains,
                      const VarCoeffArray& other,
                      const Rational& c,
                      std::vector<uint32_t>& counts){
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
      ++counts[getArithVar(*curr2)];

      addArithVar(contains, getArithVar(*curr2));
      arr.push_back( make_pair(getArithVar(*curr2), c * getCoefficient(*curr2)));
      ++curr2;
    }else{
      Rational res = getCoefficient(*curr1) + c * getCoefficient(*curr2);
      if(res != 0){
        //The variable is not new so the count stays the same
        //bug: ++counts[getArithVar(*curr2)];

        arr.push_back(make_pair(getArithVar(*curr1), res));
      }else{
        removeArithVar(contains, getArithVar(*curr2));
        --counts[getArithVar(*curr2)];
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
    ++counts[getArithVar(*curr2)];

    addArithVar(contains, getArithVar(*curr2));

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

  merge(d_entries, d_contains, other.d_entries, c, d_rowCount);
}

void RowVector::printRow(){
  for(NonZeroIterator i = beginNonZero(); i != endNonZero(); ++i){
    ArithVar nb = getArithVar(*i);
    Debug("row::print") << "{" << nb << "," << getCoefficient(*i) << "}";
  }
  Debug("row::print") << std::endl;
}

ReducedRowVector::ReducedRowVector(ArithVar basic,
                                   const std::vector<ArithVar>& variables,
                                   const std::vector<Rational>& coefficients,
                                   std::vector<uint32_t>& count):
  RowVector(variables, coefficients, count), d_basic(basic){


  VarCoeffArray justBasic;
  justBasic.push_back(make_pair(basic, Rational(-1)));

  merge(d_entries, d_contains, justBasic, Rational(1), d_rowCount);

  Assert(wellFormed());
  Assert(d_rowCount[d_basic] == 1);
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
  Assert(d_rowCount[basic()] == 1);
}

void ReducedRowVector::pivot(ArithVar x_j){
  Assert(has(x_j));
  Assert(basic() != x_j);
  Rational negInverseA_rs = -(lookup(x_j).inverse());
  multiply(negInverseA_rs);
  d_basic = x_j;

  Assert(wellFormed());
  //The invariant Assert(d_rowCount[basic()] == 1); does not hold.
  //This is because the pivot is within the row first then
  //is moved through the propagated through the rest of the tableau.
}


Node ReducedRowVector::asEquality(const ArithVarToNodeMap& map) const{
  using namespace CVC4::kind;

  Assert(size() >= 2);
  Node sum = Node::null();
  if(size() > 2){
    NodeBuilder<> sumBuilder(PLUS);

    for(NonZeroIterator i = beginNonZero(); i != endNonZero(); ++i){
      ArithVar nb = getArithVar(*i);
      if(nb == basic()) continue;
      Node var = (map.find(nb))->second;
      Node coeff = mkRationalNode(getCoefficient(*i));

      Node mult = NodeBuilder<2>(MULT) << coeff << var;
      sumBuilder << mult;
    }
    sum = sumBuilder;
  }else{
    Assert(size() == 2);
    NonZeroIterator i = beginNonZero();
    if(getArithVar(*i) == basic()){
      ++i;
    }
    Assert(getArithVar(*i) != basic());
    Node var = (map.find(getArithVar(*i)))->second;
    Node coeff = mkRationalNode(getCoefficient(*i));
    sum = NodeBuilder<2>(MULT) << coeff << var;
  }
  Node basicVar = (map.find(basic()))->second;
  return NodeBuilder<2>(EQUAL) << basicVar << sum;
}


ReducedRowVector::~ReducedRowVector(){
  //This executes before the super classes destructor RowVector,
  // which will set this to 0.
  Assert(d_rowCount[basic()] == 1);
}


#include "theory/arith/row_vector.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

using namespace std;

bool ReducedRowVector::isSorted(const VarCoeffArray& arr, bool strictlySorted) {
  if(arr.size() >= 2){
    const_iterator curr = arr.begin();
    const_iterator end = arr.end();
    ArithVar prev = (*curr).getArithVar();
    ++curr;
    for(;curr != end; ++curr){
      ArithVar v = (*curr).getArithVar();
      if(strictlySorted && prev > v) return false;
      if(!strictlySorted && prev >= v) return false;
      prev = v;
    }
  }
  return true;
}

ReducedRowVector::~ReducedRowVector(){
  //This executes before the super classes destructor RowVector,
  // which will set this to 0.
  Assert(d_rowCount[basic()] == 1);

  const_iterator curr = begin();
  const_iterator endEntries = end();
  for(;curr != endEntries; ++curr){
    ArithVar v = (*curr).getArithVar();
    Assert(d_rowCount[v] >= 1);
    d_columnMatrix[v].remove(basic());
    --(d_rowCount[v]);
  }

  Assert(matchingCounts());
}


bool ReducedRowVector::matchingCounts() const{
  for(const_iterator i=begin(), endEntries=end(); i != endEntries; ++i){
    ArithVar v = (*i).getArithVar();
    if(d_columnMatrix[v].size() != d_rowCount[v]){
      return false;
    }
  }
  return true;
}

bool ReducedRowVector::noZeroCoefficients(const VarCoeffArray& arr){
  for(const_iterator curr = arr.begin(), endEntries = arr.end();
      curr != endEntries; ++curr){
    const Rational& coeff = (*curr).getCoefficient();
    if(coeff == 0) return false;
  }
  return true;
}

void ReducedRowVector::zip(const std::vector< ArithVar >& variables,
                           const std::vector< Rational >& coefficients,
                           VarCoeffArray& output){

  Assert(coefficients.size() == variables.size() );

  vector<Rational>::const_iterator coeffIter = coefficients.begin();
  vector<Rational>::const_iterator coeffEnd = coefficients.end();
  vector<ArithVar>::const_iterator varIter = variables.begin();

  for(; coeffIter != coeffEnd; ++coeffIter, ++varIter){
    const Rational& coeff = *coeffIter;
    ArithVar var_i = *varIter;

    output.push_back(VarCoeffPair(var_i, coeff));
  }
}

void ReducedRowVector::addArithVar(ArithVarContainsSet& contains, ArithVar v){
  if(v >= contains.size()){
    contains.resize(v+1, false);
  }
  contains[v] = true;
}

void ReducedRowVector::removeArithVar(ArithVarContainsSet& contains, ArithVar v){
  Assert(v < contains.size());
  Assert(contains[v]);
  contains[v] = false;
}

void ReducedRowVector::multiply(const Rational& c){
  Assert(c != 0);

  for(iterator i = d_entries.begin(), end = d_entries.end(); i != end; ++i){
    (*i).getCoefficient() *= c;
  }
}

void ReducedRowVector::addRowTimesConstant(const Rational& c, const ReducedRowVector& other){
  Assert(c != 0);
  Assert(d_buffer.empty());
  Assert(wellFormed());

  d_buffer.reserve(other.d_entries.size());

  iterator curr1 = d_entries.begin();
  iterator end1 = d_entries.end();

  const_iterator curr2 = other.d_entries.begin();
  const_iterator end2 = other.d_entries.end();

  while(curr1 != end1 && curr2 != end2){
    ArithVar var1 = (*curr1).getArithVar();
    ArithVar var2 = (*curr2).getArithVar();

    if(var1 < var2){
      d_buffer.push_back(*curr1);
      ++curr1;
    }else if(var1 > var2){

      ++d_rowCount[var2];
      d_columnMatrix[var2].add(d_basic);

      addArithVar(d_contains, var2);
      const Rational& coeff2 = (*curr2).getCoefficient();
      d_buffer.push_back( VarCoeffPair(var2, c * coeff2));
      ++curr2;
    }else{
      Assert(var1 == var2);
      const Rational& coeff1 = (*curr1).getCoefficient();
      const Rational& coeff2 = (*curr2).getCoefficient();
      Rational res = coeff1 + (c * coeff2);
      if(res != 0){
        //The variable is not new so the count stays the same
        d_buffer.push_back(VarCoeffPair(var1, res));
      }else{
        removeArithVar(d_contains, var1);

        --d_rowCount[var1];
        d_columnMatrix[var1].remove(d_basic);
      }
      ++curr1;
      ++curr2;
    }
  }
  while(curr1 != end1){
    d_buffer.push_back(*curr1);
    ++curr1;
  }
  while(curr2 != end2){
    ArithVar var2 = (*curr2).getArithVar();
    const Rational& coeff2 = (*curr2).getCoefficient();
    ++d_rowCount[var2];
    d_columnMatrix[var2].add(d_basic);

    addArithVar(d_contains, var2);

    d_buffer.push_back(VarCoeffPair(var2, c * coeff2));
    ++curr2;
  }

  d_buffer.swap(d_entries);
  d_buffer.clear();

  Assert(d_buffer.empty());
}

void ReducedRowVector::printRow(){
  for(const_iterator i = begin(); i != end(); ++i){
    ArithVar nb = (*i).getArithVar();
    const Rational& coeff = (*i).getCoefficient();
    Debug("row::print") << "{" << nb << "," << coeff << "}";
  }
  Debug("row::print") << std::endl;
}


ReducedRowVector::ReducedRowVector(ArithVar basic,
                                   const std::vector<ArithVar>& variables,
                                   const std::vector<Rational>& coefficients,
                                   std::vector<uint32_t>& counts,
                                   std::vector<ArithVarSet>& cm):
  d_basic(basic), d_rowCount(counts),  d_columnMatrix(cm)
{
  zip(variables, coefficients, d_entries);
  d_entries.push_back(VarCoeffPair(basic, Rational(-1)));

  std::sort(d_entries.begin(), d_entries.end());

  for(const_iterator i=begin(), endEntries=end(); i != endEntries; ++i){
    ArithVar var = (*i).getArithVar();
    ++d_rowCount[var];
    addArithVar(d_contains, var);
    d_columnMatrix[var].add(d_basic);
  }

  Assert(isSorted(d_entries, true));
  Assert(noZeroCoefficients(d_entries));

  Assert(matchingCounts());
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
  Assert(matchingCounts());
  Assert(d_rowCount[basic()] == 1);
}

void ReducedRowVector::pivot(ArithVar x_j){
  Assert(has(x_j));
  Assert(basic() != x_j);
  Rational negInverseA_rs = -(lookup(x_j).inverse());
  multiply(negInverseA_rs);

  for(const_iterator i=begin(), endEntries=end(); i != endEntries; ++i){
    ArithVar var = (*i).getArithVar();
    d_columnMatrix[var].remove(d_basic);
    d_columnMatrix[var].add(x_j);
  }

  d_basic = x_j;

  Assert(matchingCounts());
  Assert(wellFormed());
  //The invariant Assert(d_rowCount[basic()] == 1); does not hold.
  //This is because the pivot is within the row first then
  //is moved through the propagated through the rest of the tableau.
}


Node ReducedRowVector::asEquality(const ArithVarToNodeMap& map) const{
  using namespace CVC4::kind;

  Assert(size() >= 2);

  vector<Node> nonBasicPairs;
  for(const_iterator i = begin(); i != end(); ++i){
    ArithVar nb = (*i).getArithVar();
    if(nb == basic()) continue;
    Node var = (map.find(nb))->second;
    Node coeff = mkRationalNode((*i).getCoefficient());

    Node mult = NodeBuilder<2>(MULT) << coeff << var;
    nonBasicPairs.push_back(mult);
  }

  Node sum = Node::null();
  if(nonBasicPairs.size() == 1 ){
    sum = nonBasicPairs.front();
  }else{
    Assert(nonBasicPairs.size() >= 2);
    NodeBuilder<> sumBuilder(PLUS);
    sumBuilder.append(nonBasicPairs);
    sum = sumBuilder;
  }
  Node basicVar = (map.find(basic()))->second;
  return NodeBuilder<2>(EQUAL) << basicVar << sum;

  /*
  Node sum = Node::null();
  if(size() > 2){
    NodeBuilder<> sumBuilder(PLUS);

    for(const_iterator i = begin(); i != end(); ++i){
      ArithVar nb = (*i).getArithVar();
      if(nb == basic()) continue;
      Node var = (map.find(nb))->second;
      Node coeff = mkRationalNode((*i).getCoefficient());

      Node mult = NodeBuilder<2>(MULT) << coeff << var;
      sumBuilder << mult;
    }
    sum = sumBuilder;
  }else{
    Assert(size() == 2);
    const_iterator i = begin();
    if((*i).getArithVar() == basic()){
      ++i;
    }
    Assert((*i).getArithVar() != basic());
    Node var = (map.find((*i).getArithVar()))->second;
    Node coeff = mkRationalNode((*i).getCoefficient());
    sum = NodeBuilder<2>(MULT) << coeff << var;
  }
  Node basicVar = (map.find(basic()))->second;
  return NodeBuilder<2>(EQUAL) << basicVar << sum;
*/
}


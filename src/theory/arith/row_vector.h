

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ROW_VECTOR_H
#define __CVC4__THEORY__ARITH__ROW_VECTOR_H

#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar_set.h"
#include "util/rational.h"
#include <vector>

namespace CVC4 {
namespace theory {
namespace arith {

class VarCoeffPair {
private:
  ArithVar d_variable;
  Rational d_coeff;

public:
  VarCoeffPair(ArithVar v, const Rational& q): d_variable(v), d_coeff(q) {}

  ArithVar getArithVar() const { return d_variable; }
  Rational& getCoefficient() { return d_coeff; }
  const Rational& getCoefficient() const { return d_coeff; }

  bool operator<(const VarCoeffPair& other) const{
    return getArithVar() < other.getArithVar();
  }

  static bool variableLess(const VarCoeffPair& a, const VarCoeffPair& b){
    return a < b;
  }
};

/**
 * ReducedRowVector is a sparse vector representation that represents the
 * row as a strictly sorted array of "VarCoeffPair"s.
 * The row has a notion of a basic variable.
 * This is a variable that must have a coefficient of -1 in the array.
 */
class ReducedRowVector {
public:
  typedef std::vector<VarCoeffPair> VarCoeffArray;
  typedef VarCoeffArray::const_iterator const_iterator;

private:
  typedef std::vector<bool> ArithVarContainsSet;
  typedef VarCoeffArray::iterator iterator;

  /**
   * Invariants:
   * - isSorted(d_entries, true)
   * - noZeroCoefficients(d_entries)
   */
  VarCoeffArray d_entries;

  /**
   * Buffer for d_entries to reduce allocations by addRowTimesConstant.
   */
  VarCoeffArray d_buffer;

  /**
   * The basic variable associated with the row.
   * Must have a coefficient of -1.
   */
  ArithVar d_basic;


  /**
   * Invariants:
   * - This set is the same as the set maintained in d_entries.
   */
  ArithVarContainsSet d_contains;

  std::vector<uint32_t>& d_rowCount;
  std::vector<PermissiveBackArithVarSet>& d_columnMatrix;


public:

  ReducedRowVector(ArithVar basic,
                   const std::vector< ArithVar >& variables,
                   const std::vector< Rational >& coefficients,
                   std::vector<uint32_t>& count,
                   std::vector< PermissiveBackArithVarSet >& columnMatrix);
  ~ReducedRowVector();

  void enqueueNonBasicVariablesAndCoefficients(std::vector< ArithVar >& variables,
                                               std::vector< Rational >& coefficients) const;

  /** Returns the basic variable.*/
  ArithVar basic() const{
    Assert(basicIsSet());
    return d_basic;
  }

  /** Returns the number of nonzero variables in the vector. */
  uint32_t size() const {
    return d_entries.size();
  }

  /** Iterates over the nonzero entries in the vector. */
  const_iterator begin() const { return d_entries.begin(); }
  const_iterator end() const { return d_entries.end(); }

  /** Returns true if the variable is in the row. */
  bool has(ArithVar x_j) const{
    if(x_j >= d_contains.size()){
      return false;
    }else{
      return d_contains[x_j];
    }
  }

  /**
   * Returns the coefficient of a variable in the row.
   */
  const Rational& lookup(ArithVar x_j) const{
    Assert(has(x_j));
    Assert(hasInEntries(x_j));
    const_iterator lb = lower_bound(x_j);
    return (*lb).getCoefficient();
  }


  /** Prints the row to the buffer Debug("row::print"). */
  void printRow();

  /**
   * Changes the basic variable to x_j.
   * Precondition: has(x_j)
   */
  void pivot(ArithVar x_j);

  /**
   * Replaces other.basic() in the current row using the other row.
   * This assumes the other row represents an equality equal to zero.
   *
   *   \sum(this->entries) -= this->lookup(other.basic()) * (\sum(other.d_entries))
   * Precondition:
   *  has(other.basic())
   *  basic != other.basic()
   */
  void substitute(const ReducedRowVector& other);

  /**
   * Returns the reduced row as an equality with
   * the basic variable on the lhs equal to the sum of the non-basics variables.
   * The mapped from ArithVars to Nodes is specificied by map.
   */
  Node asEquality(const ArithVarToNodeMap& map) const;

private:

  /**
   * \sum(this->entries) += c * (\sum(other.d_entries) )
   *
   * Updates the current row to be the sum of itself and
   * another vector times c (c != 0).
   */
  void addRowTimesConstant(const Rational& c, const ReducedRowVector& other);


  /** Multiplies the coefficients of the RowVector by c (where c != 0). */
  void multiply(const Rational& c);

  /**
   * Adds v to d_contains.
   * This may resize d_contains.
   */
  static void addArithVar(ArithVarContainsSet& contains, ArithVar v);

  /** Removes v from d_contains. */
  static void removeArithVar(ArithVarContainsSet& contains, ArithVar v);


  /**
   * Let c be -1 if strictlySorted is true and c be 0 otherwise.
   * isSorted(arr, strictlySorted) is then equivalent to
   * If i<j, cmp(getArithVar(d_entries[i]), getArithVar(d_entries[j])) <= c.
   */
  static bool isSorted(const VarCoeffArray& arr, bool strictlySorted);

  /**
   * Zips together an array of variables and coefficients and appends
   * it to the end of an output vector.
   */
  static void zip(const std::vector< ArithVar >& variables,
                  const std::vector< Rational >& coefficients,
                  VarCoeffArray& output);

  /**
   * Debugging code.
   * noZeroCoefficients(arr) is equivalent to
   *  0 != getCoefficient(arr[i]) for all i.
   */
  static bool noZeroCoefficients(const VarCoeffArray& arr);

  /** Debugging code.*/
  bool matchingCounts() const;

  const_iterator lower_bound(ArithVar x_j) const{
    return std::lower_bound(d_entries.begin(), d_entries.end(), VarCoeffPair(x_j, 0));
  }

  /** Debugging code */
  bool wellFormed() const{
    return
      isSorted(d_entries, true) &&
      noZeroCoefficients(d_entries) &&
      basicIsSet() &&
      has(basic()) &&
      lookup(basic()) == Rational(-1);
  }

  bool basicIsSet() const { return d_basic != ARITHVAR_SENTINEL; }

  /** Debugging code. */
  bool hasInEntries(ArithVar x_j) const {
    return std::binary_search(d_entries.begin(), d_entries.end(), VarCoeffPair(x_j,0));
  }

}; /* class ReducedRowVector */


}/* namespace CVC4::theory::arith */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH_ARITH_CONSTANTS_H */

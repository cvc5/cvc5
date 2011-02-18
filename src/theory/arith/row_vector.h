

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ROW_VECTOR_H
#define __CVC4__THEORY__ARITH__ROW_VECTOR_H

#include "theory/arith/arith_utilities.h"
#include "util/rational.h"
#include <vector>

namespace CVC4 {
namespace theory {
namespace arith {

typedef std::pair<ArithVar, Rational> VarCoeffPair;
inline ArithVar getArithVar(const VarCoeffPair& v) { return v.first; }
inline Rational& getCoefficient(VarCoeffPair& v) { return v.second; }
inline const Rational& getCoefficient(const VarCoeffPair& v) { return v.second; }

inline bool cmp(const VarCoeffPair& a, const VarCoeffPair& b){
  return CVC4::theory::arith::getArithVar(a) < CVC4::theory::arith::getArithVar(b);
}

/**
 * RowVector is a sparse vector representation that represents the
 * row as a strictly sorted array of "VarCoeffPair"s.
 */
class RowVector {
public:
  typedef std::vector<VarCoeffPair> VarCoeffArray;
  typedef VarCoeffArray::const_iterator NonZeroIterator;

  typedef std::vector<bool> ArithVarContainsSet;

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

  static void merge(VarCoeffArray& arr,
                    ArithVarContainsSet& contains,
                    const VarCoeffArray& other,
                    const Rational& c,
                    std::vector<uint32_t>& count);

protected:
  /**
   * Debugging code.
   * noZeroCoefficients(arr) is equivalent to
   *  0 != getCoefficient(arr[i]) for all i.
   */
  static bool noZeroCoefficients(const VarCoeffArray& arr);

  /**
   * Invariants:
   * - isSorted(d_entries, true)
   * - noZeroCoefficients(d_entries)
   */
  VarCoeffArray d_entries;

  /**
   * Invariants:
   * - This set is the same as the set maintained in d_entries.
   */
  ArithVarContainsSet d_contains;

  std::vector<uint32_t>& d_rowCount;

  NonZeroIterator lower_bound(ArithVar x_j) const{
    return std::lower_bound(d_entries.begin(), d_entries.end(), make_pair(x_j,0), cmp);
  }

  typedef VarCoeffArray::iterator iterator;

public:

  RowVector(const std::vector< ArithVar >& variables,
            const std::vector< Rational >& coefficients,
            std::vector<uint32_t>& counts);

  ~RowVector();

  /** Returns the number of nonzero variables in the vector. */
  uint32_t size() const {
    return d_entries.size();
  }

  //Iterates over the nonzero entries in the Vector
  NonZeroIterator beginNonZero() const { return d_entries.begin(); }
  NonZeroIterator endNonZero() const { return d_entries.end(); }

  /** Returns true if the variable is in the row. */
  bool has(ArithVar x_j) const{
    if(x_j >= d_contains.size()){
      return false;
    }else{
      return d_contains[x_j];
    }
  }

private:
  /** Debugging code. */
  bool hasInEntries(ArithVar x_j) const {
    return std::binary_search(d_entries.begin(), d_entries.end(), make_pair(x_j,0), cmp);
  }
public:

  /**
   * Returns the coefficient of a variable in the row.
   */
  const Rational& lookup(ArithVar x_j) const{
    Assert(has(x_j));
    Assert(hasInEntries(x_j));
    NonZeroIterator lb = lower_bound(x_j);
    return getCoefficient(*lb);
  }

  /** Multiplies the coefficients of the RowVector by c (where c != 0). */
  void multiply(const Rational& c);

  /**
   * \sum(this->entries) += c * (\sum(other.d_entries) )
   *
   * Updates the current row to be the sum of itself and
   * another vector times c (c != 0).
   */
  void addRowTimesConstant(const Rational& c, const RowVector& other);

  void printRow();

protected:
  /**
   * Adds v to d_contains.
   * This may resize d_contains.
   */
  static void addArithVar(ArithVarContainsSet& contains, ArithVar v);

  /** Removes v from d_contains. */
  static void removeArithVar(ArithVarContainsSet& contains, ArithVar v);

}; /* class RowVector */

/**
 * A reduced row is similar to a normal row except
 * that it also has a notion of a basic variable.
 * This variable that must have a coefficient of -1 in the array.
 */
class ReducedRowVector : public RowVector{
private:
  ArithVar d_basic;

  bool wellFormed() const{
    return
      isSorted(d_entries, true) &&
      noZeroCoefficients(d_entries) &&
      basicIsSet() &&
      has(basic()) &&
      lookup(basic()) == Rational(-1);
  }

public:

  bool basicIsSet() const { return d_basic != ARITHVAR_SENTINEL; }

  ReducedRowVector(ArithVar basic,
                   const std::vector< ArithVar >& variables,
                   const std::vector< Rational >& coefficients,
                   std::vector<uint32_t>& count);


  ArithVar basic() const{
    Assert(basicIsSet());
    return d_basic;
  }

  /** Return true if x is in the row and is not the basic variable. */
  bool hasNonBasic(ArithVar x) const {
    if(x == basic()){
      return false;
    }else{
      return has(x);
    }
  }

  void pivot(ArithVar x_j);

  void substitute(const ReducedRowVector& other);

  /**
   * Returns the reduced row as an equality with
   * the basic variable on the lhs equal to the sum of the non-basics variables.
   * The mapped from ArithVars to Nodes is specificied by map.
   */
  Node asEquality(const ArithVarToNodeMap& map) const;
}; /* class ReducedRowVector */


}/* namespace CVC4::theory::arith */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH_ARITH_CONSTANTS_H */

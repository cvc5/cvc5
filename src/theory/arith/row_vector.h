

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

  /**
   * Let c be -1 if strictlySorted is true and c be 0 otherwise.
   * isSorted(arr, strictlySorted) is then equivalent to
   * If i<j, cmp(getArithVar(d_entries[i]), getArithVar(d_entries[j])) <= c.
   */
  static bool isSorted(const VarCoeffArray& arr, bool strictlySorted) {
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

  /**
   * noZeroCoefficients(arr) is equivalent to
   *  0 != getCoefficient(arr[i]) for all i.
   */
  static bool noZeroCoefficients(const VarCoeffArray& arr){
    for(NonZeroIterator curr = arr.begin(), end = arr.end();
        curr != end; ++curr){
      const Rational& coeff = getCoefficient(*curr);
      if(coeff == 0) return false;
    }
    return true;
  }

  /**
   * Zips together an array of variables and coefficients and appends
   * it to the end of an output vector.
   */
  static void zip(const std::vector< ArithVar >& variables,
                  const std::vector< Rational >& coefficients,
                  VarCoeffArray& output);

  static void merge(VarCoeffArray& arr, const VarCoeffArray& other, const Rational& c);


protected:
  /**
   * Invariants:
   * - isSorted(d_entries, true)
   * - noZeroCoefficients(d_entries)
   */
  VarCoeffArray d_entries;

  NonZeroIterator lower_bound(ArithVar x_j) const{
    return std::lower_bound(d_entries.begin(), d_entries.end(), make_pair(x_j,0), cmp);
  }

  typedef VarCoeffArray::iterator iterator;

public:

  RowVector() : d_entries() {}

  RowVector(const std::vector< ArithVar >& variables,
            const std::vector< Rational >& coefficients);


  //Iterates over the nonzero entries in the Vector
  NonZeroIterator beginNonZero() const { return d_entries.begin(); }
  NonZeroIterator endNonZero() const { return d_entries.end(); }

  /** Returns true if the variable is in the row. */
  bool has(ArithVar x_j) const{
    return std::binary_search(d_entries.begin(), d_entries.end(), make_pair(x_j,0), cmp);
  }

  /**
   * Returns the coefficient of a variable in the row.
   */
  const Rational& lookup(ArithVar x_j) const{
    Assert(has(x_j));
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
                   const std::vector< Rational >& coefficients);


  ArithVar basic() const{
    Assert(basicIsSet());
    return d_basic;
  }

  void pivot(ArithVar x_j);

  void substitute(const ReducedRowVector& other);
}; /* class ReducedRowVector */


}/* namespace CVC4::theory::arith */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH_ARITH_CONSTANTS_H */

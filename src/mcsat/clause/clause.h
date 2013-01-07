#pragma once

#include <vector>
#include <iostream>

#include "cvc4_private.h"

#include "mcsat/clause/literal.h"

namespace CVC4 {
namespace mcsat {

class Clause {

  /** Size of the clause */
  size_t d_size     : 28;
  /** Rule that produced this clause */
  size_t d_ruleId   : 4;

  /** The literals */
  Literal d_literals[0];

  /** Construct the clause from given literals */
  Clause(const std::vector<Literal>& literals, size_t ruleId);

  /** Copy construction */
  Clause(const Clause& clause);
  
  friend class ClauseDatabase;

public:

  ~Clause();

  /** Number of literals in the clause */
  size_t size() const {
    return d_size;
  }

  /** Get the literal at position i */
  Literal operator[] (size_t i) const {
    return d_literals[i];
  }

  /** Swap the literals at given positions */
  void swapLiterals(size_t i, size_t j) {
    // Swap is overloaded so that no references are counted
    std::swap(d_literals[i], d_literals[j]);
  }

  /** Get the id of the rule that produced this clause */
  size_t getRuleId() const {
    return d_ruleId;
  }

  template <class Compare>
  void sort(Compare& cmp);

  /** Simple stream representation of the clause */
  void toStream(std::ostream& out) const;
};

/** Output operator for clauses */
inline std::ostream& operator << (std::ostream& out, const Clause& clause) {
  clause.toStream(out);
  return out;
}

// Sorting as Literals since we only shuffle them around
template<class Compare>
inline void Clause::sort(Compare& cmp) {
  std::sort(d_literals, d_literals + size(), cmp);
}

} /* Namespace mcsat */
} /* namespace CVC4 */


/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inst match class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_MATCH_H
#define CVC5__THEORY__QUANTIFIERS__INST_MATCH_H

#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;

/** Inst match
 *
 * This is the basic class specifying an instantiation. Its domain size (the
 * size of d_vals) is the number of bound variables of the quantified formula
 * that is passed to its constructor.
 *
 * The values of d_vals may be null, which indicate that the field has
 * yet to be initialized.
 */
class InstMatch {
 public:
  InstMatch(TNode q);
  /** add match m
   *
   * This adds the initialized fields of m to this match for each field that is
   * not already initialized in this match.
   */
  void add(InstMatch& m);
  /** is this complete, i.e. are all fields non-null? */
  bool isComplete() const;
  /** is this empty, i.e. are all fields the null node? */
  bool empty() const;
  /** clear the instantiation, i.e. set all fields to the null node */
  void clear();
  /** debug print method */
  void debugPrint(const char* c);
  /** to stream */
  void toStream(std::ostream& out) const;
  /** get the i^th term in the instantiation */
  Node get(size_t i) const;
  /** set/overwrites the i^th field in the instantiation with n */
  void setValue(size_t i, TNode n);
  /** set the i^th term in the instantiation to n
   *
   * This method returns true if the i^th field was previously uninitialized,
   * or is equivalent to n modulo the equalities given by q.
   */
  bool set(QuantifiersState& qs, size_t i, TNode n);
  /** Resets index i */
  void reset(size_t i);
  /** Get the values */
  std::vector<Node>& get();

 private:
  /**
   * Ground terms for each variable of the quantified formula, in order.
   * Null nodes indicate the variable has not been set.
   */
  std::vector<Node> d_vals;
  /** The quantified formula */
  Node d_quant;
};

inline std::ostream& operator<<(std::ostream& out, const InstMatch& m) {
  m.toStream(out);
  return out;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__INST_MATCH_H */

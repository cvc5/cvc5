/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "smt/env_obj.h"
#include "theory/quantifiers/ieval/inst_evaluator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;
class TermRegistry;

/** Inst match
 *
 * This is the basic class specifying an instantiation. Its domain size (the
 * size of d_vals) is the number of bound variables of the quantified formula
 * that is passed to its constructor.
 *
 * The values of d_vals may be null, which indicate that the field has
 * yet to be initialized.
 */
class InstMatch : protected EnvObj
{
 public:
  InstMatch(Env& env, QuantifiersState& qs, TermRegistry& tr, TNode q);
  /**
   * Set evaluator mode. This can be modified if there are no variable
   * assignments.
   */
  void setEvaluatorMode(ieval::TermEvaluatorMode tev);
  /** is this complete, i.e. are all fields non-null? */
  bool isComplete() const;
  /** is this empty, i.e. are all fields the null node? */
  bool empty() const;
  /**
   * Clear the instantiation, i.e. set all fields to the null node.
   * Note that this does not clear information regarding the instantiation
   * evaluator, e.g. its evaluation mode and watched information.
   */
  void resetAll();
  /** debug print method */
  void debugPrint(const char* c);
  /** to stream */
  void toStream(std::ostream& out) const;
  /** get the i^th term in the instantiation */
  Node get(size_t i) const;
  /** set the i^th term in the instantiation to n
   *
   * If the d_vals[i] is not null, then this return true iff it is equal to
   * n based on the quantifiers state.
   *
   * If the d_vals[i] is null, then this sets d_vals[i] to n, and pushes a
   * context scope in the inst evaluator (if used).
   */
  bool set(size_t i, TNode n);
  /**
   * Resets index i, which sets d_vals[i] to null, and pops a context scope in
   * the inst evaluator (if used).
   */
  void reset(size_t i);
  /** Get the values */
  const std::vector<Node>& get() const;

 private:
  /** Reference to the state */
  QuantifiersState& d_qs;
  /** Reference to the term registry */
  TermRegistry& d_tr;
  /**
   * Ground terms for each variable of the quantified formula, in order.
   * Null nodes indicate the variable has not been set.
   */
  std::vector<Node> d_vals;
  /** The quantified formula */
  Node d_quant;
  /** The instantiation evaluator */
  ieval::InstEvaluator* d_ieval;
};

inline std::ostream& operator<<(std::ostream& out, const InstMatch& m) {
  m.toStream(out);
  return out;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__INST_MATCH_H */

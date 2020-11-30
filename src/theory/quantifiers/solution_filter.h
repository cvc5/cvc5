/*********************                                                        */
/*! \file solution_filter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for filtering sygus solutions.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SOLUTION_FILTER_H
#define CVC4__THEORY__QUANTIFIERS__SOLUTION_FILTER_H

#include <map>
#include <unordered_set>
#include "expr/node.h"
#include "theory/quantifiers/expr_miner.h"
#include "theory/quantifiers/lazy_trie.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * This class is used to filter solutions based on logical strength.
 *
 * Currently, it is used to filter predicate solutions that are collectively
 * entailed by the previous predicate solutions (if we are looking for logically
 * stronger solutions), or to filter predicate solutions that entail any
 * previous predicate (if we are looking for logically weaker solutions).
 */
class SolutionFilterStrength : public ExprMiner
{
 public:
  SolutionFilterStrength();
  ~SolutionFilterStrength() {}
  /** initialize */
  void initialize(const std::vector<Node>& vars,
                  SygusSampler* ss = nullptr) override;
  /**
   * Add term to this miner. It is expected that n has Boolean type.
   *
   * If d_isStrong is true, then if this method returns false, then the
   * entailment n_1 ^ ... ^ n_m |= n holds, where n_1, ..., n_m are the terms
   * previously registered to this class.
   *
   * Dually, if d_isStrong is false, then if this method returns false, then
   * the entailment n |= n_1 V ... V n_m holds.
   */
  bool addTerm(Node n, std::ostream& out) override;
  /** set logically strong */
  void setLogicallyStrong(bool isStrong);

 private:
  /**
   * Set of all (non-filtered) terms registered to this class. We store the
   * negation of these terms if d_isStrong is false.
   */
  std::vector<Node> d_curr_sols;
  /** whether we are trying to find the logically strongest solutions */
  bool d_isStrong;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SOLUTION_FILTER_H */

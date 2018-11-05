/*********************                                                        */
/*! \file solution_filter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for filtering sygus solutions.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SOLUTION_FILTER_H
#define __CVC4__THEORY__QUANTIFIERS__SOLUTION_FILTER_H

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
 * This class is used to filter solutions based on some criteria.
 *
 * Currently, it is used to filter predicate solutions that are collectively
 * entailed by the previous predicate solutions.
 */
class SolutionFilter : public ExprMiner
{
 public:
  SolutionFilter();
  ~SolutionFilter() {}
  /** initialize */
  void initialize(const std::vector<Node>& vars,
                  SygusSampler* ss = nullptr) override;
  /**
   * Add term to this module. It is expected that n has Boolean type.
   * If this method returns false, then the entailment n_1 ^ ... ^ n_m |= n
   * holds, where n_1, ..., n_m are the terms previously registered to this
   * class.
   */
  bool addTerm(Node n, std::ostream& out) override;

 private:
  /** conjunction of all (non-implied) terms registered to this class */
  Node d_conj;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__SOLUTION_FILTER_H */

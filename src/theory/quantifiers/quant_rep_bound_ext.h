/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quantifiers representative bound utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUANT_REP_BOUND_EXT_H
#define CVC5__THEORY__QUANTIFIERS__QUANT_REP_BOUND_EXT_H

#include <map>

#include "expr/node.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/rep_set_iterator.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersBoundInference;
class FirstOrderModel;

/** Quantifiers representative bound
 *
 * This class is used for computing (finite) bounds for the domain of a
 * quantifier in the context of a RepSetIterator (see theory/rep_set.h)
 * based on modules from the quantifiers engine.
 */
class QRepBoundExt : public RepBoundExt
{
 public:
  QRepBoundExt(Env& env,
               QuantifiersBoundInference& qbi,
               QuantifiersState& qs,
               TermRegistry& tr,
               TNode q);
  virtual ~QRepBoundExt() {}
  /** set bound */
  RsiEnumType setBound(Node owner,
                       size_t i,
                       std::vector<Node>& elements) override;
  /** reset index */
  bool resetIndex(RepSetIterator* rsi,
                  Node owner,
                  size_t i,
                  bool initial,
                  std::vector<Node>& elements) override;
  /** initialize representative set for type */
  bool initializeRepresentativesForType(TypeNode tn) override;
  /** get variable order */
  bool getVariableOrder(Node owner, std::vector<size_t>& varOrder) override;

 private:
  /** Reference to the quantifiers bound inference */
  QuantifiersBoundInference& d_qbi;
  /** Pointer to the quantifiers model */
  FirstOrderModel* d_model;
  /** indices that are bound integer enumeration */
  std::map<size_t, bool> d_bound_int;
  /** An instantiation match */
  InstMatch d_instMatch;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__FIRST_ORDER_MODEL_H */

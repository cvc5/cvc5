/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "theory/rep_set.h"
#include "theory/theory_model.h"

namespace cvc5 {
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
  QRepBoundExt(QuantifiersBoundInference& qbi, FirstOrderModel* m);
  virtual ~QRepBoundExt() {}
  /** set bound */
  RsiEnumType setBound(Node owner,
                       unsigned i,
                       std::vector<Node>& elements) override;
  /** reset index */
  bool resetIndex(RepSetIterator* rsi,
                  Node owner,
                  unsigned i,
                  bool initial,
                  std::vector<Node>& elements) override;
  /** initialize representative set for type */
  bool initializeRepresentativesForType(TypeNode tn) override;
  /** get variable order */
  bool getVariableOrder(Node owner, std::vector<unsigned>& varOrder) override;

 private:
  /** Reference to the quantifiers bound inference */
  QuantifiersBoundInference& d_qbi;
  /** Pointer to the quantifiers model */
  FirstOrderModel* d_model;
  /** indices that are bound integer enumeration */
  std::map<unsigned, bool> d_bound_int;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__FIRST_ORDER_MODEL_H */

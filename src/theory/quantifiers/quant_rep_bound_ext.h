/*********************                                                        */
/*! \file quant_rep_bound_ext.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Quantifiers representative bound utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__QUANT_REP_BOUND_EXT_H
#define CVC4__THEORY__QUANTIFIERS__QUANT_REP_BOUND_EXT_H

#include <map>

#include "expr/node.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/rep_set.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

/** Quantifiers representative bound
 *
 * This class is used for computing (finite) bounds for the domain of a
 * quantifier in the context of a RepSetIterator (see theory/rep_set.h)
 * based on modules from the quantifiers engine.
 */
class QRepBoundExt : public RepBoundExt
{
 public:
  QRepBoundExt(QuantifiersEngine* qe);
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
  /** Quantifiers engine associated with this bound */
  QuantifiersEngine* d_qe;
  /** indices that are bound integer enumeration */
  std::map<unsigned, bool> d_bound_int;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__FIRST_ORDER_MODEL_H */

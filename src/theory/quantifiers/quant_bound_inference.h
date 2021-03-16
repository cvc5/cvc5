/*********************                                                        */
/*! \file quant_bound_inference.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Quantifiers bound inference
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__QUANT_BOUND_INFERENCE_H
#define CVC4__THEORY__QUANTIFIERS__QUANT_BOUND_INFERENCE_H

#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {
  
class RepSetIterator;

namespace quantifiers {
  
class BoundedIntegers;

class QuantifiersBoundInference {
 public:
  QuantifiersBoundInference(unsigned cardMax);
  /** finish initialize */
  void finishInit(BoundedIntegers * b);
  /** may complete type
   *
   * Returns true if the type tn is closed enumerable, is interpreted as a
   * finite type, and has cardinality less than some reasonable value
   * (currently < 1000). This method caches the results of whether each type
   * may be completed.
   */
  bool mayComplete(TypeNode tn);
  /**
   * Static version of the above method where maximum cardinality is
   * configurable.
   */
  static bool mayComplete(TypeNode tn, unsigned cardMax);
  /** does variable v of quantified formula q have a finite bound? */
  bool isFiniteBound(Node q, Node v) const;
  /** get bound var type
   *
   * This returns the type of bound that was inferred for variable v of
   * quantified formula q.
   */
  BoundVarType getBoundVarType(Node q, Node v) const;
  /**
   * Get the indices of bound variables, in the order they should be processed
   * in a RepSetIterator.
   *
   * For details, see BoundedIntegers::getBoundVarIndices.
   */
  void getBoundVarIndices(Node q, std::vector<unsigned>& indices) const;
  /**
   * Get bound elements
   *
   * This gets the (finite) enumeration of the range of variable v of quantified
   * formula q and adds it into the vector elements in the context of the
   * iteration being performed by rsi. It returns true if it could successfully
   * determine this range.
   *
   * For details, see BoundedIntegers::getBoundElements.
   */
  bool getBoundElements(RepSetIterator* rsi,
                        bool initial,
                        Node q,
                        Node v,
                        std::vector<Node>& elements) const;
private:
  /** The maximum cardinality for which we complete */
  unsigned d_cardMax;
  /** may complete */
  std::unordered_map<TypeNode, bool, TypeNodeHashFunction> d_may_complete;
  /** The bounded integers module, which may help infer bounds */
  BoundedIntegers * d_bint;
};

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__QUANT_BOUND_INFERENCE_H */

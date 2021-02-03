/*********************                                                        */
/*! \file quant_relevance.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief quantifier relevance
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANT_RELEVANCE_H
#define CVC4__THEORY__QUANT_RELEVANCE_H

#include <map>

#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** QuantRelevance
 *
* This class is used for implementing SinE-style heuristics
* (e.g. see Hoder et al. CADE 2011)
* This is enabled by the option --relevant-triggers.
*/
class QuantRelevance : public QuantifiersUtil
{
 public:
  /** constructor
   * cr is whether relevance is computed by this class.
   * if this is false, then all calls to getRelevance
   * return -1.
   */
  QuantRelevance() {}
  ~QuantRelevance() {}
  /** reset */
  bool reset(Theory::Effort e) override { return true; }
  /** register quantifier */
  void registerQuantifier(Node q) override;
  /** identify */
  std::string identify() const override { return "QuantRelevance"; }
  /** get number of quantifiers for symbol s */
  size_t getNumQuantifiersForSymbol(Node s) const;

 private:
  /** map from quantifiers to symbols they contain */
  std::map<Node, std::vector<Node> > d_syms;
  /** map from symbols to quantifiers */
  std::map<Node, std::vector<Node> > d_syms_quants;
  /** relevance for quantifiers and symbols */
  std::map<Node, int> d_relevance;
  /** compute symbols */
  void computeSymbols(Node n, std::vector<Node>& syms);
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANT_RELEVANCE_H */

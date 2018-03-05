/*********************                                                        */
/*! \file quant_relevance.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief quantifier relevance
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANT_RELEVANCE_H
#define __CVC4__THEORY__QUANT_RELEVANCE_H

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
  QuantRelevance(bool cr) : d_computeRel(cr) {}
  ~QuantRelevance() {}
  /** reset */
  bool reset(Theory::Effort e) override { return true; }
  /** register quantifier */
  void registerQuantifier(Node q) override;
  /** identify */
  std::string identify() const override { return "QuantRelevance"; }
  /** set relevance of symbol s to r */
  void setRelevance(Node s, int r);
  /** get relevance of symbol s */
  int getRelevance(Node s)
  {
    return d_relevance.find(s) == d_relevance.end() ? -1 : d_relevance[s];
  }
  /** get number of quantifiers for symbol s */
  unsigned getNumQuantifiersForSymbol(Node s)
  {
    return d_syms_quants[s].size();
  }

 private:
  /** for computing relevance */
  bool d_computeRel;
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

#endif /* __CVC4__THEORY__QUANT_RELEVANCE_H */

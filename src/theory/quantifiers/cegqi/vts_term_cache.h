/*********************                                                        */
/*! \file vts_term_cache.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief term utilities class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CEGQI__VTS_TERM_CACHE_H
#define CVC4__THEORY__QUANTIFIERS__CEGQI__VTS_TERM_CACHE_H

#include <map>
#include "expr/node.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

/** Virtual term substitution term cache
 *
 * This class stores skolems corresponding to virtual terms (e.g. delta and
 * infinity) and has methods for performing virtual term substitution.
 */
class VtsTermCache
{
 public:
  VtsTermCache(QuantifiersEngine* qe);
  ~VtsTermCache() {}
  /** get vts delta */
  Node getVtsDelta(bool isFree = false, bool create = true);
  /** get vts infinity */
  Node getVtsInfinity(TypeNode tn, bool isFree = false, bool create = true);
  /** get all vts terms */
  void getVtsTerms(std::vector<Node>& t,
                   bool isFree = false,
                   bool create = true,
                   bool inc_delta = true);
  /** rewrite delta */
  Node rewriteVtsSymbols(Node n);
  /** simple check for contains term */
  bool containsVtsTerm(Node n, bool isFree = false);
  /** simple check for contains term */
  bool containsVtsTerm(std::vector<Node>& n, bool isFree = false);
  /** simple check for contains term */
  bool containsVtsInfinity(Node n, bool isFree = false);

 private:
  /** pointer to the quantifiers engine */
  QuantifiersEngine* d_qe;
  /** constants */
  Node d_zero;
  /** The virtual term substitution delta */
  Node d_vts_delta;
  /** The virtual term substitution "free delta" */
  Node d_vts_delta_free;
  /** The virtual term substitution infinities for int/real types */
  std::map<TypeNode, Node> d_vts_inf;
  /** The virtual term substitution "free infinities" for int/real types */
  std::map<TypeNode, Node> d_vts_inf_free;
  /** substitute vts free terms */
  Node substituteVtsFreeTerms(Node n);
}; /* class TermUtil */

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__CEGQI__VTS_TERM_CACHE_H */

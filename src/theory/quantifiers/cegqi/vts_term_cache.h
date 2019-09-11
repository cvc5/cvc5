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
namespace quantifiers {

/** Virtual term substitution term cache 
 *
 * This class stores skolems corresponding to virtual terms (e.g. delta and
 * infinity) and has methods for performing virtual term substitution.
 */ 
class VtsTermCache
{
public:
  VtsTermCache();
  ~VtsTermCache(){}
  /** get vts delta */
  Node getVtsDelta( std::vector< Node >& lemmas, bool isFree = false, bool create = true );
  /** get vts infinity */
  Node getVtsInfinity( TypeNode tn, bool isFree = false, bool create = true );
  /** get all vts terms */
  void getVtsTerms( std::vector< Node >& t, bool isFree = false, bool create = true, bool inc_delta = true );
  /** rewrite delta */
  Node rewriteVtsSymbols( Node n );
  /** simple check for contains term */
  bool containsVtsTerm( Node n, bool isFree = false );
  /** simple check for contains term */
  bool containsVtsTerm( std::vector< Node >& n, bool isFree = false );
  /** simple check for contains term */
  bool containsVtsInfinity( Node n, bool isFree = false );
private:
  /** constants */
  Node d_zero;
  Node d_vts_delta;
  std::map< TypeNode, Node > d_vts_inf;
  Node d_vts_delta_free;
  std::map< TypeNode, Node > d_vts_inf_free;
  /** get vts infinity index */
  Node getVtsInfinityIndex( int i, bool isFree = false, bool create = true  );
  /** substitute vts free terms */
  Node substituteVtsFreeTerms( Node n );
};/* class TermUtil */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__CEGQI__VTS_TERM_CACHE_H */

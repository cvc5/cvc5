/*********************                                                        */
/*! \file skolem_cache.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A cache of skolems for theory of strings.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__STRINGS__SKOLEM_CACHE_H
#define __CVC4__THEORY__STRINGS__SKOLEM_CACHE_H

#include <vector>
#include "util/hash.h"
#include "theory/theory.h"
#include "theory/rewriter.h"
#include "context/cdhashmap.h"

namespace CVC4 {
namespace theory {
namespace strings {

class SkolemCache {
 public:
  SkolemCache();
  /** identifiers for skolem types */
  enum SkolemId
  {
    SK_ID_C_SPT,
    SK_ID_VC_SPT,
    SK_ID_VC_BIN_SPT,
    SK_ID_V_SPT,
    SK_ID_C_SPT_REV,
    SK_ID_VC_SPT_REV,
    SK_ID_VC_BIN_SPT_REV,
    SK_ID_V_SPT_REV,
    SK_ID_CTN_PRE,
    SK_ID_CTN_POST,
    SK_ID_DC_SPT,
    SK_ID_DC_SPT_REM,
    SK_ID_DEQ_X,
    SK_ID_DEQ_Y,
    SK_ID_DEQ_Z,
    SK_ID_FIRST_CTN,
  };  
  /** make skolem cached 
   * 
   * TODO
   */
  Node mkSkolemCached(Node a, Node b, SkolemId id, const char* c);
  /** make skolem */
  Node mkSkolem( const char * c );
  /** Returns true if n is a skolem allocated by this class */
  bool isSkolem(Node n) const;
private:
  /** map from node pairs and identifiers to skolems */
  std::map<Node, std::map<Node, std::map<SkolemId, Node> > > d_skolem_cache;
  /** the set of all skolems we have generated */
  std::unordered_set<Node, NodeHashFunction> d_all_skolems;
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__PREPROCESS_H */

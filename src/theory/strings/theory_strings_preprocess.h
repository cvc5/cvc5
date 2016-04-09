/*********************                                                        */
/*! \file theory_strings_preprocess.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Strings Preprocess
 **
 ** Strings Preprocess.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__STRINGS__PREPROCESS_H
#define __CVC4__THEORY__STRINGS__PREPROCESS_H

#include <vector>
#include "util/hash.h"
#include "theory/theory.h"
#include "theory/rewriter.h"
#include "context/cdchunk_list.h"
#include "context/cdhashmap.h"

namespace CVC4 {
namespace theory {
namespace strings {

class StringsPreprocess {
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;
  NodeNodeMap d_cache;
  //Constants
  Node d_zero;
private:
  //int checkFixLenVar( Node t );
  Node simplify( Node t, std::vector< Node > &new_nodes );
public:
  StringsPreprocess( context::UserContext* u );

  Node decompose( Node t, std::vector< Node > &new_nodes );
  void simplify(std::vector< Node > &vec_node);
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__PREPROCESS_H */

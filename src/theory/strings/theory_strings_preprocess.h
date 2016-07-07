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
  //Constants
  Node d_zero;
  Node d_one;
  //mapping from kinds to UF
  std::map< Kind, Node > d_uf;
  //get UF for node
  Node getUfForNode( Node n );
public:
  StringsPreprocess( context::UserContext* u );
  ~StringsPreprocess();
  //simplify a node
  Node simplify( Node t, std::vector< Node > &new_nodes );
  //recursive simplify
  Node simplifyRec( Node t, std::vector< Node > &new_nodes, std::map< Node, Node >& visited );
  //simplify each node in vec_node
  void processAssertions(std::vector< Node > &vec_node);
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__PREPROCESS_H */

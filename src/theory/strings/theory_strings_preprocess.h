/*********************                                                        */
/*! \file theory_strings_preprocess.h
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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

namespace CVC4 {
namespace theory {
namespace strings {

class StringsPreprocess {
  // NOTE: this class is NOT context-dependent
  std::hash_map<TNode, Node, TNodeHashFunction> d_cache;
  //Constants
  Node d_zero;
private:
  bool checkStarPlus( Node t );
  int checkFixLenVar( Node t );
  void processRegExp( Node s, Node r, std::vector< Node > &ret );
  Node simplify( Node t, std::vector< Node > &new_nodes );
  Node decompose( Node t, std::vector< Node > &new_nodes );
public:
  void simplify(std::vector< Node > &vec_node, std::vector< Node > &new_nodes);
  void simplify(std::vector< Node > &vec_node);
  StringsPreprocess();
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__PREPROCESS_H */

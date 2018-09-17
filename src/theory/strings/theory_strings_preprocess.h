/*********************                                                        */
/*! \file theory_strings_preprocess.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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
#include "context/cdhashmap.h"
#include "theory/strings/skolem_cache.h"

namespace CVC4 {
namespace theory {
namespace strings {

/** Strings preprocessor
 * 
 * This class is responsible for extended function reductions. It is used as
 * a preprocessor when --no-strings-lazy-pp is enabled. By default, it is
 * used for reducing extended functions on-demand during the "extended function
 * reductions" inference schema of TheoryStrings.
 */
class StringsPreprocess {
public:
  StringsPreprocess( SkolemCache * sc, context::UserContext* u );
  ~StringsPreprocess();
  /** 
   * Returns a node that is equivalent to t, under assumptions in new_nodes.
   */
  Node simplify( Node t, std::vector< Node > &new_nodes );
  /** 
   * 
   */
  Node processAssertion( Node n, std::vector< Node > &new_nodes );
  /**
   * Replaces all formulas n in vec_node with an equivalent formula n' that
   * contains no instances of extended functions.
   */
  void processAssertions( std::vector< Node > &vec_node );
private:
  /** commonly used constants */
  Node d_zero;
  Node d_one;
  Node d_empty_str;
  /** pointer to the skolem cache used by this class */
  SkolemCache * d_sc;
  /** recursive simplify 
   * 
   * 
   */
  Node simplifyRec( Node t, std::vector< Node > &new_nodes, std::map< Node, Node >& visited );
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__PREPROCESS_H */

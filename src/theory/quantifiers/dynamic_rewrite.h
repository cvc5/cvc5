/*********************                                                        */
/*! \file dynamic_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief dynamic_rewriter
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__DYNAMIC_REWRITER_H
#define __CVC4__THEORY__QUANTIFIERS__DYNAMIC_REWRITER_H

#include <map>

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** DynamicRewriter
 * 
 */
class DynamicRewriter 
{
public:
  DynamicRewriter( QuantifiersEngine * qe );
  ~DynamicRewriter(){}
  
  bool addRewrite( Node a, Node b );
  Node rewrite( Node a );
private:
  std::map< Node, Node > d_union_find;
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__DYNAMIC_REWRITER_H */

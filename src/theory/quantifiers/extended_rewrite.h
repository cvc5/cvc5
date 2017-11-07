/*********************                                                        */
/*! \file extended_rewrite.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief extended rewriting class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H
#define __CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H

#include <vector>
#include <unordered_map>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

//TODO
class ExtendedRewriter
{
public:
  ExtendedRewriter();
  ~ExtendedRewriter(){}
  Node extendedRewrite( Node n );
private:
  Node d_true;
  Node d_false;
  std::map< Node, Node > d_ext_rewrite_cache;
  Node extendedRewritePullIte( Node n );
};
  
} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H */

/*********************                                                        */
/*! \file model_postprocessor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief 
 **
 ** 
 **/

#include "cvc4_private.h"

#ifndef __CVC4__MODEL_POSTPROCESSOR_H
#define __CVC4__MODEL_POSTPROCESSOR_H

#include "expr/node.h"

namespace CVC4 {
namespace smt {

class ModelPostprocessor {
  std::hash_map<TNode, Node, TNodeHashFunction> d_nodes;

public:
  typedef Node return_type;

  Node rewriteAs(TNode n, TypeNode asType);

  bool alreadyVisited(TNode current, TNode parent) {
    return d_nodes.find(current) != d_nodes.end();
  }

  void visit(TNode current, TNode parent);

  void start(TNode n) { }

  Node done(TNode n) {
    Assert(alreadyVisited(n, TNode::null()));
    TNode retval = d_nodes[n];
    return retval.isNull() ? n : retval;
  }
};/* class ModelPostprocessor */

}/* CVC4::smt namespace */
}/* CVC4 namespace */

#endif /* __CVC4__MODEL_POSTPROCESSOR_H */

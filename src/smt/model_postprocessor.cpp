/*********************                                                        */
/*! \file model_postprocessor.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief 
 **
 ** 
 **/

#include "smt/model_postprocessor.h"

using namespace CVC4;
using namespace CVC4::smt;

void ModelPostprocessor::visit(TNode current, TNode parent) {
  Debug("tuprec") << "visiting " << current << std::endl;
  Assert(!alreadyVisited(current, TNode::null()));
  if(current.getType().hasAttribute(expr::DatatypeTupleAttr())) {
    Assert(current.getKind() == kind::APPLY_CONSTRUCTOR);
    NodeBuilder<> b(kind::TUPLE);
    for(TNode::iterator i = current.begin(); i != current.end(); ++i) {
      Assert(alreadyVisited(*i, TNode::null()));
      TNode n = d_nodes[*i];
      b << (n.isNull() ? *i : n);
    }
    d_nodes[current] = b;
    Debug("tuprec") << "returning " << d_nodes[current] << std::endl;
  } else if(current.getType().hasAttribute(expr::DatatypeRecordAttr())) {
    Assert(current.getKind() == kind::APPLY_CONSTRUCTOR);
    NodeBuilder<> b(kind::RECORD);
    b << current.getType().getAttribute(expr::DatatypeRecordAttr());
    for(TNode::iterator i = current.begin(); i != current.end(); ++i) {
      Assert(alreadyVisited(*i, TNode::null()));
      TNode n = d_nodes[*i];
      b << (n.isNull() ? *i : n);
    }
    d_nodes[current] = b;
    Debug("tuprec") << "returning " << d_nodes[current] << std::endl;
  } else {
    Debug("tuprec") << "returning self" << std::endl;
    // rewrite to self
    d_nodes[current] = Node::null();
  }
}/* ModelPostprocessor::visit() */


/*********************                                                        */
/*! \file node.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Reference-counted encapsulation of a pointer to node information.
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/

#include "expr/node.h"
#include "util/output.h"

#include <iostream>

using namespace std;

namespace CVC4 {

TypeCheckingExceptionPrivate::TypeCheckingExceptionPrivate(TNode node,
                                                           std::string message) :
  Exception(message),
  d_node(new Node(node)) {
}

TypeCheckingExceptionPrivate::~TypeCheckingExceptionPrivate() throw () {
  delete d_node;
}

void TypeCheckingExceptionPrivate::toStream(std::ostream& os) const {
  os << "Error type-checking " << d_node << ": " << d_msg << std::endl << *d_node;
}

Node TypeCheckingExceptionPrivate::getNode() const {
  return *d_node;
}

}/* CVC4 namespace */

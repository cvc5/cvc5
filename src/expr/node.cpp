/*********************                                                        */
/*! \file node.cpp
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
#include <cstring>

using namespace std;

namespace CVC4 {

TypeCheckingExceptionPrivate::TypeCheckingExceptionPrivate(TNode node,
                                                           std::string message) throw() :
  Exception(message),
  d_node(new Node(node)) {
#ifdef CVC4_DEBUG
  // yes, this leaks memory, but only in debug modes with exceptions occurring
  s_debugLastException = strdup(toString().c_str());
#endif /* CVC4_DEBUG */
}

TypeCheckingExceptionPrivate::~TypeCheckingExceptionPrivate() throw () {
  delete d_node;
}

void TypeCheckingExceptionPrivate::toStream(std::ostream& os) const throw() {
  os << "Error during type checking: " << d_msg << std::endl << *d_node << endl << "The ill-typed expression: " << *d_node;
}

NodeTemplate<true> TypeCheckingExceptionPrivate::getNode() const throw() {
  return *d_node;
}

UnknownTypeException::UnknownTypeException(TNode n) throw() :
  TypeCheckingExceptionPrivate(n, "this expression contains an element of unknown type (such as an abstract value);"
                               " its type cannot be computed until it is substituted away") {
}

}/* CVC4 namespace */

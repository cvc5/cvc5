/*********************                                                        */
/*! \file node.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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
namespace expr {

const int NodeSetDepth::s_iosIndex = std::ios_base::xalloc();

}/* CVC4::expr namespace */


TypeCheckingExceptionPrivate::TypeCheckingExceptionPrivate(TNode node, std::string message)
: Exception(message), d_node(new Node(node))
{
}

TypeCheckingExceptionPrivate::~TypeCheckingExceptionPrivate() throw () {
  delete d_node;
}

std::string TypeCheckingExceptionPrivate::toString() const {
  std::stringstream ss;
  ss << "Error type-checking " << d_node << ": " << d_msg;
  return ss.str();
}

Node TypeCheckingExceptionPrivate::getNode() const {
  return *d_node;
}

}/* CVC4 namespace */

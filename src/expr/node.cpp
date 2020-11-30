/*********************                                                        */
/*! \file node.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Reference-counted encapsulation of a pointer to node information.
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/
#include "expr/node.h"

#include <iostream>
#include <cstring>

#include "base/exception.h"
#include "base/output.h"
#include "expr/attribute.h"

using namespace std;

namespace CVC4 {

TypeCheckingExceptionPrivate::TypeCheckingExceptionPrivate(TNode node,
                                                           std::string message)
    : Exception(message), d_node(new Node(node))
{
#ifdef CVC4_DEBUG
  std::stringstream ss;
  LastExceptionBuffer* current = LastExceptionBuffer::getCurrent();
  if(current != NULL){
    // Since this node is malformed, we cannot use toString().
    // Instead, we print the kind and the children.
    ss << "node kind: " << node.getKind() << ". children: ";
    int i = 0;
    for (const TNode& child : node)
    {
      ss << "child[" << i << "]: " << child << ". ";
      i++;
    }
    string ssstring = ss.str();
    current->setContents(ssstring.c_str());
  }
#endif /* CVC4_DEBUG */
}

TypeCheckingExceptionPrivate::~TypeCheckingExceptionPrivate() { delete d_node; }

void TypeCheckingExceptionPrivate::toStream(std::ostream& os) const
{
  os << "Error during type checking: " << d_msg << std::endl << *d_node << endl << "The ill-typed expression: " << *d_node;
}

NodeTemplate<true> TypeCheckingExceptionPrivate::getNode() const
{
  return *d_node;
}

UnknownTypeException::UnknownTypeException(TNode n)
    : TypeCheckingExceptionPrivate(
          n,
          "this expression contains an element of unknown type (such as an "
          "abstract value);"
          " its type cannot be computed until it is substituted away")
{
}

/** Is this node constant? (and has that been computed yet?) */
struct IsConstTag { };
struct IsConstComputedTag { };
typedef expr::Attribute<IsConstTag, bool> IsConstAttr;
typedef expr::Attribute<IsConstComputedTag, bool> IsConstComputedAttr;

template <bool ref_count>
bool NodeTemplate<ref_count>::isConst() const {
  assertTNodeNotExpired();
  Debug("isConst") << "Node::isConst() for: " << *this << std::endl;
  if(isNull()) {
    return false;
  }
  switch(getMetaKind()) {
  case kind::metakind::CONSTANT:
    Debug("isConst") << "Node::isConst() returning true, it's a CONSTANT" << std::endl;
    return true;
  case kind::metakind::VARIABLE:
    Debug("isConst") << "Node::isConst() returning false, it's a VARIABLE" << std::endl;
    return false;
  default:
    if(getAttribute(IsConstComputedAttr())) {
      bool bval = getAttribute(IsConstAttr());
      Debug("isConst") << "Node::isConst() returning cached value " << (bval ? "true" : "false") << " for: " << *this << std::endl;
      return bval;
    } else {
      bool bval = expr::TypeChecker::computeIsConst(NodeManager::currentNM(), *this);
      Debug("isConst") << "Node::isConst() computed value " << (bval ? "true" : "false") << " for: " << *this << std::endl;
      const_cast< NodeTemplate<ref_count>* >(this)->setAttribute(IsConstAttr(), bval);
      const_cast< NodeTemplate<ref_count>* >(this)->setAttribute(IsConstComputedAttr(), true);
      return bval;
    }
  }
}

template bool NodeTemplate<true>::isConst() const;
template bool NodeTemplate<false>::isConst() const;

}/* CVC4 namespace */

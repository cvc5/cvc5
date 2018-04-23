/*********************                                                        */
/*! \file node.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
struct HasBoundVarTag { };
struct HasBoundVarComputedTag { };
typedef expr::Attribute<IsConstTag, bool> IsConstAttr;
typedef expr::Attribute<IsConstComputedTag, bool> IsConstComputedAttr;
/** Attribute true for expressions with bound variables in them */
typedef expr::Attribute<HasBoundVarTag, bool> HasBoundVarAttr;
typedef expr::Attribute<HasBoundVarComputedTag, bool> HasBoundVarComputedAttr;

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
    if(expr::TypeChecker::neverIsConst(NodeManager::currentNM(), *this)){
      Debug("isConst") << "Node::isConst() returning false, the kind is never const" << std::endl;
      return false;
    }
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

template <bool ref_count>
bool NodeTemplate<ref_count>::hasBoundVar() {
  assertTNodeNotExpired();
  if(! getAttribute(HasBoundVarComputedAttr())) {
    bool hasBv = false;
    if(getKind() == kind::BOUND_VARIABLE) {
      hasBv = true;
    } else {
      for(iterator i = begin(); i != end() && !hasBv; ++i) {
        hasBv = (*i).hasBoundVar();
      }
    }
    if (!hasBv && hasOperator()) {
      hasBv = getOperator().hasBoundVar();
    }
    setAttribute(HasBoundVarAttr(), hasBv);
    setAttribute(HasBoundVarComputedAttr(), true);
    Debug("bva") << *this << " has bva : " << getAttribute(HasBoundVarAttr()) << std::endl;
    return hasBv;
  }
  return getAttribute(HasBoundVarAttr());
}

template <bool ref_count>
bool NodeTemplate<ref_count>::hasFreeVar()
{
  assertTNodeNotExpired();
  std::unordered_set<TNode, TNodeHashFunction> bound_var;
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(*this);
  do
  {
    cur = visit.back();
    visit.pop_back();
    // can skip if it doesn't have a bound variable
    if (!cur.hasBoundVar())
    {
      continue;
    }
    Kind k = cur.getKind();
    bool isQuant = k == kind::FORALL || k == kind::EXISTS || k == kind::LAMBDA
                   || k == kind::CHOICE;
    std::unordered_map<TNode, bool, TNodeHashFunction>::iterator itv =
        visited.find(cur);
    if (itv == visited.end())
    {
      if (k == kind::BOUND_VARIABLE)
      {
        if (bound_var.find(cur) == bound_var.end())
        {
          return true;
        }
      }
      else if (isQuant)
      {
        for (const TNode& cn : cur[0])
        {
          // should not shadow
          Assert(bound_var.find(cn) == bound_var.end());
          bound_var.insert(cn);
        }
        visit.push_back(cur);
      }
      // must visit quantifiers again to clean up below
      visited[cur] = !isQuant;
      for (const TNode& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else if (!itv->second)
    {
      Assert(isQuant);
      for (const TNode& cn : cur[0])
      {
        bound_var.erase(cn);
      }
      visited[cur] = true;
    }
  } while (!visit.empty());
  return false;
}

template bool NodeTemplate<true>::isConst() const;
template bool NodeTemplate<false>::isConst() const;
template bool NodeTemplate<true>::hasBoundVar();
template bool NodeTemplate<false>::hasBoundVar();
template bool NodeTemplate<true>::hasFreeVar();
template bool NodeTemplate<false>::hasFreeVar();

}/* CVC4 namespace */

/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A node value.
 *
 * The actual node implementation.
 * Instances of this class are generally referenced through cvc5::internal::Node
 * rather than by pointer. Note that cvc5::internal::Node maintains the
 * reference count on NodeValue instances.
 */
#include "expr/node_value.h"

#include <sstream>

#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node.h"
#include "options/base_options.h"
#include "options/io_utils.h"
#include "options/language.h"
#include "options/options.h"
#include "printer/printer.h"

using namespace std;

namespace cvc5::internal {
namespace expr {

string NodeValue::toString() const {
  stringstream ss;
  toStream(ss);
  return ss.str();
}

void NodeValue::toStream(std::ostream& out) const
{
  // Ensure that this node value is live for the length of this call.
  // It really breaks things badly if we don't have a nonzero ref
  // count, even just for printing.
  RefCountGuard guard(this);

  Printer::getPrinter(out)->toStream(out, TNode(this));
}

void NodeValue::printAst(std::ostream& out, int ind) const {
  RefCountGuard guard(this);

  indent(out, ind);
  out << '(';
  out << getKind();
  if (getMetaKind() == kind::metakind::VARIABLE || getMetaKind() == kind::metakind::NULLARY_OPERATOR ) {
    out << ' ' << getId();
  } else if (getMetaKind() == kind::metakind::CONSTANT) {
    out << ' ';
    kind::metakind::nodeValueConstantToStream(out, this);
  } else {
    if (nv_begin() != nv_end()) {
      for (const_nv_iterator child = nv_begin(); child != nv_end(); ++child) {
        out << std::endl;
        (*child)->printAst(out, ind + 1);
      }
      out << std::endl;
      indent(out, ind);
    }
  }
  out << ')';
}

NodeValue::iterator<NodeTemplate<true> > operator+(
    NodeValue::iterator<NodeTemplate<true> >::difference_type p,
    NodeValue::iterator<NodeTemplate<true> > i)
{
  return i + p;
}

NodeValue::iterator<NodeTemplate<false> > operator+(
    NodeValue::iterator<NodeTemplate<false> >::difference_type p,
    NodeValue::iterator<NodeTemplate<false> > i)
{
  return i + p;
}

std::ostream& operator<<(std::ostream& out, const NodeValue& nv)
{
  nv.toStream(out);
  return out;
}

void NodeValue::markRefCountMaxedOut()
{
  Assert(NodeManager::currentNM() != nullptr)
      << "No current NodeManager on incrementing of NodeValue: "
         "maybe a public cvc5 interface function is missing a "
         "NodeManagerScope ?";
  NodeManager::currentNM()->markRefCountMaxedOut(this);
}

void NodeValue::markForDeletion()
{
  Assert(NodeManager::currentNM() != nullptr)
      << "No current NodeManager on destruction of NodeValue: "
         "maybe a public cvc5 interface function is missing a "
         "NodeManagerScope ?";
  NodeManager::currentNM()->markForDeletion(this);
}

}  // namespace expr
}  // namespace cvc5::internal

/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Template for the metakind header.
 */

#include "cvc5_private.h"

#ifndef CVC5__KIND__METAKIND_H
#define CVC5__KIND__METAKIND_H

#include <iosfwd>

#include "base/check.h"
#include "expr/kind.h"

namespace cvc5 {

namespace expr {
  class NodeValue;
  }  // namespace expr

namespace kind {
namespace metakind {

/**
 * Static, compile-time information about types T representing cvc5
 * constants:
 *
 *   typename ConstantMap<T>::OwningTheory
 *
 *     The theory in charge of constructing T when constructing Nodes
 *     with NodeManager::mkConst(T).
 *
 *   typename ConstantMap<T>::kind
 *
 *     The kind to use when constructing Nodes with
 *     NodeManager::mkConst(T).
 */
template <class T>
struct ConstantMap;

struct NodeValueCompare {
  template <bool pool>
  static bool compare(const ::cvc5::expr::NodeValue* nv1,
                      const ::cvc5::expr::NodeValue* nv2);
  static size_t constHash(const ::cvc5::expr::NodeValue* nv);
};/* struct NodeValueCompare */

/**
 * "metakinds" represent the "kinds" of kinds at the meta-level.
 * "metakind" is an ugly name but it's not used by client code, just
 * by the expr package, and the intent here is to keep it from
 * polluting the kind namespace.  For more documentation on what these
 * mean, see src/theory/builtin/kinds.
 */
enum MetaKind_t {
  INVALID = -1, /**< special node non-kinds like NULL_EXPR or LAST_KIND */
  VARIABLE, /**< special node kinds: no operator */
  OPERATOR, /**< operators that get "inlined" */
  PARAMETERIZED, /**< parameterized ops (like APPLYs) that carry extra data */
  CONSTANT, /**< constants */
  NULLARY_OPERATOR /**< nullary operator */
};/* enum MetaKind_t */

/**
 * Write the string representation of a payload of a constant node to an output
 * stream.
 *
 * @param out the stream to write to
 * @param nv the node value representing a constant node
 */
void nodeValueConstantToStream(std::ostream& out,
                               const ::cvc5::expr::NodeValue* nv);

/**
 * Cleanup to be performed when a NodeValue zombie is collected, and
 * it has CONSTANT metakind.  This calls the destructor for the underlying
 * C++ type representing the constant value.  See
 * NodeManager::reclaimZombies() for more information.
 *
 * This doesn't support "non-inlined" NodeValues, which shouldn't need this
 * kind of cleanup.
 */
void deleteNodeValueConstant(::cvc5::expr::NodeValue* nv);

/** Return the minimum arity of the given kind. */
uint32_t getMinArityForKind(::cvc5::Kind k);
/** Return the maximum arity of the given kind. */
uint32_t getMaxArityForKind(::cvc5::Kind k);

}  // namespace metakind

// import MetaKind into the "cvc5::kind" namespace but keep the
// individual MetaKind constants under kind::metakind::
typedef ::cvc5::kind::metakind::MetaKind_t MetaKind;

/**
 * Get the metakind for a particular kind.
 */
MetaKind metaKindOf(Kind k);

/**
 * Map a kind of the operator to the kind of the enclosing expression. For
 * example, since the kind of functions is just VARIABLE, it should map
 * VARIABLE to APPLY_UF.
 */
Kind operatorToKind(::cvc5::expr::NodeValue* nv);

}  // namespace kind

namespace expr {

// Comparison predicate
struct NodeValuePoolEq {
  bool operator()(const NodeValue* nv1, const NodeValue* nv2) const
  {
    return ::cvc5::kind::metakind::NodeValueCompare::compare<true>(nv1, nv2);
  }
};

}  // namespace expr
}  // namespace cvc5

#endif /* CVC5__KIND__METAKIND_H */

#ifdef CVC5__NODE_MANAGER_NEEDS_CONSTANT_MAP

namespace cvc5 {

// clang-format off
${metakind_fwd_decls}
// clang-format on

namespace kind {
namespace metakind {

// clang-format off
${metakind_constantMaps_decls}
// clang-format on

}  // namespace metakind
}  // namespace kind
}  // namespace cvc5

#endif /* CVC5__NODE_MANAGER_NEEDS_CONSTANT_MAP */

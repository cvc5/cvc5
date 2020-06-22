/*********************                                                        */
/*! \file metakind_template.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Template for the metakind header.
 **
 ** Template for the metakind header.
 **/

#include "cvc4_private.h"

#ifndef CVC4__KIND__METAKIND_H
#define CVC4__KIND__METAKIND_H

#include <iosfwd>

#include "base/check.h"
#include "expr/kind.h"

namespace CVC4 {

namespace expr {
  class NodeValue;
}/* CVC4::expr namespace */

namespace kind {
namespace metakind {

/**
 * Static, compile-time information about types T representing CVC4
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

/**
 * Static, compile-time information about kinds k and what type their
 * corresponding CVC4 constants are:
 *
 *   typename ConstantMapReverse<k>::T
 *
 *     Constant type for kind k.
 */
template <Kind k>
struct ConstantMapReverse;

/**
 * Static, compile-time mapping from CONSTANT kinds to comparison
 * functors on NodeValue*.  The single element of this structure is:
 *
 *   static bool NodeValueCompare<K, pool>::compare(NodeValue* x, NodeValue* y)
 *
 *     Compares x and y, given that they are both K-kinded (and the
 *     meta-kind of K is CONSTANT).  If pool == true, one of x and y
 *     (but not both) may be a "non-inlined" NodeValue.  If pool ==
 *     false, neither x nor y may be a "non-inlined" NodeValue.
 */
template <Kind k, bool pool>
struct NodeValueConstCompare {
  inline static bool compare(const ::CVC4::expr::NodeValue* x,
                             const ::CVC4::expr::NodeValue* y);
  inline static size_t constHash(const ::CVC4::expr::NodeValue* nv);
};/* NodeValueConstCompare<k, pool> */

struct NodeValueCompare {
  template <bool pool>
  static bool compare(const ::CVC4::expr::NodeValue* nv1,
                      const ::CVC4::expr::NodeValue* nv2);
  static size_t constHash(const ::CVC4::expr::NodeValue* nv);
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

}/* CVC4::kind::metakind namespace */

// import MetaKind into the "CVC4::kind" namespace but keep the
// individual MetaKind constants under kind::metakind::
typedef ::CVC4::kind::metakind::MetaKind_t MetaKind;

/**
 * Get the metakind for a particular kind.
 */
MetaKind metaKindOf(Kind k);
}/* CVC4::kind namespace */

namespace expr {

// Comparison predicate
struct NodeValuePoolEq {
  inline bool operator()(const NodeValue* nv1, const NodeValue* nv2) const {
    return ::CVC4::kind::metakind::NodeValueCompare::compare<true>(nv1, nv2);
  }
};

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#include "expr/node_value.h"

#endif /* CVC4__KIND__METAKIND_H */

${metakind_includes}

#ifdef CVC4__NODE_MANAGER_NEEDS_CONSTANT_MAP

namespace CVC4 {

namespace expr {
${metakind_getConst_decls}
}/* CVC4::expr namespace */

namespace kind {
namespace metakind {

template <Kind k, bool pool>
inline bool NodeValueConstCompare<k, pool>::compare(const ::CVC4::expr::NodeValue* x,
                                                    const ::CVC4::expr::NodeValue* y) {
  typedef typename ConstantMapReverse<k>::T T;
  if(pool) {
    if(x->d_nchildren == 1) {
      Assert(y->d_nchildren == 0);
      return compare(y, x);
    } else if(y->d_nchildren == 1) {
      Assert(x->d_nchildren == 0);
      return x->getConst<T>() == *reinterpret_cast<T*>(y->d_children[0]);
    }
  }

  Assert(x->d_nchildren == 0);
  Assert(y->d_nchildren == 0);
  return x->getConst<T>() == y->getConst<T>();
}

template <Kind k, bool pool>
inline size_t NodeValueConstCompare<k, pool>::constHash(const ::CVC4::expr::NodeValue* nv) {
  typedef typename ConstantMapReverse<k>::T T;
  return nv->getConst<T>().hash();
}

${metakind_constantMaps_decls}

struct NodeValueConstPrinter {
  static void toStream(std::ostream& out,
                              const ::CVC4::expr::NodeValue* nv);
  static void toStream(std::ostream& out, TNode n);
};

/**
 * Cleanup to be performed when a NodeValue zombie is collected, and
 * it has CONSTANT metakind.  This calls the destructor for the underlying
 * C++ type representing the constant value.  See
 * NodeManager::reclaimZombies() for more information.
 *
 * This doesn't support "non-inlined" NodeValues, which shouldn't need this
 * kind of cleanup.
 */
void deleteNodeValueConstant(::CVC4::expr::NodeValue* nv);

unsigned getLowerBoundForKind(::CVC4::Kind k);
unsigned getUpperBoundForKind(::CVC4::Kind k);

}/* CVC4::kind::metakind namespace */

/**
 * Map a kind of the operator to the kind of the enclosing expression. For
 * example, since the kind of functions is just VARIABLE, it should map
 * VARIABLE to APPLY_UF.
 */
Kind operatorToKind(::CVC4::expr::NodeValue* nv);

}/* CVC4::kind namespace */

#line 205 "${template}"

}/* CVC4 namespace */

#endif /* CVC4__NODE_MANAGER_NEEDS_CONSTANT_MAP */

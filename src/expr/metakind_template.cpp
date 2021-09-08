/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "expr/metakind.h"

#include <iostream>

// clang-format off
${metakind_includes}
// clang-format off

namespace cvc5 {
namespace kind {

/**
 * Get the metakind for a particular kind.
 */
MetaKind metaKindOf(Kind k)
{
  static const MetaKind metaKinds[] = {
      metakind::INVALID, /* UNDEFINED_KIND */
      metakind::INVALID, /* NULL_EXPR */
      // clang-format off
${metakind_kinds}  // clang-format on
      metakind::INVALID  /* LAST_KIND */
  };                     /* metaKinds[] */

  Assert(k >= kind::NULL_EXPR && k < kind::LAST_KIND);

  // We've asserted that k >= NULL_EXPR (which is 0), but we still
  // handle the UNDEFINED_KIND (-1) case.  If we don't, the compiler
  // emits warnings for non-assertion builds, since the check isn't done.
  return metaKinds[k + 1];
} /* metaKindOf(k) */

}  // namespace kind

namespace expr {

// clang-format off
${metakind_constantMaps}
// clang-format on

}  // namespace expr

namespace kind {
namespace metakind {

size_t NodeValueCompare::constHash(const ::cvc5::expr::NodeValue* nv)
{
  Assert(nv->getMetaKind() == kind::metakind::CONSTANT);

  switch (nv->d_kind)
  {
// clang-format off
    ${metakind_constHashes}
// clang-format on
default: Unhandled() << ::cvc5::expr::NodeValue::dKindToKind(nv->d_kind);
  }
}

template <bool pool>
bool NodeValueCompare::compare(const ::cvc5::expr::NodeValue* nv1,
                               const ::cvc5::expr::NodeValue* nv2)
{
  if(nv1->d_kind != nv2->d_kind) {
    return false;
  }

  if (nv1->getMetaKind() == kind::metakind::CONSTANT)
  {
    switch (nv1->d_kind)
    {
// clang-format off
${metakind_compares}
// clang-format on
default: Unhandled() << ::cvc5::expr::NodeValue::dKindToKind(nv1->d_kind);
    }
  }

  if(nv1->d_nchildren != nv2->d_nchildren) {
    return false;
  }

  ::cvc5::expr::NodeValue::const_nv_iterator i = nv1->nv_begin();
  ::cvc5::expr::NodeValue::const_nv_iterator j = nv2->nv_begin();
  ::cvc5::expr::NodeValue::const_nv_iterator i_end = nv1->nv_end();

  while(i != i_end) {
    if((*i) != (*j)) {
      return false;
    }
    ++i;
    ++j;
  }

  return true;
}

template bool NodeValueCompare::compare<true>(
    const ::cvc5::expr::NodeValue* nv1, const ::cvc5::expr::NodeValue* nv2);
template bool NodeValueCompare::compare<false>(
    const ::cvc5::expr::NodeValue* nv1, const ::cvc5::expr::NodeValue* nv2);

void NodeValueConstPrinter::toStream(std::ostream& out,
                                     const ::cvc5::expr::NodeValue* nv)
{
  Assert(nv->getMetaKind() == kind::metakind::CONSTANT);

  switch (nv->d_kind)
  {
// clang-format off
${metakind_constPrinters}
// clang-format on
default: Unhandled() << ::cvc5::expr::NodeValue::dKindToKind(nv->d_kind);
  }
}

void NodeValueConstPrinter::toStream(std::ostream& out, TNode n) {
  toStream(out, n.d_nv);
}

// The reinterpret_cast of d_children to various constant payload types
// in deleteNodeValueConstant(), below, can flag a "strict aliasing"
// warning; it should actually be okay, because we never access the
// embedded constant as a NodeValue* child, and never access an embedded
// NodeValue* child as a constant.
#pragma GCC diagnostic ignored "-Wstrict-aliasing"

/**
 * Cleanup to be performed when a NodeValue zombie is collected, and
 * it has CONSTANT metakind.  This calls the destructor for the underlying
 * C++ type representing the constant value.  See
 * NodeManager::reclaimZombies() for more information.
 *
 * This doesn't support "non-inlined" NodeValues, which shouldn't need this
 * kind of cleanup.
 */
void deleteNodeValueConstant(::cvc5::expr::NodeValue* nv)
{
  Assert(nv->getMetaKind() == kind::metakind::CONSTANT);

  switch (nv->d_kind)
  {
// clang-format off
${metakind_constDeleters}
// clang-format on
default: Unhandled() << ::cvc5::expr::NodeValue::dKindToKind(nv->d_kind);
  }
}

// re-enable the strict-aliasing warning
# pragma GCC diagnostic warning "-Wstrict-aliasing"

uint32_t getMinArityForKind(::cvc5::Kind k)
{
  static const unsigned lbs[] = {
    0, /* NULL_EXPR */
// clang-format off
${metakind_lbchildren}
// clang-format on

    0 /* LAST_KIND */
  };

  return lbs[k];
}

uint32_t getMaxArityForKind(::cvc5::Kind k)
{
  static const unsigned ubs[] = {
    0, /* NULL_EXPR */
// clang-format off
${metakind_ubchildren}
// clang-format on

    0, /* LAST_KIND */
  };

  return ubs[k];
}
}  // namespace metakind

/**
 * Map a kind of the operator to the kind of the enclosing expression. For
 * example, since the kind of functions is just VARIABLE, it should map
 * VARIABLE to APPLY_UF.
 */
Kind operatorToKind(::cvc5::expr::NodeValue* nv)
{
  if(nv->getKind() == kind::BUILTIN) {
    return nv->getConst<Kind>();
  } else if(nv->getKind() == kind::LAMBDA) {
    return kind::APPLY_UF;
  }

  switch (Kind k CVC5_UNUSED = nv->getKind())
  {
// clang-format off
    ${metakind_operatorKinds}
// clang-format on

    default: return kind::UNDEFINED_KIND; /* LAST_KIND */
  };
}

}  // namespace kind
}  // namespace cvc5

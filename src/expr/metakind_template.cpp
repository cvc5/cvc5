#include "expr/metakind.h"

#include <iostream>

namespace CVC4 {
namespace kind {

/**
 * Get the metakind for a particular kind.
 */
MetaKind metaKindOf(Kind k) {
  static const MetaKind metaKinds[] = {
    metakind::INVALID, /* UNDEFINED_KIND */
    metakind::INVALID, /* NULL_EXPR */
${metakind_kinds}
    metakind::INVALID /* LAST_KIND */
  };/* metaKinds[] */

  Assert(k >= kind::NULL_EXPR && k < kind::LAST_KIND);

  // We've asserted that k >= NULL_EXPR (which is 0), but we still
  // handle the UNDEFINED_KIND (-1) case.  If we don't, the compiler
  // emits warnings for non-assertion builds, since the check isn't done.
  return metaKinds[k + 1];
}/* metaKindOf(k) */

}/* CVC4::kind namespace */

namespace expr {

${metakind_constantMaps}

}/* CVC4::expr namespace */

namespace kind {
namespace metakind {

size_t NodeValueCompare::constHash(const ::CVC4::expr::NodeValue* nv) {
  Assert(nv->getMetaKind() == kind::metakind::CONSTANT);

  switch(nv->d_kind) {
${metakind_constHashes}
  default:
    Unhandled(::CVC4::expr::NodeValue::dKindToKind(nv->d_kind));
  }
}

template <bool pool>
bool NodeValueCompare::compare(const ::CVC4::expr::NodeValue* nv1,
                               const ::CVC4::expr::NodeValue* nv2) {
  if(nv1->d_kind != nv2->d_kind) {
    return false;
  }

  if(nv1->getMetaKind() == kind::metakind::CONSTANT) {
    switch(nv1->d_kind) {
${metakind_compares}
    default:
      Unhandled(::CVC4::expr::NodeValue::dKindToKind(nv1->d_kind));
    }
  }

  if(nv1->d_nchildren != nv2->d_nchildren) {
    return false;
  }

  ::CVC4::expr::NodeValue::const_nv_iterator i = nv1->nv_begin();
  ::CVC4::expr::NodeValue::const_nv_iterator j = nv2->nv_begin();
  ::CVC4::expr::NodeValue::const_nv_iterator i_end = nv1->nv_end();

  while(i != i_end) {
    if((*i) != (*j)) {
      return false;
    }
    ++i;
    ++j;
  }

  return true;
}

template bool NodeValueCompare::compare<true>(const ::CVC4::expr::NodeValue* nv1,
                                              const ::CVC4::expr::NodeValue* nv2);
template bool NodeValueCompare::compare<false>(const ::CVC4::expr::NodeValue* nv1,
                                               const ::CVC4::expr::NodeValue* nv2);

void NodeValueConstPrinter::toStream(std::ostream& out,
                                            const ::CVC4::expr::NodeValue* nv) {
  Assert(nv->getMetaKind() == kind::metakind::CONSTANT);

  switch(nv->d_kind) {
${metakind_constPrinters}
  default:
    Unhandled(::CVC4::expr::NodeValue::dKindToKind(nv->d_kind));
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
void deleteNodeValueConstant(::CVC4::expr::NodeValue* nv) {
  Assert(nv->getMetaKind() == kind::metakind::CONSTANT);

  switch(nv->d_kind) {
${metakind_constDeleters}
  default:
    Unhandled(::CVC4::expr::NodeValue::dKindToKind(nv->d_kind));
  }
}

// re-enable the strict-aliasing warning
# pragma GCC diagnostic warning "-Wstrict-aliasing"

unsigned getLowerBoundForKind(::CVC4::Kind k) {
  static const unsigned lbs[] = {
    0, /* NULL_EXPR */
${metakind_lbchildren}

    0 /* LAST_KIND */
  };

  return lbs[k];
}

unsigned getUpperBoundForKind(::CVC4::Kind k) {
  static const unsigned ubs[] = {
    0, /* NULL_EXPR */
${metakind_ubchildren}

    0, /* LAST_KIND */
  };

  return ubs[k];
}

}/* CVC4::metakind namespace */

/**
 * Map a kind of the operator to the kind of the enclosing expression. For
 * example, since the kind of functions is just VARIABLE, it should map
 * VARIABLE to APPLY_UF.
 */
Kind operatorToKind(::CVC4::expr::NodeValue* nv) {
  if(nv->getKind() == kind::BUILTIN) {
    return nv->getConst<Kind>();
  } else if(nv->getKind() == kind::LAMBDA) {
    return kind::APPLY_UF;
  }

  switch(Kind k CVC4_UNUSED = nv->getKind()) {
${metakind_operatorKinds}

  default:
    return kind::UNDEFINED_KIND;  /* LAST_KIND */
  };
}

}/* CVC4::kind namespace */
}/* CVC4 namespace */

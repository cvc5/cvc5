/*********************                                                        */
/*! \file ufss_mode.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Custom handlers and predicates for TheoryUF options
 **
 ** Custom handlers and predicates for TheoryUF options.
 **/

#include "cvc4_private.h"

#ifndef CVC4__BASE__UFSS_MODE_H
#define CVC4__BASE__UFSS_MODE_H

namespace CVC4 {
namespace theory {
namespace uf {

/**
 * These modes determine the role of UF with cardinality when using finite model
 * finding (--finite-model-find).
 */
enum UfssMode
{
  /**
   * Default, use UF with cardinality to find minimal models for uninterpreted
   * sorts.
   */
  UF_SS_FULL,
  /**
   * Use UF with cardinality to shrink model sizes, but do no enforce
   * minimality.
   */
  UF_SS_NO_MINIMAL,
  /** do not use UF with cardinality */
  UF_SS_NONE,
};

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__BASE__UFSS_MODE_H */

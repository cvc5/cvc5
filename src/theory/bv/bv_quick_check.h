/*********************                                                        */
/*! \file bv_quick_check.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sandboxed sat solver for bv quickchecks.
 **
 ** Sandboxed sat solver for bv quickchecks.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BV_QUICK_CHECK_H
#define __CVC4__BV_QUICK_CHECK_H

#include <vector>
#include <ext/hash_map>

#include "expr/node.h"
#include "context/cdo.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {
namespace theory {
namespace bv {

class TLazyBitblaster; 

class BVQuickCheck {
  context::Context* d_ctx;
  TLazyBitblaster* d_bitblaster;
  Node d_conflict;
  context::CDO<bool> d_inConflict;

  void setConflict();

public:
  BVQuickCheck();
  ~BVQuickCheck();
  bool inConflict();
  Node getConflict() { return d_conflict; }
  prop::SatValue checkSat(std::vector<Node>& assumptions, unsigned long budget);
  void push();
  void pop();
  void reset(); 
};



} /* bv namespace */
} /* theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__BV_QUICK_CHECK_H */

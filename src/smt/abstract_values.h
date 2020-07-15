/*********************                                                        */
/*! \file abstract_values.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for constructing and maintaining abstract values.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__PROCESS_ASSERTIONS_H
#define CVC4__SMT__PROCESS_ASSERTIONS_H

#include <map>

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "theory/substitutions.h"

namespace CVC4 {
namespace smt {

class AbstractValues
{
 public:
  AbstractValues(NodeManager* nm);
  ~AbstractValues();
  /**
   * Substitute away all AbstractValues in a node.
   */
  Node substituteAbstractValues(TNode n);

  /**
   * Make a new (or return an existing) abstract value for a node.
   * Can only use this if options::abstractValues() is on.
   */
  Node mkAbstractValue(TNode n);

 private:
  /** Pointer to the used node manager */
  NodeManager* d_nm;
  /**
   * A context that never pushes/pops, for use by CD structures (like
   * SubstitutionMaps) that should be "global".
   */
  context::Context d_fakeContext;

  /**
   * A map of AbsractValues to their actual constants.  Only used if
   * options::abstractValues() is on.
   */
  SubstitutionMap d_abstractValueMap;

  /**
   * A mapping of all abstract values (actual value |-> abstract) that
   * we've handed out.  This is necessary to ensure that we give the
   * same AbstractValues for the same real constants.  Only used if
   * options::abstractValues() is on.
   */
  NodeToNodeHashMap d_abstractValues;
};

}  // namespace smt
}  // namespace CVC4

#endif

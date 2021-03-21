/*********************                                                        */
/*! \file assertion_list.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Assertion list for justification strategy
 **/

#include "cvc4_private.h"

#ifndef CVC4__DECISION__ASSERTION_LIST_H
#define CVC4__DECISION__ASSERTION_LIST_H

#include "context/cdo.h"
#include "context/cdlist.h"
#include "expr/node.h"

namespace CVC4 {
  
class AssertionList
{
public:
  AssertionList(context::Context * ac, context::Context * ic);
  /** Add the assertion */
  void addAssertion(TNode n);
  /** Get the new assertion, increment d_assertionIndex. */
  TNode getNextAssertion();
private:
  /** The list of assertions */
  context::CDList<Node> d_assertions;
  /** The index of the next assertion to satify */
  context::CDO<size_t> d_assertionIndex;
};

}/* CVC4 namespace */

#endif /* CVC4__DECISION__ASSERTION_LIST_H */

/*********************                                                        */
/*! \file propositional_query.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A class for simple, quick, propositional
 ** satisfiability/validity checking
 **
 ** PropositionalQuery is a way for parts of CVC4 to do quick purely
 ** propositional satisfiability or validity checks on a Node.  These
 ** checks do no theory reasoning, and handle atoms as propositional
 ** variables, but can sometimes be useful for subqueries.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROPOSITIONAL_QUERY_H
#define __CVC4__PROPOSITIONAL_QUERY_H

#include "expr/node.h"
#include "util/result.h"

namespace CVC4 {

/**
 * PropositionalQuery is a way for parts of CVC4 to do quick purely
 * propositional satisfiability or validity checks on a Node.
 */
class PropositionalQuery {
public:

  /**
   * Returns whether a node q is propositionally satisfiable.
   *
   * @param q Node to be checked for satisfiability.
   * @pre q is a ground formula.
   * @pre effort is between 0 and 1.
   */
  static Result isSatisfiable(TNode q);

  /**
   * Returns whether a node q is a propositional tautology.
   *
   * @param q Node to be checked for satisfiability.
   * @pre q is a ground formula.
   * @pre effort is between 0 and 1.
   */
  static Result isTautology(TNode q);

};/* class PropositionalQuery */

}/* CVC4 namespace */

#endif /* __CVC4__PROPOSITIONAL_QUERY_H */

/*********************                                                        */
/*! \file assertion.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The representation of the assertions sent to theories.
 **
 ** The representation of the assertions sent to theories.
 **/


#include "cvc4_private.h"

#ifndef CVC4__THEORY__ASSERTION_H
#define CVC4__THEORY__ASSERTION_H

#include "expr/node.h"

namespace CVC4 {
namespace theory {

/** Information about an assertion for the theories. */
struct Assertion {
  /** The assertion expression. */
  const Node d_assertion;

  /** Has this assertion been preregistered with this theory. */
  const bool d_isPreregistered;

  Assertion(TNode assertion, bool isPreregistered)
      : d_assertion(assertion), d_isPreregistered(isPreregistered)
  {
  }

  /** Convert the assertion to a TNode. */
  operator TNode() const { return d_assertion; }

  /** Convert the assertion to a Node. */
  operator Node() const { return d_assertion; }

}; /* struct Assertion */

std::ostream& operator<<(std::ostream& out, const Assertion& a);

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ASSERTION_H */

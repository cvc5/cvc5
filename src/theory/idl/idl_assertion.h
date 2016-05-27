/*********************                                                        */
/*! \file idl_assertion.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#pragma once

#include "theory/idl/idl_model.h"

namespace CVC4 {
namespace theory {
namespace idl {

/**
 * An internal representation of the IDL assertions. Each IDL assertions is
 * of the form (x - y op c) where op is one of (<=, =, !=). IDL assertion
 * can be constructed from an expression.
 */
class IDLAssertion {

  /** The positive variable */
  TNode d_x;
  /** The negative variable */
  TNode d_y;
  /** The relation */
  Kind d_op;
  /** The RHS constant */
  Integer d_c;

  /** Original assertion we got this one from */
  TNode d_original;

  /** Parses the given node into an assertion, and return true if OK. */
  bool parse(TNode node, int c = 1, bool negated = false);

public:

  /** Null assertion */
  IDLAssertion();
  /** Create the assertion from given node */
  IDLAssertion(TNode node);
  /** Copy constructor */
  IDLAssertion(const IDLAssertion& other);

  TNode getX() const { return d_x; }
  TNode getY() const { return d_y; }
  Kind getOp() const { return d_op;}
  Integer getC() const { return d_c; }

  /**
   * Propagate the constraint using the model. For example, if the constraint
   * is of the form x - y <= -1, and the value of x in the model is 0, then
   *
   *   (x - y <= -1) and (x = 0) implies y >= x + 1 = 1
   *
   * If the value of y is less then 1, is is set to 1 and true is returned. If
   * the value of y is 1 or more, than false is return.
   *
   * @return true if value of y was updated
   */
  bool propagate(IDLModel& model) const;

  /** Is this constraint proper */
  bool ok() const {
    return !d_x.isNull() || !d_y.isNull();
  }

  /** Output to the stream */
  void toStream(std::ostream& out) const;
};

inline std::ostream& operator << (std::ostream& out, const IDLAssertion& assertion) {
  assertion.toStream(out);
  return out;
}

}
}
}

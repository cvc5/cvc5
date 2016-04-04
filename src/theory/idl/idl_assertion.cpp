/*********************                                                        */
/*! \file idl_assertion.cpp
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

#include "theory/idl/idl_assertion.h"

using namespace CVC4;
using namespace theory;
using namespace idl;

IDLAssertion::IDLAssertion()
: d_op(kind::LAST_KIND)
{}

IDLAssertion::IDLAssertion(TNode node) {
  bool ok = parse(node, 1, false);
  if (!ok) {
    d_x = d_y = TNode::null();
  } else {
    if (d_op == kind::GT) {
      // Turn GT into LT x - y > c is the same as y - x < -c
      std::swap(d_x, d_y);
      d_c = -d_c;
      d_op = kind::LT;
    }
    if (d_op == kind::GEQ) {
      // Turn GT into LT x - y >= c is the same as y - x <= -c
      std::swap(d_x, d_y);
      d_c = -d_c;
      d_op = kind::LEQ;
    }
    if (d_op == kind::LT) {
      // Turn strict into non-strict x - y < c is the same as x - y <= c-1
      d_c = d_c - 1;
      d_op = kind::LEQ;
    }
  }
  d_original = node;
}

IDLAssertion::IDLAssertion(const IDLAssertion& other)
: d_x(other.d_x)
, d_y(other.d_y)
, d_op(other.d_op)
, d_c(other.d_c)
, d_original(other.d_original)
{}

bool IDLAssertion::propagate(IDLModel& model) const {
  Debug("theory::idl::model") << model << std::endl;
  Assert(ok());
  // Should be d_x - d_y <= d_c, or d_x - d_c <= d_y
  Integer x_value = model.getValue(d_x);
  Integer y_value = model.getValue(d_y);
  if (x_value - y_value > d_c) {
    model.setValue(d_y, x_value - d_c, IDLReason(d_x, d_original));
    Debug("theory::idl::model") << model << std::endl;
    return true;
  } else {
    return false;
  }
}

void IDLAssertion::toStream(std::ostream& out) const {
  out << "IDL[" << d_x << " - " << d_y << " " << d_op << " " << d_c << "]";
}

/** Negates the given arithmetic kind */
static Kind negateOp(Kind op) {
  switch (op) {
  case kind::LT:
    // not (a < b) = (a >= b)
    return kind::GEQ;
  case kind::LEQ:
    // not (a <= b) = (a > b)
    return kind::GT;
  case kind::GT:
    // not (a > b) = (a <= b)
    return kind::LEQ;
  case kind::GEQ:
    // not (a >= b) = (a < b)
    return kind::LT;
  case kind::EQUAL:
    // not (a = b) = (a != b)
    return kind::DISTINCT;
  case kind::DISTINCT:
    // not (a != b) = (a = b)
    return kind::EQUAL;
  default:
    Unreachable();
    break;
  }
  return kind::LAST_KIND;
}

bool IDLAssertion::parse(TNode node, int c, bool negated) {

  // Only unit coefficients allowed
  if (c != 1 && c != -1) {
    return false;
  }

  // Assume we're ok
  bool ok = true;

  // The kind of the node
  switch(node.getKind()) {

  case kind::NOT:
    // We parse the negation
    ok = parse(node[0], c, true);
    // Setup the kind
    if (ok) {
      d_op = negateOp(d_op);
    }
    break;

  case kind::EQUAL:
  case kind::LT:
  case kind::LEQ:
  case kind::GT:
  case kind::GEQ: {
    // All relation operators are parsed on both sides
    d_op = node.getKind();
    ok = parse(node[0], c, negated);
    if (ok) {
      ok = parse(node[1],-c, negated);
    }
    break;
  }

  case kind::CONST_RATIONAL: {
    // Constants
    Rational m = node.getConst<Rational>();
    if (m.isIntegral()) {
      d_c +=  m.getNumerator() * (-c);
    } else {
      ok = false;
    }
    break;
  }
  case kind::MULT: {
    // Only unit multiplication of variables
    if (node.getNumChildren() == 2 && node[0].isConst()) {
      Rational a = node[0].getConst<Rational>();
      if (a == 1 || a == -1) {
        ok = parse(node[1], c * a.sgn(), negated);
      } else {
        ok = false;
      }
    } else {
      ok = false;
    }
    break;
  }

  case kind::PLUS: {
    for(unsigned i = 0; i < node.getNumChildren(); ++i) {
      ok = parse(node[i], c, negated);
      if(!ok) {
        break;
      }
    }
    break;
  }

  case kind::MINUS: {
    ok = parse(node[0], c, negated);
    if (ok) {
      ok = parse(node[1], -c, negated);
    }
    break;
  }

  case kind::UMINUS: {
    ok = parse(node[0], -c, negated);
    break;
  }

  default: {
    if (c > 0) {
      if (d_x.isNull()) {
        d_x = node;
      } else {
        ok = false;
      }
    } else {
      if (d_y.isNull()) {
        d_y = node;
      } else {
        ok = false;
      }
    }
    break;
  }
  } // End case

  // Difference logic OK
  return ok;
}

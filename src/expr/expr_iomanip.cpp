/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King, Kshitij Bansal
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Expr IO manipulation classes.
 */

#include "expr/expr_iomanip.h"

#include <iomanip>
#include <iostream>

#include "options/options.h"
#include "options/expr_options.h"

namespace cvc5 {
namespace expr {

const int ExprSetDepth::s_iosIndex = std::ios_base::xalloc();
const int ExprDag::s_iosIndex = std::ios_base::xalloc();

ExprSetDepth::ExprSetDepth(long depth) : d_depth(depth) {}

void ExprSetDepth::applyDepth(std::ostream& out) {
  out.iword(s_iosIndex) = d_depth;
}

long ExprSetDepth::getDepth(std::ostream& out) {
  long& l = out.iword(s_iosIndex);
  if(l == 0) {
    // set the default print depth on this ostream
    if(not Options::isCurrentNull()) {
      l = options::defaultExprDepth();
    }
    if(l == 0) {
      // if called from outside the library, we may not have options
      // available to us at this point (or perhaps the output language
      // is not set in Options).  Default to something reasonable, but
      // don't set "l" since that would make it "sticky" for this
      // stream.
      return s_defaultPrintDepth;
    }
  }
  return l;
}

void ExprSetDepth::setDepth(std::ostream& out, long depth) {
  out.iword(s_iosIndex) = depth;
}


ExprSetDepth::Scope::Scope(std::ostream& out, long depth)
  : d_out(out), d_oldDepth(ExprSetDepth::getDepth(out))
{
  ExprSetDepth::setDepth(out, depth);
}

ExprSetDepth::Scope::~Scope() {
  ExprSetDepth::setDepth(d_out, d_oldDepth);
}

ExprDag::ExprDag(bool dag) : d_dag(dag ? 1 : 0) {}

ExprDag::ExprDag(int dag) : d_dag(dag < 0 ? 0 : dag) {}

void ExprDag::applyDag(std::ostream& out) {
  // (offset by one to detect whether default has been set yet)
  out.iword(s_iosIndex) = static_cast<long>(d_dag) + 1;
}

size_t ExprDag::getDag(std::ostream& out) {
  long& l = out.iword(s_iosIndex);
  if(l == 0) {
    // set the default dag setting on this ostream
    // (offset by one to detect whether default has been set yet)
    if(not Options::isCurrentNull()) {
      l = options::defaultDagThresh() + 1;
    }
    if(l == 0) {
      // if called from outside the library, we may not have options
      // available to us at this point (or perhaps the output language
      // is not set in Options).  Default to something reasonable, but
      // don't set "l" since that would make it "sticky" for this
      // stream.
      return s_defaultDag + 1;
    }
  }
  return static_cast<size_t>(l - 1);
}

void ExprDag::setDag(std::ostream& out, size_t dag) {
  // (offset by one to detect whether default has been set yet)
  out.iword(s_iosIndex) = static_cast<long>(dag) + 1;
}

ExprDag::Scope::Scope(std::ostream& out, size_t dag)
  : d_out(out),
    d_oldDag(ExprDag::getDag(out)) {
  ExprDag::setDag(out, dag);
}

ExprDag::Scope::~Scope() {
  ExprDag::setDag(d_out, d_oldDag);
}

std::ostream& operator<<(std::ostream& out, ExprDag d) {
  d.applyDag(out);
  return out;
}

std::ostream& operator<<(std::ostream& out, ExprSetDepth sd) {
  sd.applyDepth(out);
  return out;
}

}  // namespace expr
}  // namespace cvc5

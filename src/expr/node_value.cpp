/*********************                                                        */
/*! \file node_value.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An expression node.
 **
 ** An expression node.
 **
 ** Instances of this class are generally referenced through
 ** cvc4::Node rather than by pointer; cvc4::Node maintains the
 ** reference count on NodeValue instances and
 **/
#include "expr/node_value.h"

#include <sstream>

#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/options.h"
#include "printer/printer.h"

using namespace std;

namespace CVC4 {
namespace expr {

string NodeValue::toString() const {
  stringstream ss;

  OutputLanguage outlang = (this == &null()) ? language::output::LANG_AUTO
                                             : options::outputLanguage();
  toStream(ss, -1, false, false, outlang);
  return ss.str();
}

void NodeValue::toStream(std::ostream& out, int toDepth, bool types, size_t dag,
                         OutputLanguage language) const {
  // Ensure that this node value is live for the length of this call.
  // It really breaks things badly if we don't have a nonzero ref
  // count, even just for printing.
  RefCountGuard guard(this);

  Printer::getPrinter(language)->toStream(out, TNode(this), toDepth, types,
                                          dag);
}

void NodeValue::printAst(std::ostream& out, int ind) const {
  RefCountGuard guard(this);

  indent(out, ind);
  out << '(';
  out << getKind();
  if (getMetaKind() == kind::metakind::VARIABLE) {
    out << ' ' << getId();
  } else if (getMetaKind() == kind::metakind::CONSTANT) {
    out << ' ';
    kind::metakind::NodeValueConstPrinter::toStream(out, this);
  } else {
    if (nv_begin() != nv_end()) {
      for (const_nv_iterator child = nv_begin(); child != nv_end(); ++child) {
        out << std::endl;
        (*child)->printAst(out, ind + 1);
      }
      out << std::endl;
      indent(out, ind);
    }
  }
  out << ')';
}

} /* CVC4::expr namespace */
} /* CVC4 namespace */

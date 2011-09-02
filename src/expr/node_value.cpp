/*********************                                                        */
/*! \file node_value.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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
#include "expr/node.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "util/language.h"
#include "printer/printer.h"
#include <sstream>

using namespace std;

namespace CVC4 {
namespace expr {

size_t NodeValue::next_id = 1;

NodeValue NodeValue::s_null(0);

string NodeValue::toString() const {
  stringstream ss;
  toStream(ss);
  return ss.str();
}

void NodeValue::toStream(std::ostream& out, int toDepth, bool types,
                         OutputLanguage language) const {
  Printer::getPrinter(language)->toStream(out, TNode(this), toDepth, types);
}

void NodeValue::printAst(std::ostream& out, int ind) const {
  indent(out, ind);
  out << '(';
  out << getKind();
  if(getMetaKind() == kind::metakind::VARIABLE) {
    out << ' ' << getId();
  } else if(getMetaKind() == kind::metakind::CONSTANT) {
    out << ' ';
    kind::metakind::NodeValueConstPrinter::toStream(out, this);
  } else {
    if(nv_begin() != nv_end()) {
      for(const_nv_iterator child = nv_begin(); child != nv_end(); ++child) {
        out << std::endl;
        (*child)->printAst(out, ind + 1);
      }
      out << std::endl;
      indent(out, ind);
    }
  }
  out << ')';
}

}/* CVC4::expr namespace */
}/* CVC4 namespace */

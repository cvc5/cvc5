/*********************                                                        */
/** node_value.cpp
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
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

void NodeValue::toStream(std::ostream& out, int toDepth) const {
  using namespace CVC4::kind;
  using namespace CVC4;

  if(getKind() == kind::NULL_EXPR) {
    out << "null";
  } else if(getMetaKind() == kind::metakind::VARIABLE) {
    if(getKind() != kind::VARIABLE) {
      out << getKind() << ':';
    }

    string s;

    // conceptually "this" is const, and hasAttribute() doesn't change
    // its argument, but it requires a non-const key arg (for now)
    if(NodeManager::currentNM()->getAttribute(const_cast<NodeValue*>(this),
                                              VarNameAttr(), s)) {
      out << s;
    } else {
      out << "var_" << d_id;
    }
  } else {
    out << '(' << Kind(d_kind);
    if(getMetaKind() == kind::metakind::CONSTANT) {
      out << ' ';
      kind::metakind::NodeValueConstPrinter::toStream(out, this);
    } else {
      for(const_nv_iterator i = nv_begin(); i != nv_end(); ++i) {
        if(i != nv_end()) {
          out << ' ';
        }
        if(toDepth != 0) {
          (*i)->toStream(out, toDepth < 0 ? toDepth : toDepth - 1);
        } else {
          out << "(...)";
        }
      }
    }
    out << ')';
  }
}

}/* CVC4::expr namespace */
}/* CVC4 namespace */

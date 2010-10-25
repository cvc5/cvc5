/*********************                                                        */
/*! \file node_value.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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
  using namespace CVC4;
  using namespace CVC4::kind;
  using namespace CVC4::language::output;

  switch(language) {
  case LANG_CVC4:
    // FIXME support cvc output language
  case LANG_SMTLIB:
    // FIXME support smt-lib output language
  case LANG_SMTLIB_V2:
    // FIXME support smt-lib v2 output language
  case LANG_AST:
    if(getKind() == kind::NULL_EXPR) {
      out << "null";
    } else if(getMetaKind() == kind::metakind::VARIABLE) {
      if(getKind() != kind::VARIABLE &&
         getKind() != kind::SORT_TYPE) {
        out << getKind() << ':';
      }

      string s;
      NodeManager* nm = NodeManager::currentNM();

      // conceptually "this" is const, and hasAttribute() doesn't change
      // its argument, but it requires a non-const key arg (for now)
      if(nm->getAttribute(const_cast<NodeValue*>(this),
                          VarNameAttr(), s)) {
        out << s;
      } else {
        out << "var_" << d_id;
      }
      if(types) {
        // print the whole type, but not *its* type
        out << ":";
        nm->getType(TNode(this)).toStream(out, -1, false, language);
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
            (*i)->toStream(out, toDepth < 0 ? toDepth : toDepth - 1,
                           types, language);
          } else {
            out << "(...)";
          }
        }
      }
      out << ')';
    }
    break;

  default:
    out << "[output language " << language << " unsupported]";
  }// end switch(language)
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

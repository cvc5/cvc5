/*********************                                                        */
/*! \file ast_printer.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The pretty-printer interface for the AST output language
 **
 ** The pretty-printer interface for the AST output language.
 **/

#include "printer/ast/ast_printer.h"
#include "util/language.h" // for LANG_AST
#include "expr/node_manager.h" // for VarNameAttr

#include <iostream>

using namespace std;

namespace CVC4 {
namespace printer {
namespace ast {

void AstPrinter::toStream(std::ostream& out, TNode n,
                                   int toDepth, bool types) const {
  // null
  if(n.getKind() == kind::NULL_EXPR) {
    out << "null";
    return;
  }

  // variable
  if(n.getMetaKind() == kind::metakind::VARIABLE) {
    if(n.getKind() != kind::VARIABLE &&
       n.getKind() != kind::SORT_TYPE) {
      out << n.getKind() << ':';
    }

    string s;
    if(n.getAttribute(expr::VarNameAttr(), s)) {
      out << s;
    } else {
      out << "var_" << n.getId();
    }
    if(types) {
      // print the whole type, but not *its* type
      out << ":";
      n.getType().toStream(out, -1, false, language::output::LANG_AST);
    }

    return;
  }

  out << '(' << n.getKind();
  if(n.getMetaKind() == kind::metakind::CONSTANT) {
    // constant
    out << ' ';
    kind::metakind::NodeValueConstPrinter::toStream(out, n);
  } else {
    // operator
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      out << ' ';
      if(toDepth != 0) {
        n.getOperator().toStream(out, toDepth < 0 ? toDepth : toDepth - 1,
                                 types, language::output::LANG_AST);
      } else {
        out << "(...)";
      }
    }
    for(TNode::iterator i = n.begin(),
          iend = n.end();
        i != iend;
        ++i) {
      if(i != iend) {
        out << ' ';
      }
      if(toDepth != 0) {
        (*i).toStream(out, toDepth < 0 ? toDepth : toDepth - 1,
                      types, language::output::LANG_AST);
      } else {
        out << "(...)";
      }
    }
  }
  out << ')';
}/* AstPrinter::toStream() */

}/* CVC4::printer::ast namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */


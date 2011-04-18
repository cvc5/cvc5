/*********************                                                        */
/*! \file cvc_printer.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The pretty-printer interface for the CVC output language
 **
 ** The pretty-printer interface for the CVC output language.
 **/

#include "printer/cvc/cvc_printer.h"
#include "util/language.h"

#include <iostream>
#include <algorithm>
#include <iterator>

using namespace std;

namespace CVC4 {
namespace printer {
namespace cvc {

void CvcPrinter::toStream(std::ostream& out, TNode n,
                          int toDepth, bool types) const {
  // null
  if(n.getKind() == kind::NULL_EXPR) {
    out << "NULL";
    return;
  }

  // variable
  if(n.getMetaKind() == kind::metakind::VARIABLE) {
    string s;
    if(n.getAttribute(expr::VarNameAttr(), s)) {
      out << s;
    } else {
      if(n.getKind() == kind::VARIABLE) {
        out << "var_";
      } else {
        out << n.getKind() << '_';
      }
      out << n.getId();
    }
    if(types) {
      // print the whole type, but not *its* type
      out << ":";
      n.getType().toStream(out, -1, false, language::output::LANG_CVC4);
    }

    return;
  }

  // constant
  if(n.getMetaKind() == kind::metakind::CONSTANT) {
    switch(n.getKind()) {
    case kind::BITVECTOR_TYPE:
      out << "BITVECTOR(" << n.getConst<BitVectorSize>().size << ")";
      break;
    case kind::CONST_BITVECTOR: {
      const BitVector& bv = n.getConst<BitVector>();
      const Integer& x = bv.getValue();
      out << "0bin";
      unsigned n = bv.getSize();
      while(n-- > 0) {
        out << (x.testBit(n) ? '1' : '0');
      }
      break;
    }
    case kind::CONST_BOOLEAN:
      // the default would print "1" or "0" for bool, that's not correct
      // for our purposes
      out << (n.getConst<bool>() ? "TRUE" : "FALSE");
      break;
    case kind::CONST_RATIONAL: {
      const Rational& rat = n.getConst<Rational>();
      out << '(' << rat.getNumerator() << '/' << rat.getDenominator() << ')';
      break;
    }
    case kind::BUILTIN:
      switch(Kind k = n.getConst<Kind>()) {
      case kind::EQUAL: out << '='; break;
      case kind::PLUS: out << '+'; break;
      case kind::MULT: out << '*'; break;
      case kind::MINUS:
      case kind::UMINUS: out << '-'; break;
      case kind::DIVISION: out << '/'; break;
      case kind::LT: out << '<'; break;
      case kind::LEQ: out << "<="; break;
      case kind::GT: out << '>'; break;
      case kind::GEQ: out << ">="; break;
      case kind::IMPLIES: out << "=>"; break;
      case kind::IFF: out << "<=>"; break;
      default:
        out << k;
      }
      break;
    default:
      // fall back on whatever operator<< does on underlying type; we
      // might luck out and be SMT-LIB v2 compliant
      kind::metakind::NodeValueConstPrinter::toStream(out, n);
    }

    return;
  } else if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
    out << n.getOperator();
    if(n.getNumChildren() > 0) {
      out << '(';
      if(n.getNumChildren() > 1) {
        copy(n.begin(), n.end() - 1, ostream_iterator<TNode>(out, ", "));
      }
      out << n[n.getNumChildren() - 1] << ')';
    }
    return;
  } else if(n.getMetaKind() == kind::metakind::OPERATOR) {
    switch(Kind k = n.getKind()) {
    case kind::FUNCTION_TYPE:
    case kind::CONSTRUCTOR_TYPE:
    case kind::SELECTOR_TYPE:
    case kind::TESTER_TYPE:
      if(n.getNumChildren() > 0) {
        copy(n.begin(), n.end() - 1, ostream_iterator<TNode>(out, " -> "));
        out << n[n.getNumChildren() - 1];
      }
      break;

    case kind::ARRAY_TYPE:
      out << "ARRAY " << n[0] << " OF " << n[1];
      break;
    case kind::SELECT:
      out << n[0] << '[' << n[1] << ']';
      break;
    case kind::STORE:
      out << n[0] << " WITH [" << n[1] << "] = " << n[2];
      break;

    case kind::TUPLE_TYPE:
      out << '[';
      copy(n.begin(), n.end() - 1, ostream_iterator<TNode>(out, ","));
      out << n[n.getNumChildren() - 1];
      out << ']';
      break;
    case kind::TUPLE:
      out << "( ";
      copy(n.begin(), n.end() - 1, ostream_iterator<TNode>(out, ", "));
      out << n[n.getNumChildren() - 1];
      out << " )";
      break;

    case kind::ITE:
      out << "IF " << n[0] << " THEN " << n[1] << " ELSE " << n[2];
      break;

    default:
      if(k == kind::NOT && n[0].getKind() == kind::EQUAL) {
        // collapse NOT-over-EQUAL
        out << n[0][0] << " /= " << n[0][1];
      } else if(n.getNumChildren() == 2) {
        // infix operator
        out << n[0] << ' ' << n.getOperator() << ' ' << n[1];
      } else {
        // prefix operator
        out << n.getOperator() << ' ';
        if(n.getNumChildren() > 0) {
          if(n.getNumChildren() > 1) {
            copy(n.begin(), n.end() - 1, ostream_iterator<TNode>(out, " "));
          }
          out << n[n.getNumChildren() - 1];
        }
      }
    }
    return;
  }

  Unhandled();

}/* CvcPrinter::toStream() */

}/* CVC4::printer::cvc namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */


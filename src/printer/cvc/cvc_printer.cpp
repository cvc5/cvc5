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

        // names are slightly different than the kind
      case kind::BITVECTOR_PLUS: out << "BVPLUS"; break;
      case kind::BITVECTOR_SUB: out << "BVSUB"; break;
      case kind::BITVECTOR_XOR: out << "BVXOR"; break;
      case kind::BITVECTOR_NAND: out << "BVNAND"; break;
      case kind::BITVECTOR_NOR: out << "BVNOR"; break;
      case kind::BITVECTOR_XNOR: out << "BVXNOR"; break;
      case kind::BITVECTOR_COMP: out << "BVCOMP"; break;
      case kind::BITVECTOR_MULT: out << "BVMULT"; break;
      case kind::BITVECTOR_UDIV: out << "BVUDIV"; break;
      case kind::BITVECTOR_UREM: out << "BVUREM"; break;
      case kind::BITVECTOR_SDIV: out << "BVSDIV"; break;
      case kind::BITVECTOR_SREM: out << "BVSREM"; break;
      case kind::BITVECTOR_SMOD: out << "BVSMOD"; break;
      case kind::BITVECTOR_SHL: out << "BVSHL"; break;
      case kind::BITVECTOR_LSHR: out << "BVLSHR"; break;
      case kind::BITVECTOR_ASHR: out << "BVASHR"; break;
      case kind::BITVECTOR_ULT: out << "BVLT"; break;
      case kind::BITVECTOR_ULE: out << "BVLE"; break;
      case kind::BITVECTOR_UGT: out << "BVGT"; break;
      case kind::BITVECTOR_UGE: out << "BVGE"; break;
      case kind::BITVECTOR_SLT: out << "BVSLT"; break;
      case kind::BITVECTOR_SLE: out << "BVSLE"; break;
      case kind::BITVECTOR_SGT: out << "BVSGT"; break;
      case kind::BITVECTOR_SGE: out << "BVSGE"; break;
      case kind::BITVECTOR_NEG: out << "BVUMINUS"; break;

      case kind::BITVECTOR_NOT: out << "~"; break;
      case kind::BITVECTOR_AND: out << "&"; break;
      case kind::BITVECTOR_OR: out << "|"; break;
      case kind::BITVECTOR_CONCAT: out << "@"; break;

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
    switch(n.getKind()) {
    case kind::BITVECTOR_EXTRACT:
      out << n[0] << n.getOperator().getConst<BitVectorExtract>();
      break;
    case kind::BITVECTOR_REPEAT:
      out << "BVREPEAT(" << n[0] << "," << n.getOperator() << ')';
      break;
    case kind::BITVECTOR_ZERO_EXTEND:
      out << "BVZEROEXTEND(" << n[0] << "," << n.getOperator() << ')';
      break;
    case kind::BITVECTOR_SIGN_EXTEND:
      out << "SX(" << n[0] << "," << n.getOperator() << ')';
      break;
    case kind::BITVECTOR_ROTATE_LEFT:
      out << "BVROTL(" << n[0] << "," << n.getOperator() << ')';
      break;
    case kind::BITVECTOR_ROTATE_RIGHT:
      out << "BVROTR(" << n[0] << "," << n.getOperator() << ')';
      break;


    default:
      out << n.getOperator();
      if(n.getNumChildren() > 0) {
        out << '(';
        if(n.getNumChildren() > 1) {
          copy(n.begin(), n.end() - 1, ostream_iterator<TNode>(out, ", "));
        }
        out << n[n.getNumChildren() - 1] << ')';
      }
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

    // these are prefix
    case kind::BITVECTOR_PLUS:
    case kind::BITVECTOR_SUB:
    case kind::BITVECTOR_XOR:
    case kind::BITVECTOR_NAND:
    case kind::BITVECTOR_NOR:
    case kind::BITVECTOR_XNOR:
    case kind::BITVECTOR_COMP:
    case kind::BITVECTOR_MULT:
    case kind::BITVECTOR_UDIV:
    case kind::BITVECTOR_UREM:
    case kind::BITVECTOR_SDIV:
    case kind::BITVECTOR_SREM:
    case kind::BITVECTOR_SMOD:
    case kind::BITVECTOR_SHL:
    case kind::BITVECTOR_LSHR:
    case kind::BITVECTOR_ASHR:
    case kind::BITVECTOR_ULT:
    case kind::BITVECTOR_ULE:
    case kind::BITVECTOR_UGT:
    case kind::BITVECTOR_UGE:
    case kind::BITVECTOR_SLT:
    case kind::BITVECTOR_SLE:
    case kind::BITVECTOR_SGT:
    case kind::BITVECTOR_SGE:
      out << n.getOperator() << '(' << n[0] << ',' << n[1] << ')';
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


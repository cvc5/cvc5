/*********************                                                        */
/*! \file smt2_printer.cpp
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
 ** \brief The pretty-printer interface for the SMT2 output language
 **
 ** The pretty-printer interface for the SMT2 output language.
 **/

#include "printer/smt2/smt2_printer.h"

#include <iostream>

using namespace std;

namespace CVC4 {
namespace printer {
namespace smt2 {

void printBvParameterizedOp(std::ostream& out, TNode n);

void Smt2Printer::toStream(std::ostream& out, TNode n,
                           int toDepth, bool types) const {
  // null
  if(n.getKind() == kind::NULL_EXPR) {
    out << "null";
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
      n.getType().toStream(out, -1, false, language::output::LANG_SMTLIB_V2);
    }

    return;
  }

  // constant
  if(n.getMetaKind() == kind::metakind::CONSTANT) {
    switch(n.getKind()) {
    case kind::BITVECTOR_TYPE:
      out << "(_ BitVec " << n.getConst<BitVectorSize>().size << ")";
      break;
    case kind::CONST_BITVECTOR: {
      const BitVector& bv = n.getConst<BitVector>();
      const Integer& x = bv.getValue();
      out << "#b";
      unsigned n = bv.getSize();
      while(n-- > 0) {
        out << (x.testBit(n) ? '1' : '0');
      }
      break;
    }
    default:
      // fall back on whatever operator<< does on underlying type; we
      // might luck out and be SMT-LIB v2 compliant
      kind::metakind::NodeValueConstPrinter::toStream(out, n);
    }

    return;
  }

  bool stillNeedToPrintParams = true;
  // operator
  out << '(';
  switch(n.getKind()) {
    // builtin theory
  case kind::EQUAL: out << "= "; break;
  case kind::DISTINCT: out << "distinct "; break;
  case kind::TUPLE: break;

    // bool theory
  case kind::NOT: out << "not "; break;
  case kind::AND: out << "and "; break;
  case kind::IFF: out << "iff "; break;
  case kind::IMPLIES: out << "implies "; break;
  case kind::OR: out << "or "; break;
  case kind::XOR: out << "xor "; break;
  case kind::ITE: out << "ite "; break;

    // uf theory
  case kind::APPLY_UF: break;
  case kind::SORT_TYPE: break;

    // arith theory
  case kind::PLUS: out << "+ "; break;
  case kind::MULT: out << "* "; break;
  case kind::MINUS: out << "- "; break;
  case kind::UMINUS: out << "- "; break;
  case kind::DIVISION: out << "/ "; break;
  case kind::LT: out << "< "; break;
  case kind::LEQ: out << "<= "; break;
  case kind::GT: out << "> "; break;
  case kind::GEQ: out << ">= "; break;

    // arrays theory
  case kind::SELECT: out << "select "; break;
  case kind::STORE: out << "store "; break;

    // bv theory
  case kind::BITVECTOR_CONCAT: out << "concat "; break;
  case kind::BITVECTOR_AND: out << "bvand "; break;
  case kind::BITVECTOR_OR: out << "bvor "; break;
  case kind::BITVECTOR_XOR: out << "bvxor "; break;
  case kind::BITVECTOR_NOT: out << "bvnot "; break;
  case kind::BITVECTOR_NAND: out << "bvnand "; break;
  case kind::BITVECTOR_NOR: out << "bvnor "; break;
  case kind::BITVECTOR_XNOR: out << "bvxnor "; break;
  case kind::BITVECTOR_COMP: out << "bvcomp "; break;
  case kind::BITVECTOR_MULT: out << "bvmul "; break;
  case kind::BITVECTOR_PLUS: out << "bvadd "; break;
  case kind::BITVECTOR_SUB: out << "bvsub "; break;
  case kind::BITVECTOR_NEG: out << "bvneg "; break;
  case kind::BITVECTOR_UDIV: out << "bvudiv "; break;
  case kind::BITVECTOR_UREM: out << "bvurem "; break;
  case kind::BITVECTOR_SDIV: out << "bvsdiv "; break;
  case kind::BITVECTOR_SREM: out << "bvsrem "; break;
  case kind::BITVECTOR_SMOD: out << "bvsmod "; break;
  case kind::BITVECTOR_SHL: out << "bvshl "; break;
  case kind::BITVECTOR_LSHR: out << "bvlshr "; break;
  case kind::BITVECTOR_ASHR: out << "bvashr "; break;
  case kind::BITVECTOR_ULT: out << "bvult "; break;
  case kind::BITVECTOR_ULE: out << "bvule "; break;
  case kind::BITVECTOR_UGT: out << "bvugt "; break;
  case kind::BITVECTOR_UGE: out << "bvuge "; break;
  case kind::BITVECTOR_SLT: out << "bvslt "; break;
  case kind::BITVECTOR_SLE: out << "bvsle "; break;
  case kind::BITVECTOR_SGT: out << "bvsgt "; break;
  case kind::BITVECTOR_SGE: out << "bvsge "; break;

  case kind::BITVECTOR_EXTRACT:
  case kind::BITVECTOR_REPEAT:
  case kind::BITVECTOR_ZERO_EXTEND:
  case kind::BITVECTOR_SIGN_EXTEND:
  case kind::BITVECTOR_ROTATE_LEFT:
  case kind::BITVECTOR_ROTATE_RIGHT:
    printBvParameterizedOp(out, n);
    out << ' ';
    stillNeedToPrintParams = false;
    break;

  default:
    // fall back on however the kind prints itself; this probably
    // won't be SMT-LIB v2 compliant, but it will be clear from the
    // output that support for the kind needs to be added here.
    out << n.getKind() << ' ';
  }
  if(n.getMetaKind() == kind::metakind::PARAMETERIZED &&
     stillNeedToPrintParams) {
    if(toDepth != 0) {
      n.getOperator().toStream(out, toDepth < 0 ? toDepth : toDepth - 1,
                               types, language::output::LANG_SMTLIB_V2);
      out << " ";
    } else {
      out << "(...)";
    }
    if(n.getNumChildren() > 0) {
      out << ' ';
    }
  }
  for(TNode::iterator i = n.begin(),
        iend = n.end();
      i != iend; ) {
    if(toDepth != 0) {
      (*i).toStream(out, toDepth < 0 ? toDepth : toDepth - 1,
                    types, language::output::LANG_SMTLIB_V2);
    } else {
      out << "(...)";
    }
    if(++i != iend) {
      out << ' ';
    }
  }
  out << ')';
}/* Smt2Printer::toStream() */

void printBvParameterizedOp(std::ostream& out, TNode n) {
  out << "(_ ";
  switch(n.getKind()) {
  case kind::BITVECTOR_EXTRACT: {
    BitVectorExtract p = n.getOperator().getConst<BitVectorExtract>();
    out << "extract " << p.high << " " << p.low;
    break;
  }
  case kind::BITVECTOR_REPEAT:
    out << "repeat "
        << n.getOperator().getConst<BitVectorRepeat>().repeatAmount;
    break;
  case kind::BITVECTOR_ZERO_EXTEND:
    out << "zero_extend "
        << n.getOperator().getConst<BitVectorZeroExtend>().zeroExtendAmount;
    break;
  case kind::BITVECTOR_SIGN_EXTEND:
    out << "sign_extend "
        << n.getOperator().getConst<BitVectorSignExtend>().signExtendAmount;
    break;
  case kind::BITVECTOR_ROTATE_LEFT:
    out << "rotate_left "
        << n.getOperator().getConst<BitVectorRotateLeft>().rotateLeftAmount;
    break;
  case kind::BITVECTOR_ROTATE_RIGHT:
    out << "rotate_right "
        << n.getOperator().getConst<BitVectorRotateRight>().rotateRightAmount;
    break;
  default:
    Unhandled(n.getKind());
  }
  out << ")";
}

}/* CVC4::printer::smt2 namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

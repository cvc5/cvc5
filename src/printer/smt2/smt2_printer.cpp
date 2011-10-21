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
#include <vector>
#include <string>
#include <typeinfo>

#include "util/boolean_simplification.h"

using namespace std;

namespace CVC4 {
namespace printer {
namespace smt2 {

string smtKindString(Kind k);

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
    case kind::TYPE_CONSTANT:
      switch(n.getConst<TypeConstant>()) {
      case BOOLEAN_TYPE: out << "Boolean"; break;
      case REAL_TYPE: out << "Real"; break;
      case INTEGER_TYPE: out << "Int"; break;
      default:
        // fall back on whatever operator<< does on underlying type; we
        // might luck out and be SMT-LIB v2 compliant
        kind::metakind::NodeValueConstPrinter::toStream(out, n);
      }
      break;
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
    case kind::CONST_BOOLEAN:
      // the default would print "1" or "0" for bool, that's not correct
      // for our purposes
      out << (n.getConst<bool>() ? "true" : "false");
      break;
    case kind::BUILTIN:
      out << smtKindString(n.getConst<Kind>());
      break;
    case kind::CONST_INTEGER: {
      Integer i = n.getConst<Integer>();
      if(i < 0) {
        out << "(- " << i << ')';
      } else {
        out << i;
      }
      break;
    }
    case kind::CONST_RATIONAL: {
      Rational r = n.getConst<Rational>();
      if(r < 0) {
        out << "(- " << r << ')';
      } else {
        out << r;
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

  if(n.getKind() == kind::SORT_TYPE) {
    string name;
    if(n.getAttribute(expr::VarNameAttr(), name)) {
      out << name;
      return;
    }
  }

  bool stillNeedToPrintParams = true;
  // operator
  out << '(';
  switch(Kind k = n.getKind()) {
    // builtin theory
  case kind::APPLY: break;
  case kind::EQUAL:
  case kind::DISTINCT: out << smtKindString(k) << " "; break;
  case kind::TUPLE: break;

    // bool theory
  case kind::NOT:
  case kind::AND:
  case kind::IFF:
  case kind::IMPLIES:
  case kind::OR:
  case kind::XOR:
  case kind::ITE: out << smtKindString(k) << " "; break;

    // uf theory
  case kind::APPLY_UF: break;

    // arith theory
  case kind::PLUS:
  case kind::MULT:
  case kind::MINUS:
  case kind::UMINUS:
  case kind::DIVISION:
  case kind::LT:
  case kind::LEQ:
  case kind::GT:
  case kind::GEQ: out << smtKindString(k) << " "; break;

    // arrays theory
  case kind::SELECT:
  case kind::STORE:
  case kind::ARRAY_TYPE: out << smtKindString(k) << " "; break;

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

string smtKindString(Kind k) {
  switch(k) {
    // builtin theory
  case kind::APPLY: break;
  case kind::EQUAL: return "=";
  case kind::DISTINCT: return "distinct";
  case kind::TUPLE: break;

    // bool theory
  case kind::NOT: return "not";
  case kind::AND: return "and";
  case kind::IFF: return "=";
  case kind::IMPLIES: return "=>";
  case kind::OR: return "or";
  case kind::XOR: return "xor";
  case kind::ITE: return "ite";

    // uf theory
  case kind::APPLY_UF: break;

    // arith theory
  case kind::PLUS: return "+";
  case kind::MULT: return "*";
  case kind::MINUS: return "-";
  case kind::UMINUS: return "-";
  case kind::DIVISION: return "/";
  case kind::LT: return "<";
  case kind::LEQ: return "<=";
  case kind::GT: return ">";
  case kind::GEQ: return ">=";

    // arrays theory
  case kind::SELECT: return "select";
  case kind::STORE: return "store";
  case kind::ARRAY_TYPE: return "Array";

    // bv theory
  case kind::BITVECTOR_CONCAT: return "concat";
  case kind::BITVECTOR_AND: return "bvand";
  case kind::BITVECTOR_OR: return "bvor";
  case kind::BITVECTOR_XOR: return "bvxor";
  case kind::BITVECTOR_NOT: return "bvnot";
  case kind::BITVECTOR_NAND: return "bvnand";
  case kind::BITVECTOR_NOR: return "bvnor";
  case kind::BITVECTOR_XNOR: return "bvxnor";
  case kind::BITVECTOR_COMP: return "bvcomp";
  case kind::BITVECTOR_MULT: return "bvmul";
  case kind::BITVECTOR_PLUS: return "bvadd";
  case kind::BITVECTOR_SUB: return "bvsub";
  case kind::BITVECTOR_NEG: return "bvneg";
  case kind::BITVECTOR_UDIV: return "bvudiv";
  case kind::BITVECTOR_UREM: return "bvurem";
  case kind::BITVECTOR_SDIV: return "bvsdiv";
  case kind::BITVECTOR_SREM: return "bvsrem";
  case kind::BITVECTOR_SMOD: return "bvsmod";
  case kind::BITVECTOR_SHL: return "bvshl";
  case kind::BITVECTOR_LSHR: return "bvlshr";
  case kind::BITVECTOR_ASHR: return "bvashr";
  case kind::BITVECTOR_ULT: return "bvult";
  case kind::BITVECTOR_ULE: return "bvule";
  case kind::BITVECTOR_UGT: return "bvugt";
  case kind::BITVECTOR_UGE: return "bvuge";
  case kind::BITVECTOR_SLT: return "bvslt";
  case kind::BITVECTOR_SLE: return "bvsle";
  case kind::BITVECTOR_SGT: return "bvsgt";
  case kind::BITVECTOR_SGE: return "bvsge";

  case kind::BITVECTOR_EXTRACT: return "extract";
  case kind::BITVECTOR_REPEAT: return "repeat";
  case kind::BITVECTOR_ZERO_EXTEND: return "zero_extend";
  case kind::BITVECTOR_SIGN_EXTEND: return "sign_extend";
  case kind::BITVECTOR_ROTATE_LEFT: return "rotate_left";
  case kind::BITVECTOR_ROTATE_RIGHT: return "rotate_right";
  default:
    ; /* fall through */
  }

  // no SMT way to print these
  return kind::kindToString(k);
}

void printBvParameterizedOp(std::ostream& out, TNode n) {
  out << "(_ ";
  switch(n.getKind()) {
  case kind::BITVECTOR_EXTRACT: {
    BitVectorExtract p = n.getOperator().getConst<BitVectorExtract>();
    out << "extract " << p.high << ' ' << p.low;
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

template <class T>
static bool tryToStream(std::ostream& out, const Command* c);

void Smt2Printer::toStream(std::ostream& out, const Command* c,
                           int toDepth, bool types) const {
  expr::ExprSetDepth::Scope sdScope(out, toDepth);
  expr::ExprPrintTypes::Scope ptScope(out, types);

  if(tryToStream<AssertCommand>(out, c) ||
     tryToStream<PushCommand>(out, c) ||
     tryToStream<PopCommand>(out, c) ||
     tryToStream<CheckSatCommand>(out, c) ||
     tryToStream<QueryCommand>(out, c) ||
     tryToStream<QuitCommand>(out, c) ||
     tryToStream<CommandSequence>(out, c) ||
     tryToStream<DeclareFunctionCommand>(out, c) ||
     tryToStream<DefineFunctionCommand>(out, c) ||
     tryToStream<DeclareTypeCommand>(out, c) ||
     tryToStream<DefineTypeCommand>(out, c) ||
     tryToStream<DefineNamedFunctionCommand>(out, c) ||
     tryToStream<SimplifyCommand>(out, c) ||
     tryToStream<GetValueCommand>(out, c) ||
     tryToStream<GetAssignmentCommand>(out, c) ||
     tryToStream<GetAssertionsCommand>(out, c) ||
     tryToStream<SetBenchmarkStatusCommand>(out, c) ||
     tryToStream<SetBenchmarkLogicCommand>(out, c) ||
     tryToStream<SetInfoCommand>(out, c) ||
     tryToStream<GetInfoCommand>(out, c) ||
     tryToStream<SetOptionCommand>(out, c) ||
     tryToStream<GetOptionCommand>(out, c) ||
     tryToStream<DatatypeDeclarationCommand>(out, c) ||
     tryToStream<CommentCommand>(out, c) ||
     tryToStream<EmptyCommand>(out, c)) {
    return;
  }

  Unhandled("don't know how to print this command as SMT-LIBv2: %s", c->toString().c_str());

}/* Smt2Printer::toStream() */

static void toStream(std::ostream& out, const AssertCommand* c) {
  out << "(assert " << c->getExpr() << ")";
}

static void toStream(std::ostream& out, const PushCommand* c) {
  out << "(push 1)";
}

static void toStream(std::ostream& out, const PopCommand* c) {
  out << "(pop 1)";
}

static void toStream(std::ostream& out, const CheckSatCommand* c) {
  BoolExpr e = c->getExpr();
  if(!e.isNull()) {
    out << PushCommand() << endl
        << AssertCommand(e) << endl
        << CheckSatCommand() << endl
        << PopCommand() << endl;
  } else {
    out << "(check-sat)";
  }
}

static void toStream(std::ostream& out, const QueryCommand* c) {
  BoolExpr e = c->getExpr();
  if(!e.isNull()) {
    out << PushCommand() << endl
        << AssertCommand(BooleanSimplification::negate(e)) << endl
        << CheckSatCommand() << endl
        << PopCommand() << endl;
  } else {
    out << "(check-sat)";
  }
}

static void toStream(std::ostream& out, const QuitCommand* c) {
  out << "(exit)";
}

static void toStream(std::ostream& out, const CommandSequence* c) {
  for(CommandSequence::const_iterator i = c->begin();
      i != c->end();
      ++i) {
    out << *i << endl;
  }
}

static void toStream(std::ostream& out, const DeclareFunctionCommand* c) {
  Type type = c->getType();
  out << "(declare-fun " << c->getSymbol() << " (";
  if(type.isFunction()) {
    FunctionType ft = type;
    const vector<Type> argTypes = ft.getArgTypes();
    if(argTypes.size() > 0) {
      copy( argTypes.begin(), argTypes.end() - 1,
            ostream_iterator<Type>(out, " ") );
      out << argTypes.back();
    }
    type = ft.getRangeType();
  }

  out << ") " << type << ")";
}

static void toStream(std::ostream& out, const DefineFunctionCommand* c) {
  Expr func = c->getFunction();
  const vector<Expr>& formals = c->getFormals();
  Expr formula = c->getFormula();
  out << "(define-fun " << func << " (";
  vector<Expr>::const_iterator i = formals.begin();
  for(;;) {
    out << "(" << (*i) << " " << (*i).getType() << ")";
    ++i;
    if(i != formals.end()) {
      out << " ";
    } else {
      break;
    }
  }
  out << ") " << FunctionType(func.getType()).getRangeType() << " " << formula << ")";
}

static void toStream(std::ostream& out, const DeclareTypeCommand* c) {
  out << "(declare-sort " << c->getSymbol() << " " << c->getArity() << ")";
}

static void toStream(std::ostream& out, const DefineTypeCommand* c) {
  const vector<Type>& params = c->getParameters();
  out << "(define-sort " << c->getSymbol() << " (";
  if(params.size() > 0) {
    copy( params.begin(), params.end() - 1,
          ostream_iterator<Type>(out, " ") );
    out << params.back();
  }
  out << ") " << c->getType() << ")";
}

static void toStream(std::ostream& out, const DefineNamedFunctionCommand* c) {
  out << "DefineNamedFunction( ";
  toStream(out, static_cast<const DefineFunctionCommand*>(c));
  out << " )";
  Unhandled("define named function command");
}

static void toStream(std::ostream& out, const SimplifyCommand* c) {
  out << "Simplify( << " << c->getTerm() << " >> )";
  Unhandled("simplify command");
}

static void toStream(std::ostream& out, const GetValueCommand* c) {
  out << "(get-value " << c->getTerm() << ")";
}

static void toStream(std::ostream& out, const GetAssignmentCommand* c) {
  out << "(get-assignment)";
}

static void toStream(std::ostream& out, const GetAssertionsCommand* c) {
  out << "(get-assertions)";
}

static void toStream(std::ostream& out, const SetBenchmarkStatusCommand* c) {
  out << "(set-info :status " << c->getStatus() << ")";
}

static void toStream(std::ostream& out, const SetBenchmarkLogicCommand* c) {
  out << "(set-logic " << c->getLogic() << ")";
}

static void toStream(std::ostream& out, const SetInfoCommand* c) {
  out << "(set-info " << c->getFlag() << " " << c->getSExpr() << ")";
}

static void toStream(std::ostream& out, const GetInfoCommand* c) {
  out << "(get-info " << c->getFlag() << ")";
}

static void toStream(std::ostream& out, const SetOptionCommand* c) {
  out << "(set-option " << c->getFlag() << " " << c->getSExpr() << ")";
}

static void toStream(std::ostream& out, const GetOptionCommand* c) {
  out << "(get-option " << c->getFlag() << ")";
}

static void toStream(std::ostream& out, const DatatypeDeclarationCommand* c) {
  const vector<DatatypeType>& datatypes = c->getDatatypes();
  out << "DatatypeDeclarationCommand([";
  for(vector<DatatypeType>::const_iterator i = datatypes.begin(),
        i_end = datatypes.end();
      i != i_end;
      ++i) {
    out << *i << ";" << endl;
  }
  out << "])";
  Unhandled("datatype declaration command");
}

static void toStream(std::ostream& out, const CommentCommand* c) {
  out << "(set-info :notes \"" << c->getComment() << "\")";
}

static void toStream(std::ostream& out, const EmptyCommand* c) {
}

template <class T>
static bool tryToStream(std::ostream& out, const Command* c) {
  if(typeid(*c) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(c));
    return true;
  }
  return false;
}

}/* CVC4::printer::smt2 namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

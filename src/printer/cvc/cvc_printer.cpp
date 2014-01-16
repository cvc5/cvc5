/*********************                                                        */
/*! \file cvc_printer.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Dejan Jovanovic
 ** Minor contributors (to current version): Francois Bobot, Liana Hadarean, Clark Barrett, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The pretty-printer interface for the CVC output language
 **
 ** The pretty-printer interface for the CVC output language.
 **/

#include "printer/cvc/cvc_printer.h"
#include "expr/expr.h" // for ExprSetDepth etc..
#include "util/language.h" // for LANG_AST
#include "expr/node_manager_attributes.h" // for VarNameAttr
#include "expr/command.h"
#include "theory/substitutions.h"
#include "smt/smt_engine.h"
#include "smt/options.h"
#include "theory/theory_model.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "printer/dagification_visitor.h"
#include "util/node_visitor.h"

#include <iostream>
#include <vector>
#include <string>
#include <typeinfo>
#include <algorithm>
#include <iterator>
#include <stack>

using namespace std;

namespace CVC4 {
namespace printer {
namespace cvc {

void CvcPrinter::toStream(std::ostream& out, TNode n, int toDepth, bool types, size_t dag) const throw() {
  if(dag != 0) {
    DagificationVisitor dv(dag);
    NodeVisitor<DagificationVisitor> visitor;
    visitor.run(dv, n);
    const theory::SubstitutionMap& lets = dv.getLets();
    if(!lets.empty()) {
      out << "LET ";
      bool first = true;
      for(theory::SubstitutionMap::const_iterator i = lets.begin();
          i != lets.end();
          ++i) {
        if(! first) {
          out << ", ";
        } else {
          first = false;
        }
        toStream(out, (*i).second, toDepth, types, false);
        out << " = ";
        toStream(out, (*i).first, toDepth, types, false);
      }
      out << " IN ";
    }
    Node body = dv.getDagifiedBody();
    toStream(out, body, toDepth, types, false);
  } else {
    toStream(out, n, toDepth, types, false);
  }
}

void CvcPrinter::toStream(std::ostream& out, TNode n, int depth, bool types, bool bracket) const throw() {
  if (depth == 0) {
    out << "(...)";
  } else {
    --depth;
  }

  // null
  if(n.getKind() == kind::NULL_EXPR) {
    out << "null";
    return;
  }

  // variables
  if(n.isVar()) {
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
      n.getType().toStream(out, language::output::LANG_CVC4);
    }
    return;
  }

  // constants
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
      if(rat.isIntegral()) {
        out << rat.getNumerator();
      } else {
        out << '(' << rat.getNumerator() << '/' << rat.getDenominator() << ')';
      }
      break;
    }
    case kind::SUBRANGE_TYPE:
      out << '[' << n.getConst<SubrangeBounds>() << ']';
      break;
    case kind::SUBTYPE_TYPE:
      out << "SUBTYPE(" << n.getConst<Predicate>() << ")";
      break;
    case kind::TYPE_CONSTANT:
      switch(TypeConstant tc = n.getConst<TypeConstant>()) {
      case REAL_TYPE:
        out << "REAL";
        break;
      case INTEGER_TYPE:
        out << "INT";
        break;
      case BOOLEAN_TYPE:
        out << "BOOLEAN";
        break;
      default:
        out << tc;
        break;
      }
      break;

    case kind::DATATYPE_TYPE:
      out << n.getConst<Datatype>().getName();
      break;

    default:
      // fall back on whatever operator<< does on underlying type; we
      // might luck out and print something reasonable
      kind::metakind::NodeValueConstPrinter::toStream(out, n);
    }

    return;
  }

  enum OpType {
    PREFIX,
    INFIX,
    POSTFIX
  } opType;

  //The default operation type is PREFIX
  opType = PREFIX;

  stringstream op;       // operation (such as '+')

  switch(n.getKind()) {

    // BUILTIN
    case kind::EQUAL:
      op << '=';
      opType = INFIX;
      break;
    case kind::ITE:
      out << "IF ";
      toStream(out, n[0], depth, types, true);
      out << " THEN ";
      toStream(out, n[1], depth, types, true);
      out << " ELSE ";
      toStream(out, n[2], depth, types, true);
      out << " ENDIF";
      return;
      break;
    case kind::TUPLE_TYPE:
    case kind::SEXPR_TYPE:
      out << '[';
      for (unsigned i = 0; i < n.getNumChildren(); ++ i) {
        if (i > 0) {
          out << ", ";
        }
        toStream(out, n[i], depth, types, false);
      }
      out << ']';
      return;
      break;
    case kind::SEXPR:
      // no-op
      break;
    case kind::LAMBDA:
      out << "(LAMBDA";
      toStream(out, n[0], depth, types, true);
      out << ": ";
      toStream(out, n[1], depth, types, true);
      out << ")";
      return;
      break;
    case kind::APPLY:
      toStream(op, n.getOperator(), depth, types, true);
      break;
    case kind::CHAIN:
    case kind::DISTINCT: // chain and distinct not supported directly in CVC4, blast them away with the rewriter
      toStream(out, theory::Rewriter::rewrite(n), depth, types, true);
      return;
    case kind::SORT_TYPE:
    {
      string name;
      if(n.getAttribute(expr::VarNameAttr(), name)) {
        out << name;
        return;
      }
    }
    break;

    // BOOL
    case kind::AND:
      op << "AND";
      opType = INFIX;
      break;
    case kind::OR:
      op << "OR";
      opType = INFIX;
      break;
    case kind::NOT:
      op << "NOT";
      opType = PREFIX;
      break;
    case kind::XOR:
      op << "XOR";
      opType = INFIX;
      break;
    case kind::IFF:
      op << "<=>";
      opType = INFIX;
      break;
    case kind::IMPLIES:
      op << "=>";
      opType = INFIX;
      break;

    // UF
    case kind::APPLY_UF:
      toStream(op, n.getOperator(), depth, types, false);
      break;
    case kind::CARDINALITY_CONSTRAINT:
    case kind::COMBINED_CARDINALITY_CONSTRAINT:
      out << "CARDINALITY_CONSTRAINT";
      break;

    case kind::FUNCTION_TYPE:
      if (n.getNumChildren() > 1) {
        if (n.getNumChildren() > 2) {
          out << '(';
        }
        for (unsigned i = 1; i < n.getNumChildren(); ++i) {
          if (i > 1) {
            out << ", ";
          }
          toStream(out, n[i - 1], depth, types, false);
        }
        if (n.getNumChildren() > 2) {
          out << ')';
        }
      }
      out << " -> ";
      toStream(out, n[n.getNumChildren() - 1], depth, types, false);
      return;
      break;

    // DATATYPES
    case kind::PARAMETRIC_DATATYPE:
      out << n[0].getConst<Datatype>().getName() << '[';
      for(unsigned i = 1; i < n.getNumChildren(); ++i) {
        if(i > 1) {
          out << ',';
        }
        out << n[i];
      }
      out << ']';
      return;
      break;
    case kind::APPLY_TYPE_ASCRIPTION: {
        toStream(out, n[0], depth, types, false);
        out << "::";
        TypeNode t = TypeNode::fromType(n.getOperator().getConst<AscriptionType>().getType());
        out << (t.isFunctionLike() ? t.getRangeType() : t);
      }
      return;
      break;
    case kind::APPLY_CONSTRUCTOR:
    case kind::APPLY_SELECTOR:
    case kind::APPLY_TESTER:
      toStream(op, n.getOperator(), depth, types, false);
      break;
    case kind::CONSTRUCTOR_TYPE:
    case kind::SELECTOR_TYPE:
      if(n.getNumChildren() > 1) {
        if(n.getNumChildren() > 2) {
          out << '(';
        }
        for(unsigned i = 0; i < n.getNumChildren() - 1; ++i) {
          if(i > 0) {
            out << ", ";
          }
          toStream(out, n[i], depth, types, false);
        }
        if(n.getNumChildren() > 2) {
          out << ')';
        }
        out << " -> ";
      }
      toStream(out, n[n.getNumChildren() - 1], depth, types, false);
      return;
    case kind::TESTER_TYPE:
      toStream(out, n[0], depth, types, false);
      out << " -> BOOLEAN";
      return;
      break;
    case kind::TUPLE_SELECT:
      toStream(out, n[0], depth, types, true);
      out << '.' << n.getOperator().getConst<TupleSelect>().getIndex();
      return;
      break;
    case kind::RECORD_SELECT:
      toStream(out, n[0], depth, types, true);
      out << '.' << n.getOperator().getConst<RecordSelect>().getField();
      return;
      break;
    case kind::TUPLE_UPDATE:
      toStream(out, n[0], depth, types, true);
      out << " WITH ." << n.getOperator().getConst<TupleUpdate>().getIndex() << " := ";
      toStream(out, n[1], depth, types, true);
      return;
      break;
    case kind::RECORD_UPDATE:
      toStream(out, n[0], depth, types, true);
      out << " WITH ." << n.getOperator().getConst<RecordUpdate>().getField() << " := ";
      toStream(out, n[1], depth, types, true);
      return;
      break;
    case kind::TUPLE:
      // no-op
      break;
    case kind::RECORD: {
      // (# _a := 2, _b := 2 #)
      const Record& rec = n.getOperator().getConst<Record>();
      out << "(# ";
      TNode::iterator i = n.begin();
      bool first = true;
      for(Record::const_iterator j = rec.begin(); j != rec.end(); ++i, ++j) {
        if(!first) {
          out << ", ";
        }
        out << (*j).first << " := ";
        toStream(out, *i, depth, types, false);
        first = false;
      }
      out << " #)";
      return;
      break;
    }

    // ARRAYS
    case kind::ARRAY_TYPE:
      out << "ARRAY ";
      toStream(out, n[0], depth, types, false);
      out << " OF ";
      toStream(out, n[1], depth, types, false);
      return;
      break;
    case kind::SELECT:
      toStream(out, n[0], depth, types, true);
      out << '[';
      toStream(out, n[1], depth, types, false);
      out << ']';
      return;
      break;
    case kind::STORE: {
      stack<TNode> stk;
      stk.push(n);
      while(stk.top()[0].getKind() == kind::STORE) {
        stk.push(stk.top()[0]);
      }
      if (bracket) {
        out << '(';
      }
      TNode x = stk.top();
      toStream(out, x[0], depth, types, false);
      out << " WITH [";
      toStream(out, x[1], depth, types, false);
      out << "] := ";
      toStream(out, x[2], depth, types, false);
      stk.pop();
      while(!stk.empty()) {
        x = stk.top();
        out << ", [";
        toStream(out, x[1], depth, types, false);
        out << "] := ";
        toStream(out, x[2], depth, types, false);
        stk.pop();
      }
      if (bracket) {
        out << ')';
      }
      return;
      break;
    }

    // ARITHMETIC
    case kind::PLUS:
      op << '+';
      opType = INFIX;
      break;
    case kind::MULT:
      op << '*';
      opType = INFIX;
      break;
    case kind::MINUS:
      op << '-';
      opType = INFIX;
      break;
    case kind::UMINUS:
      op << '-';
      opType = PREFIX;
      break;
    case kind::DIVISION:
      op << '/';
      opType = INFIX;
      break;
    case kind::INTS_DIVISION:
      op << "DIV";
      opType = INFIX;
      break;
    case kind::INTS_MODULUS:
      op << "MOD";
      opType = INFIX;
      break;
    case kind::LT:
      op << '<';
      opType = INFIX;
      break;
    case kind::LEQ:
      op << "<=";
      opType = INFIX;
      break;
    case kind::GT:
      op << '>';
      opType = INFIX;
      break;
    case kind::GEQ:
      op << ">=";
      opType = INFIX;
      break;

    // BITVECTORS
    case kind::BITVECTOR_XOR:
      op << "BVXOR";
      break;
    case kind::BITVECTOR_NAND:
      op << "BVNAND";
      break;
    case kind::BITVECTOR_NOR:
      op << "BVNOR";
      break;
    case kind::BITVECTOR_XNOR:
      op << "BVXNOR";
      break;
    case kind::BITVECTOR_COMP:
      op << "BVCOMP";
      break;
    case kind::BITVECTOR_UDIV:
      op << "BVUDIV";
      break;
    case kind::BITVECTOR_UDIV_TOTAL:
      op << "BVUDIV_TOTAL";
      break;
    case kind::BITVECTOR_UREM:
      op << "BVUREM";
      break;
    case kind::BITVECTOR_UREM_TOTAL:
      op << "BVUREM_TOTAL";
      break;
    case kind::BITVECTOR_SDIV:
      op << "BVSDIV";
      break;
    case kind::BITVECTOR_SREM:
      op << "BVSREM";
      break;
    case kind::BITVECTOR_SMOD:
      op << "BVSMOD";
      break;
    case kind::BITVECTOR_SHL:
      op << "BVSHL";
      break;
    case kind::BITVECTOR_LSHR:
      op << "BVLSHR";
      break;
    case kind::BITVECTOR_ASHR:
      op << "BVASHR";
      break;
    case kind::BITVECTOR_ULT:
      op << "BVLT";
      break;
    case kind::BITVECTOR_ULE:
      op << "BVLE";
      break;
    case kind::BITVECTOR_UGT:
      op << "BVGT";
      break;
    case kind::BITVECTOR_UGE:
      op << "BVGE";
      break;
    case kind::BITVECTOR_SLT:
      op << "BVSLT";
      break;
    case kind::BITVECTOR_SLE:
      op << "BVSLE";
      break;
    case kind::BITVECTOR_SGT:
      op << "BVSGT";
      break;
    case kind::BITVECTOR_SGE:
      op << "BVSGE";
      break;
    case kind::BITVECTOR_NEG:
      op << "BVUMINUS";
      break;
    case kind::BITVECTOR_NOT:
      op << "~";
      break;
    case kind::BITVECTOR_AND:
      op << "&";
      opType = INFIX;
      break;
    case kind::BITVECTOR_OR:
      op << "|";
      opType = INFIX;
      break;
    case kind::BITVECTOR_CONCAT:
      op << "@";
      opType = INFIX;
      break;
    case kind::BITVECTOR_PLUS: {
      //This interprets a BITVECTOR_PLUS as a bvadd in SMT-LIB
      Assert(n.getType().isBitVector());
      unsigned numc = n.getNumChildren()-2;
      unsigned child = 0;
      while (child < numc) {
        out << "BVPLUS(";
        out << BitVectorType(n.getType().toType()).getSize();
        out << ',';
        toStream(out, n[child], depth, types, false);
        out << ',';
        ++child;
      }
      out << "BVPLUS(";
      out << BitVectorType(n.getType().toType()).getSize();
      out << ',';
      toStream(out, n[child], depth, types, false);
      out << ',';
      toStream(out, n[child+1], depth, types, false);
      while (child > 0) {
        out << ')';
        --child;
      }
      out << ')';
      return;
      break;
    }
    case kind::BITVECTOR_SUB:
      out << "BVSUB(";
      Assert(n.getType().isBitVector());
      out << BitVectorType(n.getType().toType()).getSize();
      out << ',';
      toStream(out, n[0], depth, types, false);
      out << ',';
      toStream(out, n[1], depth, types, false);
      out << ')';
      return;
      break;
    case kind::BITVECTOR_MULT: {
      Assert(n.getType().isBitVector());
      unsigned numc = n.getNumChildren()-2;
      unsigned child = 0;
      while (child < numc) {
        out << "BVMULT(";
        out << BitVectorType(n.getType().toType()).getSize();
        out << ',';
        toStream(out, n[child], depth, types, false);
        out << ',';
        ++child;
        }
      out << "BVMULT(";
      out << BitVectorType(n.getType().toType()).getSize();
      out << ',';
      toStream(out, n[child], depth, types, false);
      out << ',';
      toStream(out, n[child+1], depth, types, false);
      while (child > 0) {
        out << ')';
        --child;
      }
      out << ')';
      return;
      break;
    }
    case kind::BITVECTOR_EXTRACT:
      op << n.getOperator().getConst<BitVectorExtract>();
      opType = POSTFIX;
      break;
    case kind::BITVECTOR_REPEAT:
      out << "BVREPEAT(";
      toStream(out, n[0], depth, types, false);
      out << ", " << n.getOperator().getConst<BitVectorRepeat>() << ')';
      return;
      break;
    case kind::BITVECTOR_ZERO_EXTEND:
      out << "BVZEROEXTEND(";
      toStream(out, n[0], depth, types, false);
      out << ", " << n.getOperator().getConst<BitVectorZeroExtend>() << ')';
      return;
      break;
    case kind::BITVECTOR_SIGN_EXTEND:
      out << "SX(";
      toStream(out, n[0], depth, types, false);
      out << ", " << n.getOperator().getConst<BitVectorSignExtend>() << ')';
      return;
      break;
    case kind::BITVECTOR_ROTATE_LEFT:
      out << "BVROTL(";
      toStream(out, n[0], depth, types, false);
      out << ", " << n.getOperator().getConst<BitVectorRotateLeft>() << ')';
      return;
      break;
    case kind::BITVECTOR_ROTATE_RIGHT:
      out << "BVROTR(";
      toStream(out, n[0], depth, types, false);
      out << ", " << n.getOperator().getConst<BitVectorRotateRight>() << ')';
      return;
      break;

    // Quantifiers
    case kind::FORALL:
      out << "(FORALL";
      toStream(out, n[0], depth, types, false);
      out << " : ";
      toStream(out, n[1], depth, types, false);
      out << ')';
      // TODO: user patterns?
      return;
    case kind::EXISTS:
      out << "(EXISTS";
      toStream(out, n[0], depth, types, false);
      out << " : ";
      toStream(out, n[1], depth, types, false);
      out << ')';
      // TODO: user patterns?
      return;
    case kind::INST_CONSTANT:
      out << "INST_CONSTANT";
      break;
    case kind::BOUND_VAR_LIST:
      out << '(';
      for(size_t i = 0; i < n.getNumChildren(); ++i) {
        if(i > 0) {
          out << ", ";
        }
        toStream(out, n[i], -1, true, false); // ascribe types
      }
      out << ')';
      return;
    case kind::INST_PATTERN:
      out << "INST_PATTERN";
      break;
    case kind::INST_PATTERN_LIST:
      out << "INST_PATTERN_LIST";
      break;

    default:
      Warning() << "Kind printing not implemented for the case of " << n.getKind() << endl;
      break;
  }

  switch (opType) {
  case PREFIX:
    out << op.str() << '(';
    break;
  case INFIX:
    if (bracket) {
      out << '(';
    }
    break;
  case POSTFIX:
    out << '(';
    break;
  }

  for (unsigned i = 0; i < n.getNumChildren(); ++ i) {
    if (i > 0) {
      if (opType == INFIX) {
        out << ' ' << op.str() << ' ';
      } else {
        out << ", ";
      }
    }
    toStream(out, n[i], depth, types, opType == INFIX);
  }

  switch (opType) {
    case PREFIX:
      out << ')';
      break;
    case INFIX:
      if (bracket) {
        out << ')';
      }
      break;
    case POSTFIX:
      out << ')' << op.str();
      break;
  }

}/* CvcPrinter::toStream(TNode) */

template <class T>
static bool tryToStream(std::ostream& out, const Command* c) throw();

void CvcPrinter::toStream(std::ostream& out, const Command* c,
                           int toDepth, bool types, size_t dag) const throw() {
  expr::ExprSetDepth::Scope sdScope(out, toDepth);
  expr::ExprPrintTypes::Scope ptScope(out, types);
  expr::ExprDag::Scope dagScope(out, dag);

  if(tryToStream<AssertCommand>(out, c) ||
     tryToStream<PushCommand>(out, c) ||
     tryToStream<PopCommand>(out, c) ||
     tryToStream<CheckSatCommand>(out, c) ||
     tryToStream<QueryCommand>(out, c) ||
     tryToStream<QuitCommand>(out, c) ||
     tryToStream<DeclarationSequence>(out, c) ||
     tryToStream<CommandSequence>(out, c) ||
     tryToStream<DeclareFunctionCommand>(out, c) ||
     tryToStream<DeclareTypeCommand>(out, c) ||
     tryToStream<DefineTypeCommand>(out, c) ||
     tryToStream<DefineNamedFunctionCommand>(out, c) ||
     tryToStream<DefineFunctionCommand>(out, c) ||
     tryToStream<SimplifyCommand>(out, c) ||
     tryToStream<GetValueCommand>(out, c) ||
     tryToStream<GetModelCommand>(out, c) ||
     tryToStream<GetAssignmentCommand>(out, c) ||
     tryToStream<GetAssertionsCommand>(out, c) ||
     tryToStream<GetProofCommand>(out, c) ||
     tryToStream<SetBenchmarkStatusCommand>(out, c) ||
     tryToStream<SetBenchmarkLogicCommand>(out, c) ||
     tryToStream<SetInfoCommand>(out, c) ||
     tryToStream<GetInfoCommand>(out, c) ||
     tryToStream<SetOptionCommand>(out, c) ||
     tryToStream<GetOptionCommand>(out, c) ||
     tryToStream<DatatypeDeclarationCommand>(out, c) ||
     tryToStream<CommentCommand>(out, c) ||
     tryToStream<EmptyCommand>(out, c) ||
     tryToStream<EchoCommand>(out, c)) {
    return;
  }

  out << "ERROR: don't know how to print a Command of class: "
      << typeid(*c).name() << endl;

}/* CvcPrinter::toStream(Command*) */

static inline void toStream(std::ostream& out, const SExpr& sexpr) throw() {
  Printer::getPrinter(language::output::LANG_CVC4)->toStream(out, sexpr);
}

template <class T>
static bool tryToStream(std::ostream& out, const CommandStatus* s) throw();

void CvcPrinter::toStream(std::ostream& out, const CommandStatus* s) const throw() {

  if(tryToStream<CommandSuccess>(out, s) ||
     tryToStream<CommandFailure>(out, s) ||
     tryToStream<CommandUnsupported>(out, s)) {
    return;
  }

  out << "ERROR: don't know how to print a CommandStatus of class: "
      << typeid(*s).name() << endl;

}/* CvcPrinter::toStream(CommandStatus*) */

void CvcPrinter::toStream(std::ostream& out, const Model& m, const Command* c) const throw() {
  const theory::TheoryModel& tm = (const theory::TheoryModel&) m;
  if(dynamic_cast<const DeclareTypeCommand*>(c) != NULL) {
    TypeNode tn = TypeNode::fromType( ((const DeclareTypeCommand*)c)->getType() );
    if( options::modelUninterpDtEnum() && tn.isSort() &&
        tm.d_rep_set.d_type_reps.find( tn )!=tm.d_rep_set.d_type_reps.end() ){
      out << "DATATYPE" << std::endl;
      out << "  " << dynamic_cast<const DeclareTypeCommand*>(c)->getSymbol() << " = ";
      for( size_t i=0; i<(*tm.d_rep_set.d_type_reps.find(tn)).second.size(); i++ ){
        if (i>0) {
          out << "| ";
        }
        out << (*tm.d_rep_set.d_type_reps.find(tn)).second[i] << " ";
      }
      out << std::endl << "END;" << std::endl;
    } else {
      if( tn.isSort() ){
        // print the cardinality
        if( tm.d_rep_set.d_type_reps.find( tn )!=tm.d_rep_set.d_type_reps.end() ){
          out << "% cardinality of " << tn << " is " << (*tm.d_rep_set.d_type_reps.find(tn)).second.size() << std::endl;
        }
      }
      out << c << std::endl;
      if( tn.isSort() ){
        // print the representatives
        if( tm.d_rep_set.d_type_reps.find( tn )!=tm.d_rep_set.d_type_reps.end() ){
          for( size_t i=0; i<(*tm.d_rep_set.d_type_reps.find(tn)).second.size(); i++ ){
            if( (*tm.d_rep_set.d_type_reps.find(tn)).second[i].isVar() ){
              out << (*tm.d_rep_set.d_type_reps.find(tn)).second[i] << " : " << tn << ";" << std::endl;
            }else{
              out << "% rep: " << (*tm.d_rep_set.d_type_reps.find(tn)).second[i] << std::endl;
            }
          }
        }
      }
    }
  } else if(dynamic_cast<const DeclareFunctionCommand*>(c) != NULL) {
    Node n = Node::fromExpr( ((const DeclareFunctionCommand*)c)->getFunction() );
    if(n.getKind() == kind::SKOLEM) {
      // don't print out internal stuff
      return;
    }
    TypeNode tn = n.getType();
    out << n << " : ";
    if( tn.isFunction() || tn.isPredicate() ){
      out << "(";
      for( size_t i=0; i<tn.getNumChildren()-1; i++ ){
        if( i>0 ) out << ", ";
        out << tn[i];
      }
      out << ") -> " << tn.getRangeType();
    }else{
      out << tn;
    }
    Node val = Node::fromExpr(tm.getSmtEngine()->getValue(n.toExpr()));
    if( options::modelUninterpDtEnum() && val.getKind() == kind::STORE ) {
      TypeNode tn = val[1].getType();
      if (tn.isSort() && tm.d_rep_set.d_type_reps.find( tn )!=tm.d_rep_set.d_type_reps.end() ){
        Cardinality indexCard((*tm.d_rep_set.d_type_reps.find(tn)).second.size());
        val = theory::arrays::TheoryArraysRewriter::normalizeConstant( val, indexCard );
      }
    }
    out << " = " << val << ";" << std::endl;

/*
    //for table format (work in progress)
    bool printedModel = false;
    if( tn.isFunction() ){
      if( options::modelFormatMode()==MODEL_FORMAT_MODE_TABLE ){
        //specialized table format for functions
        RepSetIterator riter( &d_rep_set );
        riter.setFunctionDomain( n );
        while( !riter.isFinished() ){
          std::vector< Node > children;
          children.push_back( n );
          for( int i=0; i<riter.getNumTerms(); i++ ){
            children.push_back( riter.getTerm( i ) );
          }
          Node nn = NodeManager::currentNM()->mkNode( APPLY_UF, children );
          Node val = getValue( nn );
          out << val << " ";
          riter.increment();
        }
        printedModel = true;
      }
    }
*/
  }else{
    out << c << std::endl;
  }
}

static void toStream(std::ostream& out, const AssertCommand* c) throw() {
  out << "ASSERT " << c->getExpr() << ";";
}

static void toStream(std::ostream& out, const PushCommand* c) throw() {
  out << "PUSH;";
}

static void toStream(std::ostream& out, const PopCommand* c) throw() {
  out << "POP;";
}

static void toStream(std::ostream& out, const CheckSatCommand* c) throw() {
  Expr e = c->getExpr();
  if(!e.isNull()) {
    out << "CHECKSAT " << e << ";";
  } else {
    out << "CHECKSAT;";
  }
}

static void toStream(std::ostream& out, const QueryCommand* c) throw() {
  Expr e = c->getExpr();
  if(!e.isNull()) {
    out << "QUERY " << e << ";";
  } else {
    out << "QUERY TRUE;";
  }
}

static void toStream(std::ostream& out, const QuitCommand* c) throw() {
  //out << "EXIT;";
}

static void toStream(std::ostream& out, const CommandSequence* c) throw() {
  for(CommandSequence::const_iterator i = c->begin();
      i != c->end();
      ++i) {
    out << *i << endl;
  }
}

static void toStream(std::ostream& out, const DeclarationSequence* c) throw() {
  DeclarationSequence::const_iterator i = c->begin();
  for(;;) {
    DeclarationDefinitionCommand* dd =
      static_cast<DeclarationDefinitionCommand*>(*i++);
    if(i != c->end()) {
      out << dd->getSymbol() << ", ";
    } else {
      out << *dd;
      break;
    }
  }
}

static void toStream(std::ostream& out, const DeclareFunctionCommand* c) throw() {
  out << c->getSymbol() << " : " << c->getType() << ";";
}

static void toStream(std::ostream& out, const DefineFunctionCommand* c) throw() {
  Expr func = c->getFunction();
  const vector<Expr>& formals = c->getFormals();
  Expr formula = c->getFormula();
  out << func << " : " << func.getType() << " = ";
  if(formals.size() > 0) {
    out << "LAMBDA(";
    vector<Expr>::const_iterator i = formals.begin();
    while(i != formals.end()) {
      out << (*i) << ":" << (*i).getType();
      if(++i != formals.end()) {
        out << ", ";
      }
    }
    out << "): ";
  }
  out << formula << ";";
}

static void toStream(std::ostream& out, const DeclareTypeCommand* c) throw() {
  if(c->getArity() > 0) {
    out << "ERROR: Don't know how to print parameterized type declaration "
           "in CVC language:" << endl << c->toString() << endl;
  } else {
    out << c->getSymbol() << " : TYPE;";
  }
}

static void toStream(std::ostream& out, const DefineTypeCommand* c) throw() {
  if(c->getParameters().size() > 0) {
    out << "ERROR: Don't know how to print parameterized type definition "
           "in CVC language:" << endl << c->toString() << endl;
  } else {
    out << c->getSymbol() << " : TYPE = " << c->getType() << ";";
  }
}

static void toStream(std::ostream& out, const DefineNamedFunctionCommand* c) throw() {
  toStream(out, static_cast<const DefineFunctionCommand*>(c));
}

static void toStream(std::ostream& out, const SimplifyCommand* c) throw() {
  out << "TRANSFORM " << c->getTerm() << ";";
}

static void toStream(std::ostream& out, const GetValueCommand* c) throw() {
  const vector<Expr>& terms = c->getTerms();
  Assert(!terms.empty());
  out << "GET_VALUE ";
  copy(terms.begin(), terms.end() - 1, ostream_iterator<Expr>(out, ";\nGET_VALUE "));
  out << terms.back() << ";";
}

static void toStream(std::ostream& out, const GetModelCommand* c) throw() {
  out << "COUNTERMODEL;";
}

static void toStream(std::ostream& out, const GetAssignmentCommand* c) throw() {
  out << "% (get-assignment)";
}

static void toStream(std::ostream& out, const GetAssertionsCommand* c) throw() {
  out << "WHERE;";
}

static void toStream(std::ostream& out, const GetProofCommand* c) throw() {
  out << "DUMP_PROOF;";
}

static void toStream(std::ostream& out, const SetBenchmarkStatusCommand* c) throw() {
  out << "% (set-info :status " << c->getStatus() << ")";
}

static void toStream(std::ostream& out, const SetBenchmarkLogicCommand* c) throw() {
  out << "OPTION \"logic\" \"" << c->getLogic() << "\";";
}

static void toStream(std::ostream& out, const SetInfoCommand* c) throw() {
  out << "% (set-info " << c->getFlag() << " ";
  toStream(out, c->getSExpr());
  out << ")";
}

static void toStream(std::ostream& out, const GetInfoCommand* c) throw() {
  out << "% (get-info " << c->getFlag() << ")";
}

static void toStream(std::ostream& out, const SetOptionCommand* c) throw() {
  out << "OPTION \"" << c->getFlag() << "\" ";
  toStream(out, c->getSExpr());
  out << ";";
}

static void toStream(std::ostream& out, const GetOptionCommand* c) throw() {
  out << "% (get-option " << c->getFlag() << ")";
}

static void toStream(std::ostream& out, const DatatypeDeclarationCommand* c) throw() {
  const vector<DatatypeType>& datatypes = c->getDatatypes();
  out << "DATATYPE" << endl;
  bool firstDatatype = true;
  for(vector<DatatypeType>::const_iterator i = datatypes.begin(),
        i_end = datatypes.end();
      i != i_end;
      ++i) {
    if(! firstDatatype) {
      out << ',' << endl;
    }
    const Datatype& dt = (*i).getDatatype();
    out << "  " << dt.getName();
    if(dt.isParametric()) {
      out << '[';
      for(size_t j = 0; j < dt.getNumParameters(); ++j) {
        if(j > 0) {
          out << ',';
        }
        out << dt.getParameter(j);
      }
      out << ']';
    }
    out << " = ";
    bool firstConstructor = true;
    for(Datatype::const_iterator j = dt.begin(); j != dt.end(); ++j) {
      if(! firstConstructor) {
        out << " | ";
      }
      firstConstructor = false;
      const DatatypeConstructor& c = *j;
      out << c.getName();
      if(c.getNumArgs() > 0) {
        out << '(';
        bool firstSelector = true;
        for(DatatypeConstructor::const_iterator k = c.begin(); k != c.end(); ++k) {
          if(! firstSelector) {
            out << ", ";
          }
          firstSelector = false;
          const DatatypeConstructorArg& selector = *k;
          out << selector.getName() << ": " << SelectorType(selector.getType()).getRangeType();
        }
        out << ')';
      }
    }
  }
  out << endl << "END;";
}

static void toStream(std::ostream& out, const CommentCommand* c) throw() {
  out << "% " << c->getComment();
}

static void toStream(std::ostream& out, const EmptyCommand* c) throw() {
}

static void toStream(std::ostream& out, const EchoCommand* c) throw() {
  out << "ECHO \"" << c->getOutput() << "\";";
}

template <class T>
static bool tryToStream(std::ostream& out, const Command* c) throw() {
  if(typeid(*c) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(c));
    return true;
  }
  return false;
}

static void toStream(std::ostream& out, const CommandSuccess* s) throw() {
  if(Command::printsuccess::getPrintSuccess(out)) {
    out << "OK" << endl;
  }
}

static void toStream(std::ostream& out, const CommandUnsupported* s) throw() {
  out << "UNSUPPORTED" << endl;
}

static void toStream(std::ostream& out, const CommandFailure* s) throw() {
  out << s->getMessage() << endl;
}

template <class T>
static bool tryToStream(std::ostream& out, const CommandStatus* s) throw() {
  if(typeid(*s) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(s));
    return true;
  }
  return false;
}

}/* CVC4::printer::cvc namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

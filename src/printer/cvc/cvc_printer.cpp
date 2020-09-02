/*********************                                                        */
/*! \file cvc_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the CVC output language
 **
 ** The pretty-printer interface for the CVC output language.
 **/

#include "printer/cvc/cvc_printer.h"

#include <algorithm>
#include <iostream>
#include <iterator>
#include <stack>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/dtype.h"
#include "expr/expr.h"  // for ExprSetDepth etc..
#include "expr/node_manager_attributes.h"  // for VarNameAttr
#include "expr/node_visitor.h"
#include "expr/sequence.h"
#include "options/language.h"  // for LANG_AST
#include "options/smt_options.h"
#include "printer/dagification_visitor.h"
#include "smt/command.h"
#include "smt/node_command.h"
#include "smt/smt_engine.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory_model.h"

using namespace std;

namespace CVC4 {
namespace printer {
namespace cvc {

void CvcPrinter::toStream(
    std::ostream& out, TNode n, int toDepth, bool types, size_t dag) const
{
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

void toStreamRational(std::ostream& out, Node n, bool forceRational)
{
  Assert(n.getKind() == kind::CONST_RATIONAL);
  const Rational& rat = n.getConst<Rational>();
  if (rat.isIntegral() && !forceRational)
  {
    out << rat.getNumerator();
  }
  else
  {
    out << '(' << rat.getNumerator() << '/' << rat.getDenominator() << ')';
  }
}

void CvcPrinter::toStream(
    std::ostream& out, TNode n, int depth, bool types, bool bracket) const
{
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
  if(n.isNullaryOp()) {
    if( n.getKind() == kind::UNIVERSE_SET ){
      out << "UNIVERSE :: " << n.getType();
    }else{
      //unknown printer
      out << n.getKind();
    }
    return;
  }

  // constants
  if(n.getMetaKind() == kind::metakind::CONSTANT) {
    switch(n.getKind()) {
    case kind::BITVECTOR_TYPE:
      out << "BITVECTOR(" << n.getConst<BitVectorSize>().d_size << ")";
      break;
    case kind::CONST_BITVECTOR: {
      const BitVector& bv = n.getConst<BitVector>();
      const Integer& x = bv.getValue();
      out << "0bin";
      unsigned size = bv.getSize();
      while (size-- > 0)
      {
        out << (x.testBit(size) ? '1' : '0');
      }
      break;
    }
    case kind::CONST_BOOLEAN:
      // the default would print "1" or "0" for bool, that's not correct
      // for our purposes
      out << (n.getConst<bool>() ? "TRUE" : "FALSE");
      break;
    case kind::CONST_RATIONAL: {
      toStreamRational(out, n, false);
      break;
    }
    case kind::CONST_STRING:
    {
      out << '"' << n.getConst<String>().toString() << '"';
      break;
    }
    case kind::CONST_SEQUENCE:
    {
      const Sequence& sn = n.getConst<Sequence>();
      const std::vector<Node>& snvec = sn.getVec();
      if (snvec.size() > 1)
      {
        out << "CONCAT(";
      }
      bool first = true;
      for (const Node& snvc : snvec)
      {
        if (!first)
        {
          out << ", ";
        }
        out << "SEQ_UNIT(" << snvc << ")";
        first = false;
      }
      if (snvec.size() > 1)
      {
        out << ")";
      }
      break;
    }
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
      case STRING_TYPE:
        out << "STRING";
        break;
      default:
        out << tc;
        break;
      }
      break;

    case kind::DATATYPE_TYPE: {
      const DType& dt = NodeManager::currentNM()->getDTypeForIndex(
          n.getConst<DatatypeIndexConstant>().getIndex());
      if( dt.isTuple() ){
        out << '[';
        for (unsigned i = 0; i < dt[0].getNumArgs(); ++ i) {
          if (i > 0) {
            out << ", ";
          }
          TypeNode t = dt[0][i].getRangeType();
          out << t;
        }
        out << ']';
      }
      else if (dt.isRecord())
      {
        out << "[# ";
        for (unsigned i = 0; i < dt[0].getNumArgs(); ++ i) {
          if (i > 0) {
            out << ", ";
          }
          TypeNode t = dt[0][i].getRangeType();
          out << dt[0][i].getSelector() << ":" << t;
        }
        out << " #]";
      }else{
        out << dt.getName();
      }
    }
      break;

    case kind::EMPTYSET:
      out << "{} :: " << n.getConst<EmptySet>().getType();
      break;

    case kind::STORE_ALL: {
      const ArrayStoreAll& asa = n.getConst<ArrayStoreAll>();
      out << "ARRAY(" << asa.getType().getArrayIndexType() << " OF "
          << asa.getType().getArrayConstituentType()
          << ") : " << asa.getValue();
      break;
    }

    default:
      // Fall back to whatever operator<< does on underlying type; we
      // might luck out and print something reasonable.
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
      if( n[0].getType().isBoolean() ){
        op << "<=>";
      }else{
        op << '=';
      }
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
    case kind::DISTINCT:
      // distinct not supported directly, blast it away with the rewriter
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
    case kind::PARAMETRIC_DATATYPE: {
      const DType& dt = NodeManager::currentNM()->getDTypeForIndex(
          n[0].getConst<DatatypeIndexConstant>().getIndex());
      out << dt.getName() << '[';
      for (unsigned i = 1; i < n.getNumChildren(); ++i)
      {
        if (i > 1)
        {
          out << ',';
        }
        out << n[i];
      }
        out << ']';
      }
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
    case kind::APPLY_CONSTRUCTOR: {
        TypeNode t = n.getType();
        if( t.isTuple() ){
          if( n.getNumChildren()==1 ){
            out << "TUPLE";
          }
        }
        else if (t.toType().isRecord())
        {
          const DType& dt = t.getDType();
          const DTypeConstructor& recCons = dt[0];
          out << "(# ";
          for (size_t i = 0, nargs = recCons.getNumArgs(); i < nargs; i++)
          {
            if (i != 0)
            {
              out << ", ";
            }
            out << recCons[i].getName() << " := ";
            toStream(out, n[i], depth, types, false);
          }
          out << " #)";
          return;
        }
        else
        {
          toStream(op, n.getOperator(), depth, types, false);
          if (n.getNumChildren() == 0)
          {
            // for datatype constants d, we print "d" and not "d()"
            out << op.str();
            return;
          }
        }
      }
      break;
    case kind::APPLY_SELECTOR:
    case kind::APPLY_SELECTOR_TOTAL: {
        TypeNode t = n[0].getType();
        Node opn = n.getOperator();
        if (!t.isDatatype())
        {
          toStream(op, opn, depth, types, false);
        }
        else if (t.isTuple() || t.isRecord())
        {
          toStream(out, n[0], depth, types, true);
          out << '.';
          const DType& dt = t.getDType();
          if (t.isTuple())
          {
            int sindex;
            if (n.getKind() == kind::APPLY_SELECTOR)
            {
              sindex = DType::indexOf(opn.toExpr());
            }
            else
            {
              sindex = dt[0].getSelectorIndexInternal(opn.toExpr());
            }
            Assert(sindex >= 0);
            out << sindex;
          }
          else
          {
            toStream(out, opn, depth, types, false);
          }
          return;
        }else{
          toStream(op, opn, depth, types, false);
        }
      }
      break;
    case kind::APPLY_TESTER: {
      Assert(!n.getType().isTuple() && !n.getType().toType().isRecord());
      op << "is_";
      unsigned cindex = DType::indexOf(n.getOperator());
      const DType& dt = DType::datatypeOf(n.getOperator());
      toStream(op, dt[cindex].getConstructor(), depth, types, false);
    }
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
    case kind::NONLINEAR_MULT:
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
    case kind::DIVISION_TOTAL:
      op << '/';
      opType = INFIX;
      break;
    case kind::INTS_DIVISION:
    case kind::INTS_DIVISION_TOTAL:
      op << "DIV";
      opType = INFIX;
      break;
    case kind::INTS_MODULUS:
    case kind::INTS_MODULUS_TOTAL:
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
    case kind::POW:
      op << '^';
      opType = INFIX;
      break;
    case kind::ABS:
      op << "ABS";
      opType = PREFIX;
      break;
    case kind::IS_INTEGER:
      op << "IS_INTEGER";
      opType = PREFIX;
      break;
    case kind::TO_INTEGER:
      op << "FLOOR";
      opType = PREFIX;
      break;
    case kind::TO_REAL:
      if (n[0].getKind() == kind::CONST_RATIONAL)
      {
        // print the constant as a rational
        toStreamRational(out, n[0], true);
      }
      else
      {
        // ignore, there is no to-real in CVC language
        toStream(out, n[0], depth, types, false);
      }
      return;
    case kind::DIVISIBLE:
      out << "DIVISIBLE(";
      toStream(out, n[0], depth, types, false);
      out << ", " << n.getOperator().getConst<Divisible>().k << ")";
      return;

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
      // This interprets a BITVECTOR_PLUS as a bvadd in SMT-LIB
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
      toStream(out, n[child + 1], depth, types, false);
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
      toStream(out, n[child + 1], depth, types, false);
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
    case kind::BITVECTOR_BITOF:
      op << n.getOperator().getConst<BitVectorBitOf>();
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
      out << ", " << BitVectorType(n.getType().toType()).getSize() << ')';
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

    // SETS
    case kind::SET_TYPE:
      out << "SET OF ";
      toStream(out, n[0], depth, types, false);
      return;
      break;
    case kind::UNION:
      op << '|';
      opType = INFIX;
      break;
    case kind::INTERSECTION:
      op << '&';
      opType = INFIX;
      break;
    case kind::SETMINUS:
      op << '-';
      opType = INFIX;
      break;
    case kind::SUBSET:
      op << "<=";
      opType = INFIX;
      break;
    case kind::MEMBER:
      op << "IS_IN";
      opType = INFIX;
      break;
    case kind::COMPLEMENT:
      op << "~";
      opType = PREFIX;
      break;
    case kind::PRODUCT:
      op << "PRODUCT";
      opType = INFIX;
      break;
    case kind::JOIN:
      op << "JOIN";
      opType = INFIX;
      break;
    case kind::TRANSPOSE:
      op << "TRANSPOSE";
      opType = PREFIX;
      break;
    case kind::TCLOSURE:
      op << "TCLOSURE";
      opType = PREFIX;
      break;
    case kind::IDEN:
      op << "IDEN";
      opType = PREFIX;
      break;
    case kind::JOIN_IMAGE:
      op << "JOIN_IMAGE";
      opType = INFIX;
      break;
    case kind::SINGLETON:
      out << "{";
      toStream(out, n[0], depth, types, false);
      out << "}";
      return;
      break;
    case kind::INSERT: {
      if(bracket) {
        out << '(';
      }
      out << '{';
      size_t i = 0;
      toStream(out, n[i++], depth, types, false);
      for(;i+1 < n.getNumChildren(); ++i) {
        out << ", ";
        toStream(out, n[i], depth, types, false);
      }
      out << "} | ";
      toStream(out, n[i], depth, types, true);
      if(bracket) {
        out << ')';
      }
      return;
      break;
    }
    case kind::CARD: {
      out << "CARD(";
      toStream(out, n[0], depth, types, false);
      out << ")";
      return;
      break;
    }

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

    // string operators
    case kind::STRING_CONCAT:
      out << "CONCAT";
      break;
    case kind::STRING_CHARAT:
      out << "CHARAT";
      break;
    case kind::STRING_LENGTH:
      out << "LENGTH";
      break;
    case kind::STRING_SUBSTR: out << "SUBSTR"; break;

    default:
      Warning() << "Kind printing not implemented for the case of " << n.getKind() << endl;
      break;
  }

  switch (opType) {
  case PREFIX:
    out << op.str();
    if (n.getNumChildren() > 0)
    {
      out << '(';
    }
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
      if (n.getNumChildren() > 0)
      {
        out << ')';
      }
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
static bool tryToStream(std::ostream& out, const Command* c, bool cvc3Mode);

template <class T>
static bool tryToStream(std::ostream& out,
                        const CommandStatus* s,
                        bool cvc3Mode);

void CvcPrinter::toStream(std::ostream& out, const CommandStatus* s) const
{
  if (tryToStream<CommandSuccess>(out, s, d_cvc3Mode)
      || tryToStream<CommandFailure>(out, s, d_cvc3Mode)
      || tryToStream<CommandRecoverableFailure>(out, s, d_cvc3Mode)
      || tryToStream<CommandUnsupported>(out, s, d_cvc3Mode)
      || tryToStream<CommandInterrupted>(out, s, d_cvc3Mode))
  {
    return;
  }

  out << "ERROR: don't know how to print a CommandStatus of class: "
      << typeid(*s).name() << endl;

}/* CvcPrinter::toStream(CommandStatus*) */

namespace {

void DeclareTypeNodeCommandToStream(std::ostream& out,
                                    const theory::TheoryModel& model,
                                    const DeclareTypeNodeCommand& command)
{
  TypeNode type_node = command.getType();
  const std::vector<Node>* type_reps =
      model.getRepSet()->getTypeRepsOrNull(type_node);
  if (options::modelUninterpDtEnum() && type_node.isSort()
      && type_reps != nullptr)
  {
    out << "DATATYPE" << std::endl;
    out << "  " << command.getSymbol() << " = ";
    for (size_t i = 0; i < type_reps->size(); i++)
    {
      if (i > 0)
      {
        out << "| ";
      }
      out << (*type_reps)[i] << " ";
    }
    out << std::endl << "END;" << std::endl;
  }
  else if (type_node.isSort() && type_reps != nullptr)
  {
    out << "% cardinality of " << type_node << " is " << type_reps->size()
        << std::endl;
    out << command << std::endl;
    for (Node type_rep : *type_reps)
    {
      if (type_rep.isVar())
      {
        out << type_rep << " : " << type_node << ";" << std::endl;
      }
      else
      {
        out << "% rep: " << type_rep << std::endl;
      }
    }
  }
  else
  {
    out << command << std::endl;
  }
}

void DeclareFunctionNodeCommandToStream(
    std::ostream& out,
    const theory::TheoryModel& model,
    const DeclareFunctionNodeCommand& command)
{
  Node n = command.getFunction();
  if (n.getKind() == kind::SKOLEM)
  {
    // don't print out internal stuff
    return;
  }
  TypeNode tn = n.getType();
  out << n << " : ";
  if (tn.isFunction() || tn.isPredicate())
  {
    out << "(";
    for (size_t i = 0; i < tn.getNumChildren() - 1; i++)
    {
      if (i > 0)
      {
        out << ", ";
      }
      out << tn[i];
    }
    out << ") -> " << tn.getRangeType();
  }
  else
  {
    out << tn;
  }
  Node val = model.getSmtEngine()->getValue(n);
  if (options::modelUninterpDtEnum() && val.getKind() == kind::STORE)
  {
    TypeNode type_node = val[1].getType();
    if (tn.isSort())
    {
      if (const std::vector<Node>* type_reps =
              model.getRepSet()->getTypeRepsOrNull(type_node))
      {
        Cardinality indexCard(type_reps->size());
        val = theory::arrays::TheoryArraysRewriter::normalizeConstant(
            val, indexCard);
      }
    }
  }
  out << " = " << val << ";" << std::endl;
}

}  // namespace

void CvcPrinter::toStream(std::ostream& out, const Model& m) const
{
  // print the model comments
  std::stringstream c;
  m.getComments(c);
  std::string ln;
  while (std::getline(c, ln))
  {
    out << "; " << ln << std::endl;
  }

  // print the model
  out << "MODEL BEGIN" << std::endl;
  this->Printer::toStream(out, m);
  out << "MODEL END;" << std::endl;
}

void CvcPrinter::toStream(std::ostream& out,
                          const Model& model,
                          const NodeCommand* command) const
{
  const auto* theory_model = dynamic_cast<const theory::TheoryModel*>(&model);
  AlwaysAssert(theory_model != nullptr);
  if (const auto* declare_type_command =
          dynamic_cast<const DeclareTypeNodeCommand*>(command))
  {
    DeclareTypeNodeCommandToStream(out, *theory_model, *declare_type_command);
  }
  else if (const auto* dfc =
               dynamic_cast<const DeclareFunctionNodeCommand*>(command))
  {
    DeclareFunctionNodeCommandToStream(out, *theory_model, *dfc);
  }
  else
  {
    out << *command << std::endl;
  }
}

void CvcPrinter::toStreamCmdAssert(std::ostream& out, Node n) const
{
  out << "ASSERT " << n << ';';
}

void CvcPrinter::toStreamCmdPush(std::ostream& out) const { out << "PUSH;"; }

void CvcPrinter::toStreamCmdPop(std::ostream& out) const { out << "POP;"; }

void CvcPrinter::toStreamCmdCheckSat(std::ostream& out, Node n) const
{
  if (d_cvc3Mode)
  {
    out << "PUSH; ";
  }
  if (!n.isNull())
  {
    out << "CHECKSAT " << n << ';';
  }
  else
  {
    out << "CHECKSAT;";
  }
  if (d_cvc3Mode)
  {
    out << " POP;";
  }
}

void CvcPrinter::toStreamCmdCheckSatAssuming(
    std::ostream& out, const std::vector<Node>& nodes) const
{
  if (d_cvc3Mode)
  {
    out << "PUSH; ";
  }
  out << "CHECKSAT";
  if (nodes.size() > 0)
  {
    out << ' ' << nodes[0];
    for (size_t i = 1, n = nodes.size(); i < n; ++i)
    {
      out << " AND " << nodes[i];
    }
  }
  out << ';';
  if (d_cvc3Mode)
  {
    out << " POP;";
  }
}

void CvcPrinter::toStreamCmdQuery(std::ostream& out, Node n) const
{
  if (d_cvc3Mode)
  {
    out << "PUSH; ";
  }
  if (!n.isNull())
  {
    out << "QUERY " << n << ';';
  }
  else
  {
    out << "QUERY TRUE;";
  }
  if (d_cvc3Mode)
  {
    out << " POP;";
  }
}

void CvcPrinter::toStreamCmdReset(std::ostream& out) const { out << "RESET;"; }

void CvcPrinter::toStreamCmdResetAssertions(std::ostream& out) const
{
  out << "RESET ASSERTIONS;";
}

void CvcPrinter::toStreamCmdQuit(std::ostream& out) const
{
  // out << "EXIT;";
}

void CvcPrinter::toStreamCmdCommandSequence(
    std::ostream& out, const std::vector<Command*>& sequence) const
{
  for (CommandSequence::const_iterator i = sequence.cbegin();
       i != sequence.cend();
       ++i)
  {
    out << *i << endl;
  }
}

void CvcPrinter::toStreamCmdDeclarationSequence(
    std::ostream& out, const std::vector<Command*>& sequence) const
{
  DeclarationSequence::const_iterator i = sequence.cbegin();
  for (;;)
  {
    DeclarationDefinitionCommand* dd =
        static_cast<DeclarationDefinitionCommand*>(*i++);
    if (i != sequence.cend())
    {
      out << dd->getSymbol() << ", ";
    }
    else
    {
      out << *dd;
      break;
    }
  }
}

void CvcPrinter::toStreamCmdDeclareFunction(std::ostream& out,
                                            const std::string& id,
                                            TypeNode type) const
{
  out << id << " : " << type << ';';
}

void CvcPrinter::toStreamCmdDefineFunction(std::ostream& out,
                                           const std::string& id,
                                           const std::vector<Node>& formals,
                                           TypeNode range,
                                           Node formula) const
{
  std::vector<TypeNode> sorts;
  sorts.reserve(formals.size() + 1);
  for (const Node& n : formals)
  {
    sorts.push_back(n.getType());
  }
  sorts.push_back(range);

  out << id << " : " << NodeManager::currentNM()->mkFunctionType(sorts)
      << " = ";
  if (formals.size() > 0)
  {
    out << "LAMBDA(";
    vector<Node>::const_iterator i = formals.cbegin();
    while (i != formals.end())
    {
      out << (*i) << ":" << (*i).getType();
      if (++i != formals.end())
      {
        out << ", ";
      }
    }
    out << "): ";
  }
  out << formula << ';';
}

void CvcPrinter::toStreamCmdDeclareType(std::ostream& out,
                                        const std::string& id,
                                        size_t arity,
                                        TypeNode type) const
{
  if (arity > 0)
  {
    // TODO?
    out << "ERROR: Don't know how to print parameterized type declaration "
           "in CVC language."
        << std::endl;
  }
  else
  {
    out << id << " : TYPE;";
  }
}

void CvcPrinter::toStreamCmdDefineType(std::ostream& out,
                                       const std::string& id,
                                       const std::vector<TypeNode>& params,
                                       TypeNode t) const
{
  if (params.size() > 0)
  {
    out << "ERROR: Don't know how to print parameterized type definition "
           "in CVC language:"
        << std::endl;
  }
  else
  {
    out << id << " : TYPE = " << t << ';';
  }
}

void CvcPrinter::toStreamCmdDefineNamedFunction(
    std::ostream& out,
    const std::string& id,
    const std::vector<Node>& formals,
    TypeNode range,
    Node formula) const
{
  toStreamCmdDefineFunction(out, id, formals, range, formula);
}

void CvcPrinter::toStreamCmdSimplify(std::ostream& out, Node n) const
{
  out << "TRANSFORM " << n << ';';
}

void CvcPrinter::toStreamCmdGetValue(std::ostream& out,
                                     const std::vector<Node>& nodes) const
{
  Assert(!nodes.empty());
  out << "GET_VALUE ";
  copy(nodes.begin(),
       nodes.end() - 1,
       ostream_iterator<Node>(out, ";\nGET_VALUE "));
  out << nodes.back() << ';';
}

void CvcPrinter::toStreamCmdGetModel(std::ostream& out) const
{
  out << "COUNTERMODEL;";
}

void CvcPrinter::toStreamCmdGetAssignment(std::ostream& out) const
{
  out << "% (get-assignment)";
}

void CvcPrinter::toStreamCmdGetAssertions(std::ostream& out) const
{
  out << "WHERE;";
}

void CvcPrinter::toStreamCmdGetProof(std::ostream& out) const
{
  out << "DUMP_PROOF;";
}

void CvcPrinter::toStreamCmdGetUnsatCore(std::ostream& out) const
{
  out << "DUMP_UNSAT_CORE;";
}

void CvcPrinter::toStreamCmdSetBenchmarkStatus(std::ostream& out,
                                               BenchmarkStatus status) const
{
  out << "% (set-info :status " << status << ')';
}

void CvcPrinter::toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                              const std::string& logic) const
{
  out << "OPTION \"logic\" \"" << logic << "\";";
}

void CvcPrinter::toStreamCmdSetInfo(std::ostream& out,
                                    const std::string& flag,
                                    SExpr sexpr) const
{
  out << "% (set-info " << flag << ' ';
  OutputLanguage language =
      d_cvc3Mode ? language::output::LANG_CVC3 : language::output::LANG_CVC4;
  SExpr::toStream(out, sexpr, language);
  out << ')';
}

void CvcPrinter::toStreamCmdGetInfo(std::ostream& out,
                                    const std::string& flag) const
{
  out << "% (get-info " << flag << ')';
}

void CvcPrinter::toStreamCmdSetOption(std::ostream& out,
                                      const std::string& flag,
                                      SExpr sexpr) const
{
  out << "OPTION \"" << flag << "\" ";
  SExpr::toStream(out, sexpr, language::output::LANG_CVC4);
  out << ';';
}

void CvcPrinter::toStreamCmdGetOption(std::ostream& out,
                                      const std::string& flag) const
{
  out << "% (get-option " << flag << ')';
}

void CvcPrinter::toStreamCmdDatatypeDeclaration(
    std::ostream& out, const std::vector<TypeNode>& datatypes) const
{
  Assert(!datatypes.empty() && datatypes[0].isDatatype());
  const DType& dt0 = datatypes[0].getDType();
  // do not print tuple/datatype internal declarations
  if (datatypes.size() != 1 || (!dt0.isTuple() && !dt0.isRecord()))
  {
    out << "DATATYPE" << endl;
    bool firstDatatype = true;
    for (const TypeNode& t : datatypes)
    {
      if (!firstDatatype)
      {
        out << ',' << endl;
      }
      const DType& dt = t.getDType();
      out << "  " << dt.getName();
      if (dt.isParametric())
      {
        out << '[';
        for (size_t j = 0; j < dt.getNumParameters(); ++j)
        {
          if (j > 0)
          {
            out << ',';
          }
          out << dt.getParameter(j);
        }
        out << ']';
      }
      out << " = ";
      for (size_t j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
      {
        const DTypeConstructor& cons = dt[j];
        if (j != 0)
        {
          out << " | ";
        }
        out << cons.getName();
        if (cons.getNumArgs() > 0)
        {
          out << '(';
          for (size_t k = 0, nargs = cons.getNumArgs(); k < nargs; k++)
          {
            if (k != 0)
            {
              out << ", ";
            }
            const DTypeSelector& selector = cons[k];
            TypeNode tr = selector.getRangeType();
            if (tr.isDatatype())
            {
              const DType& sdt = tr.getDType();
              out << selector.getName() << ": " << sdt.getName();
            }
            else
            {
              out << selector.getName() << ": " << tr;
            }
          }
          out << ')';
        }
      }
      firstDatatype = false;
    }
    out << endl << "END;";
  }
}

void CvcPrinter::toStreamCmdComment(std::ostream& out,
                                    const std::string& comment) const
{
  out << "% " << comment;
}

void CvcPrinter::toStreamCmdEmpty(std::ostream& out,
                                  const std::string& name) const
{
}

void CvcPrinter::toStreamCmdEcho(std::ostream& out,
                                 const std::string& output) const
{
  out << "ECHO \"" << output << "\";";
}

template <class T>
static bool tryToStream(std::ostream& out, const Command* c, bool cvc3Mode)
{
  if(typeid(*c) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(c), cvc3Mode);
    return true;
  }
  return false;
}

static void toStream(std::ostream& out, const CommandSuccess* s, bool cvc3Mode)
{
  if(Command::printsuccess::getPrintSuccess(out)) {
    out << "OK" << endl;
  }
}

static void toStream(std::ostream& out,
                     const CommandUnsupported* s,
                     bool cvc3Mode)
{
  out << "UNSUPPORTED" << endl;
}

static void toStream(std::ostream& out,
                     const CommandInterrupted* s,
                     bool cvc3Mode)
{
  out << "INTERRUPTED" << endl;
}

static void toStream(std::ostream& out, const CommandFailure* s, bool cvc3Mode)
{
  out << s->getMessage() << endl;
}

static void toStream(std::ostream& out,
                     const CommandRecoverableFailure* s,
                     bool cvc3Mode)
{
  out << s->getMessage() << endl;
}

template <class T>
static bool tryToStream(std::ostream& out,
                        const CommandStatus* s,
                        bool cvc3Mode)
{
  if(typeid(*s) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(s), cvc3Mode);
    return true;
  }
  return false;
}

}/* CVC4::printer::cvc namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

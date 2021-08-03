/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The pretty-printer interface for the CVC output language.
 */

#include "printer/cvc/cvc_printer.h"

#include <algorithm>
#include <iostream>
#include <iterator>
#include <stack>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/array_store_all.h"
#include "expr/ascription_type.h"
#include "expr/datatype_index.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/dtype_selector.h"
#include "expr/emptyset.h"
#include "expr/node_manager_attributes.h"  // for VarNameAttr
#include "expr/node_visitor.h"
#include "expr/sequence.h"
#include "options/language.h"  // for LANG_AST
#include "options/smt_options.h"
#include "printer/let_binding.h"
#include "smt/command.h"
#include "smt/node_command.h"
#include "smt/smt_engine.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory_model.h"
#include "util/bitvector.h"
#include "util/divisible.h"
#include "util/rational.h"
#include "util/string.h"

using namespace std;

namespace cvc5 {
namespace printer {
namespace cvc {

void CvcPrinter::toStream(std::ostream& out,
                          TNode n,
                          int toDepth,
                          size_t dag) const
{
  if(dag != 0) {
    LetBinding lbind(dag + 1);
    toStreamNodeWithLetify(out, n, toDepth, false, &lbind);
  } else {
    toStreamNode(out, n, toDepth, false, nullptr);
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

void CvcPrinter::toStreamNode(std::ostream& out,
                              TNode n,
                              int depth,
                              bool bracket,
                              LetBinding* lbind) const
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
      toStreamNode(out, n[0], depth, true, lbind);
      out << " THEN ";
      toStreamNode(out, n[1], depth, true, lbind);
      out << " ELSE ";
      toStreamNode(out, n[2], depth, true, lbind);
      out << " ENDIF";
      return;
      break;
    case kind::SEXPR:
      // no-op
      break;
    case kind::LAMBDA:
      out << "(LAMBDA";
      toStreamNode(out, n[0], depth, true, lbind);
      out << ": ";
      toStreamNodeWithLetify(out, n[1], depth, true, lbind);
      out << ")";
      return;
      break;
    case kind::WITNESS:
      out << "(WITNESS";
      toStreamNode(out, n[0], depth, true, lbind);
      out << " : ";
      toStreamNodeWithLetify(out, n[1], depth, true, lbind);
      out << ')';
      return;
    case kind::DISTINCT:
      // distinct not supported directly, blast it away with the rewriter
      toStreamNode(out, theory::Rewriter::rewrite(n), depth, true, lbind);
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
      toStreamNode(op, n.getOperator(), depth, false, lbind);
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
          toStreamNode(out, n[i - 1], depth, false, lbind);
        }
        if (n.getNumChildren() > 2) {
          out << ')';
        }
      }
      out << " -> ";
      toStreamNode(out, n[n.getNumChildren() - 1], depth, false, lbind);
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
      toStreamNode(out, n[0], depth, false, lbind);
      out << "::";
      TypeNode t = n.getOperator().getConst<AscriptionType>().getType();
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
        else if (t.isRecord())
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
            toStreamNode(out, n[i], depth, false, lbind);
          }
          out << " #)";
          return;
        }
        else
        {
          toStreamNode(op, n.getOperator(), depth, false, lbind);
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
          toStreamNode(op, opn, depth, false, lbind);
        }
        else if (t.isTuple() || t.isRecord())
        {
          toStreamNode(out, n[0], depth, true, lbind);
          out << '.';
          const DType& dt = t.getDType();
          if (t.isTuple())
          {
            int sindex;
            if (n.getKind() == kind::APPLY_SELECTOR)
            {
              sindex = DType::indexOf(opn);
            }
            else
            {
              sindex = dt[0].getSelectorIndexInternal(opn);
            }
            Assert(sindex >= 0);
            out << sindex;
          }
          else
          {
            toStreamNode(out, opn, depth, false, lbind);
          }
          return;
        }else{
          toStreamNode(op, opn, depth, false, lbind);
        }
      }
      break;
    case kind::APPLY_TESTER: {
      Assert(!n.getType().isTuple() && !n.getType().isRecord());
      op << "is_";
      unsigned cindex = DType::indexOf(n.getOperator());
      const DType& dt = DType::datatypeOf(n.getOperator());
      toStreamNode(op, dt[cindex].getConstructor(), depth, false, lbind);
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
          toStreamNode(out, n[i], depth, false, lbind);
        }
        if(n.getNumChildren() > 2) {
          out << ')';
        }
        out << " -> ";
      }
      toStreamNode(out, n[n.getNumChildren() - 1], depth, false, lbind);
      return;
    case kind::TESTER_TYPE:
      toStreamNode(out, n[0], depth, false, lbind);
      out << " -> BOOLEAN";
      return;
      break;

    // ARRAYS
    case kind::ARRAY_TYPE:
      out << "ARRAY ";
      toStreamNode(out, n[0], depth, false, lbind);
      out << " OF ";
      toStreamNode(out, n[1], depth, false, lbind);
      return;
      break;
    case kind::SELECT:
      toStreamNode(out, n[0], depth, true, lbind);
      out << '[';
      toStreamNode(out, n[1], depth, false, lbind);
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
      toStreamNode(out, x[0], depth, false, lbind);
      out << " WITH [";
      toStreamNode(out, x[1], depth, false, lbind);
      out << "] := ";
      toStreamNode(out, x[2], depth, false, lbind);
      stk.pop();
      while(!stk.empty()) {
        x = stk.top();
        out << ", [";
        toStreamNode(out, x[1], depth, false, lbind);
        out << "] := ";
        toStreamNode(out, x[2], depth, false, lbind);
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
    case kind::CAST_TO_REAL:
    {
      if (n[0].getKind() == kind::CONST_RATIONAL)
      {
        // print the constant as a rational
        toStreamRational(out, n[0], true);
      }
      else
      {
        // ignore, there is no to-real in CVC language
        toStreamNode(out, n[0], depth, false, lbind);
      }
      return;
    }
    case kind::DIVISIBLE:
      out << "DIVISIBLE(";
      toStreamNode(out, n[0], depth, false, lbind);
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
    case kind::BITVECTOR_UREM:
      op << "BVUREM";
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
    case kind::BITVECTOR_ADD:
    {
      // This interprets a BITVECTOR_ADD as a bvadd in SMT-LIB
      Assert(n.getType().isBitVector());
      unsigned numc = n.getNumChildren()-2;
      unsigned child = 0;
      while (child < numc) {
        out << "BVPLUS(";
        out << n.getType().getBitVectorSize();
        out << ',';
        toStreamNode(out, n[child], depth, false, lbind);
        out << ',';
        ++child;
      }
      out << "BVPLUS(";
      out << n.getType().getBitVectorSize();
      out << ',';
      toStreamNode(out, n[child], depth, false, lbind);
      out << ',';
      toStreamNode(out, n[child + 1], depth, false, lbind);
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
      out << n.getType().getBitVectorSize();
      out << ',';
      toStreamNode(out, n[0], depth, false, lbind);
      out << ',';
      toStreamNode(out, n[1], depth, false, lbind);
      out << ')';
      return;
      break;
    case kind::BITVECTOR_MULT: {
      Assert(n.getType().isBitVector());
      unsigned numc = n.getNumChildren()-2;
      unsigned child = 0;
      while (child < numc) {
        out << "BVMULT(";
        out << n.getType().getBitVectorSize();
        out << ',';
        toStreamNode(out, n[child], depth, false, lbind);
        out << ',';
        ++child;
        }
      out << "BVMULT(";
      out << n.getType().getBitVectorSize();
      out << ',';
      toStreamNode(out, n[child], depth, false, lbind);
      out << ',';
      toStreamNode(out, n[child + 1], depth, false, lbind);
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
      toStreamNode(out, n[0], depth, false, lbind);
      out << ", " << n.getOperator().getConst<BitVectorRepeat>() << ')';
      return;
      break;
    case kind::BITVECTOR_ZERO_EXTEND:
      out << "BVZEROEXTEND(";
      toStreamNode(out, n[0], depth, false, lbind);
      out << ", " << n.getOperator().getConst<BitVectorZeroExtend>() << ')';
      return;
      break;
    case kind::BITVECTOR_SIGN_EXTEND:
      out << "SX(";
      toStreamNode(out, n[0], depth, false, lbind);
      out << ", " << n.getType().getBitVectorSize() << ')';
      return;
      break;
    case kind::BITVECTOR_ROTATE_LEFT:
      out << "BVROTL(";
      toStreamNode(out, n[0], depth, false, lbind);
      out << ", " << n.getOperator().getConst<BitVectorRotateLeft>() << ')';
      return;
      break;
    case kind::BITVECTOR_ROTATE_RIGHT:
      out << "BVROTR(";
      toStreamNode(out, n[0], depth, false, lbind);
      out << ", " << n.getOperator().getConst<BitVectorRotateRight>() << ')';
      return;
      break;

    // SETS
    case kind::SET_TYPE:
      out << "SET OF ";
      toStreamNode(out, n[0], depth, false, lbind);
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
      toStreamNode(out, n[0], depth, false, lbind);
      out << "}";
      return;
      break;
    case kind::INSERT: {
      if(bracket) {
        out << '(';
      }
      out << '{';
      size_t i = 0;
      toStreamNode(out, n[i++], depth, false, lbind);
      for(;i+1 < n.getNumChildren(); ++i) {
        out << ", ";
        toStreamNode(out, n[i], depth, false, lbind);
      }
      out << "} | ";
      toStreamNode(out, n[i], depth, true, lbind);
      if(bracket) {
        out << ')';
      }
      return;
      break;
    }
    case kind::CARD: {
      out << "CARD(";
      toStreamNode(out, n[0], depth, false, lbind);
      out << ")";
      return;
      break;
    }

    // Quantifiers
    case kind::FORALL:
      out << "(FORALL";
      toStreamNode(out, n[0], depth, true, lbind);
      out << " : ";
      toStreamNodeWithLetify(out, n[1], depth, true, lbind);
      out << ')';
      // TODO: user patterns?
      return;
    case kind::EXISTS:
      out << "(EXISTS";
      toStreamNode(out, n[0], depth, true, lbind);
      out << " : ";
      toStreamNodeWithLetify(out, n[1], depth, true, lbind);
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
        toStreamNode(out, n[i], -1, false, lbind);
        out << ":";
        n[i].getType().toStream(out, language::output::LANG_CVC);
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
    toStreamNode(out, n[i], depth, opType == INFIX, lbind);
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
}

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

void CvcPrinter::toStreamModelSort(std::ostream& out,
                                   const smt::Model& m,
                                   TypeNode tn) const
{
  if (!tn.isSort())
  {
    out << "ERROR: don't know how to print a non uninterpreted sort in model: "
        << tn << std::endl;
    return;
  }
  const theory::TheoryModel* tm = m.getTheoryModel();
  const std::vector<Node>* type_reps = tm->getRepSet()->getTypeRepsOrNull(tn);
  if (options::modelUninterpPrint() == options::ModelUninterpPrintMode::DtEnum
      && type_reps != nullptr)
  {
    out << "DATATYPE" << std::endl;
    out << "  " << tn << " = ";
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
  else if (type_reps != nullptr)
  {
    out << "% cardinality of " << tn << " is " << type_reps->size()
        << std::endl;
    toStreamCmdDeclareType(out, tn);
    for (Node type_rep : *type_reps)
    {
      if (type_rep.isVar())
      {
        out << type_rep << " : " << tn << ";" << std::endl;
      }
      else
      {
        out << "% rep: " << type_rep << std::endl;
      }
    }
  }
  else
  {
    toStreamCmdDeclareType(out, tn);
  }
}

void CvcPrinter::toStreamModelTerm(std::ostream& out,
                                   const smt::Model& m,
                                   Node n) const
{
  const theory::TheoryModel* tm = m.getTheoryModel();
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
  // We get the value from the theory model directly, which notice
  // does not have to go through the standard SmtEngine::getValue interface.
  Node val = tm->getValue(n);
  if (options::modelUninterpPrint() == options::ModelUninterpPrintMode::DtEnum
      && val.getKind() == kind::STORE)
  {
    TypeNode type_node = val[1].getType();
    if (tn.isSort())
    {
      const std::vector<Node>* type_reps =
          tm->getRepSet()->getTypeRepsOrNull(type_node);
      if (type_reps != nullptr)
      {
        Cardinality indexCard(type_reps->size());
        val = theory::arrays::TheoryArraysRewriter::normalizeConstant(
            val, indexCard);
      }
    }
  }
  out << " = " << val << ";" << std::endl;
}

void CvcPrinter::toStream(std::ostream& out, const smt::Model& m) const
{
  const theory::TheoryModel* tm = m.getTheoryModel();
  // print the model comments
  std::stringstream c;
  tm->getComments(c);
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

void CvcPrinter::toStreamCmdAssert(std::ostream& out, Node n) const
{
  out << "ASSERT " << n << ';' << std::endl;
}

void CvcPrinter::toStreamCmdPush(std::ostream& out) const
{
  out << "PUSH;" << std::endl;
}

void CvcPrinter::toStreamCmdPop(std::ostream& out) const
{
  out << "POP;" << std::endl;
}

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
  out << std::endl;
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
  out << std::endl;
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
  out << std::endl;
}

void CvcPrinter::toStreamCmdReset(std::ostream& out) const
{
  out << "RESET;" << std::endl;
}

void CvcPrinter::toStreamCmdResetAssertions(std::ostream& out) const
{
  out << "RESET ASSERTIONS;" << std::endl;
}

void CvcPrinter::toStreamCmdQuit(std::ostream& out) const
{
  // out << "EXIT;" << std::endl;
}

void CvcPrinter::toStreamCmdCommandSequence(
    std::ostream& out, const std::vector<Command*>& sequence) const
{
  for (CommandSequence::const_iterator i = sequence.cbegin();
       i != sequence.cend();
       ++i)
  {
    out << *i;
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
    Assert(dd != nullptr);
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
  out << std::endl;
}

void CvcPrinter::toStreamCmdDeclareFunction(std::ostream& out,
                                            const std::string& id,
                                            TypeNode type) const
{
  out << id << " : " << type << ';' << std::endl;
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
  out << formula << ';' << std::endl;
}

void CvcPrinter::toStreamCmdDeclareType(std::ostream& out,
                                        TypeNode type) const
{
  size_t arity = type.isSortConstructor() ? type.getSortConstructorArity() : 0;
  if (arity > 0)
  {
    out << "ERROR: Don't know how to print parameterized type declaration "
           "in CVC language."
        << std::endl;
  }
  else
  {
    out << type << " : TYPE;" << std::endl;
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
    out << id << " : TYPE = " << t << ';' << std::endl;
  }
}

void CvcPrinter::toStreamCmdSimplify(std::ostream& out, Node n) const
{
  out << "TRANSFORM " << n << ';' << std::endl;
}

void CvcPrinter::toStreamCmdGetValue(std::ostream& out,
                                     const std::vector<Node>& nodes) const
{
  Assert(!nodes.empty());
  out << "GET_VALUE ";
  copy(nodes.begin(),
       nodes.end() - 1,
       ostream_iterator<Node>(out, ";\nGET_VALUE "));
  out << nodes.back() << ';' << std::endl;
}

void CvcPrinter::toStreamCmdGetModel(std::ostream& out) const
{
  out << "COUNTERMODEL;" << std::endl;
}

void CvcPrinter::toStreamCmdGetAssignment(std::ostream& out) const
{
  out << "% (get-assignment)" << std::endl;
}

void CvcPrinter::toStreamCmdGetAssertions(std::ostream& out) const
{
  out << "WHERE;" << std::endl;
}

void CvcPrinter::toStreamCmdGetProof(std::ostream& out) const
{
  out << "DUMP_PROOF;" << std::endl;
}

void CvcPrinter::toStreamCmdGetUnsatCore(std::ostream& out) const
{
  out << "DUMP_UNSAT_CORE;" << std::endl;
}

void CvcPrinter::toStreamCmdSetBenchmarkStatus(std::ostream& out,
                                               Result::Sat status) const
{
  out << "% (set-info :status " << status << ')' << std::endl;
}

void CvcPrinter::toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                              const std::string& logic) const
{
  out << "OPTION \"logic\" \"" << logic << "\";" << std::endl;
}

void CvcPrinter::toStreamCmdSetInfo(std::ostream& out,
                                    const std::string& flag,
                                    const std::string& value) const
{
  out << "% (set-info " << flag << ' ' << value << ')' << std::endl;
}

void CvcPrinter::toStreamCmdGetInfo(std::ostream& out,
                                    const std::string& flag) const
{
  out << "% (get-info " << flag << ')' << std::endl;
}

void CvcPrinter::toStreamCmdSetOption(std::ostream& out,
                                      const std::string& flag,
                                      const std::string& value) const
{
  out << "OPTION \"" << flag << "\" " << value << ';' << std::endl;
}

void CvcPrinter::toStreamCmdGetOption(std::ostream& out,
                                      const std::string& flag) const
{
  out << "% (get-option " << flag << ')' << std::endl;
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
    out << endl << "END;" << std::endl;
  }
}

void CvcPrinter::toStreamCmdComment(std::ostream& out,
                                    const std::string& comment) const
{
  out << "% " << comment << std::endl;
}

void CvcPrinter::toStreamCmdEmpty(std::ostream& out,
                                  const std::string& name) const
{
  out << std::endl;
}

void CvcPrinter::toStreamCmdEcho(std::ostream& out,
                                 const std::string& output) const
{
  out << "ECHO \"" << output << "\";" << std::endl;
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

void CvcPrinter::toStreamNodeWithLetify(std::ostream& out,
                                        Node n,
                                        int toDepth,
                                        bool bracket,
                                        LetBinding* lbind) const
{
  if (lbind == nullptr)
  {
    toStreamNode(out, n, toDepth, bracket, nullptr);
    return;
  }
  std::vector<Node> letList;
  lbind->letify(n, letList);
  if (!letList.empty())
  {
    std::map<Node, uint32_t>::const_iterator it;
    out << "LET ";
    bool first = true;
    for (size_t i = 0, nlets = letList.size(); i < nlets; i++)
    {
      if (!first)
      {
        out << ", ";
      }
      else
      {
        first = false;
      }
      Node nl = letList[i];
      uint32_t id = lbind->getId(nl);
      out << "_let_" << id << " = ";
      Node nlc = lbind->convert(nl, "_let_", false);
      toStreamNode(out, nlc, toDepth, true, lbind);
    }
    out << " IN ";
  }
  Node nc = lbind->convert(n, "_let_");
  // print the body, passing the lbind object
  toStreamNode(out, nc, toDepth, bracket, lbind);
  lbind->popScope();
}

}  // namespace cvc
}  // namespace printer
}  // namespace cvc5

/*********************                                                        */
/*! \file smt2_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the SMT2 output language
 **
 ** The pretty-printer interface for the SMT2 output language.
 **/

#include "printer/smt2/smt2_printer.h"

#include <iostream>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/node_manager_attributes.h"
#include "options/language.h"
#include "options/smt_options.h"
#include "printer/dagification_visitor.h"
#include "smt/smt_engine.h"
#include "smt_util/boolean_simplification.h"
#include "smt_util/node_visitor.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/substitutions.h"
#include "theory/theory_model.h"
#include "util/smt2_quote_string.h"

using namespace std;

namespace CVC4 {
namespace printer {
namespace smt2 {

static OutputLanguage variantToLanguage(Variant v);

static string smtKindString(Kind k);

static void printBvParameterizedOp(std::ostream& out, TNode n);
static void printFpParameterizedOp(std::ostream& out, TNode n);

static void toStreamRational(std::ostream& out,
                             const Rational& r,
                             bool decimal);

void Smt2Printer::toStream(
    std::ostream& out, TNode n, int toDepth, bool types, size_t dag) const
{
  if(dag != 0) {
    DagificationVisitor dv(dag);
    NodeVisitor<DagificationVisitor> visitor;
    visitor.run(dv, n);
    const theory::SubstitutionMap& lets = dv.getLets();
    if(!lets.empty()) {
      theory::SubstitutionMap::const_iterator i = lets.begin();
      theory::SubstitutionMap::const_iterator i_end = lets.end();
      for(; i != i_end; ++ i) {
        out << "(let ((";
        toStream(out, (*i).second, toDepth, types, TypeNode::null());
        out << ' ';
        toStream(out, (*i).first, toDepth, types, TypeNode::null());
        out << ")) ";
      }
    }
    Node body = dv.getDagifiedBody();
    toStream(out, body, toDepth, types, TypeNode::null());
    if(!lets.empty()) {
      theory::SubstitutionMap::const_iterator i = lets.begin();
      theory::SubstitutionMap::const_iterator i_end = lets.end();
      for(; i != i_end; ++ i) {
        out << ")";
      }
    }
  } else {
    toStream(out, n, toDepth, types, TypeNode::null());
  }
}

static std::string maybeQuoteSymbol(const std::string& s) {
  // this is the set of SMT-LIBv2 permitted characters in "simple" (non-quoted) symbols
  if(s.find_first_not_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789~!@$%^&*_-+=<>.?/") != string::npos) {
    // need to quote it
    stringstream ss;
    ss << '|' << s << '|';
    return ss.str();
  }
  return s;
}

static bool stringifyRegexp(Node n, stringstream& ss) {
  if(n.getKind() == kind::STRING_TO_REGEXP) {
    ss << n[0].getConst<String>().toString(true);
  } else if(n.getKind() == kind::REGEXP_CONCAT) {
    for(unsigned i = 0; i < n.getNumChildren(); ++i) {
      if(!stringifyRegexp(n[i], ss)) {
        return false;
      }
    }
  } else {
    return false;
  }
  return true;
}

// force_nt is the type that n must have
void Smt2Printer::toStream(std::ostream& out,
                           TNode n,
                           int toDepth,
                           bool types,
                           TypeNode force_nt) const
{
  // null
  if(n.getKind() == kind::NULL_EXPR) {
    out << "null";
    return;
  }

  // constant
  if(n.getMetaKind() == kind::metakind::CONSTANT) {
    switch(n.getKind()) {
    case kind::TYPE_CONSTANT:
      switch(n.getConst<TypeConstant>()) {
      case BOOLEAN_TYPE: out << "Bool"; break;
      case REAL_TYPE: out << "Real"; break;
      case INTEGER_TYPE: out << "Int"; break;
      case STRING_TYPE: out << "String"; break;
      case ROUNDINGMODE_TYPE: out << "RoundingMode"; break;
      default:
        // fall back on whatever operator<< does on underlying type; we
        // might luck out and be SMT-LIB v2 compliant
        kind::metakind::NodeValueConstPrinter::toStream(out, n);
      }
      break;
    case kind::BITVECTOR_TYPE:
      if(d_variant == sygus_variant ){
        out << "(BitVec " << n.getConst<BitVectorSize>().size << ")";
      }else{
        out << "(_ BitVec " << n.getConst<BitVectorSize>().size << ")";
      }
      break;
    case kind::FLOATINGPOINT_TYPE:
      out << "(_ FloatingPoint "
          << n.getConst<FloatingPointSize>().exponent() << " "
          << n.getConst<FloatingPointSize>().significand()
          << ")";
      break;
    case kind::CONST_BITVECTOR: {
      const BitVector& bv = n.getConst<BitVector>();
      const Integer& x = bv.getValue();
      unsigned n = bv.getSize();
      if(d_variant == sygus_variant ){
        out << "#b" << bv.toString();
      }else{
        out << "(_ ";
        out << "bv" << x <<" " << n;
        out << ")";
      }

      // //out << "#b";

      // while(n-- > 0) {
      //   out << (x.testBit(n) ? '1' : '0');
      // }
      break;
    }
    case kind::CONST_FLOATINGPOINT:
      out << n.getConst<FloatingPoint>();
      break;
    case kind::CONST_ROUNDINGMODE:
      switch (n.getConst<RoundingMode>()) {
      case roundNearestTiesToEven : out << "roundNearestTiesToEven"; break;
      case roundNearestTiesToAway : out << "roundNearestTiesToAway"; break;
      case roundTowardPositive : out << "roundTowardPositive"; break;
      case roundTowardNegative : out << "roundTowardNegative"; break;
      case roundTowardZero : out << "roundTowardZero"; break;
      default :
        Unreachable("Invalid value of rounding mode constant (%d)",n.getConst<RoundingMode>());
      }
      break;
    case kind::CONST_BOOLEAN:
      // the default would print "1" or "0" for bool, that's not correct
      // for our purposes
      out << (n.getConst<bool>() ? "true" : "false");
      break;
    case kind::BUILTIN:
      out << smtKindString(n.getConst<Kind>());
      break;
    case kind::CHAIN_OP:
      out << smtKindString(n.getConst<Chain>().getOperator());
      break;
    case kind::CONST_RATIONAL: {
      const Rational& r = n.getConst<Rational>();
      if(d_variant == sygus_variant ){
        if(r < 0) {
          out << "-" << -r;
        }else{
          toStreamRational(out, r, !force_nt.isNull() && !force_nt.isInteger());
        }
      }else{
        toStreamRational(out, r, !force_nt.isNull() && !force_nt.isInteger());
      }
      // Rational r = n.getConst<Rational>();
      // if(r < 0) {
      //   if(r.isIntegral()) {
      //     out << "(- " << -r << ')';
      //   } else {
      //     out << "(- (/ " << (-r).getNumerator() << ' ' << (-r).getDenominator() << "))";
      //   }
      // } else {
      //   if(r.isIntegral()) {
      //     out << r;
      //   } else {
      //     out << "(/ " << r.getNumerator() << ' ' << r.getDenominator() << ')';
      //   }
      // }
      break;
    }

    case kind::CONST_STRING: {
      //const std::vector<unsigned int>& s = n.getConst<String>().getVec();
      std::string s = n.getConst<String>().toString(true);
      out << '"';
      for(size_t i = 0; i < s.size(); ++i) {
        //char c = String::convertUnsignedIntToChar(s[i]);
        char c = s[i];
        if(c == '"') {
          if(d_variant == smt2_0_variant) {
            out << "\\\"";
          } else {
            out << "\"\"";
          }
        } else {
          out << c;
        }
      }
      out << '"';
      break;
    }

    case kind::STORE_ALL: {
      ArrayStoreAll asa = n.getConst<ArrayStoreAll>();
      out << "((as const " << asa.getType() << ") " << asa.getExpr() << ")";
      break;
    }

    case kind::DATATYPE_TYPE:
    {
      const Datatype& dt = (NodeManager::currentNM()->getDatatypeForIndex(
          n.getConst<DatatypeIndexConstant>().getIndex()));
      if (dt.isTuple())
      {
        unsigned int n = dt[0].getNumArgs();
        if (n == 0)
        {
          out << "Tuple";
        }
        else
        {
          out << "(Tuple";
          for (unsigned int i = 0; i < n; i++)
          {
            out << " " << dt[0][i].getRangeType();
          }
          out << ")";
        }
      }
      else
      {
        out << maybeQuoteSymbol(dt.getName());
      }
      break;
    }

    case kind::UNINTERPRETED_CONSTANT: {
      const UninterpretedConstant& uc = n.getConst<UninterpretedConstant>();
      out << '@' << uc;
      break;
    }

    case kind::EMPTYSET:
      out << "(as emptyset " << n.getConst<EmptySet>().getType() << ")";
      break;

    default:
      // fall back on whatever operator<< does on underlying type; we
      // might luck out and be SMT-LIB v2 compliant
      kind::metakind::NodeValueConstPrinter::toStream(out, n);
    }

    return;
  }

  if(n.getKind() == kind::SORT_TYPE) {
    string name;
    if(n.getNumChildren() != 0) {
      out << '(';
    }
    if(n.getAttribute(expr::VarNameAttr(), name)) {
      out << maybeQuoteSymbol(name);
    }
    if(n.getNumChildren() != 0) {
      for(unsigned i = 0; i < n.getNumChildren(); ++i) {
	      out << ' ';
	      toStream(out, n[i], toDepth, types, TypeNode::null());
      }
      out << ')';
    }
    return;
  }

  if (!force_nt.isNull())
  {
    if (n.getType() != force_nt)
    {
      if (force_nt.isReal())
      {
        out << "(" << smtKindString(force_nt.isInteger() ? kind::TO_INTEGER
                                                         : kind::TO_REAL)
            << " ";
        toStream(out, n, toDepth, types, TypeNode::null());
        out << ")";
      }
      else
      {
        Node nn = NodeManager::currentNM()->mkNode(
            kind::APPLY_TYPE_ASCRIPTION,
            NodeManager::currentNM()->mkConst(
                AscriptionType(force_nt.toType())),
            n);
        toStream(out, nn, toDepth, types, TypeNode::null());
      }
      return;
    }
  }

  // variable
  if (n.isVar())
  {
    string s;
    if (n.getAttribute(expr::VarNameAttr(), s))
    {
      out << maybeQuoteSymbol(s);
    }
    else
    {
      if (n.getKind() == kind::VARIABLE)
      {
        out << "var_";
      }
      else
      {
        out << n.getKind() << '_';
      }
      out << n.getId();
    }
    if (types)
    {
      // print the whole type, but not *its* type
      out << ":";
      n.getType().toStream(out, language::output::LANG_SMTLIB_V2_5);
    }

    return;
  }

  bool stillNeedToPrintParams = true;
  bool forceBinary = false; // force N-ary to binary when outputing children
  bool parametricTypeChildren = false;   // parametric operators that are (op t1 ... tn) where t1...tn must have same type
  bool typeChildren = false;  // operators (op t1...tn) where at least one of t1...tn may require a type cast e.g. Int -> Real
  // operator
  if(n.getNumChildren() != 0 &&
     n.getKind() != kind::INST_PATTERN_LIST &&
     n.getKind() != kind::APPLY_TYPE_ASCRIPTION) {
    out << '(';
  }
  switch(Kind k = n.getKind()) {
    // builtin theory
  case kind::APPLY: break;
  case kind::EQUAL:
  case kind::DISTINCT: 
    out << smtKindString(k) << " "; 
    parametricTypeChildren = true;
    break;
  case kind::CHAIN: break;
  case kind::FUNCTION_TYPE:
    out << "->";
    for (Node nc : n)
    {
      out << " ";
      toStream(out, nc, toDepth, types, TypeNode::null());
    }
    out << ")";
    return;
  case kind::SEXPR: break;

    // bool theory
  case kind::NOT:
  case kind::AND:
  case kind::IMPLIES:
  case kind::OR:
  case kind::XOR:
  case kind::ITE: out << smtKindString(k) << " "; break;

    // uf theory
  case kind::APPLY_UF: typeChildren = true; break;
  // higher-order
  case kind::HO_APPLY: break;
  case kind::LAMBDA:
    out << smtKindString(k) << " ";
    break;

  // arith theory
  case kind::PLUS:
  case kind::MULT:
  case kind::NONLINEAR_MULT:
  case kind::EXPONENTIAL:
  case kind::SINE:
  case kind::COSINE:
  case kind::TANGENT:
  case kind::COSECANT:
  case kind::SECANT:
  case kind::COTANGENT:
  case kind::ARCSINE:
  case kind::ARCCOSINE:
  case kind::ARCTANGENT:
  case kind::ARCCOSECANT:
  case kind::ARCSECANT:
  case kind::ARCCOTANGENT:
  case kind::SQRT:
  case kind::MINUS:
  case kind::UMINUS:
  case kind::LT:
  case kind::LEQ:
  case kind::GT:
  case kind::GEQ:
  case kind::DIVISION:
  case kind::DIVISION_TOTAL:
  case kind::INTS_DIVISION:
  case kind::INTS_DIVISION_TOTAL:
  case kind::INTS_MODULUS:
  case kind::INTS_MODULUS_TOTAL:
  case kind::ABS:
  case kind::IS_INTEGER:
  case kind::TO_INTEGER:
  case kind::TO_REAL:
  case kind::POW: 
    parametricTypeChildren = true;
    out << smtKindString(k) << " "; 
    break;

  case kind::DIVISIBLE:
    out << "(_ divisible " << n.getOperator().getConst<Divisible>().k << ")";
    stillNeedToPrintParams = false;
    break;

    // arrays theory
  case kind::SELECT:
  case kind::STORE: typeChildren = true;
  case kind::PARTIAL_SELECT_0:
  case kind::PARTIAL_SELECT_1:
  case kind::ARRAY_TYPE: out << smtKindString(k) << " "; break;

    // string theory
  case kind::STRING_CONCAT:
    if(d_variant == z3str_variant) {
      out << "Concat ";
      for(unsigned i = 0; i < n.getNumChildren(); ++i) {
        toStream(out, n[i], -1, types, TypeNode::null());
        if(i + 1 < n.getNumChildren()) {
          out << ' ';
        }
        if(i + 2 < n.getNumChildren()) {
          out << "(Concat ";
        }
      }
      for(unsigned i = 0; i < n.getNumChildren() - 1; ++i) {
        out << ")";
      }
      return;
    }
    out << "str.++ ";
    break;
  case kind::STRING_IN_REGEXP: {
    stringstream ss;
    if(d_variant == z3str_variant && stringifyRegexp(n[1], ss)) {
      out << "= ";
      toStream(out, n[0], -1, types, TypeNode::null());
      out << " ";
      Node str = NodeManager::currentNM()->mkConst(String(ss.str()));
      toStream(out, str, -1, types, TypeNode::null());
      out << ")";
      return;
    }
    out << "str.in.re ";
    break;
  }
  case kind::STRING_LENGTH: out << (d_variant == z3str_variant ? "Length " : "str.len "); break;
  case kind::STRING_SUBSTR: out << "str.substr "; break;
  case kind::STRING_CHARAT: out << "str.at "; break;
  case kind::STRING_STRCTN: out << "str.contains "; break;
  case kind::STRING_STRIDOF: out << "str.indexof "; break;
  case kind::STRING_STRREPL: out << "str.replace "; break;
  case kind::STRING_PREFIX: out << "str.prefixof "; break;
  case kind::STRING_SUFFIX: out << "str.suffixof "; break;
  case kind::STRING_ITOS: out << "int.to.str "; break;
  case kind::STRING_STOI: out << "str.to.int "; break;
  case kind::STRING_TO_REGEXP: out << "str.to.re "; break;
  case kind::REGEXP_CONCAT: out << "re.++ "; break;
  case kind::REGEXP_UNION: out << "re.union "; break;
  case kind::REGEXP_INTER: out << "re.inter "; break;
  case kind::REGEXP_STAR: out << "re.* "; break;
  case kind::REGEXP_PLUS: out << "re.+ "; break;
  case kind::REGEXP_OPT: out << "re.opt "; break;
  case kind::REGEXP_RANGE: out << "re.range "; break;
  case kind::REGEXP_LOOP: out << "re.loop "; break;
  case kind::REGEXP_EMPTY: out << "re.nostr "; break;
  case kind::REGEXP_SIGMA: out << "re.allchar "; break;

  case kind::CARDINALITY_CONSTRAINT: out << "fmf.card "; break;
  case kind::CARDINALITY_VALUE: out << "fmf.card.val "; break;

    // bv theory
  case kind::BITVECTOR_CONCAT: out << "concat "; forceBinary = true; break;
  case kind::BITVECTOR_AND: out << "bvand "; forceBinary = true; break;
  case kind::BITVECTOR_OR: out << "bvor "; forceBinary = true; break;
  case kind::BITVECTOR_XOR: out << "bvxor "; forceBinary = true; break;
  case kind::BITVECTOR_NOT: out << "bvnot "; break;
  case kind::BITVECTOR_NAND: out << "bvnand "; break;
  case kind::BITVECTOR_NOR: out << "bvnor "; break;
  case kind::BITVECTOR_XNOR: out << "bvxnor "; break;
  case kind::BITVECTOR_COMP: out << "bvcomp "; break;
  case kind::BITVECTOR_MULT: out << "bvmul "; forceBinary = true; break;
  case kind::BITVECTOR_PLUS: out << "bvadd "; forceBinary = true; break;
  case kind::BITVECTOR_SUB: out << "bvsub "; break;
  case kind::BITVECTOR_NEG: out << "bvneg "; break;
  case kind::BITVECTOR_UDIV: out << "bvudiv "; break;
  case kind::BITVECTOR_UDIV_TOTAL: out << "bvudiv_total "; break;
  case kind::BITVECTOR_UREM: out << "bvurem "; break;
  case kind::BITVECTOR_UREM_TOTAL: out << "bvurem_total "; break;
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
  case kind::BITVECTOR_TO_NAT: out << "bv2nat "; break;
  case kind::BITVECTOR_REDOR: out << "bvredor "; break;
  case kind::BITVECTOR_REDAND: out << "bvredand "; break;

  case kind::BITVECTOR_EXTRACT:
  case kind::BITVECTOR_REPEAT:
  case kind::BITVECTOR_ZERO_EXTEND:
  case kind::BITVECTOR_SIGN_EXTEND:
  case kind::BITVECTOR_ROTATE_LEFT:
  case kind::BITVECTOR_ROTATE_RIGHT:
  case kind::INT_TO_BITVECTOR:
    printBvParameterizedOp(out, n);
    out << ' ';
    stillNeedToPrintParams = false;
    break;

    // sets
  case kind::UNION:
  case kind::INTERSECTION:
  case kind::SETMINUS:
  case kind::SUBSET:
  case kind::CARD:
  case kind::JOIN:
  case kind::PRODUCT:
  case kind::TRANSPOSE:
  case kind::TCLOSURE:
    parametricTypeChildren = true;
    out << smtKindString(k) << " "; 
    break;
  case kind::MEMBER: typeChildren = true;
  case kind::SET_TYPE:
  case kind::SINGLETON:
  case kind::COMPLEMENT:out << smtKindString(k) << " "; break;
  case kind::UNIVERSE_SET:out << "(as univset " << n.getType() << ")";break;

    // fp theory
  case kind::FLOATINGPOINT_FP:
  case kind::FLOATINGPOINT_EQ:
  case kind::FLOATINGPOINT_ABS:
  case kind::FLOATINGPOINT_NEG:
  case kind::FLOATINGPOINT_PLUS:
  case kind::FLOATINGPOINT_SUB:
  case kind::FLOATINGPOINT_MULT:
  case kind::FLOATINGPOINT_DIV:
  case kind::FLOATINGPOINT_FMA:
  case kind::FLOATINGPOINT_SQRT:
  case kind::FLOATINGPOINT_REM:
  case kind::FLOATINGPOINT_RTI:
  case kind::FLOATINGPOINT_MIN:
  case kind::FLOATINGPOINT_MAX:
  case kind::FLOATINGPOINT_LEQ:
  case kind::FLOATINGPOINT_LT:
  case kind::FLOATINGPOINT_GEQ:
  case kind::FLOATINGPOINT_GT:
  case kind::FLOATINGPOINT_ISN:
  case kind::FLOATINGPOINT_ISSN:
  case kind::FLOATINGPOINT_ISZ:
  case kind::FLOATINGPOINT_ISINF:
  case kind::FLOATINGPOINT_ISNAN:
  case kind::FLOATINGPOINT_ISNEG:
  case kind::FLOATINGPOINT_ISPOS:
  case kind::FLOATINGPOINT_TO_REAL:
    out << smtKindString(k) << ' '; break;

  case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR:
  case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT:
  case kind::FLOATINGPOINT_TO_FP_REAL:
  case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR:
  case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR:
  case kind::FLOATINGPOINT_TO_FP_GENERIC:
  case kind::FLOATINGPOINT_TO_UBV:
  case kind::FLOATINGPOINT_TO_SBV:
    printFpParameterizedOp(out, n);
    out << ' ';
    stillNeedToPrintParams = false;
    break;

    // datatypes
  case kind::APPLY_TYPE_ASCRIPTION: {
      TypeNode t = TypeNode::fromType(n.getOperator().getConst<AscriptionType>().getType());
      if(t.getKind() == kind::TYPE_CONSTANT &&
         t.getConst<TypeConstant>() == REAL_TYPE &&
         n[0].getType().isInteger()) {
        // Special case, in model output integer constants that should be
        // Real-sorted are wrapped in a type ascription.  Handle that here.

        // Note: This is Tim making a guess about Morgan's Code.
        Assert(n[0].getKind() == kind::CONST_RATIONAL);
        toStreamRational(out, n[0].getConst<Rational>(), true);

        //toStream(out, n[0], -1, false);
        //out << ".0";

        return;
      }
      out << "(as ";
      toStream(out, n[0], toDepth < 0 ? toDepth : toDepth - 1, types, TypeNode::null());
      out << ' ' << (t.isFunctionLike() ? t.getRangeType() : t) << ')';
      return;
    }
    break;

    case kind::APPLY_CONSTRUCTOR:
    {
      typeChildren = true;
      const Datatype& dt = Datatype::datatypeOf(n.getOperator().toExpr());
      if (dt.isTuple())
      {
        stillNeedToPrintParams = false;
        out << "mkTuple" << ( dt[0].getNumArgs()==0 ? "" : " ");
      }
    }

    case kind::APPLY_TESTER:
    case kind::APPLY_SELECTOR:
    case kind::APPLY_SELECTOR_TOTAL:
    case kind::PARAMETRIC_DATATYPE: break;

    // separation logic
    case kind::SEP_EMP:
    case kind::SEP_PTO:
    case kind::SEP_STAR:
    case kind::SEP_WAND: out << smtKindString(k) << " "; break;

    case kind::SEP_NIL:
      out << "(as sep.nil " << n.getType() << ")";
      break;

      // quantifiers
    case kind::FORALL:
    case kind::EXISTS:
      if (k == kind::FORALL)
      {
        out << "forall ";
      }
      else
      {
        out << "exists ";
      }
      for (unsigned i = 0; i < 2; i++)
      {
        out << n[i] << " ";
        if (i == 0 && n.getNumChildren() == 3)
        {
          out << "(! ";
        }
      }
      if (n.getNumChildren() == 3)
      {
        out << n[2];
        out << ")";
      }
      out << ")";
      return;
      break;
    case kind::BOUND_VAR_LIST:
      // the left parenthesis is already printed (before the switch)
      for (TNode::iterator i = n.begin(), iend = n.end(); i != iend;)
      {
        out << '(';
        toStream(out, *i, toDepth < 0 ? toDepth : toDepth - 1, types, 0);
        out << ' ';
        out << (*i).getType();
        // The following code do stange things
        // (*i).getType().toStream(out, toDepth < 0 ? toDepth : toDepth - 1,
        //                         false, language::output::LANG_SMTLIB_V2_5);
        out << ')';
        if (++i != iend)
        {
          out << ' ';
        }
      }
      out << ')';
      return;
    case kind::INST_PATTERN: break;
    case kind::INST_PATTERN_LIST:
      for (unsigned i = 0; i < n.getNumChildren(); i++)
      {
        if (n[i].getKind() == kind::INST_ATTRIBUTE)
        {
          if (n[i][0].getAttribute(theory::FunDefAttribute()))
          {
            out << ":fun-def";
          }
        }
        else
        {
          out << ":pattern " << n[i];
        }
      }
      return;
      break;

    default:
      // fall back on however the kind prints itself; this probably
      // won't be SMT-LIB v2 compliant, but it will be clear from the
      // output that support for the kind needs to be added here.
      out << n.getKind() << ' ';
  }
  if( n.getMetaKind() == kind::metakind::PARAMETERIZED &&
      stillNeedToPrintParams ) {
    if(toDepth != 0) {
      if( d_variant==sygus_variant && n.getKind()==kind::APPLY_CONSTRUCTOR ){
        std::stringstream ss;
        toStream(ss, n.getOperator(), toDepth < 0 ? toDepth : toDepth - 1, types, TypeNode::null());
        std::string tmp = ss.str();
        size_t pos = 0;
        if((pos = tmp.find("__Enum__", pos)) != std::string::npos){
           tmp.replace(pos, 8, "::");
        }
        out << tmp;
      }else if( n.getKind()==kind::APPLY_TESTER ){
        unsigned cindex = Datatype::indexOf(n.getOperator().toExpr());
        const Datatype& dt = Datatype::datatypeOf(n.getOperator().toExpr());
        if( d_variant==smt2_6_variant ){
          out << "(_ is ";
          toStream(out, Node::fromExpr(dt[cindex].getConstructor()), toDepth < 0 ? toDepth : toDepth - 1, types, TypeNode::null());
          out << ")";
        }else{
          out << "is-";
          toStream(out, Node::fromExpr(dt[cindex].getConstructor()), toDepth < 0 ? toDepth : toDepth - 1, types, TypeNode::null());
        }
      }else{
        toStream(out, n.getOperator(), toDepth < 0 ? toDepth : toDepth - 1, types, TypeNode::null());
      }
    } else {
      out << "(...)";
    }
    if(n.getNumChildren() > 0) {
      out << ' ';
    }
  }
  stringstream parens;
  
  // calculate the child type casts
  std::map< unsigned, TypeNode > force_child_type;
  if( parametricTypeChildren ){
    if( n.getNumChildren()>1 ){
      TypeNode force_ct = n[0].getType();
      bool do_force = false;
      for(size_t i = 1; i < n.getNumChildren(); ++i ) {
        TypeNode ct = n[i].getType();
        if( ct!=force_ct ){
          force_ct = TypeNode::leastCommonTypeNode( force_ct, ct );
          do_force = true;
        }
      }
      if( do_force ){
        for(size_t i = 0; i < n.getNumChildren(); ++i ) {
          force_child_type[i] = force_ct;
        }
      }
    }
  // operators that may require type casting
  }else if( typeChildren ){
    if(n.getKind()==kind::SELECT){
      TypeNode indexType = TypeNode::leastCommonTypeNode( n[0].getType().getArrayIndexType(), n[1].getType() );
      TypeNode elemType = n[0].getType().getArrayConstituentType();
      force_child_type[0] = NodeManager::currentNM()->mkArrayType( indexType, elemType );
      force_child_type[1] = indexType;
    }else if(n.getKind()==kind::STORE){
      TypeNode indexType = TypeNode::leastCommonTypeNode( n[0].getType().getArrayIndexType(), n[1].getType() );
      TypeNode elemType = TypeNode::leastCommonTypeNode( n[0].getType().getArrayConstituentType(), n[2].getType() );
      force_child_type[0] = NodeManager::currentNM()->mkArrayType( indexType, elemType );
      force_child_type[1] = indexType;
      force_child_type[2] = elemType;
    }else if(n.getKind()==kind::MEMBER){
      TypeNode elemType = TypeNode::leastCommonTypeNode( n[0].getType(), n[1].getType().getSetElementType() );
      force_child_type[0] = elemType;
      force_child_type[1] = NodeManager::currentNM()->mkSetType( elemType );
    }else{
      // APPLY_UF, APPLY_CONSTRUCTOR, etc.
      Assert( n.hasOperator() );
      TypeNode opt = n.getOperator().getType();
      Assert( opt.getNumChildren() == n.getNumChildren() + 1 );
      for(size_t i = 0; i < n.getNumChildren(); ++i ) {
        force_child_type[i] = opt[i];
      }
    }
  }
  
  for(size_t i = 0, c = 1; i < n.getNumChildren(); ) {
    if(toDepth != 0) {
      Node cn = n[i];
      std::map< unsigned, TypeNode >::iterator itfc = force_child_type.find( i );
      if( itfc!=force_child_type.end() ){
        toStream(out, cn, toDepth < 0 ? toDepth : toDepth - c, types, itfc->second);
      }else{
        toStream(out, cn, toDepth < 0 ? toDepth : toDepth - c, types, TypeNode::null());
      }
    } else {
      out << "(...)";
    }
    if(++i < n.getNumChildren()) {
      if(forceBinary && i < n.getNumChildren() - 1) {
        // not going to work properly for parameterized kinds!
        Assert(n.getMetaKind() != kind::metakind::PARAMETERIZED);
        out << " (" << smtKindString(n.getKind()) << ' ';
        parens << ')';
        ++c;
      } else {
        out << ' ';
      }
    }
  }
  if(n.getNumChildren() != 0) {
    out << parens.str() << ')';
  }
}/* Smt2Printer::toStream(TNode) */

static string smtKindString(Kind k)
{
  switch(k) {
    // builtin theory
  case kind::APPLY: break;
  case kind::EQUAL: return "=";
  case kind::DISTINCT: return "distinct";
  case kind::CHAIN: break;
  case kind::SEXPR: break;

    // bool theory
  case kind::NOT: return "not";
  case kind::AND: return "and";
  case kind::IMPLIES: return "=>";
  case kind::OR: return "or";
  case kind::XOR: return "xor";
  case kind::ITE: return "ite";

    // uf theory
  case kind::APPLY_UF: break;

  case kind::LAMBDA:
    return "lambda";

  // arith theory
  case kind::PLUS: return "+";
  case kind::MULT:
  case kind::NONLINEAR_MULT: return "*";
  case kind::EXPONENTIAL: return "exp";
  case kind::SINE: return "sin";
  case kind::COSINE: return "cos";
  case kind::TANGENT: return "tan";
  case kind::COSECANT: return "csc";
  case kind::SECANT: return "sec";
  case kind::COTANGENT: return "cot";
  case kind::ARCSINE: return "arcsin";
  case kind::ARCCOSINE: return "arccos";
  case kind::ARCTANGENT: return "arctan";
  case kind::ARCCOSECANT: return "arccsc";
  case kind::ARCSECANT: return "arcsec";
  case kind::ARCCOTANGENT: return "arccot";
  case kind::SQRT: return "sqrt";
  case kind::MINUS: return "-";
  case kind::UMINUS: return "-";
  case kind::LT: return "<";
  case kind::LEQ: return "<=";
  case kind::GT: return ">";
  case kind::GEQ: return ">=";
  case kind::DIVISION:
  case kind::DIVISION_TOTAL: return "/";
  case kind::INTS_DIVISION_TOTAL: 
  case kind::INTS_DIVISION: return "div";
  case kind::INTS_MODULUS_TOTAL: 
  case kind::INTS_MODULUS: return "mod";
  case kind::ABS: return "abs";
  case kind::IS_INTEGER: return "is_int";
  case kind::TO_INTEGER: return "to_int";
  case kind::TO_REAL: return "to_real";
  case kind::POW: return "^";

    // arrays theory
  case kind::SELECT: return "select";
  case kind::STORE: return "store";
  case kind::ARRAY_TYPE: return "Array";
  case kind::PARTIAL_SELECT_0: return "partial_select_0";
  case kind::PARTIAL_SELECT_1: return "partial_select_1";

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
  case kind::BITVECTOR_UDIV_TOTAL:
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
  case kind::BITVECTOR_REDOR: return "bvredor";
  case kind::BITVECTOR_REDAND: return "bvredand";

  case kind::BITVECTOR_EXTRACT: return "extract";
  case kind::BITVECTOR_REPEAT: return "repeat";
  case kind::BITVECTOR_ZERO_EXTEND: return "zero_extend";
  case kind::BITVECTOR_SIGN_EXTEND: return "sign_extend";
  case kind::BITVECTOR_ROTATE_LEFT: return "rotate_left";
  case kind::BITVECTOR_ROTATE_RIGHT: return "rotate_right";

  case kind::UNION: return "union";
  case kind::INTERSECTION: return "intersection";
  case kind::SETMINUS: return "setminus";
  case kind::SUBSET: return "subset";
  case kind::MEMBER: return "member";
  case kind::SET_TYPE: return "Set";
  case kind::SINGLETON: return "singleton";
  case kind::INSERT: return "insert";
  case kind::COMPLEMENT: return "complement";
  case kind::CARD: return "card";
  case kind::JOIN: return "join";
  case kind::PRODUCT: return "product";
  case kind::TRANSPOSE: return "transpose";
  case kind::TCLOSURE:
    return "tclosure";

    // fp theory
  case kind::FLOATINGPOINT_FP: return "fp";
  case kind::FLOATINGPOINT_EQ: return "fp.eq";
  case kind::FLOATINGPOINT_ABS: return "fp.abs";
  case kind::FLOATINGPOINT_NEG: return "fp.neg";
  case kind::FLOATINGPOINT_PLUS: return "fp.add";
  case kind::FLOATINGPOINT_SUB: return "fp.sub";
  case kind::FLOATINGPOINT_MULT: return "fp.mul";
  case kind::FLOATINGPOINT_DIV: return "fp.div";
  case kind::FLOATINGPOINT_FMA: return "fp.fma";
  case kind::FLOATINGPOINT_SQRT: return "fp.sqrt";
  case kind::FLOATINGPOINT_REM: return "fp.rem";
  case kind::FLOATINGPOINT_RTI: return "fp.roundToIntegral";
  case kind::FLOATINGPOINT_MIN: return "fp.min";
  case kind::FLOATINGPOINT_MAX: return "fp.max";
  case kind::FLOATINGPOINT_MIN_TOTAL: return "fp.min_total";
  case kind::FLOATINGPOINT_MAX_TOTAL: return "fp.max_total";

  case kind::FLOATINGPOINT_LEQ: return "fp.leq";
  case kind::FLOATINGPOINT_LT: return "fp.lt";
  case kind::FLOATINGPOINT_GEQ: return "fp.geq";
  case kind::FLOATINGPOINT_GT: return "fp.gt";

  case kind::FLOATINGPOINT_ISN: return "fp.isNormal";
  case kind::FLOATINGPOINT_ISSN: return "fp.isSubnormal";
  case kind::FLOATINGPOINT_ISZ: return "fp.isZero";
  case kind::FLOATINGPOINT_ISINF: return "fp.isInfinite";
  case kind::FLOATINGPOINT_ISNAN: return "fp.isNaN";
  case kind::FLOATINGPOINT_ISNEG: return "fp.isNegative";
  case kind::FLOATINGPOINT_ISPOS: return "fp.isPositive";

  case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR: return "to_fp";
  case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT: return "to_fp";
  case kind::FLOATINGPOINT_TO_FP_REAL: return "to_fp";
  case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR: return "to_fp";
  case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR: return "to_fp_unsigned";
  case kind::FLOATINGPOINT_TO_FP_GENERIC: return "to_fp_unsigned";
  case kind::FLOATINGPOINT_TO_UBV: return "fp.to_ubv";
  case kind::FLOATINGPOINT_TO_UBV_TOTAL: return "fp.to_ubv_total";
  case kind::FLOATINGPOINT_TO_SBV: return "fp.to_sbv";
  case kind::FLOATINGPOINT_TO_SBV_TOTAL: return "fp.to_sbv_total";
  case kind::FLOATINGPOINT_TO_REAL: return "fp.to_real";
  case kind::FLOATINGPOINT_TO_REAL_TOTAL: return "fp.to_real_total";

  //string theory
  case kind::STRING_CONCAT: return "str.++";
  case kind::STRING_LENGTH: return "str.len";
  case kind::STRING_SUBSTR: return "str.substr" ;
  case kind::STRING_STRCTN: return "str.contains" ;
  case kind::STRING_CHARAT: return "str.at" ;
  case kind::STRING_STRIDOF: return "str.indexof" ;
  case kind::STRING_STRREPL: return "str.replace" ;
  case kind::STRING_PREFIX: return "str.prefixof" ;
  case kind::STRING_SUFFIX: return "str.suffixof" ;
  case kind::STRING_ITOS: return "int.to.str" ;
  case kind::STRING_STOI: return "str.to.int" ;
  case kind::STRING_IN_REGEXP: return "str.in.re";
  case kind::STRING_TO_REGEXP: return "str.to.re";
  case kind::REGEXP_CONCAT: return "re.++";
  case kind::REGEXP_UNION: return "re.union";
  case kind::REGEXP_INTER: return "re.inter";
  case kind::REGEXP_STAR: return "re.*";
  case kind::REGEXP_PLUS: return "re.+";
  case kind::REGEXP_OPT: return "re.opt";
  case kind::REGEXP_RANGE: return "re.range";
  case kind::REGEXP_LOOP: return "re.loop";

  //sep theory
  case kind::SEP_STAR: return "sep";
  case kind::SEP_PTO: return "pto";
  case kind::SEP_WAND: return "wand";
  case kind::SEP_EMP: return "emp";

  default:
    ; /* fall through */
  }

  // no SMT way to print these
  return kind::kindToString(k);
}

static void printBvParameterizedOp(std::ostream& out, TNode n)
{
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
  case kind::INT_TO_BITVECTOR:
    out << "int2bv "
        << n.getOperator().getConst<IntToBitVector>().size;
    break;
  default:
    out << n.getKind();
  }
  out << ")";
}

static void printFpParameterizedOp(std::ostream& out, TNode n)
{
  out << "(_ ";
  switch(n.getKind()) {
  case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR:
    //out << "to_fp_bv "
    out << "to_fp "
        << n.getOperator().getConst<FloatingPointToFPIEEEBitVector>().t.exponent() << ' '
        << n.getOperator().getConst<FloatingPointToFPIEEEBitVector>().t.significand();
    break;
  case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT:
    //out << "to_fp_fp "
    out << "to_fp "
        << n.getOperator().getConst<FloatingPointToFPFloatingPoint>().t.exponent() << ' '
        << n.getOperator().getConst<FloatingPointToFPFloatingPoint>().t.significand();
    break;
  case kind::FLOATINGPOINT_TO_FP_REAL:
    //out << "to_fp_real "
    out << "to_fp "
        << n.getOperator().getConst<FloatingPointToFPReal>().t.exponent() << ' '
        << n.getOperator().getConst<FloatingPointToFPReal>().t.significand();
    break;
  case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR:
    //out << "to_fp_signed "
    out << "to_fp "
        << n.getOperator().getConst<FloatingPointToFPSignedBitVector>().t.exponent() << ' '
        << n.getOperator().getConst<FloatingPointToFPSignedBitVector>().t.significand();
    break;
  case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR:
    out << "to_fp_unsigned "
        << n.getOperator().getConst<FloatingPointToFPUnsignedBitVector>().t.exponent() << ' '
        << n.getOperator().getConst<FloatingPointToFPUnsignedBitVector>().t.significand();
    break;
  case kind::FLOATINGPOINT_TO_FP_GENERIC:
    out << "to_fp "
        << n.getOperator().getConst<FloatingPointToFPGeneric>().t.exponent() << ' '
        << n.getOperator().getConst<FloatingPointToFPGeneric>().t.significand();
    break;
  case kind::FLOATINGPOINT_TO_UBV:
    out << "fp.to_ubv "
        << n.getOperator().getConst<FloatingPointToUBV>().bvs.size;
    break;
  case kind::FLOATINGPOINT_TO_SBV:
    out << "fp.to_sbv "
        << n.getOperator().getConst<FloatingPointToSBV>().bvs.size;
    break;
  case kind::FLOATINGPOINT_TO_UBV_TOTAL:
    out << "fp.to_ubv_total "
        << n.getOperator().getConst<FloatingPointToUBVTotal>().bvs.size;
    break;
  case kind::FLOATINGPOINT_TO_SBV_TOTAL:
    out << "fp.to_sbv_total "
        << n.getOperator().getConst<FloatingPointToSBVTotal>().bvs.size;
    break;
  default:
    out << n.getKind();
  }
  out << ")";
}

template <class T>
static bool tryToStream(std::ostream& out, const Command* c);
template <class T>
static bool tryToStream(std::ostream& out, const Command* c, Variant v);

void Smt2Printer::toStream(std::ostream& out,
                           const Command* c,
                           int toDepth,
                           bool types,
                           size_t dag) const
{
  expr::ExprSetDepth::Scope sdScope(out, toDepth);
  expr::ExprPrintTypes::Scope ptScope(out, types);
  expr::ExprDag::Scope dagScope(out, dag);

  if (tryToStream<AssertCommand>(out, c) || tryToStream<PushCommand>(out, c)
      || tryToStream<PopCommand>(out, c)
      || tryToStream<CheckSatCommand>(out, c)
      || tryToStream<CheckSatAssumingCommand>(out, c)
      || tryToStream<QueryCommand>(out, c, d_variant)
      || tryToStream<ResetCommand>(out, c)
      || tryToStream<ResetAssertionsCommand>(out, c)
      || tryToStream<QuitCommand>(out, c)
      || tryToStream<DeclarationSequence>(out, c)
      || tryToStream<CommandSequence>(out, c)
      || tryToStream<DeclareFunctionCommand>(out, c)
      || tryToStream<DeclareTypeCommand>(out, c)
      || tryToStream<DefineTypeCommand>(out, c)
      || tryToStream<DefineNamedFunctionCommand>(out, c)
      || tryToStream<DefineFunctionCommand>(out, c)
      || tryToStream<DefineFunctionRecCommand>(out, c)
      || tryToStream<SimplifyCommand>(out, c)
      || tryToStream<GetValueCommand>(out, c)
      || tryToStream<GetModelCommand>(out, c)
      || tryToStream<GetAssignmentCommand>(out, c)
      || tryToStream<GetAssertionsCommand>(out, c)
      || tryToStream<GetProofCommand>(out, c)
      || tryToStream<GetUnsatCoreCommand>(out, c)
      || tryToStream<SetBenchmarkStatusCommand>(out, c, d_variant)
      || tryToStream<SetBenchmarkLogicCommand>(out, c, d_variant)
      || tryToStream<SetInfoCommand>(out, c, d_variant)
      || tryToStream<GetInfoCommand>(out, c)
      || tryToStream<SetOptionCommand>(out, c)
      || tryToStream<GetOptionCommand>(out, c)
      || tryToStream<DatatypeDeclarationCommand>(out, c, d_variant)
      || tryToStream<CommentCommand>(out, c, d_variant)
      || tryToStream<EmptyCommand>(out, c)
      || tryToStream<EchoCommand>(out, c, d_variant))
  {
    return;
  }

  out << "ERROR: don't know how to print a Command of class: "
      << typeid(*c).name() << endl;

}/* Smt2Printer::toStream(Command*) */


static std::string quoteSymbol(TNode n) {
  // #warning "check the old implementation. It seems off."
  std::stringstream ss;
  ss << language::SetLanguage(language::output::LANG_SMTLIB_V2_5);
  return CVC4::quoteSymbol(ss.str());
}

template <class T>
static bool tryToStream(std::ostream& out, const CommandStatus* s, Variant v);

void Smt2Printer::toStream(std::ostream& out, const CommandStatus* s) const
{
  if (tryToStream<CommandSuccess>(out, s, d_variant) ||
      tryToStream<CommandFailure>(out, s, d_variant) ||
      tryToStream<CommandRecoverableFailure>(out, s, d_variant) ||
      tryToStream<CommandUnsupported>(out, s, d_variant) ||
      tryToStream<CommandInterrupted>(out, s, d_variant)) {
    return;
  }

  out << "ERROR: don't know how to print a CommandStatus of class: "
      << typeid(*s).name() << endl;

}/* Smt2Printer::toStream(CommandStatus*) */

void Smt2Printer::toStream(std::ostream& out, const UnsatCore& core) const
{
  out << "(" << std::endl;
  SmtEngine * smt = core.getSmtEngine();
  Assert( smt!=NULL );
  for(UnsatCore::const_iterator i = core.begin(); i != core.end(); ++i) {
    std::string name;
    if (smt->getExpressionName(*i,name)) {
      // Named assertions always get printed
      out << maybeQuoteSymbol(name) << endl;
    } else if (options::dumpUnsatCoresFull()) {
      // Unnamed assertions only get printed if the option is set
      out << *i << endl;
    }
  }
  out << ")" << endl;
}/* Smt2Printer::toStream(UnsatCore, map<Expr, string>) */

void Smt2Printer::toStream(std::ostream& out, const Model& m) const
{
  //print the model comments
  std::stringstream c;
  m.getComments( c );
  std::string ln;
  while( std::getline( c, ln ) ){
    out << "; " << ln << std::endl;
  }
  //print the model
  out << "(model" << endl;
  this->Printer::toStream(out, m);
  out << ")" << endl;
  //print the heap model, if it exists
  Expr h, neq;
  if( m.getHeapModel( h, neq ) ){
    // description of the heap+what nil is equal to fully describes model
    out << "(heap" << endl;
    out << h << endl;
    out << neq << endl;
    out << ")" << std::endl;
  }
}

namespace {

void DeclareTypeCommandToStream(std::ostream& out,
                                const theory::TheoryModel& model,
                                const DeclareTypeCommand& command,
                                Variant variant)
{
  TypeNode tn = TypeNode::fromType(command.getType());
  const std::vector<Node>* type_refs = model.getRepSet()->getTypeRepsOrNull(tn);
  if (options::modelUninterpDtEnum() && tn.isSort() && type_refs != nullptr)
  {
    if (variant == smt2_6_variant)
    {
      out << "(declare-datatypes ((" << command.getSymbol() << " 0)) (";
    }
    else
    {
      out << "(declare-datatypes () ((" << command.getSymbol() << " ";
    }
    for (Node type_ref : *type_refs)
    {
      out << "(" << type_ref << ")";
    }
    out << ")))" << endl;
  }
  else if (tn.isSort() && type_refs != nullptr)
  {
    // print the cardinality
    out << "; cardinality of " << tn << " is " << type_refs->size() << endl;
    out << command << endl;
    // print the representatives
    for (Node type_ref : *type_refs)
    {
      if (type_ref.isVar())
      {
        out << "(declare-fun " << quoteSymbol(type_ref) << " () " << tn << ")"
            << endl;
      }
      else
      {
        out << "; rep: " << type_ref << endl;
      }
    }
  }
  else
  {
    out << command << endl;
  }
}

void DeclareFunctionCommandToStream(std::ostream& out,
                                    const theory::TheoryModel& model,
                                    const DeclareFunctionCommand& command)
{
  Node n = Node::fromExpr(command.getFunction());
  if (command.getPrintInModelSetByUser())
  {
    if (!command.getPrintInModel())
    {
      return;
    }
  }
  else if (n.getKind() == kind::SKOLEM)
  {
    // don't print out internal stuff
    return;
  }
  Node val = Node::fromExpr(model.getSmtEngine()->getValue(n.toExpr()));
  if (val.getKind() == kind::LAMBDA)
  {
    out << "(define-fun " << n << " " << val[0] << " "
        << n.getType().getRangeType() << " " << val[1] << ")" << endl;
  }
  else
  {
    if (options::modelUninterpDtEnum() && val.getKind() == kind::STORE)
    {
      TypeNode tn = val[1].getType();
      const std::vector<Node>* type_refs =
          model.getRepSet()->getTypeRepsOrNull(tn);
      if (tn.isSort() && type_refs != nullptr)
      {
        Cardinality indexCard(type_refs->size());
        val = theory::arrays::TheoryArraysRewriter::normalizeConstant(
            val, indexCard);
      }
    }
    out << "(define-fun " << n << " () " << n.getType() << " ";
    if (val.getType().isInteger() && n.getType().isReal()
        && !n.getType().isInteger())
    {
      // toStreamReal(out, val, true);
      toStreamRational(out, val.getConst<Rational>(), true);
      // out << val << ".0";
    }
    else
    {
      out << val;
    }
    out << ")" << endl;
  }
}

}  // namespace

void Smt2Printer::toStream(std::ostream& out,
                           const Model& model,
                           const Command* command) const
{
  const theory::TheoryModel* theory_model =
      dynamic_cast<const theory::TheoryModel*>(&model);
  AlwaysAssert(theory_model != nullptr);
  if (const DeclareTypeCommand* dtc =
          dynamic_cast<const DeclareTypeCommand*>(command))
  {
    DeclareTypeCommandToStream(out, *theory_model, *dtc, d_variant);
  }
  else if (const DeclareFunctionCommand* dfc =
               dynamic_cast<const DeclareFunctionCommand*>(command))
  {
    DeclareFunctionCommandToStream(out, *theory_model, *dfc);
  }
  else if (const DatatypeDeclarationCommand* datatype_declaration_command =
               dynamic_cast<const DatatypeDeclarationCommand*>(command))
  {
    if (!datatype_declaration_command->getDatatypes()[0].isTuple())
    {
      out << command << endl;
    }
  }
  else
  {
    Unreachable();
  }
}

void Smt2Printer::toStreamSygus(std::ostream& out, TNode n) const
{
  if (n.getKind() == kind::APPLY_CONSTRUCTOR)
  {
    TypeNode tn = n.getType();
    const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
    if (dt.isSygus())
    {
      int cIndex = Datatype::indexOf(n.getOperator().toExpr());
      Assert(!dt[cIndex].getSygusOp().isNull());
      SygusPrintCallback* spc = dt[cIndex].getSygusPrintCallback().get();
      if (spc != nullptr && options::sygusPrintCallbacks())
      {
        spc->toStreamSygus(this, out, n.toExpr());
      }
      else
      {
        if (n.getNumChildren() > 0)
        {
          out << "(";
        }
        out << dt[cIndex].getSygusOp();
        if (n.getNumChildren() > 0)
        {
          for (Node nc : n)
          {
            out << " ";
            toStreamSygus(out, nc);
          }
          out << ")";
        }
      }
      return;
    }
  }
  else
  {
    Node p = n.getAttribute(theory::SygusPrintProxyAttribute());
    if (!p.isNull())
    {
      out << p;
    }
    else
    {
      // cannot convert term to analog, print original
      out << n;
    }
  }
}

static void toStream(std::ostream& out, const AssertCommand* c)
{
  out << "(assert " << c->getExpr() << ")";
}

static void toStream(std::ostream& out, const PushCommand* c)
{
  out << "(push 1)";
}

static void toStream(std::ostream& out, const PopCommand* c)
{
  out << "(pop 1)";
}

static void toStream(std::ostream& out, const CheckSatCommand* c)
{
  Expr e = c->getExpr();
  if(!e.isNull() && !(e.getKind() == kind::CONST_BOOLEAN && e.getConst<bool>())) {
    out << PushCommand() << endl
        << AssertCommand(e) << endl
        << CheckSatCommand() << endl
        << PopCommand();
  } else {
    out << "(check-sat)";
  }
}

static void toStream(std::ostream& out, const CheckSatAssumingCommand* c)
{
  out << "(check-sat-assuming ( ";
  const vector<Expr>& terms = c->getTerms();
  copy(terms.begin(), terms.end(), ostream_iterator<Expr>(out, " "));
  out << "))";
}

static void toStream(std::ostream& out, const QueryCommand* c, Variant v)
{
  Expr e = c->getExpr();
  if(!e.isNull()) {
    if (v == smt2_0_variant)
    {
      out << PushCommand() << endl
          << AssertCommand(BooleanSimplification::negate(e)) << endl
          << CheckSatCommand() << endl
          << PopCommand();
    }
    else
    {
      out << CheckSatAssumingCommand(e.notExpr()) << endl;
    }
  } else {
    out << "(check-sat)";
  }
}

static void toStream(std::ostream& out, const ResetCommand* c)
{
  out << "(reset)";
}

static void toStream(std::ostream& out, const ResetAssertionsCommand* c)
{
  out << "(reset-assertions)";
}

static void toStream(std::ostream& out, const QuitCommand* c)
{
  out << "(exit)";
}

static void toStream(std::ostream& out, const CommandSequence* c)
{
  CommandSequence::const_iterator i = c->begin();
  if(i != c->end()) {
    for(;;) {
      out << *i;
      if(++i != c->end()) {
        out << endl;
      } else {
        break;
      }
    }
  }
}

static void toStream(std::ostream& out, const DeclareFunctionCommand* c)
{
  Type type = c->getType();
  out << "(declare-fun " << CVC4::quoteSymbol(c->getSymbol()) << " (";
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

static void toStream(std::ostream& out, const DefineFunctionCommand* c)
{
  Expr func = c->getFunction();
  const vector<Expr>* formals = &c->getFormals();
  out << "(define-fun " << func << " (";
  Type type = func.getType();
  Expr formula = c->getFormula();
  if(type.isFunction()) {
    vector<Expr> f;
    if(formals->empty()) {
      const vector<Type>& params = FunctionType(type).getArgTypes();
      for(vector<Type>::const_iterator j = params.begin(); j != params.end(); ++j) {
        f.push_back(NodeManager::currentNM()->mkSkolem("a", TypeNode::fromType(*j), "",
                                                       NodeManager::SKOLEM_NO_NOTIFY).toExpr());
      }
      formula = NodeManager::currentNM()->toExprManager()->mkExpr(kind::APPLY_UF, formula, f);
      formals = &f;
    }
    vector<Expr>::const_iterator i = formals->begin();
    for(;;) {
      out << "(" << (*i) << " " << (*i).getType() << ")";
      ++i;
      if(i != formals->end()) {
        out << " ";
      } else {
        break;
      }
    }
    type = FunctionType(type).getRangeType();
  }
  out << ") " << type << " " << formula << ")";
}

static void toStream(std::ostream& out, const DefineFunctionRecCommand* c)
{
  const vector<Expr>& funcs = c->getFunctions();
  const vector<vector<Expr> >& formals = c->getFormals();
  out << "(define-fun";
  if (funcs.size() > 1)
  {
    out << "s";
  }
  out << "-rec ";
  if (funcs.size() > 1)
  {
    out << "(";
  }
  for (unsigned i = 0, size = funcs.size(); i < size; i++)
  {
    if (funcs.size() > 1)
    {
      if (i > 0)
      {
        out << " ";
      }
      out << "(";
    }
    out << funcs[i] << " (";
    // print its type signature
    vector<Expr>::const_iterator itf = formals[i].begin();
    for (;;)
    {
      out << "(" << (*itf) << " " << (*itf).getType() << ")";
      ++itf;
      if (itf != formals[i].end())
      {
        out << " ";
      }
      else
      {
        break;
      }
    }
    Type type = funcs[i].getType();
    type = static_cast<FunctionType>(type).getRangeType();
    out << ") " << type;
    if (funcs.size() > 1)
    {
      out << ")";
    }
  }
  if (funcs.size() > 1)
  {
    out << ") (";
  }
  const vector<Expr>& formulas = c->getFormulas();
  for (unsigned i = 0, size = formulas.size(); i < size; i++)
  {
    if (i > 0)
    {
      out << " ";
    }
    out << formulas[i];
  }
  if (funcs.size() > 1)
  {
    out << ")";
  }
  out << ")";
}

static void toStreamRational(std::ostream& out, const Rational& r, bool decimal)
{
  bool neg = r.sgn() < 0;

  // TODO:
  // We are currently printing (- (/ 5 3))
  // instead of (/ (- 5) 3) which is what is in the SMT-LIB value in the theory definition.
  // Before switching, I'll keep to what was there and send an email.

  // Tim: Apologies for the ifs on one line but in this case they are cleaner.

  if (neg) { out << "(- "; }

  if(r.isIntegral()) {
    if (neg) {
      out << (-r);
    }else {
      out << r;
    }
    if (decimal) { out << ".0"; }
  }else{
    out << "(/ ";
    if(neg) {
      Rational abs_r = (-r);
      out << abs_r.getNumerator();
      if(decimal) { out << ".0"; }
      out << ' ' << abs_r.getDenominator();
      if(decimal) { out << ".0"; }
    }else{
      out << r.getNumerator();
      if(decimal) { out << ".0"; }
      out << ' ' << r.getDenominator();
      if(decimal) { out << ".0"; }
    }
    out << ')';
  }

  if (neg) { out << ')';}

  // if(r < 0) {
  //   Rational abs_r = -r;
  //   if(r.isIntegral()) {
  //     out << "(- " << abs_r << ')';
  //   } else {
  //     out << "(- (/ " << (-r).getNumerator() << ' ' << (-r).getDenominator() << "))";
  //   }
  // } else {
  //   if(r.isIntegral()) {
  //         out << r;
  //       } else {
  //         out << "(/ " << r.getNumerator() << ' ' << r.getDenominator() << ')';
  //       }
  //     }
}

static void toStream(std::ostream& out, const DeclareTypeCommand* c)
{
  out << "(declare-sort " << c->getSymbol() << " " << c->getArity() << ")";
}

static void toStream(std::ostream& out, const DefineTypeCommand* c)
{
  const vector<Type>& params = c->getParameters();
  out << "(define-sort " << c->getSymbol() << " (";
  if(params.size() > 0) {
    copy( params.begin(), params.end() - 1,
          ostream_iterator<Type>(out, " ") );
    out << params.back();
  }
  out << ") " << c->getType() << ")";
}

static void toStream(std::ostream& out, const DefineNamedFunctionCommand* c)
{
  out << "DefineNamedFunction( ";
  toStream(out, static_cast<const DefineFunctionCommand*>(c));
  out << " )";

  out << "ERROR: don't know how to output define-named-function command" << endl;
}

static void toStream(std::ostream& out, const SimplifyCommand* c)
{
  out << "(simplify " << c->getTerm() << ")";
}

static void toStream(std::ostream& out, const GetValueCommand* c)
{
  out << "(get-value ( ";
  const vector<Expr>& terms = c->getTerms();
  copy(terms.begin(), terms.end(), ostream_iterator<Expr>(out, " "));
  out << "))";
}

static void toStream(std::ostream& out, const GetModelCommand* c)
{
  out << "(get-model)";
}

static void toStream(std::ostream& out, const GetAssignmentCommand* c)
{
  out << "(get-assignment)";
}

static void toStream(std::ostream& out, const GetAssertionsCommand* c)
{
  out << "(get-assertions)";
}

static void toStream(std::ostream& out, const GetProofCommand* c)
{
  out << "(get-proof)";
}

static void toStream(std::ostream& out, const GetUnsatCoreCommand* c)
{
  out << "(get-unsat-core)";
}

static void toStream(std::ostream& out,
                     const SetBenchmarkStatusCommand* c,
                     Variant v)
{
  if(v == z3str_variant || v == smt2_0_variant) {
    out << "(set-info :status " << c->getStatus() << ")";
  } else {
    out << "(meta-info :status " << c->getStatus() << ")";
  }
}

static void toStream(std::ostream& out,
                     const SetBenchmarkLogicCommand* c,
                     Variant v)
{
  // Z3-str doesn't have string-specific logic strings(?), so comment it
  if(v == z3str_variant) {
    out << "; (set-logic " << c->getLogic() << ")";
  } else {
    out << "(set-logic " << c->getLogic() << ")";
  }
}

static void toStream(std::ostream& out, const SetInfoCommand* c, Variant v)
{
  if(v == z3str_variant || v == smt2_0_variant) {
    out << "(set-info :" << c->getFlag() << " ";
  } else {
    out << "(meta-info :" << c->getFlag() << " ";
  }

  SExpr::toStream(out, c->getSExpr(), variantToLanguage(v));
  out << ")";
}

static void toStream(std::ostream& out, const GetInfoCommand* c)
{
  out << "(get-info :" << c->getFlag() << ")";
}

static void toStream(std::ostream& out, const SetOptionCommand* c)
{
  out << "(set-option :" << c->getFlag() << " ";
  SExpr::toStream(out, c->getSExpr(), language::output::LANG_SMTLIB_V2_5);
  out << ")";
}

static void toStream(std::ostream& out, const GetOptionCommand* c)
{
  out << "(get-option :" << c->getFlag() << ")";
}

static void toStream(std::ostream& out, const Datatype & d) {
  for(Datatype::const_iterator ctor = d.begin(), ctor_end = d.end();
      ctor != ctor_end; ++ctor){
    if( ctor!=d.begin() ) out << " ";
    out << "(" << maybeQuoteSymbol(ctor->getName());

    for(DatatypeConstructor::const_iterator arg = ctor->begin(), arg_end = ctor->end();
        arg != arg_end; ++arg){
      out << " (" << arg->getSelector() << " "
          << static_cast<SelectorType>(arg->getType()).getRangeType() << ")";
    }
    out << ")";
  }
}

static void toStream(std::ostream& out,
                     const DatatypeDeclarationCommand* c,
                     Variant v)
{
  const vector<DatatypeType>& datatypes = c->getDatatypes();
  out << "(declare-";
  Assert(!datatypes.empty());
  if (datatypes[0].getDatatype().isCodatatype())
  {
    out << "co";
  }
  out << "datatypes";
  if (v == smt2_6_variant)
  {
    out << " (";
    for (vector<DatatypeType>::const_iterator i = datatypes.begin(),
                                              i_end = datatypes.end();
         i != i_end;
         ++i)
    {
      const Datatype& d = i->getDatatype();
      out << "(" << maybeQuoteSymbol(d.getName());
      out << " " << d.getNumParameters() << ")";
    }
    out << ") (";
    for (vector<DatatypeType>::const_iterator i = datatypes.begin(),
                                              i_end = datatypes.end();
         i != i_end;
         ++i)
    {
      const Datatype& d = i->getDatatype();
      out << "(";
      toStream(out, d);
      out << ")" << endl;
    }
    out << ")";
  }
  else
  {
    out << " () (";
    for (vector<DatatypeType>::const_iterator i = datatypes.begin(),
                                              i_end = datatypes.end();
         i != i_end;
         ++i)
    {
      const Datatype& d = i->getDatatype();
      out << "(" << maybeQuoteSymbol(d.getName()) << " ";
      toStream(out, d);
      out << ")" << endl;
    }
    out << ")";
  }
  out << ")";
}

static void toStream(std::ostream& out, const CommentCommand* c, Variant v)
{
  string s = c->getComment();
  size_t pos = 0;
  while((pos = s.find_first_of('"', pos)) != string::npos) {
    s.replace(pos, 1, (v == z3str_variant || v == smt2_0_variant) ? "\\\"" : "\"\"");
    pos += 2;
  }
  out << "(set-info :notes \"" << s << "\")";
}

static void toStream(std::ostream& out, const EmptyCommand* c) {}

static void toStream(std::ostream& out, const EchoCommand* c, Variant v)
{
  std::string s = c->getOutput();
  // escape all double-quotes
  size_t pos = 0;
  while((pos = s.find('"', pos)) != string::npos) {
    s.replace(pos, 1, (v == z3str_variant || v == smt2_0_variant) ? "\\\"" : "\"\"");
    pos += 2;
  }
  out << "(echo \"" << s << "\")";
}

template <class T>
static bool tryToStream(std::ostream& out, const Command* c)
{
  if(typeid(*c) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(c));
    return true;
  }
  return false;
}

template <class T>
static bool tryToStream(std::ostream& out, const Command* c, Variant v)
{
  if(typeid(*c) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(c), v);
    return true;
  }
  return false;
}

static void toStream(std::ostream& out, const CommandSuccess* s, Variant v)
{
  if(Command::printsuccess::getPrintSuccess(out)) {
    out << "success" << endl;
  }
}

static void toStream(std::ostream& out, const CommandInterrupted* s, Variant v)
{
  out << "interrupted" << endl;
}

static void toStream(std::ostream& out, const CommandUnsupported* s, Variant v)
{
#ifdef CVC4_COMPETITION_MODE
  // if in competition mode, lie and say we're ok
  // (we have nothing to lose by saying success, and everything to lose
  // if we say "unsupported")
  out << "success" << endl;
#else /* CVC4_COMPETITION_MODE */
  out << "unsupported" << endl;
#endif /* CVC4_COMPETITION_MODE */
}

static void errorToStream(std::ostream& out, std::string message, Variant v) {
  // escape all double-quotes
  size_t pos = 0;
  while((pos = message.find('"', pos)) != string::npos) {
    message.replace(pos, 1, (v == z3str_variant || v == smt2_0_variant) ? "\\\"" : "\"\"");
    pos += 2;
  }
  out << "(error \"" << message << "\")" << endl;
}

static void toStream(std::ostream& out, const CommandFailure* s, Variant v) {
  errorToStream(out, s->getMessage(), v);
}

static void toStream(std::ostream& out, const CommandRecoverableFailure* s,
                     Variant v) {
  errorToStream(out, s->getMessage(), v);
}

template <class T>
static bool tryToStream(std::ostream& out, const CommandStatus* s, Variant v)
{
  if(typeid(*s) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(s), v);
    return true;
  }
  return false;
}

static OutputLanguage variantToLanguage(Variant variant)
{
  switch(variant) {
  case smt2_0_variant:
    return language::output::LANG_SMTLIB_V2_0;
  case z3str_variant:
    return language::output::LANG_Z3STR;
  case sygus_variant:
    return language::output::LANG_SYGUS;
  case no_variant:
  default:
    return language::output::LANG_SMTLIB_V2_5;
  }
}

}/* CVC4::printer::smt2 namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

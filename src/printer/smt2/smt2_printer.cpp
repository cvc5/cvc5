/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The pretty-printer interface for the SMT2 output language.
 */

#include "printer/smt2/smt2_printer.h"

#include <iostream>
#include <list>
#include <string>
#include <typeinfo>
#include <vector>

#include "api/cpp/cvc5.h"
#include "expr/array_store_all.h"
#include "expr/ascription_type.h"
#include "expr/datatype_index.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/emptybag.h"
#include "expr/emptyset.h"
#include "expr/node_manager_attributes.h"
#include "expr/node_visitor.h"
#include "expr/sequence.h"
#include "expr/uninterpreted_constant.h"
#include "options/bv_options.h"
#include "options/language.h"
#include "options/printer_options.h"
#include "options/smt_options.h"
#include "printer/let_binding.h"
#include "proof/unsat_core.h"
#include "smt/command.h"
#include "smt/node_command.h"
#include "smt/smt_engine.h"
#include "smt_util/boolean_simplification.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/datatypes/tuple_project_op.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/theory_model.h"
#include "util/bitvector.h"
#include "util/divisible.h"
#include "util/floatingpoint.h"
#include "util/iand.h"
#include "util/indexed_root_predicate.h"
#include "util/regexp.h"
#include "util/smt2_quote_string.h"
#include "util/string.h"

using namespace std;

namespace cvc5 {
namespace printer {
namespace smt2 {

static void toStreamRational(std::ostream& out,
                             const Rational& r,
                             bool decimal,
                             Variant v)
{
  bool neg = r.sgn() < 0;
  // Print the rational, possibly as decimal.
  // Notice that we print (/ (- 5) 3) instead of (- (/ 5 3)),
  // the former is compliant with real values in the smt lib standard.
  if (r.isIntegral())
  {
    if (neg)
    {
      out << "(- " << -r;
    }
    else
    {
      out << r;
    }
    if (decimal)
    {
      out << ".0";
    }
    if (neg)
    {
      out << ")";
    }
  }
  else
  {
    out << "(/ ";
    if (neg)
    {
      Rational abs_r = (-r);
      out << "(- " << abs_r.getNumerator();
      out << ") " << abs_r.getDenominator();
    }
    else
    {
      out << r.getNumerator();
      out << ' ' << r.getDenominator();
    }
    out << ')';
  }
}

void Smt2Printer::toStream(std::ostream& out,
                           TNode n,
                           int toDepth,
                           size_t dag) const
{
  if(dag != 0) {
    LetBinding lbind(dag + 1);
    toStreamWithLetify(out, n, toDepth, &lbind);
  } else {
    toStream(out, n, toDepth);
  }
}

void Smt2Printer::toStreamWithLetify(std::ostream& out,
                                     Node n,
                                     int toDepth,
                                     LetBinding* lbind) const
{
  if (lbind == nullptr)
  {
    toStream(out, n, toDepth);
    return;
  }
  std::stringstream cparen;
  std::vector<Node> letList;
  lbind->letify(n, letList);
  if (!letList.empty())
  {
    std::map<Node, uint32_t>::const_iterator it;
    for (size_t i = 0, nlets = letList.size(); i < nlets; i++)
    {
      Node nl = letList[i];
      out << "(let ((";
      uint32_t id = lbind->getId(nl);
      out << "_let_" << id << " ";
      Node nlc = lbind->convert(nl, "_let_", false);
      toStream(out, nlc, toDepth, lbind);
      out << ")) ";
      cparen << ")";
    }
  }
  Node nc = lbind->convert(n, "_let_");
  // print the body, passing the lbind object
  toStream(out, nc, toDepth, lbind);
  out << cparen.str();
  lbind->popScope();
}

void Smt2Printer::toStream(std::ostream& out,
                           TNode n,
                           int toDepth,
                           LetBinding* lbind) const
{
  // null
  if(n.getKind() == kind::NULL_EXPR) {
    out << "null";
    return;
  }

  NodeManager* nm = NodeManager::currentNM();
  // constant
  if(n.getMetaKind() == kind::metakind::CONSTANT) {
    switch(n.getKind()) {
    case kind::TYPE_CONSTANT:
      switch(n.getConst<TypeConstant>()) {
      case BOOLEAN_TYPE: out << "Bool"; break;
      case REAL_TYPE: out << "Real"; break;
      case INTEGER_TYPE: out << "Int"; break;
      case STRING_TYPE: out << "String"; break;
      case REGEXP_TYPE: out << "RegLan"; break;
      case ROUNDINGMODE_TYPE: out << "RoundingMode"; break;
      default:
        // fall back on whatever operator<< does on underlying type; we
        // might luck out and be SMT-LIB v2 compliant
        kind::metakind::NodeValueConstPrinter::toStream(out, n);
      }
      break;
    case kind::BITVECTOR_TYPE:
      out << "(_ BitVec " << n.getConst<BitVectorSize>().d_size << ")";
      break;
    case kind::FLOATINGPOINT_TYPE:
      out << "(_ FloatingPoint "
          << n.getConst<FloatingPointSize>().exponentWidth() << " "
          << n.getConst<FloatingPointSize>().significandWidth() << ")";
      break;
    case kind::CONST_BITVECTOR:
    {
      const BitVector& bv = n.getConst<BitVector>();
      if (options::bvPrintConstsAsIndexedSymbols())
      {
        out << "(_ bv" << bv.getValue() << " " << bv.getSize() << ")";
      }
      else
      {
        out << "#b" << bv.toString();
      }
      break;
    }
    case kind::CONST_FLOATINGPOINT:
    {
      out << n.getConst<FloatingPoint>().toString(
          options::bvPrintConstsAsIndexedSymbols());
      break;
    }
    case kind::CONST_ROUNDINGMODE:
      switch (n.getConst<RoundingMode>()) {
        case RoundingMode::ROUND_NEAREST_TIES_TO_EVEN:
          out << "roundNearestTiesToEven";
          break;
        case RoundingMode::ROUND_NEAREST_TIES_TO_AWAY:
          out << "roundNearestTiesToAway";
          break;
        case RoundingMode::ROUND_TOWARD_POSITIVE:
          out << "roundTowardPositive";
          break;
        case RoundingMode::ROUND_TOWARD_NEGATIVE:
          out << "roundTowardNegative";
          break;
        case RoundingMode::ROUND_TOWARD_ZERO: out << "roundTowardZero"; break;
        default:
          Unreachable() << "Invalid value of rounding mode constant ("
                        << n.getConst<RoundingMode>() << ")";
      }
      break;
    case kind::CONST_BOOLEAN:
      // the default would print "1" or "0" for bool, that's not correct
      // for our purposes
      out << (n.getConst<bool>() ? "true" : "false");
      break;
    case kind::BUILTIN:
      out << smtKindString(n.getConst<Kind>(), d_variant);
      break;
    case kind::CONST_RATIONAL: {
      const Rational& r = n.getConst<Rational>();
      toStreamRational(out, r, false, d_variant);
      break;
    }

    case kind::CONST_STRING: {
      std::string s = n.getConst<String>().toString();
      out << '"';
      for(size_t i = 0; i < s.size(); ++i) {
        char c = s[i];
        if(c == '"') {
          out << "\"\"";
        } else {
          out << c;
        }
      }
      out << '"';
      break;
    }
    case kind::CONST_SEQUENCE:
    {
      const Sequence& sn = n.getConst<Sequence>();
      const std::vector<Node>& snvec = sn.getVec();
      if (snvec.empty())
      {
        out << "(as seq.empty ";
        toStreamType(out, n.getType());
        out << ")";
      }
      if (snvec.size() > 1)
      {
        out << "(seq.++ ";
      }
      for (const Node& snvc : snvec)
      {
        out << "(seq.unit " << snvc << ")";
      }
      if (snvec.size() > 1)
      {
        out << ")";
      }
      break;
    }

    case kind::STORE_ALL: {
      ArrayStoreAll asa = n.getConst<ArrayStoreAll>();
      out << "((as const ";
      toStreamType(out, asa.getType());
      out << ") " << asa.getValue() << ")";
      break;
    }

    case kind::DATATYPE_TYPE:
    {
      const DType& dt = (NodeManager::currentNM()->getDTypeForIndex(
          n.getConst<DatatypeIndexConstant>().getIndex()));
      if (dt.isTuple())
      {
        unsigned int nargs = dt[0].getNumArgs();
        if (nargs == 0)
        {
          out << "Tuple";
        }
        else
        {
          out << "(Tuple";
          for (unsigned int i = 0; i < nargs; i++)
          {
            out << " ";
            toStreamType(out, dt[0][i].getRangeType());
          }
          out << ")";
        }
      }
      else
      {
        out << cvc5::quoteSymbol(dt.getName());
      }
      break;
    }
    
    case kind::UNINTERPRETED_CONSTANT: {
      const UninterpretedConstant& uc = n.getConst<UninterpretedConstant>();
      std::stringstream ss;
      ss << "(as @" << uc << " " << n.getType() << ")";
      out << ss.str();
      break;
    }

    case kind::EMPTYSET:
      out << "(as emptyset ";
      toStreamType(out, n.getConst<EmptySet>().getType());
      out << ")";
      break;

    case kind::EMPTYBAG:
      out << "(as emptybag ";
      toStreamType(out, n.getConst<EmptyBag>().getType());
      out << ")";
      break;
    case kind::BITVECTOR_EXTRACT_OP:
    {
      BitVectorExtract p = n.getConst<BitVectorExtract>();
      out << "(_ extract " << p.d_high << ' ' << p.d_low << ")";
      break;
    }
    case kind::BITVECTOR_REPEAT_OP:
      out << "(_ repeat " << n.getConst<BitVectorRepeat>().d_repeatAmount
          << ")";
      break;
    case kind::BITVECTOR_ZERO_EXTEND_OP:
      out << "(_ zero_extend "
          << n.getConst<BitVectorZeroExtend>().d_zeroExtendAmount << ")";
      break;
    case kind::BITVECTOR_SIGN_EXTEND_OP:
      out << "(_ sign_extend "
          << n.getConst<BitVectorSignExtend>().d_signExtendAmount << ")";
      break;
    case kind::BITVECTOR_ROTATE_LEFT_OP:
      out << "(_ rotate_left "
          << n.getConst<BitVectorRotateLeft>().d_rotateLeftAmount << ")";
      break;
    case kind::BITVECTOR_ROTATE_RIGHT_OP:
      out << "(_ rotate_right "
          << n.getConst<BitVectorRotateRight>().d_rotateRightAmount << ")";
      break;
    case kind::INT_TO_BITVECTOR_OP:
      out << "(_ int2bv " << n.getConst<IntToBitVector>().d_size << ")";
      break;
    case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP:
      out << "(_ to_fp "
          << n.getConst<FloatingPointToFPIEEEBitVector>()
                 .getSize()
                 .exponentWidth()
          << ' '
          << n.getConst<FloatingPointToFPIEEEBitVector>()
                 .getSize()
                 .significandWidth()
          << ")";
      break;
    case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP:
      out << "(_ to_fp "
          << n.getConst<FloatingPointToFPFloatingPoint>()
                 .getSize()
                 .exponentWidth()
          << ' '
          << n.getConst<FloatingPointToFPFloatingPoint>()
                 .getSize()
                 .significandWidth()
          << ")";
      break;
    case kind::FLOATINGPOINT_TO_FP_REAL_OP:
      out << "(_ to_fp "
          << n.getConst<FloatingPointToFPReal>().getSize().exponentWidth()
          << ' '
          << n.getConst<FloatingPointToFPReal>().getSize().significandWidth()
          << ")";
      break;
    case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP:
      out << "(_ to_fp "
          << n.getConst<FloatingPointToFPSignedBitVector>()
                 .getSize()
                 .exponentWidth()
          << ' '
          << n.getConst<FloatingPointToFPSignedBitVector>()
                 .getSize()
                 .significandWidth()
          << ")";
      break;
    case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP:
      out << "(_ to_fp_unsigned "
          << n.getConst<FloatingPointToFPUnsignedBitVector>()
                 .getSize()
                 .exponentWidth()
          << ' '
          << n.getConst<FloatingPointToFPUnsignedBitVector>()
                 .getSize()
                 .significandWidth()
          << ")";
      break;
    case kind::FLOATINGPOINT_TO_FP_GENERIC_OP:
      out << "(_ to_fp "
          << n.getConst<FloatingPointToFPGeneric>().getSize().exponentWidth()
          << ' '
          << n.getConst<FloatingPointToFPGeneric>().getSize().significandWidth()
          << ")";
      break;
    case kind::FLOATINGPOINT_TO_UBV_OP:
      out << "(_ fp.to_ubv "
          << n.getConst<FloatingPointToUBV>().d_bv_size.d_size << ")";
      break;
    case kind::FLOATINGPOINT_TO_SBV_OP:
      out << "(_ fp.to_sbv "
          << n.getConst<FloatingPointToSBV>().d_bv_size.d_size << ")";
      break;
    case kind::FLOATINGPOINT_TO_UBV_TOTAL_OP:
      out << "(_ fp.to_ubv_total "
          << n.getConst<FloatingPointToUBVTotal>().d_bv_size.d_size << ")";
      break;
    case kind::FLOATINGPOINT_TO_SBV_TOTAL_OP:
      out << "(_ fp.to_sbv_total "
          << n.getConst<FloatingPointToSBVTotal>().d_bv_size.d_size << ")";
      break;
    case kind::REGEXP_REPEAT_OP:
      out << "(_ re.^ " << n.getConst<RegExpRepeat>().d_repeatAmount << ")";
      break;
    case kind::REGEXP_LOOP_OP:
      out << "(_ re.loop " << n.getConst<RegExpLoop>().d_loopMinOcc << " "
          << n.getConst<RegExpLoop>().d_loopMaxOcc << ")";
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
      out << cvc5::quoteSymbol(name);
    }
    if(n.getNumChildren() != 0) {
      for(unsigned i = 0; i < n.getNumChildren(); ++i) {
	      out << ' ';
              toStream(out, n[i], toDepth);
      }
      out << ')';
    }
    return;
  }

  // determine if we are printing out a type ascription, store the argument of
  // the type ascription into type_asc_arg.
  Kind k = n.getKind();
  Node type_asc_arg;
  TypeNode force_nt;
  if (k == kind::APPLY_TYPE_ASCRIPTION)
  {
    force_nt = n.getOperator().getConst<AscriptionType>().getType();
    type_asc_arg = n[0];
  }
  else if (k == kind::CAST_TO_REAL)
  {
    force_nt = nm->realType();
    type_asc_arg = n[0];
  }
  if (!type_asc_arg.isNull())
  {
    if (force_nt.isReal())
    {
      // we prefer using (/ x 1) instead of (to_real x) here.
      // the reason is that (/ x 1) is SMT-LIB compliant when x is a constant
      // or the logic is non-linear, whereas (to_real x) is compliant when
      // the logic is mixed int/real. The former occurs more frequently.
      bool is_int = force_nt.isInteger();
      // If constant rational, print as special case
      if (type_asc_arg.getKind() == kind::CONST_RATIONAL)
      {
        const Rational& r = type_asc_arg.getConst<Rational>();
        toStreamRational(out, r, !is_int, d_variant);
      }
      else
      {
        out << "("
            << smtKindString(is_int ? kind::TO_INTEGER : kind::DIVISION,
                             d_variant)
            << " ";
        toStream(out, type_asc_arg, toDepth, lbind);
        if (!is_int)
        {
          out << " 1";
        }
        out << ")";
      }
    }
    else
    {
      // use type ascription
      out << "(as ";
      toStream(out, type_asc_arg, toDepth < 0 ? toDepth : toDepth - 1, lbind);
      out << " " << force_nt << ")";
    }
    return;
  }

  // variable
  if (n.isVar())
  {
    string s;
    if (n.getAttribute(expr::VarNameAttr(), s))
    {
      out << cvc5::quoteSymbol(s);
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
    return;
  }

  bool stillNeedToPrintParams = true;
  bool forceBinary = false; // force N-ary to binary when outputing children
  // operator
  if (n.getNumChildren() != 0 && k != kind::CONSTRUCTOR_TYPE)
  {
    out << '(';
  }
  switch(k) {
    // builtin theory
  case kind::EQUAL:
  case kind::DISTINCT:
    out << smtKindString(k, d_variant) << " ";
    break;
  case kind::FUNCTION_TYPE:
    out << "->";
    for (Node nc : n)
    {
      out << " ";
      toStream(out, nc, toDepth);
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
  case kind::ITE:
    out << smtKindString(k, d_variant) << " ";
    break;

  // uf theory
  case kind::APPLY_UF: break;
  // higher-order
  case kind::HO_APPLY:
    if (!options::flattenHOChains())
    {
      break;
    }
    // collapse "@" chains, i.e.
    //
    // ((a b) c) --> (a b c)
    //
    // (((a b) ((c d) e)) f) --> (a b (c d e) f)
    {
      Node head = n;
      std::vector<Node> args;
      while (head.getKind() == kind::HO_APPLY)
      {
        args.insert(args.begin(), head[1]);
        head = head[0];
      }
      toStream(out, head, toDepth, lbind);
      for (unsigned i = 0, size = args.size(); i < size; ++i)
      {
        out << " ";
        toStream(out, args[i], toDepth, lbind);
      }
      out << ")";
    }
    return;

  case kind::MATCH:
    out << smtKindString(k, d_variant) << " ";
    toStream(out, n[0], toDepth, lbind);
    out << " (";
    for (size_t i = 1, nchild = n.getNumChildren(); i < nchild; i++)
    {
      if (i > 1)
      {
        out << " ";
      }
      toStream(out, n[i], toDepth, lbind);
    }
    out << "))";
    return;
  case kind::MATCH_BIND_CASE:
    // ignore the binder
    toStream(out, n[1], toDepth, lbind);
    out << " ";
    toStream(out, n[2], toDepth, lbind);
    out << ")";
    return;
  case kind::MATCH_CASE:
    // do nothing
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
  case kind::PI:
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
    out << smtKindString(k, d_variant) << " ";
    break;
  case kind::IAND:
    out << "(_ iand " << n.getOperator().getConst<IntAnd>().d_size << ") ";
    stillNeedToPrintParams = false;
    break;

  case kind::DIVISIBLE:
    out << "(_ divisible " << n.getOperator().getConst<Divisible>().k << ")";
    stillNeedToPrintParams = false;
    break;
  case kind::INDEXED_ROOT_PREDICATE_OP:
  {
    const IndexedRootPredicate& irp = n.getConst<IndexedRootPredicate>();
    out << "(_ root_predicate " << irp.d_index << ")";
    break;
  }

    // arrays theory
  case kind::SELECT:
  case kind::STORE:
  case kind::PARTIAL_SELECT_0:
  case kind::PARTIAL_SELECT_1:
  case kind::ARRAY_TYPE:
  case kind::EQ_RANGE: out << smtKindString(k, d_variant) << " "; break;

  // string theory
  case kind::STRING_CONCAT:
    out << "str.++ ";
    break;
  case kind::STRING_IN_REGEXP: {
    stringstream ss;
    out << smtKindString(k, d_variant) << " ";
    break;
  }
  case kind::STRING_LENGTH:
  case kind::STRING_SUBSTR:
  case kind::STRING_UPDATE:
  case kind::STRING_CHARAT:
  case kind::STRING_STRCTN:
  case kind::STRING_STRIDOF:
  case kind::STRING_INDEXOF_RE:
  case kind::STRING_STRREPL:
  case kind::STRING_STRREPLALL:
  case kind::STRING_REPLACE_RE:
  case kind::STRING_REPLACE_RE_ALL:
  case kind::STRING_TOLOWER:
  case kind::STRING_TOUPPER:
  case kind::STRING_REV:
  case kind::STRING_PREFIX:
  case kind::STRING_SUFFIX:
  case kind::STRING_LEQ:
  case kind::STRING_LT:
  case kind::STRING_ITOS:
  case kind::STRING_STOI:
  case kind::STRING_FROM_CODE:
  case kind::STRING_TO_CODE:
  case kind::STRING_TO_REGEXP:
  case kind::REGEXP_CONCAT:
  case kind::REGEXP_UNION:
  case kind::REGEXP_INTER:
  case kind::REGEXP_STAR:
  case kind::REGEXP_PLUS:
  case kind::REGEXP_OPT:
  case kind::REGEXP_RANGE:
  case kind::REGEXP_COMPLEMENT:
  case kind::REGEXP_DIFF:
  case kind::REGEXP_EMPTY:
  case kind::REGEXP_SIGMA:
  case kind::SEQ_UNIT:
  case kind::SEQ_NTH:
  case kind::SEQUENCE_TYPE: out << smtKindString(k, d_variant) << " "; break;
  case kind::REGEXP_REPEAT:
  case kind::REGEXP_LOOP:
  {
    out << n.getOperator() << ' ';
    stillNeedToPrintParams = false;
    break;
  }

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
  case kind::BITVECTOR_ADD:
    out << "bvadd ";
    forceBinary = true;
    break;
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
    toStream(out, n.getOperator(), toDepth, nullptr);
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
    out << smtKindString(k, d_variant) << " ";
    break;
  case kind::COMPREHENSION: out << smtKindString(k, d_variant) << " "; break;
  case kind::SINGLETON:
  {
    out << smtKindString(k, d_variant) << " ";
    TypeNode elemType = n.getType().getSetElementType();
    toStreamCastToType(
        out, n[0], toDepth < 0 ? toDepth : toDepth - 1, elemType);
    out << ")";
    return;
  }
  break;
  case kind::MEMBER:
  case kind::INSERT:
  case kind::SET_TYPE:
  case kind::COMPLEMENT:
  case kind::CHOOSE:
  case kind::IS_SINGLETON: out << smtKindString(k, d_variant) << " "; break;
  case kind::UNIVERSE_SET:out << "(as univset " << n.getType() << ")";break;

  // bags
  case kind::BAG_TYPE:
  case kind::UNION_MAX:
  case kind::UNION_DISJOINT:
  case kind::INTERSECTION_MIN:
  case kind::DIFFERENCE_SUBTRACT:
  case kind::DIFFERENCE_REMOVE:
  case kind::SUBBAG:
  case kind::BAG_COUNT:
  case kind::DUPLICATE_REMOVAL:
  case kind::BAG_CARD:
  case kind::BAG_CHOOSE:
  case kind::BAG_IS_SINGLETON:
  case kind::BAG_FROM_SET:
  case kind::BAG_TO_SET: out << smtKindString(k, d_variant) << " "; break;
  case kind::MK_BAG:
  {
    // print (bag (mkBag_op Real) 1 3) as (bag 1.0 3)
    out << smtKindString(k, d_variant) << " ";
    TypeNode elemType = n.getType().getBagElementType();
    toStreamCastToType(
        out, n[0], toDepth < 0 ? toDepth : toDepth - 1, elemType);
    out << " " << n[1] << ")";
    return;
  }

    // fp theory
  case kind::FLOATINGPOINT_FP:
  case kind::FLOATINGPOINT_EQ:
  case kind::FLOATINGPOINT_ABS:
  case kind::FLOATINGPOINT_NEG:
  case kind::FLOATINGPOINT_ADD:
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
  case kind::FLOATINGPOINT_COMPONENT_NAN:
  case kind::FLOATINGPOINT_COMPONENT_INF:
  case kind::FLOATINGPOINT_COMPONENT_ZERO:
  case kind::FLOATINGPOINT_COMPONENT_SIGN:
  case kind::FLOATINGPOINT_COMPONENT_EXPONENT:
  case kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND:
  case kind::ROUNDINGMODE_BITBLAST:
    out << smtKindString(k, d_variant) << ' ';
    break;

  case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR:
  case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT:
  case kind::FLOATINGPOINT_TO_FP_REAL:
  case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR:
  case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR:
  case kind::FLOATINGPOINT_TO_FP_GENERIC:
  case kind::FLOATINGPOINT_TO_UBV:
  case kind::FLOATINGPOINT_TO_SBV:
    out << n.getOperator() << ' ';
    stillNeedToPrintParams = false;
    break;

  case kind::APPLY_CONSTRUCTOR:
  {
    const DType& dt = DType::datatypeOf(n.getOperator());
    if (dt.isTuple())
    {
      stillNeedToPrintParams = false;
      out << "mkTuple" << ( dt[0].getNumArgs()==0 ? "" : " ");
    }
    break;
  }
  case kind::TUPLE_PROJECT:
  {
    TupleProjectOp op = n.getOperator().getConst<TupleProjectOp>();
    if (op.getIndices().empty())
    {
      // e.g. (tuple_project tuple)
      out << "project " << n[0] << ")";
    }
    else
    {
      // e.g. ((_ tuple_project 2 4 4) tuple)
      out << "(_ tuple_project" << op << ") " << n[0] << ")";
    }
    return;
  }
  case kind::CONSTRUCTOR_TYPE:
  {
    out << n[n.getNumChildren()-1];
    return;
    break;
  }
  case kind::APPLY_SELECTOR:
  {
    Node op = n.getOperator();
    const DType& dt = DType::datatypeOf(op);
    if (dt.isTuple())
    {
      stillNeedToPrintParams = false;
      out << "(_ tupSel " << DType::indexOf(op) << ") ";
    }
  }
  break;
  case kind::APPLY_TESTER:
  {
    stillNeedToPrintParams = false;
    Node op = n.getOperator();
    size_t cindex = DType::indexOf(op);
    const DType& dt = DType::datatypeOf(op);
    out << "(_ is ";
    toStream(
        out, dt[cindex].getConstructor(), toDepth < 0 ? toDepth : toDepth - 1);
    out << ") ";
  }
  break;
  case kind::APPLY_UPDATER:
  {
    Node op = n.getOperator();
    size_t index = DType::indexOf(op);
    const DType& dt = DType::datatypeOf(op);
    size_t cindex = DType::cindexOf(op);
    out << "(_ update ";
    toStream(out,
             dt[cindex][index].getSelector(),
             toDepth < 0 ? toDepth : toDepth - 1);
    out << ") ";
  }
  break;
  case kind::APPLY_SELECTOR_TOTAL:
  case kind::PARAMETRIC_DATATYPE: break;

  // separation logic
  case kind::SEP_EMP:
  case kind::SEP_PTO:
  case kind::SEP_STAR:
  case kind::SEP_WAND: out << smtKindString(k, d_variant) << " "; break;

  case kind::SEP_NIL:
    out << "(as sep.nil " << n.getType() << ")";
    break;

    // quantifiers
  case kind::FORALL:
  case kind::EXISTS:
  case kind::LAMBDA:
  case kind::WITNESS:
  {
    out << smtKindString(k, d_variant) << " ";
    // do not letify the bound variable list
    toStream(out, n[0], toDepth, nullptr);
    out << " ";
    std::stringstream annot;
    if (n.getNumChildren() == 3)
    {
      annot << " ";
      for (const Node& nc : n[2])
      {
        if (nc.getKind() == kind::INST_PATTERN)
        {
          out << "(! ";
          annot << ":pattern ";
          toStream(annot, nc, toDepth, nullptr);
          annot << ") ";
        }
        else if (nc.getKind() == kind::INST_NO_PATTERN)
        {
          out << "(! ";
          annot << ":no-pattern ";
          toStream(annot, nc, toDepth, nullptr);
          annot << ") ";
        }
      }
    }
    // Use a fresh let binder, since using existing let symbols may violate
    // scoping issues for let-bound variables, see explanation in let_binding.h.
    size_t dag = lbind == nullptr ? 0 : lbind->getThreshold()-1;
    toStream(out, n[1], toDepth - 1, dag);
    out << annot.str() << ")";
    return;
    break;
  }
  case kind::BOUND_VAR_LIST:
  {
    // the left parenthesis is already printed (before the switch)
    for (TNode::iterator i = n.begin(), iend = n.end(); i != iend;)
    {
      out << '(';
      toStream(out, *i, toDepth < 0 ? toDepth : toDepth - 1);
      out << ' ';
      out << (*i).getType();
      out << ')';
      if (++i != iend)
      {
        out << ' ';
      }
    }
    out << ')';
    return;
  }
  case kind::INST_PATTERN:
  case kind::INST_NO_PATTERN:
  case kind::INST_PATTERN_LIST: break;
  default:
    // fall back on however the kind prints itself; this probably
    // won't be SMT-LIB v2 compliant, but it will be clear from the
    // output that support for the kind needs to be added here.
    out << n.getKind() << ' ';
  }
  if( n.getMetaKind() == kind::metakind::PARAMETERIZED &&
      stillNeedToPrintParams ) {
    if(toDepth != 0) {
      toStream(
          out, n.getOperator(), toDepth < 0 ? toDepth : toDepth - 1, lbind);
    } else {
      out << "(...)";
    }
    if(n.getNumChildren() > 0) {
      out << ' ';
    }
  }
  stringstream parens;
  
  for(size_t i = 0, c = 1; i < n.getNumChildren(); ) {
    if(toDepth != 0) {
      toStream(out, n[i], toDepth < 0 ? toDepth : toDepth - c, lbind);
    } else {
      out << "(...)";
    }
    if(++i < n.getNumChildren()) {
      if(forceBinary && i < n.getNumChildren() - 1) {
        // not going to work properly for parameterized kinds!
        Assert(n.getMetaKind() != kind::metakind::PARAMETERIZED);
        out << " (" << smtKindString(n.getKind(), d_variant) << ' ';
        parens << ')';
        ++c;
      } else {
        out << ' ';
      }
    }
  }
  if (n.getNumChildren() != 0)
  {
    out << parens.str() << ')';
  }
}

void Smt2Printer::toStreamCastToType(std::ostream& out,
                                     TNode n,
                                     int toDepth,
                                     TypeNode tn) const
{
  Node nasc;
  if (n.getType().isInteger() && !tn.isInteger())
  {
    Assert(tn.isReal());
    // probably due to subtyping integers and reals, cast it
    nasc = NodeManager::currentNM()->mkNode(kind::CAST_TO_REAL, n);
  }
  else
  {
    nasc = n;
  }
  toStream(out, nasc, toDepth);
}

std::string Smt2Printer::smtKindString(Kind k, Variant v)
{
  switch(k) {
    // builtin theory
  case kind::EQUAL: return "=";
  case kind::DISTINCT: return "distinct";
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

  case kind::LAMBDA: return "lambda";
  case kind::MATCH: return "match";
  case kind::WITNESS: return "witness";

  // arith theory
  case kind::PLUS: return "+";
  case kind::MULT:
  case kind::NONLINEAR_MULT: return "*";
  case kind::IAND: return "iand";
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
  case kind::PI: return "real.pi";
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
  case kind::EQ_RANGE:
    return "eqrange";

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
  case kind::BITVECTOR_ADD: return "bvadd";
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
  case kind::BITVECTOR_TO_NAT: return "bv2nat";
  case kind::BITVECTOR_REDOR: return "bvredor";
  case kind::BITVECTOR_REDAND: return "bvredand";

  case kind::BITVECTOR_EXTRACT: return "extract";
  case kind::BITVECTOR_REPEAT: return "repeat";
  case kind::BITVECTOR_ZERO_EXTEND: return "zero_extend";
  case kind::BITVECTOR_SIGN_EXTEND: return "sign_extend";
  case kind::BITVECTOR_ROTATE_LEFT: return "rotate_left";
  case kind::BITVECTOR_ROTATE_RIGHT: return "rotate_right";
  case kind::INT_TO_BITVECTOR: return "int2bv";

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
  case kind::COMPREHENSION: return "comprehension";
  case kind::CHOOSE: return "choose";
  case kind::IS_SINGLETON: return "is_singleton";
  case kind::JOIN: return "join";
  case kind::PRODUCT: return "product";
  case kind::TRANSPOSE: return "transpose";
  case kind::TCLOSURE: return "tclosure";

  // bag theory
  case kind::BAG_TYPE: return "Bag";
  case kind::UNION_MAX: return "union_max";
  case kind::UNION_DISJOINT: return "union_disjoint";
  case kind::INTERSECTION_MIN: return "intersection_min";
  case kind::DIFFERENCE_SUBTRACT: return "difference_subtract";
  case kind::DIFFERENCE_REMOVE: return "difference_remove";
  case kind::SUBBAG: return "subbag";
  case kind::BAG_COUNT: return "bag.count";
  case kind::DUPLICATE_REMOVAL: return "duplicate_removal";
  case kind::MK_BAG: return "bag";
  case kind::BAG_CARD: return "bag.card";
  case kind::BAG_CHOOSE: return "bag.choose";
  case kind::BAG_IS_SINGLETON: return "bag.is_singleton";
  case kind::BAG_FROM_SET: return "bag.from_set";
  case kind::BAG_TO_SET: return "bag.to_set";

    // fp theory
  case kind::FLOATINGPOINT_FP: return "fp";
  case kind::FLOATINGPOINT_EQ: return "fp.eq";
  case kind::FLOATINGPOINT_ABS: return "fp.abs";
  case kind::FLOATINGPOINT_NEG: return "fp.neg";
  case kind::FLOATINGPOINT_ADD: return "fp.add";
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

  case kind::FLOATINGPOINT_COMPONENT_NAN: return "NAN";
  case kind::FLOATINGPOINT_COMPONENT_INF: return "INF";
  case kind::FLOATINGPOINT_COMPONENT_ZERO: return "ZERO";
  case kind::FLOATINGPOINT_COMPONENT_SIGN: return "SIGN";
  case kind::FLOATINGPOINT_COMPONENT_EXPONENT: return "EXPONENT";
  case kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND: return "SIGNIFICAND";
  case kind::ROUNDINGMODE_BITBLAST:
    return "RMBITBLAST";

  //string theory
  case kind::STRING_CONCAT: return "str.++";
  case kind::STRING_LENGTH: return "str.len";
  case kind::STRING_SUBSTR: return "str.substr" ;
  case kind::STRING_UPDATE: return "str.update";
  case kind::STRING_STRCTN: return "str.contains" ;
  case kind::STRING_CHARAT: return "str.at" ;
  case kind::STRING_STRIDOF: return "str.indexof" ;
  case kind::STRING_INDEXOF_RE: return "str.indexof_re";
  case kind::STRING_STRREPL: return "str.replace" ;
  case kind::STRING_STRREPLALL: return "str.replace_all";
  case kind::STRING_REPLACE_RE: return "str.replace_re";
  case kind::STRING_REPLACE_RE_ALL: return "str.replace_re_all";
  case kind::STRING_TOLOWER: return "str.tolower";
  case kind::STRING_TOUPPER: return "str.toupper";
  case kind::STRING_REV: return "str.rev";
  case kind::STRING_PREFIX: return "str.prefixof" ;
  case kind::STRING_SUFFIX: return "str.suffixof" ;
  case kind::STRING_LEQ: return "str.<=";
  case kind::STRING_LT: return "str.<";
  case kind::STRING_FROM_CODE: return "str.from_code";
  case kind::STRING_TO_CODE: return "str.to_code";
  case kind::STRING_ITOS: return "str.from_int";
  case kind::STRING_STOI: return "str.to_int";
  case kind::STRING_IN_REGEXP: return "str.in_re";
  case kind::STRING_TO_REGEXP: return "str.to_re";
  case kind::REGEXP_EMPTY: return "re.none";
  case kind::REGEXP_SIGMA: return "re.allchar";
  case kind::REGEXP_CONCAT: return "re.++";
  case kind::REGEXP_UNION: return "re.union";
  case kind::REGEXP_INTER: return "re.inter";
  case kind::REGEXP_STAR: return "re.*";
  case kind::REGEXP_PLUS: return "re.+";
  case kind::REGEXP_OPT: return "re.opt";
  case kind::REGEXP_RANGE: return "re.range";
  case kind::REGEXP_REPEAT: return "re.^";
  case kind::REGEXP_LOOP: return "re.loop";
  case kind::REGEXP_COMPLEMENT: return "re.comp";
  case kind::REGEXP_DIFF: return "re.diff";
  case kind::SEQUENCE_TYPE: return "Seq";
  case kind::SEQ_UNIT: return "seq.unit";
  case kind::SEQ_NTH: return "seq.nth";

  //sep theory
  case kind::SEP_STAR: return "sep";
  case kind::SEP_PTO: return "pto";
  case kind::SEP_WAND: return "wand";
  case kind::SEP_EMP: return "emp";

  // quantifiers
  case kind::FORALL: return "forall";
  case kind::EXISTS: return "exists";

  default:
    ; /* fall through */
  }

  // no SMT way to print these
  return kind::kindToString(k);
}

void Smt2Printer::toStreamType(std::ostream& out, TypeNode tn) const
{
  // we currently must call TypeNode::toStream here.
  tn.toStream(out, language::output::LANG_SMTLIB_V2_6);
}

template <class T>
static bool tryToStream(std::ostream& out, const Command* c);
template <class T>
static bool tryToStream(std::ostream& out, const Command* c, Variant v);

static std::string quoteSymbol(TNode n) {
  std::stringstream ss;
  ss << n;
  return cvc5::quoteSymbol(ss.str());
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
  if (core.useNames())
  {
    // use the names
    const std::vector<std::string>& cnames = core.getCoreNames();
    for (const std::string& cn : cnames)
    {
      out << cvc5::quoteSymbol(cn) << std::endl;
    }
  }
  else
  {
    // otherwise, use the formulas
    for (UnsatCore::const_iterator i = core.begin(); i != core.end(); ++i)
    {
      out << *i << endl;
    }
  }
  out << ")" << endl;
}/* Smt2Printer::toStream(UnsatCore, map<Expr, string>) */

void Smt2Printer::toStream(std::ostream& out, const smt::Model& m) const
{
  const theory::TheoryModel* tm = m.getTheoryModel();
  //print the model comments
  std::stringstream c;
  tm->getComments(c);
  std::string ln;
  while( std::getline( c, ln ) ){
    out << "; " << ln << std::endl;
  }
  //print the model
  out << "(" << endl;
  // don't need to print approximations since they are built into choice
  // functions in the values of variables.
  this->Printer::toStream(out, m);
  out << ")" << endl;
  //print the heap model, if it exists
  Node h, neq;
  if (tm->getHeapModel(h, neq))
  {
    // description of the heap+what nil is equal to fully describes model
    out << "(heap" << endl;
    out << h << endl;
    out << neq << endl;
    out << ")" << std::endl;
  }
}

void Smt2Printer::toStreamModelSort(std::ostream& out,
                                    const smt::Model& m,
                                    TypeNode tn) const
{
  if (!tn.isSort())
  {
    out << "ERROR: don't know how to print non uninterpreted sort in model: "
        << tn << std::endl;
    return;
  }
  const theory::TheoryModel* tm = m.getTheoryModel();
  std::vector<Node> elements = tm->getDomainElements(tn);
  if (options::modelUninterpPrint() == options::ModelUninterpPrintMode::DtEnum)
  {
    out << "(declare-datatypes ((" << tn << " 0)) (";
    for (const Node& type_ref : elements)
    {
      out << "(" << type_ref << ")";
    }
    out << ")))" << endl;
    return;
  }
  // print the cardinality
  out << "; cardinality of " << tn << " is " << elements.size() << endl;
  if (options::modelUninterpPrint()
      == options::ModelUninterpPrintMode::DeclSortAndFun)
  {
    toStreamCmdDeclareType(out, tn);
  }
  // print the representatives
  for (const Node& trn : elements)
  {
    if (trn.isVar())
    {
      if (options::modelUninterpPrint()
              == options::ModelUninterpPrintMode::DeclSortAndFun
          || options::modelUninterpPrint()
                 == options::ModelUninterpPrintMode::DeclFun)
      {
        out << "(declare-fun " << quoteSymbol(trn) << " () " << tn << ")"
            << endl;
      }
    }
    else
    {
      out << "; rep: " << trn << endl;
    }
  }
}

void Smt2Printer::toStreamModelTerm(std::ostream& out,
                                    const smt::Model& m,
                                    Node n) const
{
  const theory::TheoryModel* tm = m.getTheoryModel();
  // We get the value from the theory model directly, which notice
  // does not have to go through the standard SmtEngine::getValue interface.
  Node val = tm->getValue(n);
  if (val.getKind() == kind::LAMBDA)
  {
    TypeNode rangeType = n.getType().getRangeType();
    out << "(define-fun " << n << " " << val[0] << " " << rangeType << " ";
    // call toStream and force its type to be proper
    toStreamCastToType(out, val[1], -1, rangeType);
    out << ")" << endl;
  }
  else
  {
    if (options::modelUninterpPrint() == options::ModelUninterpPrintMode::DtEnum
        && val.getKind() == kind::STORE)
    {
      TypeNode tn = val[1].getType();
      const std::vector<Node>* type_refs =
          tm->getRepSet()->getTypeRepsOrNull(tn);
      if (tn.isSort() && type_refs != nullptr)
      {
        Cardinality indexCard(type_refs->size());
        val = theory::arrays::TheoryArraysRewriter::normalizeConstant(
            val, indexCard);
      }
    }
    out << "(define-fun " << n << " () " << n.getType() << " ";
    // call toStream and force its type to be proper
    toStreamCastToType(out, val, -1, n.getType());
    out << ")" << endl;
  }
}

void Smt2Printer::toStreamCmdAssert(std::ostream& out, Node n) const
{
  out << "(assert " << n << ')' << std::endl;
}

void Smt2Printer::toStreamCmdPush(std::ostream& out) const
{
  out << "(push 1)" << std::endl;
}

void Smt2Printer::toStreamCmdPop(std::ostream& out) const
{
  out << "(pop 1)" << std::endl;
}

void Smt2Printer::toStreamCmdCheckSat(std::ostream& out, Node n) const
{
  if (!n.isNull())
  {
    toStreamCmdPush(out);
    out << std::endl;
    toStreamCmdAssert(out, n);
    out << std::endl;
    toStreamCmdCheckSat(out);
    out << std::endl;
    toStreamCmdPop(out);
  }
  else
  {
    out << "(check-sat)";
  }
  out << std::endl;
}

void Smt2Printer::toStreamCmdCheckSatAssuming(
    std::ostream& out, const std::vector<Node>& nodes) const
{
  out << "(check-sat-assuming ( ";
  copy(nodes.begin(), nodes.end(), ostream_iterator<Node>(out, " "));
  out << "))" << std::endl;
}

void Smt2Printer::toStreamCmdQuery(std::ostream& out, Node n) const
{
  if (!n.isNull())
  {
    toStreamCmdCheckSatAssuming(out, {n});
  }
  else
  {
    toStreamCmdCheckSat(out);
  }
}

void Smt2Printer::toStreamCmdReset(std::ostream& out) const
{
  out << "(reset)" << std::endl;
}

void Smt2Printer::toStreamCmdResetAssertions(std::ostream& out) const
{
  out << "(reset-assertions)" << std::endl;
}

void Smt2Printer::toStreamCmdQuit(std::ostream& out) const
{
  out << "(exit)" << std::endl;
}

void Smt2Printer::toStreamCmdCommandSequence(
    std::ostream& out, const std::vector<Command*>& sequence) const
{
  for (Command* i : sequence)
  {
    out << *i;
  }
}

void Smt2Printer::toStreamCmdDeclarationSequence(
    std::ostream& out, const std::vector<Command*>& sequence) const
{
  toStreamCmdCommandSequence(out, sequence);
}

void Smt2Printer::toStreamCmdDeclareFunction(std::ostream& out,
                                             const std::string& id,
                                             TypeNode type) const
{
  out << "(declare-fun " << cvc5::quoteSymbol(id) << " (";
  if (type.isFunction())
  {
    const vector<TypeNode> argTypes = type.getArgTypes();
    if (argTypes.size() > 0)
    {
      copy(argTypes.begin(),
           argTypes.end() - 1,
           ostream_iterator<TypeNode>(out, " "));
      out << argTypes.back();
    }
    type = type.getRangeType();
  }

  out << ") " << type << ')' << std::endl;
}

void Smt2Printer::toStreamCmdDefineFunction(std::ostream& out,
                                            const std::string& id,
                                            const std::vector<Node>& formals,
                                            TypeNode range,
                                            Node formula) const
{
  out << "(define-fun " << id << " (";
  if (!formals.empty())
  {
    vector<Node>::const_iterator i = formals.cbegin();
    for (;;)
    {
      out << "(" << (*i) << " " << (*i).getType() << ")";
      ++i;
      if (i != formals.cend())
      {
        out << " ";
      }
      else
      {
        break;
      }
    }
  }
  out << ") " << range << ' ' << formula << ')' << std::endl;
}

void Smt2Printer::toStreamCmdDefineFunctionRec(
    std::ostream& out,
    const std::vector<Node>& funcs,
    const std::vector<std::vector<Node>>& formals,
    const std::vector<Node>& formulas) const
{
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
    vector<Node>::const_iterator itf = formals[i].cbegin();
    while (itf != formals[i].cend())
    {
      out << "(" << (*itf) << " " << (*itf).getType() << ")";
      ++itf;
      if (itf != formals[i].cend())
      {
        out << " ";
      }
    }
    TypeNode type = funcs[i].getType();
    if (type.isFunction())
    {
      type = type.getRangeType();
    }
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
  else
  {
    out << " ";
  }
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
  out << ")" << std::endl;
}

void Smt2Printer::toStreamCmdDeclareType(std::ostream& out,
                                         TypeNode type) const
{
  Assert(type.isSort() || type.isSortConstructor());
  std::stringstream id;
  id << type;
  size_t arity = type.isSortConstructor() ? type.getSortConstructorArity() : 0;
  out << "(declare-sort " << cvc5::quoteSymbol(id.str()) << " " << arity << ")"
      << std::endl;
}

void Smt2Printer::toStreamCmdDefineType(std::ostream& out,
                                        const std::string& id,
                                        const std::vector<TypeNode>& params,
                                        TypeNode t) const
{
  out << "(define-sort " << cvc5::quoteSymbol(id) << " (";
  if (params.size() > 0)
  {
    copy(
        params.begin(), params.end() - 1, ostream_iterator<TypeNode>(out, " "));
    out << params.back();
  }
  out << ") " << t << ")" << std::endl;
}

void Smt2Printer::toStreamCmdSimplify(std::ostream& out, Node n) const
{
  out << "(simplify " << n << ')' << std::endl;
}

void Smt2Printer::toStreamCmdGetValue(std::ostream& out,
                                      const std::vector<Node>& nodes) const
{
  out << "(get-value ( ";
  copy(nodes.begin(), nodes.end(), ostream_iterator<Node>(out, " "));
  out << "))" << std::endl;
}

void Smt2Printer::toStreamCmdGetModel(std::ostream& out) const
{
  out << "(get-model)" << std::endl;
}

void Smt2Printer::toStreamCmdGetAssignment(std::ostream& out) const
{
  out << "(get-assignment)" << std::endl;
}

void Smt2Printer::toStreamCmdGetAssertions(std::ostream& out) const
{
  out << "(get-assertions)" << std::endl;
}

void Smt2Printer::toStreamCmdGetProof(std::ostream& out) const
{
  out << "(get-proof)" << std::endl;
}

void Smt2Printer::toStreamCmdGetUnsatAssumptions(std::ostream& out) const
{
  out << "(get-unsat-assumptions)" << std::endl;
}

void Smt2Printer::toStreamCmdGetUnsatCore(std::ostream& out) const
{
  out << "(get-unsat-core)" << std::endl;
}

void Smt2Printer::toStreamCmdSetBenchmarkStatus(std::ostream& out,
                                                Result::Sat status) const
{
  out << "(set-info :status " << status << ')' << std::endl;
}

void Smt2Printer::toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                               const std::string& logic) const
{
  out << "(set-logic " << logic << ')' << std::endl;
}

void Smt2Printer::toStreamCmdSetInfo(std::ostream& out,
                                     const std::string& flag,
                                     const std::string& value) const
{
  out << "(set-info :" << flag << ' ' << value << ')' << std::endl;
}

void Smt2Printer::toStreamCmdGetInfo(std::ostream& out,
                                     const std::string& flag) const
{
  out << "(get-info :" << flag << ')' << std::endl;
}

void Smt2Printer::toStreamCmdSetOption(std::ostream& out,
                                       const std::string& flag,
                                       const std::string& value) const
{
  out << "(set-option :" << flag << ' ' << value << ')' << std::endl;
}

void Smt2Printer::toStreamCmdGetOption(std::ostream& out,
                                       const std::string& flag) const
{
  out << "(get-option :" << flag << ')' << std::endl;
}

void Smt2Printer::toStream(std::ostream& out, const DType& dt) const
{
  for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    const DTypeConstructor& cons = dt[i];
    if (i != 0)
    {
      out << " ";
    }
    out << "(" << cvc5::quoteSymbol(cons.getName());
    for (size_t j = 0, nargs = cons.getNumArgs(); j < nargs; j++)
    {
      const DTypeSelector& arg = cons[j];
      out << " (" << arg.getSelector() << " " << arg.getRangeType() << ")";
    }
    out << ")";
  }
}

void Smt2Printer::toStreamCmdDatatypeDeclaration(
    std::ostream& out, const std::vector<TypeNode>& datatypes) const
{
  Assert(!datatypes.empty());
  Assert(datatypes[0].isDatatype());
  const DType& d0 = datatypes[0].getDType();
  if (d0.isTuple())
  {
    // not necessary to print tuples
    Assert(datatypes.size() == 1);
    return;
  }
  out << "(declare-";
  if (d0.isCodatatype())
  {
    out << "co";
  }
  out << "datatypes";
  out << " (";
  for (const TypeNode& t : datatypes)
  {
    Assert(t.isDatatype());
    const DType& d = t.getDType();
    out << "(" << cvc5::quoteSymbol(d.getName());
    out << " " << d.getNumParameters() << ")";
  }
  out << ") (";
  for (const TypeNode& t : datatypes)
  {
    Assert(t.isDatatype());
    const DType& d = t.getDType();
    if (d.isParametric())
    {
      out << "(par (";
      for (unsigned p = 0, nparam = d.getNumParameters(); p < nparam; p++)
      {
        out << (p > 0 ? " " : "") << d.getParameter(p);
      }
      out << ")";
    }
    out << "(";
    toStream(out, d);
    out << ")";
    if (d.isParametric())
    {
      out << ")";
    }
  }
  out << ")";
  out << ")" << std::endl;
}

void Smt2Printer::toStreamCmdComment(std::ostream& out,
                                     const std::string& comment) const
{
  std::string s = comment;
  size_t pos = 0;
  while ((pos = s.find_first_of('"', pos)) != string::npos)
  {
    s.replace(pos, 1, "\"\"");
    pos += 2;
  }
  out << "(set-info :notes \"" << s << "\")" << std::endl;
}

void Smt2Printer::toStreamCmdDeclareHeap(std::ostream& out,
                                         TypeNode locType,
                                         TypeNode dataType) const
{
  out << "(declare-heap (" << locType << " " << dataType << "))" << std::endl;
}

void Smt2Printer::toStreamCmdEmpty(std::ostream& out,
                                   const std::string& name) const
{
  out << std::endl;
}

void Smt2Printer::toStreamCmdEcho(std::ostream& out,
                                  const std::string& output) const
{
  std::string s = output;
  // escape all double-quotes
  size_t pos = 0;
  while ((pos = s.find('"', pos)) != string::npos)
  {
    s.replace(pos, 1, "\"\"");
    pos += 2;
  }
  out << "(echo \"" << s << "\")" << std::endl;
}

/*
   --------------------------------------------------------------------------
    Handling SyGuS commands
   --------------------------------------------------------------------------
*/

static void toStreamSygusGrammar(std::ostream& out, const TypeNode& t)
{
  if (!t.isNull() && t.isDatatype() && t.getDType().isSygus())
  {
    std::stringstream types_predecl, types_list;
    std::set<TypeNode> grammarTypes;
    std::list<TypeNode> typesToPrint;
    grammarTypes.insert(t);
    typesToPrint.push_back(t);
    NodeManager* nm = NodeManager::currentNM();
    // for each datatype in grammar
    //   name
    //   sygus type
    //   constructors in order
    do
    {
      TypeNode curr = typesToPrint.front();
      typesToPrint.pop_front();
      Assert(curr.isDatatype() && curr.getDType().isSygus());
      const DType& dt = curr.getDType();
      types_list << '(' << dt.getName() << ' ' << dt.getSygusType() << " (";
      types_predecl << '(' << dt.getName() << ' ' << dt.getSygusType() << ") ";
      if (dt.getSygusAllowConst())
      {
        types_list << "(Constant " << dt.getSygusType() << ") ";
      }
      for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
      {
        const DTypeConstructor& cons = dt[i];
        // make a sygus term
        std::vector<Node> cchildren;
        cchildren.push_back(cons.getConstructor());
        for (size_t j = 0, nargs = cons.getNumArgs(); j < nargs; j++)
        {
          TypeNode argType = cons[j].getRangeType();
          std::stringstream ss;
          ss << argType;
          Node bv = nm->mkBoundVar(ss.str(), argType);
          cchildren.push_back(bv);
          // if fresh type, store it for later processing
          if (grammarTypes.insert(argType).second)
          {
            typesToPrint.push_back(argType);
          }
        }
        Node consToPrint = nm->mkNode(kind::APPLY_CONSTRUCTOR, cchildren);
        // now, print it using the conversion to builtin with external
        types_list << theory::datatypes::utils::sygusToBuiltin(consToPrint,
                                                               true);
        types_list << ' ';
      }
      types_list << "))\n";
    } while (!typesToPrint.empty());

    out << "\n(" << types_predecl.str() << ")\n(" << types_list.str() << ')';
  }
}

void Smt2Printer::toStreamCmdSynthFun(std::ostream& out,
                                      Node f,
                                      const std::vector<Node>& vars,
                                      bool isInv,
                                      TypeNode sygusType) const
{
  std::stringstream sym;
  sym << f;
  out << '(' << (isInv ? "synth-inv " : "synth-fun ")
      << cvc5::quoteSymbol(sym.str()) << ' ';
  out << '(';
  if (!vars.empty())
  {
    // print variable list
    std::vector<Node>::const_iterator i = vars.cbegin(), i_end = vars.cend();
    out << '(' << *i << ' ' << i->getType() << ')';
    ++i;
    while (i != i_end)
    {
      out << " (" << *i << ' ' << i->getType() << ')';
      ++i;
    }
  }
  out << ')';
  // if not invariant-to-synthesize, print return type
  if (!isInv)
  {
    TypeNode ftn = f.getType();
    TypeNode range = ftn.isFunction() ? ftn.getRangeType() : ftn;
    out << ' ' << range;
  }
  out << '\n';
  // print grammar, if any
  if (!sygusType.isNull())
  {
    toStreamSygusGrammar(out, sygusType);
  }
  out << ')' << std::endl;
}

void Smt2Printer::toStreamCmdDeclareVar(std::ostream& out,
                                        Node var,
                                        TypeNode type) const
{
  out << "(declare-var " << var << ' ' << type << ')' << std::endl;
}

void Smt2Printer::toStreamCmdConstraint(std::ostream& out, Node n) const
{
  out << "(constraint " << n << ')' << std::endl;
}

void Smt2Printer::toStreamCmdInvConstraint(
    std::ostream& out, Node inv, Node pre, Node trans, Node post) const
{
  out << "(inv-constraint " << inv << ' ' << pre << ' ' << trans << ' ' << post
      << ')' << std::endl;
}

void Smt2Printer::toStreamCmdCheckSynth(std::ostream& out) const
{
  out << "(check-synth)" << std::endl;
}

void Smt2Printer::toStreamCmdGetAbduct(std::ostream& out,
                                       const std::string& name,
                                       Node conj,
                                       TypeNode sygusType) const
{
  out << "(get-abduct ";
  out << name << ' ';
  out << conj << ' ';

  // print grammar, if any
  if (!sygusType.isNull())
  {
    toStreamSygusGrammar(out, sygusType);
  }
  out << ')' << std::endl;
}

/*
   --------------------------------------------------------------------------
    End of Handling SyGuS commands
   --------------------------------------------------------------------------
*/

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
#ifdef CVC5_COMPETITION_MODE
  // if in competition mode, lie and say we're ok
  // (we have nothing to lose by saying success, and everything to lose
  // if we say "unsupported")
  out << "success" << endl;
#else  /* CVC5_COMPETITION_MODE */
  out << "unsupported" << endl;
#endif /* CVC5_COMPETITION_MODE */
}

static void errorToStream(std::ostream& out, std::string message, Variant v) {
  // escape all double-quotes
  size_t pos = 0;
  while((pos = message.find('"', pos)) != string::npos) {
    message.replace(pos, 1, "\"\"");
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

}  // namespace smt2
}  // namespace printer
}  // namespace cvc5

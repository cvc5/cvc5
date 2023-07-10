/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The pretty-printer interface for the SMT2 output language.
 */

#include "printer/smt2/smt2_printer.h"

#include <cvc5/cvc5.h>

#include <iostream>
#include <list>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/array_store_all.h"
#include "expr/ascription_type.h"
#include "expr/cardinality_constraint.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/emptybag.h"
#include "expr/emptyset.h"
#include "expr/function_array_const.h"
#include "expr/node_visitor.h"
#include "expr/sequence.h"
#include "expr/skolem_manager.h"
#include "expr/sygus_datatype.h"
#include "options/io_utils.h"
#include "options/language.h"
#include "printer/let_binding.h"
#include "proof/unsat_core.h"
#include "smt/model.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/builtin/abstract_type.h"
#include "theory/builtin/generic_op.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/theory_model.h"
#include "theory/uf/function_const.h"
#include "theory/uf/theory_uf_rewriter.h"
#include "util/bitvector.h"
#include "util/divisible.h"
#include "util/finite_field_value.h"
#include "util/floatingpoint.h"
#include "util/iand.h"
#include "util/indexed_root_predicate.h"
#include "util/real_algebraic_number.h"
#include "util/regexp.h"
#include "util/smt2_quote_string.h"
#include "util/string.h"
#include "util/uninterpreted_sort_value.h"

using namespace std;

namespace cvc5::internal {
namespace printer {
namespace smt2 {

static void toStreamRational(std::ostream& out,
                             const Rational& r,
                             bool isReal,
                             Variant v)
{
  bool neg = r.sgn() < 0;
  // Print the rational, possibly as a real.
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
    if (isReal)
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
    Assert(isReal);
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

void Smt2Printer::toStream(std::ostream& out, TNode n) const
{
  size_t dag = options::ioutils::getDagThresh(out);
  int toDepth = options::ioutils::getNodeDepth(out);
  toStream(out, n, toDepth, dag);
}

void Smt2Printer::toStream(std::ostream& out, Kind k) const
{
  out << smtKindString(k);
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
        n.constToStream(out);
      }
      break;
    case kind::ABSTRACT_TYPE:
    {
      const AbstractType& at = n.getConst<AbstractType>();
      Kind atk = at.getKind();
      out << "?";
      // note that the fully abstract type (where atk is ABSTRACT_TYPE) is
      // printed simply as "?", not, e.g., "?Abstract"
      if (atk != kind::ABSTRACT_TYPE)
      {
        out << smtKindString(atk);
      }
      break;
    }
    case kind::APPLY_INDEXED_SYMBOLIC_OP:
      out << smtKindString(n.getConst<GenericOp>().getKind());
      break;
    case kind::BITVECTOR_TYPE:
      out << "(_ BitVec " << n.getConst<BitVectorSize>().d_size << ")";
      break;
    case kind::FINITE_FIELD_TYPE:
      out << "(_ FiniteField " << n.getConst<FfSize>().d_size << ")";
      break;
    case kind::FLOATINGPOINT_TYPE:
      out << "(_ FloatingPoint "
          << n.getConst<FloatingPointSize>().exponentWidth() << " "
          << n.getConst<FloatingPointSize>().significandWidth() << ")";
      break;
    case kind::CONST_BITVECTOR:
    {
      const BitVector& bv = n.getConst<BitVector>();
      if (options::ioutils::getBvPrintConstsAsIndexedSymbols(out))
      {
        out << "(_ bv" << bv.getValue() << " " << bv.getSize() << ")";
      }
      else
      {
        out << "#b" << bv.toString();
      }
      break;
    }
    case kind::CONST_FINITE_FIELD:
    {
      const FiniteFieldValue& ff = n.getConst<FiniteFieldValue>();
      out << "#f" << ff.getValue() << "m" << ff.getFieldSize();
      break;
    }
    case kind::CONST_FLOATINGPOINT:
    {
      out << n.getConst<FloatingPoint>().toString(
          options::ioutils::getBvPrintConstsAsIndexedSymbols(out));
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
      out << smtKindString(n.getConst<Kind>());
      break;
    case kind::CONST_RATIONAL: {
      const Rational& r = n.getConst<Rational>();
      toStreamRational(out, r, true, d_variant);
      break;
    }
    case kind::CONST_INTEGER:
    {
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
      TypeNode type = n.getType();
      TypeNode elemType = type.getSequenceElementType();
      if (snvec.empty())
      {
        out << "(as seq.empty ";
        toStreamType(out, type);
        out << ")";
      }
      else if (snvec.size() > 1)
      {
        out << "(seq.++";
        for (const Node& snvc : snvec)
        {
          out << " (seq.unit ";
          toStream(out, snvc, toDepth);
          out << ")";
        }
        out << ")";
      }
      else
      {
        out << "(seq.unit ";
        toStream(out, snvec[0], toDepth);
        out << ")";
      }
      break;
    }

    case kind::STORE_ALL: {
      ArrayStoreAll asa = n.getConst<ArrayStoreAll>();
      out << "((as const ";
      toStreamType(out, asa.getType());
      out << ") ";
      toStream(out, asa.getValue(), toDepth < 0 ? toDepth : toDepth - 1);
      out << ")";
      break;
    }
    case kind::FUNCTION_ARRAY_CONST:
    {
      // prints as the equivalent lambda
      Node lam = theory::uf::FunctionConst::toLambda(n);
      toStream(out, lam, toDepth);
      break;
    }

    case kind::UNINTERPRETED_SORT_VALUE:
    {
      const UninterpretedSortValue& v = n.getConst<UninterpretedSortValue>();
      std::stringstream ss;
      ss << "(as " << v << " " << n.getType() << ")";
      out << ss.str();
      break;
    }
    case kind::DIVISIBLE_OP:
      out << "(_ divisible " << n.getConst<Divisible>().k << ")";
      break;
    case kind::SET_EMPTY:
      out << "(as set.empty ";
      toStreamType(out, n.getConst<EmptySet>().getType());
      out << ")";
      break;

    case kind::BAG_EMPTY:
      out << "(as bag.empty ";
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
    case kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV_OP:
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
    case kind::FLOATINGPOINT_TO_FP_FROM_FP_OP:
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
    case kind::FLOATINGPOINT_TO_FP_FROM_REAL_OP:
      out << "(_ to_fp "
          << n.getConst<FloatingPointToFPReal>().getSize().exponentWidth()
          << ' '
          << n.getConst<FloatingPointToFPReal>().getSize().significandWidth()
          << ")";
      break;
    case kind::FLOATINGPOINT_TO_FP_FROM_SBV_OP:
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
    case kind::FLOATINGPOINT_TO_FP_FROM_UBV_OP:
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
    case kind::TUPLE_PROJECT_OP:
    case kind::TABLE_PROJECT_OP:
    case kind::TABLE_AGGREGATE_OP:
    case kind::TABLE_JOIN_OP:
    case kind::TABLE_GROUP_OP:
    case kind::RELATION_GROUP_OP:
    case kind::RELATION_AGGREGATE_OP:
    case kind::RELATION_PROJECT_OP:
    {
      ProjectOp op = n.getConst<ProjectOp>();
      const std::vector<uint32_t>& indices = op.getIndices();
      Kind k = NodeManager::operatorToKind(n);
      if (indices.empty())
      {
        out << smtKindString(k);
      }
      else
      {
        out << "(_ " << smtKindString(k);
        for (uint32_t i : indices)
        {
          out << " " << i;
        }
        out << ")";
      }
    }
      break;
    default:
      // fall back on whatever operator<< does on underlying type; we
      // might luck out and be SMT-LIB v2 compliant
      n.constToStream(out);
    }

    return;
  }

  Kind k = n.getKind();
  if (k == kind::SORT_TYPE)
  {
    if(n.getNumChildren() != 0) {
      out << '(';
    }
    if (n.hasName())
    {
      std::string name = n.getName();
      out << cvc5::internal::quoteSymbol(name);
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
  else if (k == kind::DATATYPE_TYPE)
  {
    const DType& dt = NodeManager::currentNM()->getDTypeFor(n);
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
      out << cvc5::internal::quoteSymbol(dt.getName());
    }
    return;
  }

  // determine if we are printing out a type ascription
  if (k == kind::APPLY_TYPE_ASCRIPTION)
  {
    TypeNode typeAsc = n.getOperator().getConst<AscriptionType>().getType();
    // use type ascription
    out << "(as ";
    toStream(out, n[0], toDepth < 0 ? toDepth : toDepth - 1, lbind);
    out << " " << typeAsc << ")";
    return;
  }

  if (k == kind::SKOLEM && nm->getSkolemManager()->isAbstractValue(n))
  {
    // abstract value
    std::string s = n.getName();
    out << "(as " << cvc5::internal::quoteSymbol(s) << " " << n.getType() << ")";
    return;
  }
  else if (n.isVar())
  {
    // variable
    if (n.hasName())
    {
      std::string s = n.getName();
      if (k == kind::RAW_SYMBOL)
      {
        // raw symbols are never quoted
        out << s;
      }
      else
      {
        out << cvc5::internal::quoteSymbol(s);
      }
    }
    else
    {
      if (k == kind::VARIABLE)
      {
        out << "var_";
      }
      else
      {
        out << k << '_';
      }
      out << n.getId();
    }
    return;
  }
  if (k == kind::APPLY_UF && !n.getOperator().isVar())
  {
    // Must print as HO apply instead. This ensures un-beta-reduced function
    // applications can be reparsed.
    Node hoa = theory::uf::TheoryUfRewriter::getHoApplyForApplyUf(n);
    toStream(out, hoa, toDepth);
    return;
  }

  bool stillNeedToPrintParams = true;
  // operator
  if (n.getNumChildren() != 0 && k != kind::CONSTRUCTOR_TYPE)
  {
    out << '(';
  }
  switch(k) {
    // builtin theory
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

    // uf theory
    case kind::APPLY_UF: break;
    // higher-order
    case kind::HO_APPLY:
      if (!options::ioutils::getFlattenHOChains(out))
      {
        out << smtKindString(k) << ' ';
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
    case kind::APPLY_INDEXED_SYMBOLIC:
      // operator is printed as kind
      break;

    case kind::MATCH:
      out << smtKindString(k) << " ";
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
    case kind::MATCH_CASE:
    {
      // ignore the binder for MATCH_BIND_CASE
      size_t patIndex = (k == kind::MATCH_BIND_CASE ? 1 : 0);
      // The pattern should be printed as a pattern (symbol applied to symbols),
      // not as a term. In particular, this means we should not print any
      // type ascriptions (if any).
      if (n[patIndex].getKind() == kind::APPLY_CONSTRUCTOR)
      {
        if (n[patIndex].getNumChildren() > 0)
        {
          out << "(";
        }
        Node op = n[patIndex].getOperator();
        const DType& dt = DType::datatypeOf(op);
        size_t index = DType::indexOf(op);
        out << dt[index].getConstructor();
        for (const Node& nc : n[patIndex])
        {
          out << " ";
          toStream(out, nc, toDepth, lbind);
        }
        if (n[patIndex].getNumChildren() > 0)
        {
          out << ")";
        }
      }
      else
      {
        // otherwise, a variable, just print
        Assert(n[patIndex].isVar());
        toStream(out, n[patIndex], toDepth, lbind);
      }
      out << " ";
      toStream(out, n[patIndex + 1], toDepth, lbind);
      out << ")";
    }
      return;

    // arith theory
    case kind::IAND:
      out << "(_ iand " << n.getOperator().getConst<IntAnd>().d_size << ") ";
      stillNeedToPrintParams = false;
      break;

    case kind::DIVISIBLE:
      toStream(out, n.getOperator(), toDepth, nullptr);
      out << ' ';
      stillNeedToPrintParams = false;
      break;
    case kind::REAL_ALGEBRAIC_NUMBER:
    {
      const RealAlgebraicNumber& ran = n.getOperator().getConst<RealAlgebraicNumber>();
      out << "(_ real_algebraic_number " << ran << ")";
      stillNeedToPrintParams = false;
      break;
    }
    case kind::INDEXED_ROOT_PREDICATE_OP:
    {
      const IndexedRootPredicate& irp = n.getConst<IndexedRootPredicate>();
      out << "(_ root_predicate " << irp.d_index << ")";
      break;
    }

  // string theory
  case kind::REGEXP_REPEAT:
  case kind::REGEXP_LOOP:
  {
    out << n.getOperator() << ' ';
    stillNeedToPrintParams = false;
    break;
  }

    // bv theory
  case kind::BITVECTOR_CONCAT:
  case kind::BITVECTOR_AND:
  case kind::BITVECTOR_OR:
  case kind::BITVECTOR_XOR:
  case kind::BITVECTOR_MULT:
  case kind::BITVECTOR_ADD:
  {
    out << smtKindString(k) << " ";
  }
  break;

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
  case kind::BITVECTOR_BITOF:
    out << "(_ bitOf " << n.getOperator().getConst<BitVectorBitOf>().d_bitIndex
        << ") ";
    stillNeedToPrintParams = false;
    break;

  // strings
  case kind::SEQ_UNIT:
  {
    out << smtKindString(k) << " ";
    toStream(out, n[0], toDepth < 0 ? toDepth : toDepth - 1);
    out << ")";
    return;
  }
  break;

  // sets
  case kind::SET_SINGLETON:
  {
    out << smtKindString(k) << " ";
    toStream(out, n[0], toDepth < 0 ? toDepth : toDepth - 1);
    out << ")";
    return;
  }
  break;
  case kind::SET_UNIVERSE: out << "(as set.universe " << n.getType() << ")"; break;

  // bags
  case kind::BAG_MAKE:
  {
    // print (bag (BAG_MAKE_OP Real) 1 3) as (bag 1.0 3)
    out << smtKindString(k) << " ";
    toStream(out, n[0], toDepth < 0 ? toDepth : toDepth - 1);
    out << " " << n[1] << ")";
    return;
  }

  // fp theory
  case kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV:
  case kind::FLOATINGPOINT_TO_FP_FROM_FP:
  case kind::FLOATINGPOINT_TO_FP_FROM_REAL:
  case kind::FLOATINGPOINT_TO_FP_FROM_SBV:
  case kind::FLOATINGPOINT_TO_FP_FROM_UBV:
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
      out << "tuple" << ( dt[0].getNumArgs()==0 ? "" : " ");
    }
    break;
  }
  case kind::TUPLE_PROJECT:
  case kind::TABLE_PROJECT:
  case kind::TABLE_AGGREGATE:
  case kind::TABLE_JOIN:
  case kind::TABLE_GROUP:
  case kind::RELATION_GROUP:
  case kind::RELATION_AGGREGATE:
  case kind::RELATION_PROJECT:
  {
    toStream(out, n.getOperator(), toDepth, nullptr);
    out << ' ';
    stillNeedToPrintParams = false;
    break;
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
      out << "(_ tuple.select " << DType::indexOf(op) << ") ";
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
    stillNeedToPrintParams = false;
    Node op = n.getOperator();
    size_t index = DType::indexOf(op);
    const DType& dt = DType::datatypeOf(op);
    size_t cindex = DType::cindexOf(op);
    if (dt.isTuple())
    {
      stillNeedToPrintParams = false;
      out << "(_ tuple.update " << DType::indexOf(op) << ") ";
    }
    else
    {
      out << "(_ update ";
      toStream(out,
               dt[cindex][index].getSelector(),
               toDepth < 0 ? toDepth : toDepth - 1);
      out << ") ";
    }
  }
  break;
  case kind::INSTANTIATED_SORT_TYPE: break;
  case kind::PARAMETRIC_DATATYPE: break;

  // separation logic
  case kind::SEP_NIL:
    out << "(as sep.nil " << n.getType() << ")";
    break;

  // cardinality constraints.
  case kind::CARDINALITY_CONSTRAINT:
    out << "(_ fmf.card ";
    out << n.getOperator().getConst<CardinalityConstraint>().getType();
    out << " ";
    out << n.getOperator().getConst<CardinalityConstraint>().getUpperBound();
    out << ")";
    return;

    // quantifiers
  case kind::FORALL:
  case kind::EXISTS:
  case kind::LAMBDA:
  case kind::WITNESS:
  {
    out << smtKindString(k) << " ";
    // do not letify the bound variable list
    toStream(out, n[0], toDepth, nullptr);
    out << " ";
    bool needsPrintAnnot = false;
    std::stringstream annot;
    if (n.getNumChildren() == 3)
    {
      for (const Node& nc : n[2])
      {
        Kind nck = nc.getKind();
        if (nck == kind::INST_PATTERN)
        {
          needsPrintAnnot = true;
          annot << " :pattern ";
          toStream(annot, nc, toDepth, nullptr);
        }
        else if (nck == kind::INST_NO_PATTERN)
        {
          needsPrintAnnot = true;
          annot << " :no-pattern ";
          toStream(annot, nc[0], toDepth, nullptr);
        }
        else if (nck == kind::INST_ATTRIBUTE)
        {
          // notice that INST_ATTRIBUTES either have an "internal" form,
          // where the argument is a variable with an internal attribute set
          // on it, or an "external" form where it is of the form
          // (INST_ATTRIBUTE "keyword" [nodeValues]). We print the latter
          // here only.
          if (nc[0].getKind() == kind::CONST_STRING)
          {
            needsPrintAnnot = true;
            // print out as string to avoid quotes
            annot << " :" << nc[0].getConst<String>().toString();
            for (size_t j = 1, nchild = nc.getNumChildren(); j < nchild; j++)
            {
              annot << " ";
              toStream(annot, nc[j], toDepth, nullptr);
            }
          }
        }
      }
    }
    // Use a fresh let binder, since using existing let symbols may violate
    // scoping issues for let-bound variables, see explanation in let_binding.h.
    size_t dag = lbind == nullptr ? 0 : lbind->getThreshold()-1;
    if (needsPrintAnnot)
    {
      out << "(! ";
      annot << ")";
    }
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
    // by default, print the kind using the smtKindString utility
    out << smtKindString(k);
    if (n.getNumChildren() > 0)
    {
      out << " ";
    }
    break;
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
      out << ' ';
    }
  }
  if (n.getNumChildren() != 0)
  {
    out << parens.str() << ')';
  }
}

std::string Smt2Printer::smtKindString(Kind k)
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
    case kind::ADD: return "+";
    case kind::MULT:
    case kind::NONLINEAR_MULT: return "*";
    case kind::IAND: return "iand";
    case kind::POW2: return "int.pow2";
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
    case kind::SUB: return "-";
    case kind::NEG: return "-";
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
    case kind::EQ_RANGE: return "eqrange";

    // ff theory
  case kind::FINITE_FIELD_ADD: return "ff.add";
  case kind::FINITE_FIELD_MULT: return "ff.mul";
  case kind::FINITE_FIELD_NEG: return "ff.neg";

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
    case kind::BITVECTOR_UADDO: return "bvuaddo";
    case kind::BITVECTOR_SADDO: return "bvsaddo";
    case kind::BITVECTOR_UMULO: return "bvumulo";
    case kind::BITVECTOR_SMULO: return "bvsmulo";
    case kind::BITVECTOR_USUBO: return "bvusubo";
    case kind::BITVECTOR_SSUBO: return "bvssubo";
    case kind::BITVECTOR_SDIVO: return "bvsdivo";
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
    case kind::BITVECTOR_BB_TERM: return "bbT";

    // datatypes theory
    case kind::APPLY_TESTER: return "is";
    case kind::APPLY_UPDATER: return "update";
    case kind::TUPLE_TYPE: return "Tuple";
    case kind::TUPLE_PROJECT: return "tuple.project";

    // set theory
    case kind::SET_UNION: return "set.union";
    case kind::SET_INTER: return "set.inter";
    case kind::SET_MINUS: return "set.minus";
    case kind::SET_SUBSET: return "set.subset";
    case kind::SET_MEMBER: return "set.member";
    case kind::SET_TYPE: return "Set";
    case kind::SET_SINGLETON: return "set.singleton";
    case kind::SET_INSERT: return "set.insert";
    case kind::SET_COMPLEMENT: return "set.complement";
    case kind::SET_CARD: return "set.card";
    case kind::SET_COMPREHENSION: return "set.comprehension";
    case kind::SET_CHOOSE: return "set.choose";
    case kind::SET_IS_SINGLETON: return "set.is_singleton";
    case kind::SET_MAP: return "set.map";
    case kind::SET_FILTER: return "set.filter";
    case kind::SET_FOLD: return "set.fold";
    case kind::RELATION_JOIN: return "rel.join";
    case kind::RELATION_PRODUCT: return "rel.product";
    case kind::RELATION_TRANSPOSE: return "rel.transpose";
    case kind::RELATION_TCLOSURE: return "rel.tclosure";
    case kind::RELATION_IDEN: return "rel.iden";
    case kind::RELATION_JOIN_IMAGE: return "rel.join_image";
    case kind::RELATION_GROUP: return "rel.group";
    case kind::RELATION_AGGREGATE: return "rel.aggr";
    case kind::RELATION_PROJECT: return "rel.project";

    // bag theory
    case kind::BAG_TYPE: return "Bag";
    case kind::BAG_UNION_MAX: return "bag.union_max";
    case kind::BAG_UNION_DISJOINT: return "bag.union_disjoint";
    case kind::BAG_INTER_MIN: return "bag.inter_min";
    case kind::BAG_DIFFERENCE_SUBTRACT: return "bag.difference_subtract";
    case kind::BAG_DIFFERENCE_REMOVE: return "bag.difference_remove";
    case kind::BAG_SUBBAG: return "bag.subbag";
    case kind::BAG_COUNT: return "bag.count";
    case kind::BAG_MEMBER: return "bag.member";
    case kind::BAG_DUPLICATE_REMOVAL: return "bag.duplicate_removal";
    case kind::BAG_MAKE: return "bag";
    case kind::BAG_CARD: return "bag.card";
    case kind::BAG_CHOOSE: return "bag.choose";
    case kind::BAG_IS_SINGLETON: return "bag.is_singleton";
    case kind::BAG_FROM_SET: return "bag.from_set";
    case kind::BAG_TO_SET: return "bag.to_set";
    case kind::BAG_MAP: return "bag.map";
    case kind::BAG_FILTER: return "bag.filter";
    case kind::BAG_FOLD: return "bag.fold";
    case kind::BAG_PARTITION: return "bag.partition";
    case kind::TABLE_PRODUCT: return "table.product";
    case kind::TABLE_PROJECT: return "table.project";
    case kind::TABLE_AGGREGATE: return "table.aggr";
    case kind::TABLE_JOIN: return "table.join";
    case kind::TABLE_GROUP:
      return "table.group";

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

    case kind::FLOATINGPOINT_IS_NORMAL: return "fp.isNormal";
    case kind::FLOATINGPOINT_IS_SUBNORMAL: return "fp.isSubnormal";
    case kind::FLOATINGPOINT_IS_ZERO: return "fp.isZero";
    case kind::FLOATINGPOINT_IS_INF: return "fp.isInfinite";
    case kind::FLOATINGPOINT_IS_NAN: return "fp.isNaN";
    case kind::FLOATINGPOINT_IS_NEG: return "fp.isNegative";
    case kind::FLOATINGPOINT_IS_POS: return "fp.isPositive";

    case kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV: return "to_fp";
    case kind::FLOATINGPOINT_TO_FP_FROM_FP: return "to_fp";
    case kind::FLOATINGPOINT_TO_FP_FROM_REAL: return "to_fp";
    case kind::FLOATINGPOINT_TO_FP_FROM_SBV: return "to_fp";
    case kind::FLOATINGPOINT_TO_FP_FROM_UBV: return "to_fp_unsigned";
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
    case kind::ROUNDINGMODE_BITBLAST: return "RMBITBLAST";

    // string theory
    case kind::STRING_CONCAT: return "str.++";
    case kind::STRING_LENGTH: return "str.len";
    case kind::STRING_SUBSTR: return "str.substr";
    case kind::STRING_UPDATE: return "str.update";
    case kind::STRING_CONTAINS: return "str.contains";
    case kind::STRING_CHARAT: return "str.at";
    case kind::STRING_INDEXOF: return "str.indexof";
    case kind::STRING_INDEXOF_RE: return "str.indexof_re";
    case kind::STRING_REPLACE: return "str.replace";
    case kind::STRING_REPLACE_ALL: return "str.replace_all";
    case kind::STRING_REPLACE_RE: return "str.replace_re";
    case kind::STRING_REPLACE_RE_ALL: return "str.replace_re_all";
    case kind::STRING_TO_LOWER: return "str.to_lower";
    case kind::STRING_TO_UPPER: return "str.to_upper";
    case kind::STRING_REV: return "str.rev";
    case kind::STRING_PREFIX: return "str.prefixof";
    case kind::STRING_SUFFIX: return "str.suffixof";
    case kind::STRING_LEQ: return "str.<=";
    case kind::STRING_LT: return "str.<";
    case kind::STRING_FROM_CODE: return "str.from_code";
    case kind::STRING_TO_CODE: return "str.to_code";
    case Kind::STRING_IS_DIGIT: return "str.is_digit";
    case kind::STRING_ITOS: return "str.from_int";
    case kind::STRING_STOI: return "str.to_int";
    case kind::STRING_IN_REGEXP: return "str.in_re";
    case kind::STRING_TO_REGEXP: return "str.to_re";
    case kind::STRING_UNIT: return "str.unit";
    case kind::REGEXP_NONE: return "re.none";
    case kind::REGEXP_ALL: return "re.all";
    case kind::REGEXP_ALLCHAR: return "re.allchar";
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

    // sep theory
    case kind::SEP_STAR: return "sep";
    case kind::SEP_PTO: return "pto";
    case kind::SEP_WAND: return "wand";
    case kind::SEP_EMP: return "sep.emp";

    // quantifiers
    case kind::FORALL: return "forall";
    case kind::EXISTS: return "exists";

    // HO
    case kind::HO_APPLY: return "@";

    default:; /* fall through */
  }

  // fall back on however the kind prints itself; this probably
  // won't be SMT-LIB v2 compliant, but it will be clear from the
  // output that support for the kind needs to be added here.
  // no SMT way to print these
  return kind::kindToString(k);
}

std::string Smt2Printer::smtKindStringOf(const Node& n)
{
  Kind k = n.getKind();
  if (n.getNumChildren() > 0 && n[0].getType().isSequence())
  {
    // this method parallels cvc5::Term::getKind
    switch (k)
    {
      case kind::STRING_CONCAT: return "seq.concat";
      case kind::STRING_LENGTH: return "seq.len";
      case kind::STRING_SUBSTR: return "seq.extract";
      case kind::STRING_UPDATE: return "seq.update";
      case kind::STRING_CHARAT: return "seq.at";
      case kind::STRING_CONTAINS: return "seq.contains";
      case kind::STRING_INDEXOF: return "seq.indexof";
      case kind::STRING_REPLACE: return "seq.replace";
      case kind::STRING_REPLACE_ALL: return "seq.replace_all";
      case kind::STRING_REV: return "seq.rev";
      case kind::STRING_PREFIX: return "seq.prefixof";
      case kind::STRING_SUFFIX: return "seq.suffixof";
      default:
        // fall through to conversion below
        break;
    }
  }
  // by default
  return smtKindString(k);
}

void Smt2Printer::toStreamDeclareType(std::ostream& out, TypeNode tn) const
{
  out << "(";
  if (tn.isFunction())
  {
    const vector<TypeNode> argTypes = tn.getArgTypes();
    if (argTypes.size() > 0)
    {
      copy(argTypes.begin(),
           argTypes.end() - 1,
           ostream_iterator<TypeNode>(out, " "));
      out << argTypes.back();
    }
    tn = tn.getRangeType();
  }
  out << ") " << tn;
}

void Smt2Printer::toStreamType(std::ostream& out, TypeNode tn) const
{
  // we currently must call TypeNode::toStream here.
  tn.toStream(out);
}

void Smt2Printer::toStream(std::ostream& out, const UnsatCore& core) const
{
  out << "(" << std::endl;
  if (core.useNames())
  {
    // use the names
    const std::vector<std::string>& cnames = core.getCoreNames();
    for (const std::string& cn : cnames)
    {
      out << cvc5::internal::quoteSymbol(cn) << std::endl;
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
  //print the model
  out << "(" << endl;
  // don't need to print approximations since they are built into choice
  // functions in the values of variables.
  this->Printer::toStream(out, m);
  out << ")" << endl;
  //print the heap model, if it exists
  Node h, neq;
  if (m.getHeapModel(h, neq))
  {
    // description of the heap+what nil is equal to fully describes model
    out << "(heap" << endl;
    out << h << endl;
    out << neq << endl;
    out << ")" << std::endl;
  }
}

void Smt2Printer::toStreamModelSort(std::ostream& out,
                                    TypeNode tn,
                                    const std::vector<Node>& elements) const
{
  if (!tn.isUninterpretedSort())
  {
    out << "ERROR: don't know how to print non uninterpreted sort in model: "
        << tn << std::endl;
    return;
  }
  auto modelUninterpPrint = options::ioutils::getModelUninterpPrint(out);
  // print the cardinality
  out << "; cardinality of " << tn << " is " << elements.size() << endl;
  if (modelUninterpPrint == options::ModelUninterpPrintMode::DeclSortAndFun)
  {
    toStreamCmdDeclareType(out, tn);
  }
  // print the representatives
  for (const Node& trn : elements)
  {
    if (modelUninterpPrint == options::ModelUninterpPrintMode::DeclSortAndFun
        || modelUninterpPrint == options::ModelUninterpPrintMode::DeclFun)
    {
      out << "(declare-fun ";
      if (trn.getKind() == kind::UNINTERPRETED_SORT_VALUE)
      {
        // prints as raw symbol
        const UninterpretedSortValue& av =
            trn.getConst<UninterpretedSortValue>();
        out << av;
      }
      else
      {
        Assert(false)
            << "model domain element is not an uninterpreted sort value: "
            << trn;
        out << trn;
      }
      out << " () " << tn << ")" << endl;
    }
    else
    {
      out << "; rep: " << trn << endl;
    }
  }
}

void Smt2Printer::toStreamModelTerm(std::ostream& out,
                                    const Node& n,
                                    const Node& value) const
{
  if (value.getKind() == kind::LAMBDA)
  {
    TypeNode rangeType = n.getType().getRangeType();
    out << "(define-fun " << n << " " << value[0] << " " << rangeType << " ";
    // call toStream and force its type to be proper
    toStream(out, value[1], -1);
    out << ")" << endl;
  }
  else
  {
    out << "(define-fun " << n << " () " << n.getType() << " ";
    // call toStream and force its type to be proper
    toStream(out, value, -1);
    out << ")" << endl;
  }
}

void Smt2Printer::toStreamCmdSuccess(std::ostream& out) const
{
  out << "success" << endl;
}

void Smt2Printer::toStreamCmdInterrupted(std::ostream& out) const
{
  out << "interrupted" << endl;
}

void Smt2Printer::toStreamCmdUnsupported(std::ostream& out) const
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

static void errorToStream(std::ostream& out, std::string message)
{
  out << "(error " << cvc5::internal::quoteString(message) << ')' << endl;
}

void Smt2Printer::toStreamCmdFailure(std::ostream& out,
                                     const std::string& message) const
{
  errorToStream(out, message);
}

void Smt2Printer::toStreamCmdRecoverableFailure(
    std::ostream& out, const std::string& message) const
{
  errorToStream(out, message);
}

void Smt2Printer::toStreamCmdAssert(std::ostream& out, Node n) const
{
  out << "(assert " << n << ')' << std::endl;
}

void Smt2Printer::toStreamCmdPush(std::ostream& out, uint32_t nscopes) const
{
  out << "(push " << nscopes << ")" << std::endl;
}

void Smt2Printer::toStreamCmdPop(std::ostream& out, uint32_t nscopes) const
{
  out << "(pop " << nscopes << ")" << std::endl;
}

void Smt2Printer::toStreamCmdCheckSat(std::ostream& out) const
{
  out << "(check-sat)" << std::endl;
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

void Smt2Printer::toStreamCmdDeclareFunction(std::ostream& out,
                                             const std::string& id,
                                             TypeNode type) const
{
  out << "(declare-fun " << cvc5::internal::quoteSymbol(id) << " ";
  toStreamDeclareType(out, type);
  out << ')' << std::endl;
}

void Smt2Printer::toStreamCmdDeclareOracleFun(std::ostream& out,
                                              const std::string& id,
                                              TypeNode type,
                                              const std::string& binName) const
{
  out << "(declare-oracle-fun " << cvc5::internal::quoteSymbol(id) << " ";
  toStreamDeclareType(out, type);
  out << " " << binName << ")" << std::endl;
}

void Smt2Printer::toStreamCmdDeclarePool(
    std::ostream& out,
    const std::string& id,
    TypeNode type,
    const std::vector<Node>& initValue) const
{
  out << "(declare-pool " << cvc5::internal::quoteSymbol(id) << ' ' << type << " (";
  for (size_t i = 0, n = initValue.size(); i < n; ++i)
  {
    if (i != 0) {
      out << ' ';
    }
    out << initValue[i];
  }
  out << "))" << std::endl;
}

void Smt2Printer::toStreamCmdDefineFunction(std::ostream& out,
                                            const std::string& id,
                                            const std::vector<Node>& formals,
                                            TypeNode range,
                                            Node formula) const
{
  out << "(define-fun " << cvc5::internal::quoteSymbol(id) << " ";
  toStreamSortedVarList(out, formals);
  out << " " << range << ' ' << formula << ')' << std::endl;
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
    out << funcs[i] << " ";
    // print its type signature
    toStreamSortedVarList(out, formals[i]);
    TypeNode type = funcs[i].getType();
    if (type.isFunction())
    {
      type = type.getRangeType();
    }
    out << " " << type;
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

void Smt2Printer::toStreamSortedVarList(std::ostream& out,
                                        const std::vector<Node>& vars) const
{
  out << "(";
  for (size_t i = 0, nvars = vars.size(); i < nvars; i++)
  {
    out << "(" << vars[i] << " " << vars[i].getType() << ")";
    if (i + 1 < nvars)
    {
      out << " ";
    }
  }
  out << ")";
}

void Smt2Printer::toStreamCmdDeclareType(std::ostream& out,
                                         TypeNode type) const
{
  Assert(type.isUninterpretedSort() || type.isUninterpretedSortConstructor());
  size_t arity = type.isUninterpretedSortConstructor()
                     ? type.getUninterpretedSortConstructorArity()
                     : 0;
  out << "(declare-sort " << type << " " << arity << ")" << std::endl;
}

void Smt2Printer::toStreamCmdDefineType(std::ostream& out,
                                        const std::string& id,
                                        const std::vector<TypeNode>& params,
                                        TypeNode t) const
{
  out << "(define-sort " << cvc5::internal::quoteSymbol(id) << " (";
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

void Smt2Printer::toStreamCmdBlockModel(std::ostream& out,
                                        modes::BlockModelsMode mode) const
{
  out << "(block-model :";
  switch (mode)
  {
    case modes::BlockModelsMode::LITERALS: out << "literals"; break;
    case modes::BlockModelsMode::VALUES: out << "values"; break;
    default: Unreachable() << "Invalid block models mode " << mode;
  }
  out << ")" << std::endl;
}

void Smt2Printer::toStreamCmdBlockModelValues(
    std::ostream& out, const std::vector<Node>& nodes) const
{
  out << "(block-model-values (";
  for (size_t i = 0, n = nodes.size(); i < n; ++i)
  {
    if (i != 0)
    {
      out << ' ';
    }
    out << nodes[i];
  }
  out << "))" << std::endl;
}

void Smt2Printer::toStreamCmdGetAssignment(std::ostream& out) const
{
  out << "(get-assignment)" << std::endl;
}

void Smt2Printer::toStreamCmdGetAssertions(std::ostream& out) const
{
  out << "(get-assertions)" << std::endl;
}

void Smt2Printer::toStreamCmdGetProof(std::ostream& out,
                                      modes::ProofComponent c) const
{
  out << "(get-proof";
  if (c != modes::PROOF_COMPONENT_FULL)
  {
    out << " :" << c;
  }
  out << ")" << std::endl;
}

void Smt2Printer::toStreamCmdGetUnsatAssumptions(std::ostream& out) const
{
  out << "(get-unsat-assumptions)" << std::endl;
}

void Smt2Printer::toStreamCmdGetUnsatCore(std::ostream& out) const
{
  out << "(get-unsat-core)" << std::endl;
}

void Smt2Printer::toStreamCmdGetDifficulty(std::ostream& out) const
{
  out << "(get-difficulty)" << std::endl;
}

void Smt2Printer::toStreamCmdGetTimeoutCore(std::ostream& out) const
{
  out << "(get-timeout-core)" << std::endl;
}

void Smt2Printer::toStreamCmdGetLearnedLiterals(std::ostream& out,
                                                modes::LearnedLitType t) const
{
  out << "(get-learned-literals";
  if (t != modes::LEARNED_LIT_INPUT)
  {
    out << " :" << t;
  }
  out << ")" << std::endl;
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
  out << "(set-info :" << flag << " " << value << ")" << std::endl;
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
  out << "(set-option :" << flag << ' ';
  // special cases: output channels require surrounding quotes in smt2 format
  if (flag == "diagnostic-output-channel" || flag == "regular-output-channel"
      || flag == "in")
  {
    out << "\"" << value << "\"";
  }
  else
  {
    out << value;
  }
  out << ')' << std::endl;
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
    out << "(" << cvc5::internal::quoteSymbol(cons.getName());
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
    out << "(" << cvc5::internal::quoteSymbol(d.getName());
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
  out << "(echo " << cvc5::internal::quoteString(output) << ')' << std::endl;
}

/*
   --------------------------------------------------------------------------
    Handling SyGuS commands
   --------------------------------------------------------------------------
*/

std::string Smt2Printer::sygusGrammarString(const TypeNode& t)
{
  std::stringstream out;
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
      // skip builtin fields, which can originate from any-constant constructors
      if (!curr.isDatatype() || !curr.getDType().isSygus())
      {
        continue;
      }
      const DType& dt = curr.getDType();
      types_list << '(' << dt.getName() << ' ' << dt.getSygusType() << " (";
      types_predecl << '(' << dt.getName() << ' ' << dt.getSygusType() << ") ";
      for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
      {
        const DTypeConstructor& cons = dt[i];
        if (cons.isSygusAnyConstant())
        {
          types_list << "(Constant " << cons[0].getRangeType() << ") ";
        }
        else
        {
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
      }
      types_list << "))\n";
    } while (!typesToPrint.empty());

    out << "\n(" << types_predecl.str() << ")\n(" << types_list.str() << ')';
  }
  return out.str();
}

void Smt2Printer::toStreamCmdSynthFun(std::ostream& out,
                                      const std::string& id,
                                      const std::vector<Node>& vars,
                                      TypeNode rangeType,
                                      TypeNode sygusType) const
{
  out << "(synth-fun " << cvc5::internal::quoteSymbol(id) << ' ';
  // print variable list
  toStreamSortedVarList(out, vars);
  // print return type
  out << ' ' << rangeType;
  out << '\n';
  // print grammar, if any
  if (!sygusType.isNull())
  {
    out << sygusGrammarString(sygusType);
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

void Smt2Printer::toStreamCmdAssume(std::ostream& out, Node n) const
{
  out << "(assume " << n << ')' << std::endl;
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

void Smt2Printer::toStreamCmdCheckSynthNext(std::ostream& out) const
{
  out << "(check-synth-next)" << std::endl;
}

void Smt2Printer::toStreamCmdGetInterpol(std::ostream& out,
                                         const std::string& name,
                                         Node conj,
                                         TypeNode sygusType) const
{
  out << "(get-interpolant " << cvc5::internal::quoteSymbol(name) << ' ' << conj;
  if (!sygusType.isNull())
  {
    out << ' ' << sygusGrammarString(sygusType);
  }
  out << ')' << std::endl;
}

void Smt2Printer::toStreamCmdGetInterpolNext(std::ostream& out) const
{
  out << "(get-interpolant-next)" << std::endl;
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
    out << sygusGrammarString(sygusType);
  }
  out << ')' << std::endl;
}

void Smt2Printer::toStreamCmdGetAbductNext(std::ostream& out) const
{
  out << "(get-abduct-next)" << std::endl;
}

void Smt2Printer::toStreamCmdGetQuantifierElimination(std::ostream& out,
                                                      Node n,
                                                      bool doFull) const
{
  out << '(' << (doFull ? "get-qe" : "get-qe-disjunct") << ' ' << n << ')'
      << std::endl;
}

/*
   --------------------------------------------------------------------------
    End of Handling SyGuS commands
   --------------------------------------------------------------------------
*/

}  // namespace smt2
}  // namespace printer
}  // namespace cvc5::internal

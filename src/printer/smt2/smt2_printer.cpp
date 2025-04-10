/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include "theory/strings/theory_strings_utils.h"
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
  bool arithTokens = options::ioutils::getPrintArithLitToken(out);
  // Print the rational, possibly as a real.
  // Notice that we print (/ (- 5) 3) instead of (- (/ 5 3)),
  // the former is compliant with real values in the smt lib standard.
  if (r.isIntegral())
  {
    if (arithTokens)
    {
      if (neg)
      {
        out << "-" << -r;
      }
      else
      {
        out << r;
      }
      if (isReal)
      {
        out << "/1";
      }
    }
    else
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
  }
  else
  {
    Assert(isReal);
    if (arithTokens)
    {
      if (neg)
      {
        Rational abs_r = (-r);
        out << '-' << abs_r.getNumerator() << '/' << abs_r.getDenominator();
      }
      else
      {
        out << r.getNumerator() << '/' << r.getDenominator();
      }
    }
    else
    {
      out << "(/ ";
      if (neg)
      {
        Rational abs_r = (-r);
        out << "(- " << abs_r.getNumerator() << ") " << abs_r.getDenominator();
      }
      else
      {
        out << r.getNumerator() << ' ' << r.getDenominator();
      }
      out << ')';
    }
  }
}

void Smt2Printer::toStream(std::ostream& out,
                           TNode n,
                           int toDepth,
                           size_t dag) const
{
  if (dag == 0)
  {
    toStream(out, n, nullptr, toDepth);
    return;
  }
  LetBinding lbind("_let_", dag + 1);

  std::string cparen;
  std::vector<Node> letList;
  lbind.letify(n, letList);
  if (!letList.empty())
  {
    std::stringstream cparens;
    std::map<Node, uint32_t>::const_iterator it;
    for (size_t i = 0, nlets = letList.size(); i < nlets; i++)
    {
      Node nl = letList[i];
      out << "(let ((";
      uint32_t id = lbind.getId(nl);
      out << "_let_" << id << " ";
      toStream(out, nl, &lbind, toDepth, false);
      out << ")) ";
      cparens << ")";
    }
    cparen = cparens.str();
  }
  // Print the body, passing the lbind object. Note that we don't convert
  // n here, and instead rely on the printing method to lookup ids in the
  // given let binding.
  toStream(out, n, &lbind, toDepth);
  out << cparen;
  lbind.popScope();
}

void Smt2Printer::toStream(std::ostream& out,
                           TNode n,
                           const LetBinding* lbind,
                           bool lbindTop) const
{
  int toDepth = options::ioutils::getNodeDepth(out);
  toStream(out, n, lbind, toDepth, lbindTop);
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

bool Smt2Printer::toStreamBase(std::ostream& out,
                               TNode n,
                               const LetBinding* lbind,
                               int toDepth) const
{
  // null
  if (n.getKind() == Kind::NULL_EXPR)
  {
    out << "null";
    return true;
  }

  NodeManager* nm = n.getNodeManager();
  // constant
  if (n.getMetaKind() == kind::metakind::CONSTANT)
  {
    switch (n.getKind())
    {
      case Kind::TYPE_CONSTANT:
        switch (n.getConst<TypeConstant>())
        {
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
      case Kind::ABSTRACT_TYPE:
      {
        const AbstractType& at = n.getConst<AbstractType>();
        Kind atk = at.getKind();
        out << "?";
        // note that the fully abstract type (where atk is ABSTRACT_TYPE) is
        // printed simply as "?", not, e.g., "?Abstract"
        if (atk != Kind::ABSTRACT_TYPE)
        {
          out << smtKindString(atk);
        }
        break;
    }
    case Kind::APPLY_INDEXED_SYMBOLIC_OP:
      out << smtKindString(n.getConst<GenericOp>().getKind());
      break;
    case Kind::BITVECTOR_TYPE:
      out << "(_ BitVec " << n.getConst<BitVectorSize>().d_size << ")";
      break;
    case Kind::FINITE_FIELD_TYPE:
      out << "(_ FiniteField " << n.getConst<FfSize>().d_val << ")";
      break;
    case Kind::FLOATINGPOINT_TYPE:
      out << "(_ FloatingPoint "
          << n.getConst<FloatingPointSize>().exponentWidth() << " "
          << n.getConst<FloatingPointSize>().significandWidth() << ")";
      break;
    case Kind::CONST_BITVECTOR:
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
    case Kind::CONST_FINITE_FIELD:
    {
      const FiniteFieldValue& ff = n.getConst<FiniteFieldValue>();
      out << "#f" << ff.getValue() << "m" << ff.getFieldSize();
      break;
    }
    case Kind::CONST_FLOATINGPOINT:
    {
      out << n.getConst<FloatingPoint>().toString(
          options::ioutils::getBvPrintConstsAsIndexedSymbols(out));
      break;
    }
    case Kind::CONST_ROUNDINGMODE:
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
    case Kind::CONST_BOOLEAN:
      // the default would print "1" or "0" for bool, that's not correct
      // for our purposes
      out << (n.getConst<bool>() ? "true" : "false");
      break;
    case Kind::BUILTIN: out << smtKindString(n.getConst<Kind>()); break;
    case Kind::CONST_RATIONAL:
    {
      const Rational& r = n.getConst<Rational>();
      toStreamRational(out, r, true, d_variant);
      break;
    }
    case Kind::CONST_INTEGER:
    {
      const Rational& r = n.getConst<Rational>();
      toStreamRational(out, r, false, d_variant);
      break;
    }

    case Kind::CONST_STRING:
    {
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
    case Kind::CONST_SEQUENCE:
    {
      const Sequence& sn = n.getConst<Sequence>();
      const std::vector<Node>& snvec = sn.getVec();
      if (snvec.empty())
      {
        out << "(as seq.empty ";
        toStreamType(out, n.getType());
        out << ")";
      }
      else
      {
        // prints as the corresponding concatenation of seq.unit
        Node cc = theory::strings::utils::mkConcatForConstSequence(n);
        toStream(out, cc, lbind, toDepth);
      }
      break;
    }

    case Kind::STORE_ALL:
    {
      ArrayStoreAll asa = n.getConst<ArrayStoreAll>();
      out << "((as const ";
      toStreamType(out, asa.getType());
      out << ") ";
      toStream(out, asa.getValue(), lbind, toDepth < 0 ? toDepth : toDepth - 1);
      out << ")";
      break;
    }
    case Kind::FUNCTION_ARRAY_CONST:
    {
      // prints as the equivalent lambda
      Node lam = theory::uf::FunctionConst::toLambda(n);
      toStream(out, lam, lbind, toDepth);
      break;
    }

    case Kind::UNINTERPRETED_SORT_VALUE:
    {
      const UninterpretedSortValue& v = n.getConst<UninterpretedSortValue>();
      std::stringstream ss;
      ss << "(as " << v << " " << n.getType() << ")";
      out << ss.str();
      break;
    }
    case Kind::CARDINALITY_CONSTRAINT_OP:
    {
      const CardinalityConstraint& cc =
          n.getConst<CardinalityConstraint>();
      TypeNode tn = cc.getType();
      out << "(_ fmf.card " << tn << " " << cc.getUpperBound() << ")";
    }
      break;
    case Kind::COMBINED_CARDINALITY_CONSTRAINT_OP:
    {
      const CombinedCardinalityConstraint& cc =
          n.getConst<CombinedCardinalityConstraint>();
      out << "(_ fmf.combined_card " << cc.getUpperBound() << ")";
    }
      break;
    case Kind::DIVISIBLE_OP:
      out << "(_ divisible " << n.getConst<Divisible>().k << ")";
      break;
    case Kind::SET_EMPTY:
      out << "(as set.empty ";
      toStreamType(out, n.getConst<EmptySet>().getType());
      out << ")";
      break;

    case Kind::BAG_EMPTY:
      out << "(as bag.empty ";
      toStreamType(out, n.getConst<EmptyBag>().getType());
      out << ")";
      break;
    case Kind::BITVECTOR_EXTRACT_OP:
    {
      BitVectorExtract p = n.getConst<BitVectorExtract>();
      out << "(_ extract " << p.d_high << ' ' << p.d_low << ")";
      break;
    }
    case Kind::BITVECTOR_REPEAT_OP:
      out << "(_ repeat " << n.getConst<BitVectorRepeat>().d_repeatAmount
          << ")";
      break;
    case Kind::BITVECTOR_ZERO_EXTEND_OP:
      out << "(_ zero_extend "
          << n.getConst<BitVectorZeroExtend>().d_zeroExtendAmount << ")";
      break;
    case Kind::BITVECTOR_SIGN_EXTEND_OP:
      out << "(_ sign_extend "
          << n.getConst<BitVectorSignExtend>().d_signExtendAmount << ")";
      break;
    case Kind::BITVECTOR_ROTATE_LEFT_OP:
      out << "(_ rotate_left "
          << n.getConst<BitVectorRotateLeft>().d_rotateLeftAmount << ")";
      break;
    case Kind::BITVECTOR_ROTATE_RIGHT_OP:
      out << "(_ rotate_right "
          << n.getConst<BitVectorRotateRight>().d_rotateRightAmount << ")";
      break;
    case Kind::INT_TO_BITVECTOR_OP:
      out << "(_ int_to_bv " << n.getConst<IntToBitVector>().d_size << ")";
      break;
    case Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV_OP:
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
    case Kind::FLOATINGPOINT_TO_FP_FROM_FP_OP:
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
    case Kind::FLOATINGPOINT_TO_FP_FROM_REAL_OP:
      out << "(_ to_fp "
          << n.getConst<FloatingPointToFPReal>().getSize().exponentWidth()
          << ' '
          << n.getConst<FloatingPointToFPReal>().getSize().significandWidth()
          << ")";
      break;
    case Kind::FLOATINGPOINT_TO_FP_FROM_SBV_OP:
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
    case Kind::FLOATINGPOINT_TO_FP_FROM_UBV_OP:
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
    case Kind::FLOATINGPOINT_TO_UBV_OP:
      out << "(_ fp.to_ubv "
          << n.getConst<FloatingPointToUBV>().d_bv_size.d_size << ")";
      break;
    case Kind::FLOATINGPOINT_TO_SBV_OP:
      out << "(_ fp.to_sbv "
          << n.getConst<FloatingPointToSBV>().d_bv_size.d_size << ")";
      break;
    case Kind::FLOATINGPOINT_TO_UBV_TOTAL_OP:
      out << "(_ fp.to_ubv_total "
          << n.getConst<FloatingPointToUBVTotal>().d_bv_size.d_size << ")";
      break;
    case Kind::FLOATINGPOINT_TO_SBV_TOTAL_OP:
      out << "(_ fp.to_sbv_total "
          << n.getConst<FloatingPointToSBVTotal>().d_bv_size.d_size << ")";
      break;
    case Kind::REGEXP_REPEAT_OP:
      out << "(_ re.^ " << n.getConst<RegExpRepeat>().d_repeatAmount << ")";
      break;
    case Kind::REGEXP_LOOP_OP:
      out << "(_ re.loop " << n.getConst<RegExpLoop>().d_loopMinOcc << " "
          << n.getConst<RegExpLoop>().d_loopMaxOcc << ")";
      break;
    case Kind::TUPLE_PROJECT_OP:
    case Kind::TABLE_PROJECT_OP:
    case Kind::TABLE_AGGREGATE_OP:
    case Kind::TABLE_JOIN_OP:
    case Kind::TABLE_GROUP_OP:
    case Kind::RELATION_GROUP_OP:
    case Kind::RELATION_AGGREGATE_OP:
    case Kind::RELATION_PROJECT_OP:
    case Kind::RELATION_TABLE_JOIN_OP:
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

    return true;
  }

  Kind k = n.getKind();
  if (k == Kind::DATATYPE_TYPE || k == Kind::TUPLE_TYPE
      || k == Kind::NULLABLE_TYPE)
  {
    const DType& dt = n.getNodeManager()->getDTypeFor(n);
    if (dt.isTuple())
    {
      unsigned int nargs = dt[0].getNumArgs();
      if (nargs == 0)
      {
        out << "UnitTuple";
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
      return true;
    }
    if (dt.isNullable())
    {
      out << "(Nullable " << dt[1][0].getRangeType() << ")";
    }
    else
    {
      out << cvc5::internal::quoteSymbol(dt.getName());
    }
    return true;
  }
  else if (k == Kind::APPLY_TYPE_ASCRIPTION)
  {
    TypeNode typeAsc = n.getOperator().getConst<AscriptionType>().getType();
    // use type ascription
    out << "(as ";
    toStream(out, n[0], lbind, toDepth < 0 ? toDepth : toDepth - 1);
    out << " " << typeAsc << ")";
    return true;
  }
  else if (n.isVar())
  {
    bool printed = false;
    if (k == Kind::SKOLEM)
    {
      SkolemManager* sm = nm->getSkolemManager();
      SkolemId id;
      Node cacheVal;
      if (sm->isSkolemFunction(n, id, cacheVal))
      {
        if (id == SkolemId::INTERNAL)
        {
          if (sm->isAbstractValue(n))
          {
            // abstract value
            std::string s = n.getName();
            out << "(as " << cvc5::internal::quoteSymbol(s) << " " << n.getType()
                << ")";
            printed = true;
          }
        }
        else if (options::ioutils::getPrintSkolemDefinitions(out))
        {
          toStreamSkolem(
              out, cacheVal, id, /*isApplied=*/false, toDepth, lbind);
          printed = true;
        }
      }
    }
    if (!printed)
    {
      // variable
      if (n.hasName())
      {
        std::string s = n.getName();
        if (k == Kind::RAW_SYMBOL)
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
        if (k == Kind::VARIABLE)
        {
          out << "var_";
        }
        else
        {
          out << k << '_';
        }
        out << n.getId();
      }
    }
    return true;
  }
  else if (k == Kind::APPLY_UF)
  {
    if (!n.getOperator().isVar())
    {
      // Must print as HO apply instead. This ensures un-beta-reduced function
      // applications can be reparsed.
      Node hoa = theory::uf::TheoryUfRewriter::getHoApplyForApplyUf(n);
      toStream(out, hoa, lbind, toDepth);
      return true;
    }
    else if (n.getOperator().getKind() == Kind::SKOLEM)
    {
      SkolemManager* sm = nm->getSkolemManager();
      SkolemId id;
      Node cacheVal;
      if (sm->isSkolemFunction(n.getOperator(), id, cacheVal))
      {
        if (options::ioutils::getPrintSkolemDefinitions(out))
        {
          if (n.getNumChildren() != 0)
          {
            out << '(';
          }
          toStreamSkolem(out, cacheVal, id, /*isApplied=*/true, toDepth, lbind);
          return false;
        }
      }
    }
  }
  else if (k == Kind::CONSTRUCTOR_TYPE)
  {
    Node range = n[n.getNumChildren() - 1];
    toStream(out, range, lbind, toDepth);
    return true;
  }
  else if (k == Kind::HO_APPLY && options::ioutils::getFlattenHOChains(out))
  {
    out << "(";
    // collapse "@" chains, i.e.
    //
    // ((a b) c) --> (a b c)
    //
    // (((a b) ((c d) e)) f) --> (a b (c d e) f)
    {
      Node head = n;
      std::vector<Node> args;
      while (head.getKind() == Kind::HO_APPLY)
      {
        args.insert(args.begin(), head[1]);
        head = head[0];
      }
      toStream(out, head, lbind, toDepth);
      for (unsigned i = 0, size = args.size(); i < size; ++i)
      {
        out << " ";
        toStream(out, args[i], lbind, toDepth);
      }
      out << ")";
    }
    return true;
  }
  else if (k == Kind::MATCH)
  {
    out << '(' << smtKindString(k) << " ";
    toStream(out, n[0], lbind, toDepth);
    out << " (";
    for (size_t i = 1, nchild = n.getNumChildren(); i < nchild; i++)
    {
      if (i > 1)
      {
        out << " ";
      }
      toStream(out, n[i], lbind, toDepth);
    }
    out << "))";
    return true;
  }
  else if (k == Kind::MATCH_BIND_CASE || k == Kind::MATCH_CASE)
  {
    out << '(';
    // ignore the binder for MATCH_BIND_CASE
    size_t patIndex = (k == Kind::MATCH_BIND_CASE ? 1 : 0);
    // The pattern should be printed as a pattern (symbol applied to symbols),
    // not as a term. In particular, this means we should not print any
    // type ascriptions (if any).
    if (n[patIndex].getKind() == Kind::APPLY_CONSTRUCTOR)
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
        toStream(out, nc, lbind, toDepth);
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
      toStream(out, n[patIndex], lbind, toDepth);
    }
    out << " ";
    toStream(out, n[patIndex + 1], lbind, toDepth);
    out << ")";
    return true;
  }
  else if (k == Kind::BOUND_VAR_LIST)
  {
    out << '(';
    for (TNode::iterator i = n.begin(), iend = n.end(); i != iend;)
    {
      out << '(';
      toStream(out, *i, nullptr, toDepth < 0 ? toDepth : toDepth - 1);
      out << ' ' << (*i).getType() << ')';
      if (++i != iend)
      {
        out << ' ';
      }
    }
    out << ')';
    return true;
  }
  else if (k == Kind::SET_UNIVERSE)
  {
    out << "(as set.universe " << n.getType() << ")";
    return true;
  }
  else if (k == Kind::SEP_NIL)
  {
    out << "(as sep.nil " << n.getType() << ")";
    return true;
  }
  else if (k == Kind::FORALL || k == Kind::EXISTS || k == Kind::LAMBDA
           || k == Kind::WITNESS)
  {
    out << '(' << smtKindString(k) << " ";
    // do not letify the bound variable list
    toStream(out, n[0], nullptr, toDepth);
    out << " ";
    bool needsPrintAnnot = false;
    size_t dag = options::ioutils::getDagThresh(out);
    size_t newDepth = (toDepth < 0 ? toDepth : toDepth - 1);
    std::stringstream annot;
    if (n.getNumChildren() == 3)
    {
      for (const Node& nc : n[2])
      {
        Kind nck = nc.getKind();
        if (nck == Kind::INST_PATTERN)
        {
          needsPrintAnnot = true;
          annot << " :pattern (";
          for (size_t i = 0, nchild = nc.getNumChildren(); i < nchild; i++)
          {
            if (i > 0)
            {
              annot << " ";
            }
            toStream(annot, nc[i], newDepth, dag);
          }
          annot << ")";
        }
        else if (nck == Kind::INST_NO_PATTERN)
        {
          needsPrintAnnot = true;
          annot << " :no-pattern ";
          toStream(annot, nc[0], newDepth, dag);
        }
        else if (nck == Kind::INST_POOL || nck == Kind::INST_ADD_TO_POOL
                 || nck == Kind::SKOLEM_ADD_TO_POOL)
        {
          needsPrintAnnot = true;
          switch (nck)
          {
            case Kind::INST_POOL: annot << " :pool"; break;
            case Kind::INST_ADD_TO_POOL: annot << " :inst-add-to-pool"; break;
            case Kind::SKOLEM_ADD_TO_POOL:
              annot << " :skolem-add-to-pool";
              break;
            default: break;
          }
          annot << " (";
          for (size_t i = 0, nchild = nc.getNumChildren(); i < nchild; i++)
          {
            if (i > 0)
            {
              annot << " ";
            }
            toStream(annot, nc[i], newDepth, dag);
          }
          annot << ")";
        }
        else if (nck == Kind::INST_ATTRIBUTE)
        {
          // notice that INST_ATTRIBUTES either have an "internal" form,
          // where the argument is a variable with an internal attribute set
          // on it, or an "external" form where it is of the form
          // (INST_ATTRIBUTE "keyword" [nodeValues]). We print the latter
          // here only.
          if (nc[0].getKind() == Kind::CONST_STRING)
          {
            needsPrintAnnot = true;
            // print out as string to avoid quotes
            annot << " :" << nc[0].getConst<String>().toString();
            for (size_t j = 1, nchild = nc.getNumChildren(); j < nchild; j++)
            {
              annot << " ";
              toStream(annot, nc[j], newDepth, dag);
            }
          }
        }
      }
    }
    // Use a fresh let binder, since using existing let symbols may violate
    // scoping issues for let-bound variables, see explanation in let_binding.h.
    if (needsPrintAnnot)
    {
      out << "(! ";
      annot << ")";
    }
    toStream(out, n[1], newDepth, dag);
    out << annot.str() << ")";
    return true;
  }

  bool stillNeedToPrintParams = true;
  bool printed = true;
  // operator
  if (n.getNumChildren() != 0)
  {
    out << '(';
  }
  switch (k)
  {
    case Kind::REAL_ALGEBRAIC_NUMBER:
    {
      const RealAlgebraicNumber& ran =
          n.getOperator().getConst<RealAlgebraicNumber>();
      out << "(_ real_algebraic_number " << ran << ")";
      stillNeedToPrintParams = false;
      break;
    }
    case Kind::INDEXED_ROOT_PREDICATE_OP:
    {
      const IndexedRootPredicate& irp = n.getConst<IndexedRootPredicate>();
      out << "(_ root_predicate " << irp.d_index << ")";
      stillNeedToPrintParams = false;
      break;
    }
    case Kind::BITVECTOR_BIT:
      out << "(_ @bit " << n.getOperator().getConst<BitVectorBit>().d_bitIndex
          << ")";
      stillNeedToPrintParams = false;
      break;
    case Kind::APPLY_CONSTRUCTOR:
    {
      const DType& dt = DType::datatypeOf(n.getOperator());
      if (dt.isTuple())
      {
        stillNeedToPrintParams = false;
        if (dt[0].getNumArgs() == 0)
        {
          out << "tuple.unit";
        }
        else
        {
          out << "tuple";
        }
      }
      if (dt.isNullable())
      {
        stillNeedToPrintParams = false;
        if (n.getNumChildren() == 0)
        {
          out << "(as nullable.null " << n.getType() << ")";
        }
        else
        {
          out << "nullable.some";
        }
      }
      break;
    }
    case Kind::APPLY_SELECTOR:
    {
      Node op = n.getOperator();
      const DType& dt = DType::datatypeOf(op);
      if (dt.isTuple())
      {
        stillNeedToPrintParams = false;
        out << "(_ tuple.select " << DType::indexOf(op) << ")";
      }
      else if (dt.isNullable())
      {
        stillNeedToPrintParams = false;
        out << "nullable.val";
      }
    }
    break;
    case Kind::APPLY_TESTER:
    {
      Node op = n.getOperator();
      size_t cindex = DType::indexOf(op);
      const DType& dt = DType::datatypeOf(op);
      if (dt.isNullable())
      {
        stillNeedToPrintParams = false;
        if (cindex == 0)
        {
          out << "nullable.is_null";
        }
        else
        {
          out << "nullable.is_some";
        }
      }
      else
      {
        stillNeedToPrintParams = false;
        out << "(_ is ";
        toStream(out,
                 dt[cindex].getConstructor(),
                 lbind,
                 toDepth < 0 ? toDepth : toDepth - 1);
        out << ")";
      }
    }
    break;
    case Kind::APPLY_UPDATER:
    {
      stillNeedToPrintParams = false;
      Node op = n.getOperator();
      size_t index = DType::indexOf(op);
      const DType& dt = DType::datatypeOf(op);
      size_t cindex = DType::cindexOf(op);
      if (dt.isTuple())
      {
        out << "(_ tuple.update " << index << ")";
      }
      else
      {
        out << "(_ update ";
        toStream(out,
                 dt[cindex][index].getSelector(),
                 lbind,
                 toDepth < 0 ? toDepth : toDepth - 1);
        out << ")";
      }
    }
    break;
    // kinds that don't print their operator
    case Kind::SEXPR:
    case Kind::INSTANTIATED_SORT_TYPE:
    case Kind::PARAMETRIC_DATATYPE:
    case Kind::INST_PATTERN:
    case Kind::INST_NO_PATTERN:
    case Kind::INST_PATTERN_LIST: printed = false; break;
    case Kind::STRING_CONCAT:
    case Kind::STRING_LENGTH:
    case Kind::STRING_SUBSTR:
    case Kind::STRING_UPDATE:
    case Kind::STRING_CHARAT:
    case Kind::STRING_CONTAINS:
    case Kind::STRING_INDEXOF:
    case Kind::STRING_REPLACE:
    case Kind::STRING_REPLACE_ALL:
    case Kind::STRING_REV:
    case Kind::STRING_PREFIX:
    case Kind::STRING_SUFFIX:
      // maybe print seq. instead of str.
      out << smtKindStringOf(n);
      break;
    default:
      // by default, print the kind using the smtKindString utility
      if (n.getMetaKind() != kind::metakind::PARAMETERIZED)
      {
        out << smtKindString(k);
      }
      break;
  }
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED
      && stillNeedToPrintParams)
  {
    if (toDepth != 0)
    {
      toStream(
          out, n.getOperator(), lbind, toDepth < 0 ? toDepth : toDepth - 1);
    }
    else
    {
      out << "(...)";
    }
  }
  // finished if we have no children
  if (n.getNumChildren() == 0)
  {
    return true;
  }
  if (printed)
  {
    // if printed anything, now add a space
    out << ' ';
  }
  return false;
}

void Smt2Printer::toStream(std::ostream& out,
                           TNode n,
                           const LetBinding* lbind,
                           int toDepth,
                           bool lbindTop) const
{
  std::vector<std::tuple<TNode, size_t, int>> visit;
  TNode cur;
  size_t curChild;
  int cdepth;
  visit.emplace_back(n, 0, toDepth);
  do
  {
    cur = std::get<0>(visit.back());
    curChild = std::get<1>(visit.back());
    cdepth = std::get<2>(visit.back());
    if (curChild == 0)
    {
      if (lbind != nullptr)
      {
        if (lbindTop)
        {
          // see if its letified
          uint32_t lid = lbind->getId(cur);
          if (lid != 0)
          {
            out << lbind->getPrefix() << lid;
            visit.pop_back();
            continue;
          }
        }
        else
        {
          lbindTop = true;
        }
      }
      // print the operator
      // if printed as standalone, we are done
      if (toStreamBase(out, cur, lbind, cdepth))
      {
        visit.pop_back();
        continue;
      }
      else if (cdepth == 0)
      {
        visit.pop_back();
        out << "(...)";
        if (cur.getNumChildren() > 0)
        {
          out << ')';
        }
        continue;
      }
    }
    if (curChild < cur.getNumChildren())
    {
      std::get<1>(visit.back())++;
      // toStreamBase akready adds space, skip adding space before first child
      if (curChild > 0)
      {
        out << ' ';
      }
      visit.emplace_back(cur[curChild], 0, cdepth < 0 ? cdepth : cdepth - 1);
    }
    else
    {
      Assert(cur.getNumChildren() > 0);
      out << ')';
      visit.pop_back();
    }
  } while (!visit.empty());
}

std::string Smt2Printer::smtKindString(Kind k)
{
  switch(k) {
    // builtin theory
    case Kind::FUNCTION_TYPE: return "->";
    case Kind::EQUAL: return "=";
    case Kind::DISTINCT: return "distinct";
    case Kind::SEXPR: break;

    case Kind::TYPE_OF: return "@type_of";

    // bool theory
    case Kind::NOT: return "not";
    case Kind::AND: return "and";
    case Kind::IMPLIES: return "=>";
    case Kind::OR: return "or";
    case Kind::XOR: return "xor";
    case Kind::ITE: return "ite";

    // uf theory
    case Kind::APPLY_UF: break;

    case Kind::LAMBDA: return "lambda";
    case Kind::MATCH: return "match";
    case Kind::WITNESS: return "witness";

    // arith theory
    case Kind::ADD: return "+";
    case Kind::MULT:
    case Kind::NONLINEAR_MULT: return "*";
    case Kind::IAND: return "iand";
    case Kind::POW2: return "int.pow2";
    case Kind::EXPONENTIAL: return "exp";
    case Kind::SINE: return "sin";
    case Kind::COSINE: return "cos";
    case Kind::TANGENT: return "tan";
    case Kind::COSECANT: return "csc";
    case Kind::SECANT: return "sec";
    case Kind::COTANGENT: return "cot";
    case Kind::ARCSINE: return "arcsin";
    case Kind::ARCCOSINE: return "arccos";
    case Kind::ARCTANGENT: return "arctan";
    case Kind::ARCCOSECANT: return "arccsc";
    case Kind::ARCSECANT: return "arcsec";
    case Kind::ARCCOTANGENT: return "arccot";
    case Kind::PI: return "real.pi";
    case Kind::SQRT: return "sqrt";
    case Kind::SUB: return "-";
    case Kind::NEG: return "-";
    case Kind::LT: return "<";
    case Kind::LEQ: return "<=";
    case Kind::GT: return ">";
    case Kind::GEQ: return ">=";
    case Kind::DIVISION: return "/";
    case Kind::DIVISION_TOTAL: return "/_total";
    case Kind::INTS_DIVISION: return "div";
    case Kind::INTS_DIVISION_TOTAL: return "div_total";
    case Kind::INTS_MODULUS: return "mod";
    case Kind::INTS_MODULUS_TOTAL: return "mod_total";
    case Kind::INTS_LOG2: return "int.log2";
    case Kind::INTS_ISPOW2: return "int.ispow2";
    case Kind::ABS: return "abs";
    case Kind::IS_INTEGER: return "is_int";
    case Kind::TO_INTEGER: return "to_int";
    case Kind::TO_REAL: return "to_real";
    case Kind::POW: return "^";
    case Kind::DIVISIBLE: return "divisible";

    // arrays theory
    case Kind::SELECT: return "select";
    case Kind::STORE: return "store";
    case Kind::ARRAY_TYPE: return "Array";
    case Kind::EQ_RANGE: return "eqrange";

    // ff theory
    case Kind::FINITE_FIELD_ADD: return "ff.add";
    case Kind::FINITE_FIELD_BITSUM: return "ff.bitsum";
    case Kind::FINITE_FIELD_MULT: return "ff.mul";
    case Kind::FINITE_FIELD_NEG: return "ff.neg";

    // bv theory
    case Kind::BITVECTOR_CONCAT: return "concat";
    case Kind::BITVECTOR_AND: return "bvand";
    case Kind::BITVECTOR_OR: return "bvor";
    case Kind::BITVECTOR_XOR: return "bvxor";
    case Kind::BITVECTOR_NOT: return "bvnot";
    case Kind::BITVECTOR_NAND: return "bvnand";
    case Kind::BITVECTOR_NOR: return "bvnor";
    case Kind::BITVECTOR_XNOR: return "bvxnor";
    case Kind::BITVECTOR_COMP: return "bvcomp";
    case Kind::BITVECTOR_MULT: return "bvmul";
    case Kind::BITVECTOR_ADD: return "bvadd";
    case Kind::BITVECTOR_SUB: return "bvsub";
    case Kind::BITVECTOR_NEG: return "bvneg";
    case Kind::BITVECTOR_UDIV: return "bvudiv";
    case Kind::BITVECTOR_UREM: return "bvurem";
    case Kind::BITVECTOR_SDIV: return "bvsdiv";
    case Kind::BITVECTOR_SREM: return "bvsrem";
    case Kind::BITVECTOR_SMOD: return "bvsmod";
    case Kind::BITVECTOR_SHL: return "bvshl";
    case Kind::BITVECTOR_LSHR: return "bvlshr";
    case Kind::BITVECTOR_ASHR: return "bvashr";
    case Kind::BITVECTOR_ULT: return "bvult";
    case Kind::BITVECTOR_ULE: return "bvule";
    case Kind::BITVECTOR_UGT: return "bvugt";
    case Kind::BITVECTOR_UGE: return "bvuge";
    case Kind::BITVECTOR_SLT: return "bvslt";
    case Kind::BITVECTOR_SLE: return "bvsle";
    case Kind::BITVECTOR_SGT: return "bvsgt";
    case Kind::BITVECTOR_SGE: return "bvsge";
    case Kind::BITVECTOR_NEGO: return "bvnego";
    case Kind::BITVECTOR_UADDO: return "bvuaddo";
    case Kind::BITVECTOR_SADDO: return "bvsaddo";
    case Kind::BITVECTOR_UMULO: return "bvumulo";
    case Kind::BITVECTOR_SMULO: return "bvsmulo";
    case Kind::BITVECTOR_USUBO: return "bvusubo";
    case Kind::BITVECTOR_SSUBO: return "bvssubo";
    case Kind::BITVECTOR_SDIVO: return "bvsdivo";
    case Kind::BITVECTOR_UBV_TO_INT: return "ubv_to_int";
    case Kind::BITVECTOR_SBV_TO_INT: return "sbv_to_int";
    case Kind::BITVECTOR_REDOR: return "bvredor";
    case Kind::BITVECTOR_REDAND: return "bvredand";

    case Kind::BITVECTOR_EXTRACT: return "extract";
    case Kind::BITVECTOR_REPEAT: return "repeat";
    case Kind::BITVECTOR_ZERO_EXTEND: return "zero_extend";
    case Kind::BITVECTOR_SIGN_EXTEND: return "sign_extend";
    case Kind::BITVECTOR_ROTATE_LEFT: return "rotate_left";
    case Kind::BITVECTOR_ROTATE_RIGHT: return "rotate_right";
    case Kind::INT_TO_BITVECTOR: return "int_to_bv";
    case Kind::BITVECTOR_ITE: return "bvite";
    case Kind::BITVECTOR_ULTBV: return "bvultbv";
    case Kind::BITVECTOR_SLTBV: return "bvsltbv";

    case Kind::BITVECTOR_FROM_BOOLS: return "@from_bools";
    case Kind::BITVECTOR_BIT: return "@bit";
    case Kind::BITVECTOR_SIZE: return "@bvsize";
    case Kind::CONST_BITVECTOR_SYMBOLIC: return "@bv";

    // datatypes theory
    case Kind::APPLY_TESTER: return "is";
    case Kind::APPLY_UPDATER: return "update";
    case Kind::TUPLE_TYPE: return "Tuple";
    case Kind::NULLABLE_TYPE: return "Nullable";
    case Kind::TUPLE_PROJECT: return "tuple.project";
    case Kind::NULLABLE_LIFT: return "nullable.lift";

    // set theory
    case Kind::SET_EMPTY: return "set.empty";
    case Kind::SET_UNIVERSE: return "set.universe";
    case Kind::SET_UNION: return "set.union";
    case Kind::SET_INTER: return "set.inter";
    case Kind::SET_MINUS: return "set.minus";
    case Kind::SET_SUBSET: return "set.subset";
    case Kind::SET_MEMBER: return "set.member";
    case Kind::SET_TYPE: return "Set";
    case Kind::SET_SINGLETON: return "set.singleton";
    case Kind::SET_INSERT: return "set.insert";
    case Kind::SET_COMPLEMENT: return "set.complement";
    case Kind::SET_CARD: return "set.card";
    case Kind::SET_COMPREHENSION: return "set.comprehension";
    case Kind::SET_CHOOSE: return "set.choose";
    case Kind::SET_IS_EMPTY: return "set.is_empty";
    case Kind::SET_IS_SINGLETON: return "set.is_singleton";
    case Kind::SET_MAP: return "set.map";
    case Kind::SET_FILTER: return "set.filter";
    case Kind::SET_ALL: return "set.all";
    case Kind::SET_SOME: return "set.some";
    case Kind::SET_FOLD: return "set.fold";
    case Kind::RELATION_JOIN: return "rel.join";
    case Kind::RELATION_TABLE_JOIN: return "rel.table_join";
    case Kind::RELATION_PRODUCT: return "rel.product";
    case Kind::RELATION_TRANSPOSE: return "rel.transpose";
    case Kind::RELATION_TCLOSURE: return "rel.tclosure";
    case Kind::RELATION_IDEN: return "rel.iden";
    case Kind::RELATION_JOIN_IMAGE: return "rel.join_image";
    case Kind::RELATION_GROUP: return "rel.group";
    case Kind::RELATION_AGGREGATE: return "rel.aggr";
    case Kind::RELATION_PROJECT: return "rel.project";
    case Kind::SET_EMPTY_OF_TYPE: return "@set.empty_of_type";

    // bag theory
    case Kind::BAG_TYPE: return "Bag";
    case Kind::BAG_EMPTY: return "bag.empty";
    case Kind::BAG_UNION_MAX: return "bag.union_max";
    case Kind::BAG_UNION_DISJOINT: return "bag.union_disjoint";
    case Kind::BAG_INTER_MIN: return "bag.inter_min";
    case Kind::BAG_DIFFERENCE_SUBTRACT: return "bag.difference_subtract";
    case Kind::BAG_DIFFERENCE_REMOVE: return "bag.difference_remove";
    case Kind::BAG_SUBBAG: return "bag.subbag";
    case Kind::BAG_COUNT: return "bag.count";
    case Kind::BAG_MEMBER: return "bag.member";
    case Kind::BAG_SETOF: return "bag.setof";
    case Kind::BAG_MAKE: return "bag";
    case Kind::BAG_CARD: return "bag.card";
    case Kind::BAG_CHOOSE: return "bag.choose";
    case Kind::BAG_MAP: return "bag.map";
    case Kind::BAG_FILTER: return "bag.filter";
    case Kind::BAG_ALL: return "bag.all";
    case Kind::BAG_SOME: return "bag.some";
    case Kind::BAG_FOLD: return "bag.fold";
    case Kind::BAG_PARTITION: return "bag.partition";
    case Kind::TABLE_PRODUCT: return "table.product";
    case Kind::TABLE_PROJECT: return "table.project";
    case Kind::TABLE_AGGREGATE: return "table.aggr";
    case Kind::TABLE_JOIN: return "table.join";
    case Kind::TABLE_GROUP:
      return "table.group";

      // fp theory
    case Kind::FLOATINGPOINT_FP: return "fp";
    case Kind::FLOATINGPOINT_EQ: return "fp.eq";
    case Kind::FLOATINGPOINT_ABS: return "fp.abs";
    case Kind::FLOATINGPOINT_NEG: return "fp.neg";
    case Kind::FLOATINGPOINT_ADD: return "fp.add";
    case Kind::FLOATINGPOINT_SUB: return "fp.sub";
    case Kind::FLOATINGPOINT_MULT: return "fp.mul";
    case Kind::FLOATINGPOINT_DIV: return "fp.div";
    case Kind::FLOATINGPOINT_FMA: return "fp.fma";
    case Kind::FLOATINGPOINT_SQRT: return "fp.sqrt";
    case Kind::FLOATINGPOINT_REM: return "fp.rem";
    case Kind::FLOATINGPOINT_RTI: return "fp.roundToIntegral";
    case Kind::FLOATINGPOINT_MIN: return "fp.min";
    case Kind::FLOATINGPOINT_MAX: return "fp.max";
    case Kind::FLOATINGPOINT_MIN_TOTAL: return "fp.min_total";
    case Kind::FLOATINGPOINT_MAX_TOTAL: return "fp.max_total";

    case Kind::FLOATINGPOINT_LEQ: return "fp.leq";
    case Kind::FLOATINGPOINT_LT: return "fp.lt";
    case Kind::FLOATINGPOINT_GEQ: return "fp.geq";
    case Kind::FLOATINGPOINT_GT: return "fp.gt";

    case Kind::FLOATINGPOINT_IS_NORMAL: return "fp.isNormal";
    case Kind::FLOATINGPOINT_IS_SUBNORMAL: return "fp.isSubnormal";
    case Kind::FLOATINGPOINT_IS_ZERO: return "fp.isZero";
    case Kind::FLOATINGPOINT_IS_INF: return "fp.isInfinite";
    case Kind::FLOATINGPOINT_IS_NAN: return "fp.isNaN";
    case Kind::FLOATINGPOINT_IS_NEG: return "fp.isNegative";
    case Kind::FLOATINGPOINT_IS_POS: return "fp.isPositive";

    case Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV: return "to_fp";
    case Kind::FLOATINGPOINT_TO_FP_FROM_FP: return "to_fp";
    case Kind::FLOATINGPOINT_TO_FP_FROM_REAL: return "to_fp";
    case Kind::FLOATINGPOINT_TO_FP_FROM_SBV: return "to_fp";
    case Kind::FLOATINGPOINT_TO_FP_FROM_UBV: return "to_fp_unsigned";
    case Kind::FLOATINGPOINT_TO_UBV: return "fp.to_ubv";
    case Kind::FLOATINGPOINT_TO_UBV_TOTAL: return "fp.to_ubv_total";
    case Kind::FLOATINGPOINT_TO_SBV: return "fp.to_sbv";
    case Kind::FLOATINGPOINT_TO_SBV_TOTAL: return "fp.to_sbv_total";
    case Kind::FLOATINGPOINT_TO_REAL: return "fp.to_real";
    case Kind::FLOATINGPOINT_TO_REAL_TOTAL: return "fp.to_real_total";

    case Kind::FLOATINGPOINT_COMPONENT_NAN: return "@fp.NAN";
    case Kind::FLOATINGPOINT_COMPONENT_INF: return "@fp.INF";
    case Kind::FLOATINGPOINT_COMPONENT_ZERO: return "@fp.ZERO";
    case Kind::FLOATINGPOINT_COMPONENT_SIGN: return "@fp.SIGN";
    case Kind::FLOATINGPOINT_COMPONENT_EXPONENT: return "@fp.EXPONENT";
    case Kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND: return "@fp.SIGNIFICAND";
    case Kind::ROUNDINGMODE_BITBLAST: return "@fp.RMBITBLAST";

    // string theory
    case Kind::STRING_CONCAT: return "str.++";
    case Kind::STRING_LENGTH: return "str.len";
    case Kind::STRING_SUBSTR: return "str.substr";
    case Kind::STRING_UPDATE: return "str.update";
    case Kind::STRING_CONTAINS: return "str.contains";
    case Kind::STRING_CHARAT: return "str.at";
    case Kind::STRING_INDEXOF: return "str.indexof";
    case Kind::STRING_INDEXOF_RE: return "str.indexof_re";
    case Kind::STRING_REPLACE: return "str.replace";
    case Kind::STRING_REPLACE_ALL: return "str.replace_all";
    case Kind::STRING_REPLACE_RE: return "str.replace_re";
    case Kind::STRING_REPLACE_RE_ALL: return "str.replace_re_all";
    case Kind::STRING_TO_LOWER: return "str.to_lower";
    case Kind::STRING_TO_UPPER: return "str.to_upper";
    case Kind::STRING_REV: return "str.rev";
    case Kind::STRING_PREFIX: return "str.prefixof";
    case Kind::STRING_SUFFIX: return "str.suffixof";
    case Kind::STRING_LEQ: return "str.<=";
    case Kind::STRING_LT: return "str.<";
    case Kind::STRING_FROM_CODE: return "str.from_code";
    case Kind::STRING_TO_CODE: return "str.to_code";
    case Kind::STRING_IS_DIGIT: return "str.is_digit";
    case Kind::STRING_ITOS: return "str.from_int";
    case Kind::STRING_STOI: return "str.to_int";
    case Kind::STRING_IN_REGEXP: return "str.in_re";
    case Kind::STRING_TO_REGEXP: return "str.to_re";
    case Kind::STRING_UNIT: return "str.unit";
    case Kind::REGEXP_NONE: return "re.none";
    case Kind::REGEXP_ALL: return "re.all";
    case Kind::REGEXP_ALLCHAR: return "re.allchar";
    case Kind::REGEXP_CONCAT: return "re.++";
    case Kind::REGEXP_UNION: return "re.union";
    case Kind::REGEXP_INTER: return "re.inter";
    case Kind::REGEXP_STAR: return "re.*";
    case Kind::REGEXP_PLUS: return "re.+";
    case Kind::REGEXP_OPT: return "re.opt";
    case Kind::REGEXP_RANGE: return "re.range";
    case Kind::REGEXP_REPEAT: return "re.^";
    case Kind::REGEXP_LOOP: return "re.loop";
    case Kind::REGEXP_COMPLEMENT: return "re.comp";
    case Kind::REGEXP_DIFF: return "re.diff";
    case Kind::SEQUENCE_TYPE: return "Seq";
    case Kind::SEQ_UNIT: return "seq.unit";
    case Kind::SEQ_NTH: return "seq.nth";
    case Kind::SEQ_EMPTY_OF_TYPE: return "@seq.empty_of_type";

    // sep theory
    case Kind::SEP_STAR: return "sep";
    case Kind::SEP_PTO: return "pto";
    case Kind::SEP_WAND: return "wand";
    case Kind::SEP_EMP: return "sep.emp";
    case Kind::SEP_NIL: return "sep.nil";
    case Kind::SEP_LABEL: return "@sep_label";

    // quantifiers
    case Kind::FORALL: return "forall";
    case Kind::EXISTS: return "exists";

    // HO
    case Kind::HO_APPLY: return "@";

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
      case Kind::STRING_CONCAT: return "seq.++";
      case Kind::STRING_LENGTH: return "seq.len";
      case Kind::STRING_SUBSTR: return "seq.extract";
      case Kind::STRING_UPDATE: return "seq.update";
      case Kind::STRING_CHARAT: return "seq.at";
      case Kind::STRING_CONTAINS: return "seq.contains";
      case Kind::STRING_INDEXOF: return "seq.indexof";
      case Kind::STRING_REPLACE: return "seq.replace";
      case Kind::STRING_REPLACE_ALL: return "seq.replace_all";
      case Kind::STRING_REV: return "seq.rev";
      case Kind::STRING_PREFIX: return "seq.prefixof";
      case Kind::STRING_SUFFIX: return "seq.suffixof";
      default:
        // fall through to conversion below
        break;
    }
  }
  // by default
  return smtKindString(k);
}

void Smt2Printer::toStreamDeclareType(std::ostream& out,
                                      const std::vector<TypeNode>& argTypes,
                                      TypeNode tn) const
{
  out << "(";
  if (!argTypes.empty())
  {
    copy(argTypes.begin(),
         argTypes.end() - 1,
         ostream_iterator<TypeNode>(out, " "));
    out << argTypes.back();
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
  if (modelUninterpPrint == options::ModelUninterpPrintMode::Datatype)
  {
    out << "(declare-datatype " << tn << " (";
    for (size_t i=0, nelements=elements.size(); i<nelements; i++)
    {
      Node trn = elements[i];
      if (i>0)
      {
        out << " ";
      }
      Assert (trn.getKind() == Kind::UNINTERPRETED_SORT_VALUE);
      // prints as raw symbol
      const UninterpretedSortValue& av =
          trn.getConst<UninterpretedSortValue>();
      out << "(" << av << ")";
    }
    out << "))" << std::endl;
    return;
  }
  // print the cardinality
  out << "; cardinality of " << tn << " is " << elements.size() << endl;
  if (modelUninterpPrint == options::ModelUninterpPrintMode::DeclSortAndFun)
  {
    Printer::toStreamCmdDeclareType(out, tn);
    out << std::endl;
  }
  // print the representatives
  for (const Node& trn : elements)
  {
    if (modelUninterpPrint == options::ModelUninterpPrintMode::DeclSortAndFun
        || modelUninterpPrint == options::ModelUninterpPrintMode::DeclFun)
    {
      out << "(declare-fun ";
      if (trn.getKind() == Kind::UNINTERPRETED_SORT_VALUE)
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
  if (value.getKind() == Kind::LAMBDA)
  {
    TypeNode rangeType = n.getType().getRangeType();
    out << "(define-fun " << n << " " << value[0] << " " << rangeType << " ";
    toStream(out, value[1]);
    out << ")" << endl;
  }
  else
  {
    out << "(define-fun " << n << " () " << n.getType() << " ";
    toStream(out, value);
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
  out << "(assert " << n << ')';
}

void Smt2Printer::toStreamCmdPush(std::ostream& out, uint32_t nscopes) const
{
  out << "(push " << nscopes << ")";
}

void Smt2Printer::toStreamCmdPop(std::ostream& out, uint32_t nscopes) const
{
  out << "(pop " << nscopes << ")";
}

void Smt2Printer::toStreamCmdCheckSat(std::ostream& out) const
{
  out << "(check-sat)";
}

void Smt2Printer::toStreamCmdCheckSatAssuming(
    std::ostream& out, const std::vector<Node>& nodes) const
{
  out << "(check-sat-assuming ( ";
  copy(nodes.begin(), nodes.end(), ostream_iterator<Node>(out, " "));
  out << "))";
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
  out << "(reset)";
}

void Smt2Printer::toStreamCmdResetAssertions(std::ostream& out) const
{
  out << "(reset-assertions)";
}

void Smt2Printer::toStreamCmdQuit(std::ostream& out) const { out << "(exit)"; }

void Smt2Printer::toStreamCmdDeclareFunction(
    std::ostream& out,
    const std::string& id,
    const std::vector<TypeNode>& argTypes,
    TypeNode type) const
{
  if (d_variant == Variant::alf_variant)
  {
    out << "(declare-const " << cvc5::internal::quoteSymbol(id);
    if (!argTypes.empty())
    {
      out << " (->";
      for (const TypeNode& tn : argTypes)
      {
        out << " " << tn;
      }
    }
    out << " " << type;
    if (!argTypes.empty())
    {
      out << ')';
    }
    out << ')';
    return;
  }
  out << "(declare-fun " << cvc5::internal::quoteSymbol(id) << " ";
  toStreamDeclareType(out, argTypes, type);
  out << ')';
}

void Smt2Printer::toStreamCmdDeclareOracleFun(
    std::ostream& out,
    const std::string& id,
    const std::vector<TypeNode>& argTypes,
    TypeNode type,
    const std::string& binName) const
{
  out << "(declare-oracle-fun " << cvc5::internal::quoteSymbol(id) << " ";
  toStreamDeclareType(out, argTypes, type);
  out << " " << binName << ")";
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
  out << "))";
}

void Smt2Printer::toStreamCmdDefineFunction(std::ostream& out,
                                            const std::string& id,
                                            const std::vector<Node>& formals,
                                            TypeNode range,
                                            Node formula) const
{
  if (d_variant == Variant::alf_variant)
  {
    out << "(define " << cvc5::internal::quoteSymbol(id) << " ";
    toStreamSortedVarList(out, formals);
    out << " " << formula << ')';
    return;
  }
  out << "(define-fun " << cvc5::internal::quoteSymbol(id) << " ";
  toStreamSortedVarList(out, formals);
  out << " " << range << ' ' << formula << ')';
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
  out << ")";
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
                                         const std::string& id,
                                         size_t arity) const
{
  if (d_variant == Variant::alf_variant)
  {
    out << "(declare-type " << cvc5::internal::quoteSymbol(id) << " (";
    for (size_t i = 0; i < arity; i++)
    {
      if (i > 0)
      {
        out << " ";
      }
      out << "Type";
    }
    out << "))";
    return;
  }
  out << "(declare-sort " << cvc5::internal::quoteSymbol(id) << " " << arity
      << ")";
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
  out << ") " << t << ")";
}

void Smt2Printer::toStreamCmdSimplify(std::ostream& out, Node n) const
{
  out << "(simplify " << n << ')';
}

void Smt2Printer::toStreamCmdGetValue(std::ostream& out,
                                      const std::vector<Node>& nodes) const
{
  out << "(get-value ( ";
  copy(nodes.begin(), nodes.end(), ostream_iterator<Node>(out, " "));
  out << "))";
}

void Smt2Printer::toStreamCmdGetModel(std::ostream& out) const
{
  out << "(get-model)";
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
  out << ")";
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
  out << "))";
}

void Smt2Printer::toStreamCmdGetAssignment(std::ostream& out) const
{
  out << "(get-assignment)";
}

void Smt2Printer::toStreamCmdGetAssertions(std::ostream& out) const
{
  out << "(get-assertions)";
}

void Smt2Printer::toStreamCmdGetProof(std::ostream& out,
                                      modes::ProofComponent c) const
{
  out << "(get-proof";
  if (c != modes::ProofComponent::FULL)
  {
    out << " :" << c;
  }
  out << ")";
}

void Smt2Printer::toStreamCmdGetUnsatAssumptions(std::ostream& out) const
{
  out << "(get-unsat-assumptions)";
}

void Smt2Printer::toStreamCmdGetUnsatCore(std::ostream& out) const
{
  out << "(get-unsat-core)";
}

void Smt2Printer::toStreamCmdGetDifficulty(std::ostream& out) const
{
  out << "(get-difficulty)";
}

void Smt2Printer::toStreamCmdGetTimeoutCore(std::ostream& out) const
{
  out << "(get-timeout-core)";
}

void Smt2Printer::toStreamCmdGetTimeoutCoreAssuming(
    std::ostream& out, const std::vector<Node>& assumptions) const
{
  out << "(get-timeout-core-assuming (";
  bool firstTime = true;
  for (const Node& a : assumptions)
  {
    if (firstTime)
    {
      firstTime = false;
    }
    else
    {
      out << " ";
    }
    out << a;
  }
  out << "))";
}

void Smt2Printer::toStreamCmdGetLearnedLiterals(std::ostream& out,
                                                modes::LearnedLitType t) const
{
  out << "(get-learned-literals";
  if (t != modes::LearnedLitType::INPUT)
  {
    out << " :" << t;
  }
  out << ")";
}

void Smt2Printer::toStreamCmdSetBenchmarkLogic(std::ostream& out,
                                               const std::string& logic) const
{
  out << "(set-logic " << logic << ')';
}

void Smt2Printer::toStreamCmdSetInfo(std::ostream& out,
                                     const std::string& flag,
                                     const std::string& value) const
{
  out << "(set-info :" << flag << " " << value << ")";
}

void Smt2Printer::toStreamCmdGetInfo(std::ostream& out,
                                     const std::string& flag) const
{
  out << "(get-info :" << flag << ')';
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
  out << ')';
}

void Smt2Printer::toStreamCmdGetOption(std::ostream& out,
                                       const std::string& flag) const
{
  out << "(get-option :" << flag << ')';
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
  out << ")";
}

void Smt2Printer::toStreamCmdDeclareHeap(std::ostream& out,
                                         TypeNode locType,
                                         TypeNode dataType) const
{
  out << "(declare-heap (" << locType << " " << dataType << "))";
}

void Smt2Printer::toStreamSkolem(std::ostream& out,
                                 Node cacheVal,
                                 SkolemId id,
                                 bool isApplied,
                                 int toDepth,
                                 const LetBinding* lbind) const
{
  // true if this is a standalone skolem that requires printing with arguments
  bool unappliedApp = (!isApplied && !cacheVal.isNull());
  if (unappliedApp)
  {
    out << "(";
  }
  out << "@" << id;
  if (cacheVal.getKind() == Kind::SEXPR)
  {
    for (const Node& cv : cacheVal)
    {
      out << " ";
      toStream(out, cv, lbind, toDepth);
    }
  }
  else if (!cacheVal.isNull())
  {
    out << " ";
    toStream(out, cacheVal, lbind, toDepth);
  }
  if (unappliedApp)
  {
    out << ")";
  }
  else if (isApplied)
  {
    // separates further arguments
    out << " ";
  }
}

void Smt2Printer::toStreamCmdEmpty(std::ostream& out,
                                   const std::string& name) const
{
}

void Smt2Printer::toStreamCmdEcho(std::ostream& out,
                                  const std::string& output) const
{
  out << "(echo " << cvc5::internal::quoteString(output) << ')';
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
    NodeManager* nm = t.getNodeManager();
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
        if (i > 0)
        {
          types_list << ' ';
        }
        const DTypeConstructor& cons = dt[i];
        if (cons.isSygusAnyConstant())
        {
          types_list << "(Constant " << cons[0].getRangeType() << ")";
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
            Node bv = NodeManager::mkBoundVar(ss.str(), argType);
            cchildren.push_back(bv);
            // if fresh type, store it for later processing
            if (grammarTypes.insert(argType).second)
            {
              typesToPrint.push_back(argType);
            }
          }
          Node consToPrint = nm->mkNode(Kind::APPLY_CONSTRUCTOR, cchildren);
          // now, print it using the conversion to builtin with external
          types_list << theory::datatypes::utils::sygusToBuiltin(consToPrint,
                                                                true);
        }
      }
      types_list << "))";
    } while (!typesToPrint.empty());

    out << "(" << types_predecl.str() << ")(" << types_list.str() << ')';
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
  // print grammar, if any
  if (!sygusType.isNull())
  {
    out << sygusGrammarString(sygusType);
  }
  out << ')';
}

void Smt2Printer::toStreamCmdDeclareVar(std::ostream& out,
                                        const std::string& id,
                                        TypeNode type) const
{
  out << "(declare-var " << cvc5::internal::quoteSymbol(id) << ' ' << type
      << ')';
}

void Smt2Printer::toStreamCmdConstraint(std::ostream& out, Node n) const
{
  out << "(constraint " << n << ')';
}

void Smt2Printer::toStreamCmdAssume(std::ostream& out, Node n) const
{
  out << "(assume " << n << ')';
}

void Smt2Printer::toStreamCmdInvConstraint(
    std::ostream& out, Node inv, Node pre, Node trans, Node post) const
{
  out << "(inv-constraint " << inv << ' ' << pre << ' ' << trans << ' ' << post
      << ')';
}

void Smt2Printer::toStreamCmdCheckSynth(std::ostream& out) const
{
  out << "(check-synth)";
}

void Smt2Printer::toStreamCmdCheckSynthNext(std::ostream& out) const
{
  out << "(check-synth-next)";
}

void Smt2Printer::toStreamCmdFindSynth(std::ostream& out,
                                       modes::FindSynthTarget fst,
                                       TypeNode sygusType) const
{
  out << "(find-synth :" << fst;
  // print grammar, if any
  if (!sygusType.isNull())
  {
    out << " " << sygusGrammarString(sygusType);
  }
  out << ")";
}

void Smt2Printer::toStreamCmdFindSynthNext(std::ostream& out) const
{
  out << "(find-synth-next)";
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
  out << ')';
}

void Smt2Printer::toStreamCmdGetInterpolNext(std::ostream& out) const
{
  out << "(get-interpolant-next)";
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
  out << ')';
}

void Smt2Printer::toStreamCmdGetAbductNext(std::ostream& out) const
{
  out << "(get-abduct-next)";
}

void Smt2Printer::toStreamCmdGetQuantifierElimination(std::ostream& out,
                                                      Node n,
                                                      bool doFull) const
{
  out << '(' << (doFull ? "get-qe" : "get-qe-disjunct") << ' ' << n << ')';
}

/*
   --------------------------------------------------------------------------
    End of Handling SyGuS commands
   --------------------------------------------------------------------------
*/

}  // namespace smt2
}  // namespace printer
}  // namespace cvc5::internal

/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Dejan Jovanovic, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * BV rewrite rule enum.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__THEORY_BV_REWRITE_RULES_H
#define CVC5__THEORY__BV__THEORY_BV_REWRITE_RULES_H

#include <sstream>

#include "context/context.h"
#include "printer/printer.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

enum RewriteRuleId
{

  /// core normalization rules
  EmptyRule,
  ConcatFlatten,
  ConcatExtractMerge,
  ConcatConstantMerge,
  ExtractExtract,
  ExtractWhole,
  ExtractConcat,
  ExtractConstant,
  FailEq,
  SimplifyEq,
  ReflexivityEq,

  /// operator elimination rules
  UgtEliminate,
  UgeEliminate,
  SgeEliminate,
  SgtEliminate,
  RedorEliminate,
  RedandEliminate,
  SubEliminate,
  SleEliminate,
  UleEliminate,
  RepeatEliminate,
  RotateLeftEliminate,
  RotateRightEliminate,
  NandEliminate,
  NorEliminate,
  XnorEliminate,
  SdivEliminate,
  UdivEliminate,
  SmodEliminate,
  SremEliminate,
  ZeroExtendEliminate,
  NegoEliminate,
  UaddoEliminate,
  SaddoEliminate,
  UmuloEliminate,
  SmuloEliminate,
  UsuboEliminate,
  SsuboEliminate,
  SdivoEliminate,
  SizeEliminate,

  /// ground term evaluation
  EvalEquals,
  EvalConcat,
  EvalAnd,
  EvalOr,
  EvalXor,
  EvalNot,
  EvalMult,
  EvalAdd,
  EvalUdiv,
  EvalUrem,
  EvalShl,
  EvalLshr,
  EvalAshr,
  EvalUlt,
  EvalUltBv,
  EvalUle,
  EvalExtract,
  EvalSignExtend,
  EvalRotateLeft,
  EvalRotateRight,
  EvalNeg,
  EvalSlt,
  EvalSltBv,
  EvalSle,
  EvalITEBv,
  EvalComp,
  EvalConstBvSym,
  EvalEagerAtom,

  /// simplification rules
  /// all of these rules decrease formula size
  BvIteConstCond,
  BvIteEqualChildren,
  BvIteConstChildren,
  BvIteEqualCond,
  BvIteMergeThenIf,
  BvIteMergeElseIf,
  BvIteMergeThenElse,
  BvIteMergeElseElse,
  BvComp,
  ShlByConst,
  LshrByConst,
  AshrByConst,
  AndOrXorConcatPullUp,
  NegEliminate,
  OrEliminate,
  XorEliminate,
  OrZero,
  OrOne,
  XorOnes,
  XorZero,
  NotIdemp,
  UltZero,
  UltSelf,
  UleZero,
  UleSelf,
  ZeroUle,
  UleMax,
  MultPow2,
  MultSlice,
  ExtractMultLeadingBit,
  NegIdemp,
  UdivPow2,
  UdivZero,
  UdivOne,
  UremPow2,
  UremOne,
  UremSelf,
  ShiftZero,
  UgtUrem,

  UltOne,
  UltOnes,
  SltZero,
  SltSelf,
  MergeSignExtend,
  SignExtendEqConst,
  ZeroExtendEqConst,
  SignExtendUltConst,
  ZeroExtendUltConst,
  IneqElimConversion,

  /// normalization rules
  ExtractNot,
  ExtractSignExtend,
  DoubleNeg,
  NegMult,
  NegSub,
  NegAdd,
  NotConcat,
  FlattenAssocCommut,
  FlattenAssocCommutNoDuplicates,
  AddCombineLikeTerms,
  MultSimplify,
  MultDistribConst,
  MultDistrib,
  SolveEq,
  BitwiseEq,
  AndSimplify,
  OrSimplify,
  XorSimplify,
  BitwiseSlicing,
  // rules to simplify bitblasting
  UltAddOne,
  ConcatToMult,
  MultSltMult,
  BitConst,
};

inline std::ostream& operator << (std::ostream& out, RewriteRuleId ruleId) {
  switch (ruleId) {
  case EmptyRule:           out << "EmptyRule";           return out;
  case ConcatFlatten:       out << "ConcatFlatten";       return out;
  case ConcatExtractMerge:  out << "ConcatExtractMerge";  return out;
  case ConcatConstantMerge: out << "ConcatConstantMerge"; return out;
  case AndOrXorConcatPullUp:out << "AndOrXorConcatPullUp";return out;
  case NegEliminate: out << "NegEliminate"; return out;
  case OrEliminate: out << "OrEliminate"; return out;
  case XorEliminate: out << "XorEliminate"; return out;
  case ExtractExtract:      out << "ExtractExtract";      return out;
  case ExtractWhole:        out << "ExtractWhole";        return out;
  case ExtractConcat:       out << "ExtractConcat";       return out;
  case ExtractConstant:     out << "ExtractConstant";     return out;
  case FailEq:              out << "FailEq";              return out;
  case SimplifyEq:          out << "SimplifyEq";          return out;
  case ReflexivityEq:       out << "ReflexivityEq";       return out;
  case UgtEliminate:        out << "UgtEliminate";        return out;
  case SgtEliminate:        out << "SgtEliminate";        return out;
  case UgeEliminate:        out << "UgeEliminate";        return out;
  case SgeEliminate:        out << "SgeEliminate";        return out;
  case RedorEliminate:      out << "RedorEliminate";      return out;
  case RedandEliminate:     out << "RedandEliminate";     return out;
  case RepeatEliminate:     out << "RepeatEliminate";     return out;
  case RotateLeftEliminate: out << "RotateLeftEliminate"; return out;
  case RotateRightEliminate:out << "RotateRightEliminate";return out;
  case SizeEliminate: out << "SizeEliminate"; return out;
  case NandEliminate:       out << "NandEliminate";       return out;
  case NorEliminate :       out << "NorEliminate";        return out;
  case SdivEliminate :      out << "SdivEliminate";       return out;
  case SremEliminate :      out << "SremEliminate";       return out;
  case SmodEliminate :      out << "SmodEliminate";       return out;
  case ZeroExtendEliminate :out << "ZeroExtendEliminate"; return out;
  case EvalEquals :         out << "EvalEquals";          return out;
  case EvalConcat :         out << "EvalConcat";          return out;
  case EvalAnd :            out << "EvalAnd";             return out;
  case EvalOr :             out << "EvalOr";              return out;
  case EvalXor :            out << "EvalXor";             return out;
  case EvalNot :            out << "EvalNot";             return out;
  case EvalMult :           out << "EvalMult";            return out;
  case EvalAdd: out << "EvalAdd"; return out;
  case EvalUdiv :           out << "EvalUdiv";            return out;
  case EvalUrem :           out << "EvalUrem";            return out;
  case EvalShl :            out << "EvalShl";             return out;
  case EvalLshr :           out << "EvalLshr";            return out;
  case EvalAshr :           out << "EvalAshr";            return out;
  case EvalUlt :            out << "EvalUlt";             return out;
  case EvalUle :            out << "EvalUle";             return out;
  case EvalSlt :            out << "EvalSlt";             return out;
  case EvalSle :            out << "EvalSle";             return out; 
  case EvalSltBv:           out << "EvalSltBv";           return out;
  case EvalITEBv:           out << "EvalITEBv";           return out;
  case EvalComp:            out << "EvalComp";            return out;
  case EvalConstBvSym: out << "EvalConstBvSym"; return out;
  case EvalEagerAtom: out << "EvalEagerAtom"; return out;
  case EvalExtract :        out << "EvalExtract";         return out;
  case EvalSignExtend :     out << "EvalSignExtend";      return out;
  case EvalRotateLeft :     out << "EvalRotateLeft";      return out;
  case EvalRotateRight :    out << "EvalRotateRight";     return out;
  case EvalNeg :            out << "EvalNeg";             return out;
  case BvIteConstCond :     out << "BvIteConstCond";      return out;
  case BvIteEqualChildren : out << "BvIteEqualChildren";  return out;
  case BvIteConstChildren : out << "BvIteConstChildren";  return out;
  case BvIteEqualCond :     out << "BvIteEqualCond";      return out;
  case BvIteMergeThenIf :   out << "BvIteMergeThenIf";    return out;
  case BvIteMergeElseIf :   out << "BvIteMergeElseIf";    return out;
  case BvIteMergeThenElse : out << "BvIteMergeThenElse";  return out;
  case BvIteMergeElseElse : out << "BvIteMergeElseElse";  return out;
  case BvComp :             out << "BvComp";              return out;
  case ShlByConst :         out << "ShlByConst";          return out;
  case LshrByConst :        out << "LshrByConst";         return out;
  case AshrByConst :        out << "AshrByConst";         return out;
  case ExtractNot :         out << "ExtractNot";          return out;
  case DoubleNeg :          out << "DoubleNeg";           return out;
  case NotConcat :          out << "NotConcat";           return out;
  case UltZero :            out << "UltZero";             return out;
  case UleZero :            out << "UleZero";             return out;
  case ZeroUle :            out << "ZeroUle";             return out;
  case UleMax :             out << "UleMax";              return out;
  case SleEliminate :       out << "SleEliminate";        return out;
  case XorOnes: out << "XorOnes"; return out;
  case XorZero :       out << "XorZero";        return out;
  case MultPow2 :            out << "MultPow2";             return out;
  case MultSlice :            out << "MultSlice";             return out;
  case ExtractMultLeadingBit :            out << "ExtractMultLeadingBit";             return out;
  case NegIdemp :            out << "NegIdemp";             return out;
  case UdivPow2 :            out << "UdivPow2";             return out;
  case UdivZero:
    out << "UdivZero";
    return out;
  case UdivOne :            out << "UdivOne";             return out;
  case UremPow2 :            out << "UremPow2";             return out;
  case UremOne :            out << "UremOne";             return out;
  case UremSelf :            out << "UremSelf";             return out;
  case ShiftZero :            out << "ShiftZero";             return out;
  case UgtUrem: out << "UgtUrem"; return out;
  case SubEliminate :            out << "SubEliminate";             return out;
  case XnorEliminate :            out << "XnorEliminate";             return out;
  case UaddoEliminate:            out << "UaddoEliminate";             return out;
  case SaddoEliminate:            out << "SaddoEliminate";             return out;
  case UmuloEliminate:            out << "UmuloEliminate";             return out;
  case SmuloEliminate:            out << "SmuloEliminate";             return out;
  case UsuboEliminate:            out << "SsuboEliminate";             return out;
  case SsuboEliminate: out << "SsuboEliminate"; return out;
  case NotIdemp :                  out << "NotIdemp"; return out;
  case UleSelf:                    out << "UleSelf"; return out; 
  case FlattenAssocCommut:     out << "FlattenAssocCommut"; return out;
  case FlattenAssocCommutNoDuplicates:
    out << "FlattenAssocCommutNoDuplicates";
    return out;
  case AddCombineLikeTerms: out << "AddCombineLikeTerms"; return out;
  case MultSimplify: out << "MultSimplify"; return out;
  case MultDistribConst: out << "MultDistribConst"; return out;
  case SolveEq : out << "SolveEq"; return out;
  case BitwiseEq : out << "BitwiseEq"; return out;
  case NegMult : out << "NegMult"; return out;
  case NegSub : out << "NegSub"; return out;
  case AndSimplify : out << "AndSimplify"; return out;
  case OrSimplify : out << "OrSimplify"; return out;
  case XorSimplify : out << "XorSimplify"; return out;
  case NegAdd: out << "NegAdd"; return out;
  case UltOne : out << "UltOne"; return out;
  case UltOnes: out << "UltOnes"; return out;
  case MergeSignExtend : out << "MergeSignExtend"; return out;
  case SignExtendEqConst: out << "SignExtendEqConst"; return out;
  case ZeroExtendEqConst: out << "ZeroExtendEqConst"; return out;
  case SignExtendUltConst: out << "SignExtendUltConst"; return out;
  case ZeroExtendUltConst: out << "ZeroExtendUltConst"; return out;
  case IneqElimConversion: out << "IneqElimConversion"; return out;

  case UleEliminate : out << "UleEliminate"; return out;
  case BitwiseSlicing : out << "BitwiseSlicing"; return out;
  case ExtractSignExtend : out << "ExtractSignExtend"; return out;
  case MultDistrib: out << "MultDistrib"; return out;
  case UltAddOne: out << "UltAddOne"; return out;
  case ConcatToMult: out << "ConcatToMult"; return out;
  case MultSltMult: out << "MultSltMult"; return out;
  case BitConst: out << "BitConst"; return out;
  default:
    Unreachable();
  }
};

template <RewriteRuleId rule>
class RewriteRule {

  /** Actually apply the rewrite rule */
  static inline Node apply(TNode node) {
    Unreachable();
    SuppressWrongNoReturnWarning;
  }

public:

  RewriteRule() {
    
  }

  ~RewriteRule() {
    
  }

  static inline bool applies(TNode node)
  {
    Unreachable();
    SuppressWrongNoReturnWarning;
  }

  template <bool checkApplies>
  static inline Node run(TNode node)
  {
    if (!checkApplies || applies(node))
    {
      Trace("theory::bv::rewrite")
          << "RewriteRule<" << rule << ">(" << node << ")" << std::endl;
      Assert(checkApplies || applies(node));
      Node result = apply(node);
      Trace("theory::bv::rewrite") << "RewriteRule<" << rule << ">(" << node
                                   << ") => " << result << std::endl;
      return result;
    }
    else
    {
      return node;
    }
  }
};

/** Have to list all the rewrite rules to get the statistics out */
struct AllRewriteRules {
  RewriteRule<EmptyRule>                      rule00;
  RewriteRule<ConcatFlatten>                  rule01;
  RewriteRule<ConcatExtractMerge>             rule02;
  RewriteRule<ConcatConstantMerge>            rule03;
  RewriteRule<ExtractExtract>                 rule04;
  RewriteRule<ExtractWhole>                   rule05;
  RewriteRule<ExtractConcat>                  rule06;
  RewriteRule<ExtractConstant>                rule07;
  RewriteRule<FailEq>                         rule08;
  RewriteRule<SimplifyEq>                     rule09;
  RewriteRule<ReflexivityEq>                  rule10;
  RewriteRule<UgtEliminate>                   rule11;
  RewriteRule<SgtEliminate>                   rule12;
  RewriteRule<UgeEliminate>                   rule13;
  RewriteRule<SgeEliminate>                   rule14;
  RewriteRule<NegMult>                        rule15;
  RewriteRule<NegSub>                         rule16;
  RewriteRule<RepeatEliminate>                rule17;
  RewriteRule<RotateLeftEliminate>            rule18;
  RewriteRule<RotateRightEliminate>           rule19;
  RewriteRule<NandEliminate>                  rule20;
  RewriteRule<NorEliminate>                   rule21;
  RewriteRule<SdivEliminate>                  rule22;
  RewriteRule<SremEliminate>                  rule23;
  RewriteRule<SmodEliminate>                  rule24;
  RewriteRule<EvalConcat>                     rule25;
  RewriteRule<EvalAnd>                        rule26;
  RewriteRule<EvalOr>                         rule27;
  RewriteRule<EvalXor>                        rule28;
  RewriteRule<EvalNot>                        rule29;
  RewriteRule<EvalSlt>                        rule30;
  RewriteRule<EvalMult>                       rule31;
  RewriteRule<EvalAdd> rule32;
  RewriteRule<XorSimplify>                    rule33;
  RewriteRule<EvalUdiv>                       rule34;
  RewriteRule<EvalUrem>                       rule35;
  RewriteRule<EvalShl>                        rule36;
  RewriteRule<EvalLshr>                       rule37;
  RewriteRule<EvalAshr>                       rule38;
  RewriteRule<EvalUlt>                        rule39;
  RewriteRule<EvalUle>                        rule40;
  RewriteRule<EvalSle>                        rule41;
  RewriteRule<EvalExtract>                    rule43;
  RewriteRule<EvalSignExtend>                 rule44;
  RewriteRule<EvalRotateLeft>                 rule45;
  RewriteRule<EvalRotateRight>                rule46;
  RewriteRule<EvalEquals>                     rule47;
  RewriteRule<EvalNeg>                        rule48;
  RewriteRule<ShlByConst>                     rule50;
  RewriteRule<LshrByConst>                    rule51;
  RewriteRule<AshrByConst>                    rule52;
  RewriteRule<ExtractNot>                     rule54;
  RewriteRule<DoubleNeg>                      rule56;
  RewriteRule<NotConcat>                      rule57;
  RewriteRule<UltZero>                        rule68;
  RewriteRule<UleZero>                        rule69;
  RewriteRule<ZeroUle>                        rule70;
  RewriteRule<ZeroExtendEliminate>            rule73;
  RewriteRule<UleMax>                         rule74;
  RewriteRule<SleEliminate>                   rule77;
  RewriteRule<SubEliminate>                   rule82;
  RewriteRule<XorOnes> rule83;
  RewriteRule<XorZero>                        rule84;
  RewriteRule<MultSlice>                      rule85;
  RewriteRule<FlattenAssocCommutNoDuplicates> rule86;
  RewriteRule<MultPow2>                       rule87;
  RewriteRule<ExtractMultLeadingBit>          rule88;
  RewriteRule<NegIdemp>                       rule91;
  RewriteRule<UdivPow2>                       rule92;
  RewriteRule<UdivZero>                       rule93;
  RewriteRule<UdivOne>                        rule94;
  RewriteRule<UremPow2>                       rule95;
  RewriteRule<UremOne>                        rule96;
  RewriteRule<UremSelf>                       rule97;
  RewriteRule<ShiftZero>                      rule98;
  RewriteRule<XnorEliminate>                  rule100;
  RewriteRule<NotIdemp>                       rule102;
  RewriteRule<UleSelf>                        rule103;
  RewriteRule<FlattenAssocCommut>             rule104;
  RewriteRule<AddCombineLikeTerms> rule105;
  RewriteRule<MultSimplify>                   rule106;
  RewriteRule<MultDistribConst>               rule107;
  RewriteRule<AndSimplify>                    rule108;
  RewriteRule<OrSimplify>                     rule109;
  RewriteRule<NegAdd> rule110;
  RewriteRule<SolveEq>                        rule112;
  RewriteRule<BitwiseEq>                      rule113;
  RewriteRule<UltOne>                         rule114;
  RewriteRule<MultDistrib>                    rule118;
  RewriteRule<UltAddOne> rule119;
  RewriteRule<ConcatToMult>                   rule120;
  RewriteRule<RedorEliminate>                 rule122;
  RewriteRule<RedandEliminate>                rule123;
  RewriteRule<SignExtendEqConst>              rule124;
  RewriteRule<ZeroExtendEqConst>              rule125;
  RewriteRule<SignExtendUltConst>             rule126;
  RewriteRule<ZeroExtendUltConst>             rule127;
  RewriteRule<MultSltMult>                    rule128;
  RewriteRule<BvComp>                         rule130;
  RewriteRule<BvIteConstCond>                 rule131;
  RewriteRule<BvIteEqualChildren>             rule132;
  RewriteRule<BvIteConstChildren>             rule133;
  RewriteRule<BvIteEqualCond>                 rule134;
  RewriteRule<BvIteMergeThenIf>               rule135;
  RewriteRule<BvIteMergeElseIf>               rule136;
  RewriteRule<BvIteMergeThenElse>             rule137;
  RewriteRule<BvIteMergeElseElse>             rule138;
  RewriteRule<AndOrXorConcatPullUp>           rule139;
  RewriteRule<NegEliminate> rule140;
  RewriteRule<OrEliminate> rule141;
  RewriteRule<XorEliminate> rule142;
  RewriteRule<SdivEliminate> rule143;
  RewriteRule<SremEliminate> rule144;
  RewriteRule<SmodEliminate> rule145;
  RewriteRule<UgtUrem> rule146;
  RewriteRule<UltOnes> rule147;
  RewriteRule<UaddoEliminate> rule148;
  RewriteRule<SaddoEliminate> rule149;
  RewriteRule<UmuloEliminate> rule150;
  RewriteRule<SmuloEliminate> rule151;
  RewriteRule<UsuboEliminate> rule152;
  RewriteRule<SsuboEliminate> rule153;
};

template <>
inline bool RewriteRule<EmptyRule>::applies(CVC5_UNUSED TNode node)
{
  return false;
}

template<> inline
Node RewriteRule<EmptyRule>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<EmptyRule> for " << node.getKind() <<"\n"; 
  Unreachable();
  return node;
}

template<Kind kind, RewriteRuleId rule>
struct ApplyRuleToChildren {

  static Node apply(TNode node) {
    if (node.getKind() != kind) {
      return RewriteRule<rule>::template run<true>(node);
    }
    NodeBuilder result(node.getNodeManager(), kind);
    for (unsigned i = 0, end = node.getNumChildren(); i < end; ++ i) {
      result << RewriteRule<rule>::template run<true>(node[i]);
    }
    return result;
  }

  static bool applies(TNode node) {
    if (node.getKind() == kind) return true;
    return RewriteRule<rule>::applies(node);
  }

  template <bool checkApplies>
  static Node run(TNode node) {
    if (!checkApplies || applies(node)) {
      return apply(node);
    } else {
      return node;
    }
  }
};

template <
  typename R1,
  typename R2  = RewriteRule<EmptyRule>,
  typename R3  = RewriteRule<EmptyRule>,
  typename R4  = RewriteRule<EmptyRule>,
  typename R5  = RewriteRule<EmptyRule>,
  typename R6  = RewriteRule<EmptyRule>,
  typename R7  = RewriteRule<EmptyRule>,
  typename R8  = RewriteRule<EmptyRule>,
  typename R9  = RewriteRule<EmptyRule>,
  typename R10 = RewriteRule<EmptyRule>,
  typename R11 = RewriteRule<EmptyRule>,
  typename R12 = RewriteRule<EmptyRule>,
  typename R13 = RewriteRule<EmptyRule>,
  typename R14 = RewriteRule<EmptyRule>,
  typename R15 = RewriteRule<EmptyRule>,
  typename R16 = RewriteRule<EmptyRule>,
  typename R17 = RewriteRule<EmptyRule>,
  typename R18 = RewriteRule<EmptyRule>,
  typename R19 = RewriteRule<EmptyRule>,
  typename R20 = RewriteRule<EmptyRule>
  >
struct LinearRewriteStrategy {
  static Node apply(TNode node) {
    Node current = node;
    if (R1::applies(current)) current  = R1::template run<false>(current);
    if (R2::applies(current)) current  = R2::template run<false>(current);
    if (R3::applies(current)) current  = R3::template run<false>(current);
    if (R4::applies(current)) current  = R4::template run<false>(current);
    if (R5::applies(current)) current  = R5::template run<false>(current);
    if (R6::applies(current)) current  = R6::template run<false>(current);
    if (R7::applies(current)) current  = R7::template run<false>(current);
    if (R8::applies(current)) current  = R8::template run<false>(current);
    if (R9::applies(current)) current  = R9::template run<false>(current);
    if (R10::applies(current)) current = R10::template run<false>(current);
    if (R11::applies(current)) current = R11::template run<false>(current);
    if (R12::applies(current)) current = R12::template run<false>(current);
    if (R13::applies(current)) current = R13::template run<false>(current);
    if (R14::applies(current)) current = R14::template run<false>(current);
    if (R15::applies(current)) current = R15::template run<false>(current);
    if (R16::applies(current)) current = R16::template run<false>(current);
    if (R17::applies(current)) current = R17::template run<false>(current);
    if (R18::applies(current)) current = R18::template run<false>(current);
    if (R19::applies(current)) current = R19::template run<false>(current);
    if (R20::applies(current)) current = R20::template run<false>(current);
    return current;
  }
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
#endif

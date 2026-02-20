/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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

#include <ostream>

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

inline std::ostream& operator<<(std::ostream& o, RewriteRuleId ruleId)
{
  // clang-format off
  switch (ruleId) 
  {
  case EmptyRule:                      o << "EmptyRule";                      break;
  case ConcatFlatten:                  o << "ConcatFlatten";                  break;
  case ConcatExtractMerge:             o << "ConcatExtractMerge";             break;
  case ConcatConstantMerge:            o << "ConcatConstantMerge";            break;
  case AndOrXorConcatPullUp:           o << "AndOrXorConcatPullUp";           break;    
  case NegEliminate:                   o << "NegEliminate";                   break;
  case OrEliminate:                    o << "OrEliminate";                    break;
  case XorEliminate:                   o << "XorEliminate";                   break;
  case ExtractExtract:                 o << "ExtractExtract";                 break;
  case ExtractWhole:                   o << "ExtractWhole";                   break;
  case ExtractConcat:                  o << "ExtractConcat";                  break;
  case ExtractConstant:                o << "ExtractConstant";                break;
  case FailEq:                         o << "FailEq";                         break;
  case SimplifyEq:                     o << "SimplifyEq";                     break;
  case ReflexivityEq:                  o << "ReflexivityEq";                  break;
  case UgtEliminate:                   o << "UgtEliminate";                   break;
  case SgtEliminate:                   o << "SgtEliminate";                   break;
  case UgeEliminate:                   o << "UgeEliminate";                   break;
  case SgeEliminate:                   o << "SgeEliminate";                   break;
  case RedorEliminate:                 o << "RedorEliminate";                 break;
  case RedandEliminate:                o << "RedandEliminate";                break;
  case RepeatEliminate:                o << "RepeatEliminate";                break;
  case RotateLeftEliminate:            o << "RotateLeftEliminate";            break;
  case RotateRightEliminate:           o << "RotateRightEliminate";           break;    
  case SizeEliminate:                  o << "SizeEliminate";                  break;
  case NandEliminate:                  o << "NandEliminate";                  break;
  case NorEliminate:                   o << "NorEliminate";                   break;
  case SdivEliminate:                  o << "SdivEliminate";                  break;
  case SremEliminate:                  o << "SremEliminate";                  break;
  case SmodEliminate:                  o << "SmodEliminate";                  break;
  case ZeroExtendEliminate:            o << "ZeroExtendEliminate";            break;
  case EvalEquals:                     o << "EvalEquals";                     break;
  case EvalConcat:                     o << "EvalConcat";                     break;
  case EvalAnd:                        o << "EvalAnd";                        break;
  case EvalOr:                         o << "EvalOr";                         break;
  case EvalXor:                        o << "EvalXor";                        break;
  case EvalNot:                        o << "EvalNot";                        break;
  case EvalMult:                       o << "EvalMult";                       break;
  case EvalAdd:                        o << "EvalAdd";                        break;
  case EvalUdiv:                       o << "EvalUdiv";                       break;
  case EvalUrem:                       o << "EvalUrem";                       break;
  case EvalShl:                        o << "EvalShl";                        break;
  case EvalLshr:                       o << "EvalLshr";                       break;
  case EvalAshr:                       o << "EvalAshr";                       break;
  case EvalUlt:                        o << "EvalUlt";                        break;
  case EvalUle:                        o << "EvalUle";                        break;
  case EvalSlt:                        o << "EvalSlt";                        break;
  case EvalSle:                        o << "EvalSle";                        break;
  case EvalSltBv:                      o << "EvalSltBv";                      break;
  case EvalITEBv:                      o << "EvalITEBv";                      break;
  case EvalComp:                       o << "EvalComp";                       break;
  case EvalConstBvSym:                 o << "EvalConstBvSym";                 break;
  case EvalEagerAtom:                  o << "EvalEagerAtom";                  break;
  case EvalExtract:                    o << "EvalExtract";                    break;
  case EvalSignExtend:                 o << "EvalSignExtend";                 break;
  case EvalRotateLeft:                 o << "EvalRotateLeft";                 break;
  case EvalRotateRight:                o << "EvalRotateRight";                break;
  case EvalNeg:                        o << "EvalNeg";                        break;
  case BvIteConstCond:                 o << "BvIteConstCond";                 break;
  case BvIteEqualChildren:             o << "BvIteEqualChildren";             break;
  case BvIteConstChildren:             o << "BvIteConstChildren";             break;
  case BvIteEqualCond:                 o << "BvIteEqualCond";                 break;
  case BvIteMergeThenIf:               o << "BvIteMergeThenIf";               break;
  case BvIteMergeElseIf:               o << "BvIteMergeElseIf";               break;
  case BvIteMergeThenElse:             o << "BvIteMergeThenElse";             break;
  case BvIteMergeElseElse:             o << "BvIteMergeElseElse";             break;
  case BvComp:                         o << "BvComp";                         break;
  case ShlByConst:                     o << "ShlByConst";                     break;
  case LshrByConst:                    o << "LshrByConst";                    break;
  case AshrByConst:                    o << "AshrByConst";                    break;
  case ExtractNot:                     o << "ExtractNot";                     break;
  case DoubleNeg:                      o << "DoubleNeg";                      break;
  case NotConcat:                      o << "NotConcat";                      break;
  case UltZero:                        o << "UltZero";                        break;
  case UleZero:                        o << "UleZero";                        break;
  case ZeroUle:                        o << "ZeroUle";                        break;
  case UleMax:                         o << "UleMax";                         break;
  case SleEliminate:                   o << "SleEliminate";                   break;
  case XorOnes:                        o << "XorOnes";                        break;
  case XorZero:                        o << "XorZero";                        break;
  case MultPow2:                       o << "MultPow2";                       break;
  case MultSlice:                      o << "MultSlice";                      break;
  case ExtractMultLeadingBit:          o << "ExtractMultLeadingBit";          break;
  case NegIdemp:                       o << "NegIdemp";                       break;
  case UdivPow2:                       o << "UdivPow2";                       break;
  case UdivZero:                       o << "UdivZero";                       break;
  case UdivOne:                        o << "UdivOne";                        break;
  case UremPow2:                       o << "UremPow2";                       break;
  case UremOne:                        o << "UremOne";                        break;
  case UremSelf:                       o << "UremSelf";                       break;
  case ShiftZero:                      o << "ShiftZero";                      break;
  case UgtUrem:                        o << "UgtUrem";                        break;
  case SubEliminate:                   o << "SubEliminate";                   break;
  case XnorEliminate:                  o << "XnorEliminate";                  break;
  case UaddoEliminate:                 o << "UaddoEliminate";                 break;
  case SaddoEliminate:                 o << "SaddoEliminate";                 break;
  case UmuloEliminate:                 o << "UmuloEliminate";                 break;
  case SmuloEliminate:                 o << "SmuloEliminate";                 break;
  case UsuboEliminate:                 o << "UsuboEliminate";                 break;
  case SsuboEliminate:                 o << "SsuboEliminate";                 break;
  case NotIdemp:                       o << "NotIdemp";                       break;
  case UleSelf:                        o << "UleSelf";                        break;
  case FlattenAssocCommut:             o << "FlattenAssocCommut";             break;
  case FlattenAssocCommutNoDuplicates: o << "FlattenAssocCommutNoDuplicates"; break;
  case AddCombineLikeTerms:            o << "AddCombineLikeTerms";            break;
  case MultSimplify:                   o << "MultSimplify";                   break;
  case MultDistribConst:               o << "MultDistribConst";               break;
  case SolveEq:                        o << "SolveEq";                        break;
  case BitwiseEq:                      o << "BitwiseEq";                      break;
  case NegMult:                        o << "NegMult";                        break;
  case NegSub:                         o << "NegSub";                         break;
  case AndSimplify:                    o << "AndSimplify";                    break;
  case OrSimplify:                     o << "OrSimplify";                     break;
  case XorSimplify:                    o << "XorSimplify";                    break;
  case NegAdd:                         o << "NegAdd";                         break;
  case UltOne:                         o << "UltOne";                         break;
  case UltOnes:                        o << "UltOnes";                        break;
  case MergeSignExtend:                o << "MergeSignExtend";                break;
  case SignExtendEqConst:              o << "SignExtendEqConst";              break;
  case ZeroExtendEqConst:              o << "ZeroExtendEqConst";              break;
  case SignExtendUltConst:             o << "SignExtendUltConst";             break;
  case ZeroExtendUltConst:             o << "ZeroExtendUltConst";             break;
  case IneqElimConversion:             o << "IneqElimConversion";             break;
  case UleEliminate:                   o << "UleEliminate";                   break;
  case BitwiseSlicing:                 o << "BitwiseSlicing";                 break;
  case ExtractSignExtend:              o << "ExtractSignExtend";              break;
  case MultDistrib:                    o << "MultDistrib";                    break;
  case UltAddOne:                      o << "UltAddOne";                      break;
  case ConcatToMult:                   o << "ConcatToMult";                   break;
  case MultSltMult:                    o << "MultSltMult";                    break;
  case BitConst:                       o << "BitConst";                       break;
  default:
    Unreachable();
  }
  return o;
  // clang-format on
};

template <RewriteRuleId rule>
class RewriteRule
{

  /** Actually apply the rewrite rule */
  static inline Node apply(TNode node) {
    Unreachable();
    SuppressWrongNoReturnWarning;
  }

public:

  RewriteRule() = default;

  ~RewriteRule() = default;

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

// clang-format off
/** Have to list all the rewrite rules to get the statistics out */
struct AllRewriteRules
{
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
  RewriteRule<EvalAdd>                        rule32;
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
  RewriteRule<XorOnes>                        rule83;
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
  RewriteRule<AddCombineLikeTerms>            rule105;
  RewriteRule<MultSimplify>                   rule106;
  RewriteRule<MultDistribConst>               rule107;
  RewriteRule<AndSimplify>                    rule108;
  RewriteRule<OrSimplify>                     rule109;
  RewriteRule<NegAdd>                         rule110;
  RewriteRule<SolveEq>                        rule112;
  RewriteRule<BitwiseEq>                      rule113;
  RewriteRule<UltOne>                         rule114;
  RewriteRule<MultDistrib>                    rule118;
  RewriteRule<UltAddOne>                      rule119;
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
  RewriteRule<NegEliminate>                   rule140;
  RewriteRule<OrEliminate>                    rule141;
  RewriteRule<XorEliminate>                   rule142;
  RewriteRule<SdivEliminate>                  rule143;
  RewriteRule<SremEliminate>                  rule144;
  RewriteRule<SmodEliminate>                  rule145;
  RewriteRule<UgtUrem>                        rule146;
  RewriteRule<UltOnes>                        rule147;
  RewriteRule<UaddoEliminate>                 rule148;
  RewriteRule<SaddoEliminate>                 rule149;
  RewriteRule<UmuloEliminate>                 rule150;
  RewriteRule<SmuloEliminate>                 rule151;
  RewriteRule<UsuboEliminate>                 rule152;
  RewriteRule<SsuboEliminate>                 rule153;
};
// clang-format on

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

template <Kind Kind, RewriteRuleId Rule>
struct ApplyRuleToChildren
{
  static Node apply(TNode node)
  {
    if (node.getKind() != Kind)
    {
      return RewriteRule<Rule>::template run<true>(node);
    }
    NodeBuilder result(node.getNodeManager(), Kind);
    for (unsigned i = 0, end = node.getNumChildren(); i < end; ++i)
    {
      result << RewriteRule<Rule>::template run<true>(node[i]);
    }
    return result;
  }

  static bool applies(TNode node)
  {
    if (node.getKind() == Kind) return true;
    return RewriteRule<Rule>::applies(node);
  }

  template <bool checkApplies>
  static Node run(TNode node)
  {
    if (!checkApplies || applies(node))
    {
      return apply(node);
    }
    else
    {
      return node;
    }
  }
};

template <typename... Rules>
struct LinearRewriteStrategy;

template <typename Rule, typename... Rest>
struct LinearRewriteStrategy<Rule, Rest...>
{
  static Node apply(TNode node)
  {
    Node current = node;
    if (Rule::applies(current)) current = Rule::template run<false>(current);
    return LinearRewriteStrategy<Rest...>::apply(current);
  }
};

template <>
struct LinearRewriteStrategy<>
{
  static Node apply(TNode node) { return node; }
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
#endif

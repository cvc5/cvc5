/*********************                                                        */
/*! \file theory_bv_rewrite_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Dejan Jovanovic, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include <sstream>

#include "context/context.h"
#include "printer/printer.h"
#include "smt/dump.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory.h"
#include "util/statistics_registry.h"

namespace CVC4 {
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
  SltEliminate,
  SleEliminate,
  UleEliminate,
  CompEliminate,
  RepeatEliminate,
  RotateLeftEliminate,
  RotateRightEliminate,
  NandEliminate,
  NorEliminate,
  XnorEliminate,
  SdivEliminate,
  SdivEliminateFewerBitwiseOps,
  UdivEliminate,
  SmodEliminate,
  SmodEliminateFewerBitwiseOps,
  SremEliminate,
  SremEliminateFewerBitwiseOps,
  ZeroExtendEliminate,
  SignExtendEliminate,
  BVToNatEliminate,
  IntToBVEliminate,

  /// ground term evaluation
  EvalEquals,
  EvalConcat,
  EvalAnd,
  EvalOr,
  EvalXor,
  EvalNot,
  EvalMult,
  EvalPlus,
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
  BitwiseIdemp,
  AndZero,
  AndOne,
  AndOrXorConcatPullUp,
  NegEliminate,
  OrEliminate,
  XorEliminate,
  OrZero,
  OrOne,
  XorDuplicate,
  XorOne,
  XorZero,
  BitwiseNotAnd,
  BitwiseNotOr,
  XorNot,
  NotIdemp,
  LtSelf,
  LteSelf,
  UltZero,
  UltSelf,
  UleZero,
  UleSelf,
  ZeroUle,
  UleMax,
  NotUlt,
  NotUle,
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
  SltZero,
  ZeroUlt,
  MergeSignExtend,
  SignExtendEqConst,
  ZeroExtendEqConst,
  SignExtendUltConst,
  ZeroExtendUltConst,

  /// normalization rules
  ExtractBitwise,
  ExtractNot,
  ExtractArith,
  ExtractArith2,
  ExtractSignExtend,
  DoubleNeg,
  NegMult,
  NegSub,
  NegPlus,
  NotConcat,
  NotAnd,  // not sure why this would help (not done)
  NotOr,   // not sure why this would help (not done)
  NotXor,  // not sure why this would help (not done)
  FlattenAssocCommut,
  FlattenAssocCommutNoDuplicates,
  PlusCombineLikeTerms,
  MultSimplify,
  MultDistribConst,
  MultDistrib,
  SolveEq,
  BitwiseEq,
  AndSimplify,
  OrSimplify,
  XorSimplify,
  BitwiseSlicing,
  NormalizeEqPlusNeg,
  // rules to simplify bitblasting
  BBPlusNeg,
  UltPlusOne,
  ConcatToMult,
  IsPowerOfTwo,
  MultSltMult,
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
  case BVToNatEliminate:    out << "BVToNatEliminate";    return out;
  case IntToBVEliminate:    out << "IntToBVEliminate";    return out;
  case NandEliminate:       out << "NandEliminate";       return out;
  case NorEliminate :       out << "NorEliminate";        return out;
  case SdivEliminate :      out << "SdivEliminate";       return out;
  case SdivEliminateFewerBitwiseOps:
    out << "SdivEliminateFewerBitwiseOps";
    return out;
  case SremEliminate :      out << "SremEliminate";       return out;
  case SremEliminateFewerBitwiseOps:
    out << "SremEliminateFewerBitwiseOps";
    return out;
  case SmodEliminate :      out << "SmodEliminate";       return out;
  case SmodEliminateFewerBitwiseOps:
    out << "SmodEliminateFewerBitwiseOps";
    return out;
  case ZeroExtendEliminate :out << "ZeroExtendEliminate"; return out;
  case EvalEquals :         out << "EvalEquals";          return out;
  case EvalConcat :         out << "EvalConcat";          return out;
  case EvalAnd :            out << "EvalAnd";             return out;
  case EvalOr :             out << "EvalOr";              return out;
  case EvalXor :            out << "EvalXor";             return out;
  case EvalNot :            out << "EvalNot";             return out;
  case EvalMult :           out << "EvalMult";            return out;
  case EvalPlus :           out << "EvalPlus";            return out;
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
  case ExtractBitwise :     out << "ExtractBitwise";      return out;
  case ExtractNot :         out << "ExtractNot";          return out;
  case ExtractArith :       out << "ExtractArith";        return out;
  case ExtractArith2 :      out << "ExtractArith2";       return out;
  case DoubleNeg :          out << "DoubleNeg";           return out;
  case NotConcat :          out << "NotConcat";           return out;
  case NotAnd :             out << "NotAnd";              return out;
  case NotOr :              out << "NotOr";               return out;
  case NotXor :             out << "NotXor";              return out;
  case BitwiseIdemp :       out << "BitwiseIdemp";        return out;
  case XorDuplicate :       out << "XorDuplicate";        return out;
  case BitwiseNotAnd :      out << "BitwiseNotAnd";       return out;
  case BitwiseNotOr :       out << "BitwiseNotOr";        return out;
  case XorNot :             out << "XorNot";              return out;
  case LtSelf :             out << "LtSelf";              return out;
  case LteSelf :            out << "LteSelf";             return out;
  case UltZero :            out << "UltZero";             return out;
  case UleZero :            out << "UleZero";             return out;
  case ZeroUle :            out << "ZeroUle";             return out;
  case NotUlt :             out << "NotUlt";              return out;
  case NotUle :             out << "NotUle";              return out;
  case UleMax :             out << "UleMax";              return out;
  case SltEliminate :       out << "SltEliminate";        return out;
  case SleEliminate :       out << "SleEliminate";        return out;
  case AndZero :       out << "AndZero";        return out;
  case AndOne :       out << "AndOne";        return out;
  case OrZero :       out << "OrZero";        return out;
  case OrOne :       out << "OrOne";        return out;
  case XorOne :       out << "XorOne";        return out;
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
  case CompEliminate :            out << "CompEliminate";             return out;
  case XnorEliminate :            out << "XnorEliminate";             return out;
  case SignExtendEliminate :            out << "SignExtendEliminate";             return out;
  case NotIdemp :                  out << "NotIdemp"; return out;
  case UleSelf:                    out << "UleSelf"; return out; 
  case FlattenAssocCommut:     out << "FlattenAssocCommut"; return out;
  case FlattenAssocCommutNoDuplicates:     out << "FlattenAssocCommutNoDuplicates"; return out; 
  case PlusCombineLikeTerms: out << "PlusCombineLikeTerms"; return out;
  case MultSimplify: out << "MultSimplify"; return out;
  case MultDistribConst: out << "MultDistribConst"; return out;
  case SolveEq : out << "SolveEq"; return out;
  case BitwiseEq : out << "BitwiseEq"; return out;
  case NegMult : out << "NegMult"; return out;
  case NegSub : out << "NegSub"; return out;
  case AndSimplify : out << "AndSimplify"; return out;
  case OrSimplify : out << "OrSimplify"; return out;
  case XorSimplify : out << "XorSimplify"; return out;
  case NegPlus : out << "NegPlus"; return out;
  case BBPlusNeg : out << "BBPlusNeg"; return out;
  case UltOne : out << "UltOne"; return out;
  case SltZero : out << "SltZero"; return out;
  case ZeroUlt : out << "ZeroUlt"; return out;
  case MergeSignExtend : out << "MergeSignExtend"; return out;
  case SignExtendEqConst: out << "SignExtendEqConst"; return out;
  case ZeroExtendEqConst: out << "ZeroExtendEqConst"; return out;
  case SignExtendUltConst: out << "SignExtendUltConst"; return out;
  case ZeroExtendUltConst: out << "ZeroExtendUltConst"; return out;
    
  case UleEliminate : out << "UleEliminate"; return out;
  case BitwiseSlicing : out << "BitwiseSlicing"; return out;
  case ExtractSignExtend : out << "ExtractSignExtend"; return out;
  case MultDistrib: out << "MultDistrib"; return out;
  case UltPlusOne: out << "UltPlusOne"; return out;
  case ConcatToMult: out << "ConcatToMult"; return out;
  case IsPowerOfTwo: out << "IsPowerOfTwo"; return out;
  case MultSltMult: out << "MultSltMult"; return out;
  case NormalizeEqPlusNeg: out << "NormalizeEqPlusNeg"; return out;
  default:
    Unreachable();
  }
};

template <RewriteRuleId rule>
class RewriteRule {

  // class RuleStatistics {

  //   /** The name of the rule prefixed with the prefix */
  //   static std::string getStatName(const char* prefix) {
  //     std::stringstream statName;
  //     statName << prefix << rule;
  //     return statName.str();
  //   }

  // public:

  //   /** Number of applications of this rule */
  //   IntStat d_ruleApplications;

  //   /** Constructor */
  //   RuleStatistics()
  //   : d_ruleApplications(getStatName("theory::bv::RewriteRules::count"), 0) {
  //     currentStatisticsRegistry()->registerStat(&d_ruleApplications);
  //   }

  //   /** Destructor */
  //   ~RuleStatistics() {
  //     StatisticsRegistry::unregisterStat(&d_ruleApplications);
  //   }
  // };

  // /* Statistics about the rule */
  // // NOTE: Cannot have static fields like this, or else you can't have
  // // two SmtEngines in the process (the second-to-be-destroyed will
  // // have a dangling pointer and segfault).  If this statistic is needed,
  // // fix the rewriter by making it an instance per-SmtEngine (instead of
  // // static).
  // static RuleStatistics* s_statistics;

  /** Actually apply the rewrite rule */
  static inline Node apply(TNode node) {
    Unreachable();
    SuppressWrongNoReturnWarning;
  }

public:

  RewriteRule() {
    
    // if (s_statistics == NULL) {
    //   s_statistics = new RuleStatistics();
    // }
    
  }

  ~RewriteRule() {
    
    // delete s_statistics;
    // s_statistics = NULL;
    
  }

  static inline bool applies(TNode node)
  {
    Unreachable();
    SuppressWrongNoReturnWarning;
  }

  template<bool checkApplies>
  static inline Node run(TNode node) {
    if (!checkApplies || applies(node)) {
      Debug("theory::bv::rewrite") << "RewriteRule<" << rule << ">(" << node << ")" << std::endl;
      Assert(checkApplies || applies(node));
      //++ s_statistics->d_ruleApplications;
      Node result = apply(node);
      if (result != node) {
        if(Dump.isOn("bv-rewrites")) {
          std::ostringstream os;
          os << "RewriteRule <"<<rule<<">; expect unsat";

          Node condition = node.eqNode(result).notNode();

          const Printer& printer =
              smt::currentSmtEngine()->getOutputManager().getPrinter();
          std::ostream& out =
              smt::currentSmtEngine()->getOutputManager().getDumpOut();

          printer.toStreamCmdComment(out, os.str());
          printer.toStreamCmdCheckSat(out, condition);
        }
      }
      Debug("theory::bv::rewrite") << "RewriteRule<" << rule << ">(" << node << ") => " << result << std::endl;
      return result;
    } else {
      return node;
    }
  }
};


 // template<RewriteRuleId rule>
 //   typename RewriteRule<rule>::RuleStatistics* RewriteRule<rule>::s_statistics = NULL;


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
  RewriteRule<EvalPlus>                       rule32;
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
  RewriteRule<ExtractBitwise>                 rule53;
  RewriteRule<ExtractNot>                     rule54;
  RewriteRule<ExtractArith>                   rule55;
  RewriteRule<DoubleNeg>                      rule56;
  RewriteRule<NotConcat>                      rule57;
  RewriteRule<NotAnd>                         rule58;
  RewriteRule<NotOr>                          rule59;
  RewriteRule<NotXor>                         rule60;
  RewriteRule<BitwiseIdemp>                   rule61;
  RewriteRule<XorDuplicate>                   rule62;
  RewriteRule<BitwiseNotAnd>                  rule63;
  RewriteRule<BitwiseNotOr>                   rule64;
  RewriteRule<XorNot>                         rule65;
  RewriteRule<LtSelf>                         rule66;
  RewriteRule<LtSelf>                         rule67;
  RewriteRule<UltZero>                        rule68;
  RewriteRule<UleZero>                        rule69;
  RewriteRule<ZeroUle>                        rule70;
  RewriteRule<NotUlt>                         rule71;
  RewriteRule<NotUle>                         rule72;
  RewriteRule<ZeroExtendEliminate>            rule73;
  RewriteRule<UleMax>                         rule74;
  RewriteRule<LteSelf>                        rule75;
  RewriteRule<SltEliminate>                   rule76;
  RewriteRule<SleEliminate>                   rule77;
  RewriteRule<AndZero>                        rule78;
  RewriteRule<AndOne>                         rule79;
  RewriteRule<OrZero>                         rule80;
  RewriteRule<OrOne>                          rule81;
  RewriteRule<SubEliminate>                   rule82;
  RewriteRule<XorOne>                         rule83;
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
  RewriteRule<CompEliminate>                  rule99;
  RewriteRule<XnorEliminate>                  rule100;
  RewriteRule<SignExtendEliminate>            rule101;
  RewriteRule<NotIdemp>                       rule102;
  RewriteRule<UleSelf>                        rule103;
  RewriteRule<FlattenAssocCommut>             rule104;
  RewriteRule<PlusCombineLikeTerms>           rule105;
  RewriteRule<MultSimplify>                   rule106;
  RewriteRule<MultDistribConst>               rule107;
  RewriteRule<AndSimplify>                    rule108;
  RewriteRule<OrSimplify>                     rule109;
  RewriteRule<NegPlus>                        rule110;
  RewriteRule<BBPlusNeg>                      rule111;
  RewriteRule<SolveEq>                        rule112;
  RewriteRule<BitwiseEq>                      rule113;
  RewriteRule<UltOne>                         rule114;
  RewriteRule<SltZero>                        rule115;
  RewriteRule<BVToNatEliminate>               rule116;
  RewriteRule<IntToBVEliminate>               rule117;
  RewriteRule<MultDistrib>                    rule118;
  RewriteRule<UltPlusOne>                     rule119;
  RewriteRule<ConcatToMult>                   rule120;
  RewriteRule<IsPowerOfTwo>                   rule121;
  RewriteRule<RedorEliminate>                 rule122;
  RewriteRule<RedandEliminate>                rule123;
  RewriteRule<SignExtendEqConst>              rule124;
  RewriteRule<ZeroExtendEqConst>              rule125;
  RewriteRule<SignExtendUltConst>             rule126;
  RewriteRule<ZeroExtendUltConst>             rule127;
  RewriteRule<MultSltMult>                    rule128;
  RewriteRule<NormalizeEqPlusNeg>             rule129;
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
};

template<> inline
bool RewriteRule<EmptyRule>::applies(TNode node) {
  return false;
}

template<> inline
Node RewriteRule<EmptyRule>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EmptyRule> for " << node.getKind() <<"\n"; 
  Unreachable();
  return node;
}

template<Kind kind, RewriteRuleId rule>
struct ApplyRuleToChildren {

  static Node apply(TNode node) {
    if (node.getKind() != kind) {
      return RewriteRule<rule>::template run<true>(node);
    }
    NodeBuilder<> result(kind);
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
struct FixpointRewriteStrategy {
  static Node apply(TNode node) {
    Node previous = node; 
    Node current = node;
    do {
      previous = current;
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
    } while (previous != current);
    
    return current;
  }
};


} // End namespace bv
} // End namespace theory
} // End namespace CVC4

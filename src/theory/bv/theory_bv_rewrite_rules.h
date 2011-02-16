/*********************                                                        */
/*! \file theory_bv_rewrite_rules.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#pragma once 

#include "cvc4_private.h"
#include "theory/theory.h"
#include "context/context.h"
#include "util/stats.h"
#include <sstream>

namespace CVC4 {
namespace theory {
namespace bv {

enum RewriteRuleId {
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
};

inline std::ostream& operator << (std::ostream& out, RewriteRuleId ruleId) {
  switch (ruleId) {
  case EmptyRule:           out << "EmptyRule";           return out;
  case ConcatFlatten:       out << "ConcatFlatten";       return out;
  case ConcatExtractMerge:  out << "ConcatExtractMerge";  return out;
  case ConcatConstantMerge: out << "ConcatConstantMerge"; return out;
  case ExtractExtract:      out << "ExtractExtract";      return out;
  case ExtractWhole:        out << "ExtractWhole";        return out;
  case ExtractConcat:       out << "ExtractConcat";       return out;
  case ExtractConstant:     out << "ExtractConstant";     return out;
  case FailEq:              out << "FailEq";              return out;
  case SimplifyEq:          out << "SimplifyEq";          return out;
  case ReflexivityEq:       out << "ReflexivityEq";       return out;
  default:
    Unreachable();
  }
};

template <RewriteRuleId rule>
class RewriteRule {

  class RuleStatistics {

    /** The name of the rule prefixed with the prefix */
    static std::string getStatName(const char* prefix) {
      std::stringstream statName;
      statName << prefix << rule;
      return statName.str();
    }

  public:

    /** Number of applications of this rule */
    IntStat d_ruleApplications;

    /** Constructor */
    RuleStatistics()
    : d_ruleApplications(getStatName("theory::bv::count"), 0) {
      StatisticsRegistry::registerStat(&d_ruleApplications);
    }

    /** Destructor */
    ~RuleStatistics() {
      StatisticsRegistry::unregisterStat(&d_ruleApplications);
    }
  };

  /** Statistics about the rule */
  static RuleStatistics* s_statictics;

  /** Actually apply the rewrite rule */
  static inline Node apply(Node node) {
    Unreachable();
  }

public:

  RewriteRule() {
    if (s_statictics == NULL) {
      s_statictics = new RuleStatistics();
    }
  }

  ~RewriteRule() {
    delete s_statictics;
    s_statictics = NULL;
  }

  static inline bool applies(Node node) {
    Unreachable();
  }

  template<bool checkApplies>
  static inline Node run(Node node) {
    if (!checkApplies || applies(node)) {
      Debug("theory::bv::rewrite") << "RewriteRule<" << rule << ">(" << node << ")" << std::endl;
      Assert(checkApplies || applies(node));
      ++ s_statictics->d_ruleApplications;
      Node result = apply(node);
      Debug("theory::bv::rewrite") << "RewriteRule<" << rule << ">(" << node << ") => " << result << std::endl;
      return result;
    } else {
      return node;
    }
  }
};

template<RewriteRuleId rule>
typename RewriteRule<rule>::RuleStatistics* RewriteRule<rule>::s_statictics = NULL;

/** Have to list all the rewrite rules to get the statistics out */
struct AllRewriteRules {
  RewriteRule<EmptyRule>            rule00;
  RewriteRule<ConcatFlatten>        rule01;
  RewriteRule<ConcatExtractMerge>   rule02;
  RewriteRule<ConcatConstantMerge>  rule03;
  RewriteRule<ExtractExtract>       rule04;
  RewriteRule<ExtractWhole>         rule05;
  RewriteRule<ExtractConcat>        rule06;
  RewriteRule<ExtractConstant>      rule07;
  RewriteRule<FailEq>               rule08;
  RewriteRule<SimplifyEq>           rule09;
  RewriteRule<ReflexivityEq>        rule10;
};

template<>
bool RewriteRule<EmptyRule>::applies(Node node) {
  return false;
}

template<>
Node RewriteRule<EmptyRule>::apply(Node node) {
  Unreachable();
  return node;
}

template<Kind kind, RewriteRuleId rule>
struct ApplyRuleToChildren {

  static Node apply(Node node) {
    if (node.getKind() != kind) {
      return RewriteRule<rule>::template run<true>(node);
    }
    NodeBuilder<> result(kind);
    for (unsigned i = 0, end = node.getNumChildren(); i < end; ++ i) {
      result << RewriteRule<rule>::template run<true>(node[i]);
    }
    return result;
  }

  static bool applies(Node node) {
    if (node.getKind() == kind) return true;
    return RewriteRule<rule>::applies(node);
  }

  template <bool checkApplies>
  static Node run(Node node) {
    if (!checkApplies || applies(node)) {
      return apply(node);
    } else {
      return node;
    }
  }
};

template <
  typename R1,
  typename R2,
  typename R3 = RewriteRule<EmptyRule>,
  typename R4 = RewriteRule<EmptyRule>,
  typename R5 = RewriteRule<EmptyRule>,
  typename R6 = RewriteRule<EmptyRule>,
  typename R7 = RewriteRule<EmptyRule>,
  typename R8 = RewriteRule<EmptyRule>
  >
struct LinearRewriteStrategy {
  static Node apply(Node node) {
    Node current = node;
    if (R1::applies(current)) current = R1::template run<false>(current);
    if (R2::applies(current)) current = R2::template run<false>(current);
    if (R3::applies(current)) current = R3::template run<false>(current);
    if (R4::applies(current)) current = R4::template run<false>(current);
    if (R5::applies(current)) current = R5::template run<false>(current);
    if (R6::applies(current)) current = R6::template run<false>(current);
    if (R7::applies(current)) current = R7::template run<false>(current);
    if (R8::applies(current)) current = R8::template run<false>(current);
    return current;
  }
};

} // End namespace bv
} // End namespace theory
} // End namespace CVC4

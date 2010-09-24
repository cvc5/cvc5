#pragma once 

#include "cvc4_private.h"
#include "theory/theory.h"
#include "context/context.h"

namespace CVC4 {
namespace theory {
namespace bv {

struct CoreRewriteRules {

  struct EmptyRule {
    static inline Node apply(Node node) { return node; }
    static inline bool applies(Node node) { return false; }
  };

  struct ConcatFlatten {
    static Node apply(Node node);
    static bool applies(Node node);
  };

  struct ConcatExtractMerge {
    static Node apply(Node node);
    static bool applies(Node node);
  };

  struct ConcatConstantMerge {
    static Node apply(Node node);
    static bool applies(Node node);
  };

  struct ExtractExtract {
    static Node apply(Node node);
    static bool applies(Node node);
  };

  struct ExtractWhole {
    static Node apply(Node node);
    static bool applies(Node node);
  };

  struct ExtractConcat {
    static Node apply(Node node);
    static bool applies(Node node);
  };

  struct ExtractConstant {
    static Node apply(Node node);
    static bool applies(Node node);
  };

  struct FailEq {
    static Node apply(Node node);
    static bool applies(Node node);
  };

  struct SimplifyEq {
    static Node apply(Node node);
    static bool applies(Node node);
  };

};

template<Kind kind, typename Rule>
struct ApplyRuleToChildren {

  static Node apply(Node node) {
    if (node.getKind() != kind) {
      if (Rule::applies(node)) return Rule::apply(node);
      else return node;
    }
    NodeBuilder<> result(kind);
    for (unsigned i = 0, end = node.getNumChildren(); i < end; ++ i) {
      if (Rule::applies(node[i])) result << Rule::apply(node[i]);
      else result << node[i];
    }
    return result;
  }

  static bool applies(Node node) {
    if (node.getKind() == kind) return true;
    return Rule::applies(node);
  }

};


template <
  typename R1,
  typename R2,
  typename R3 = CoreRewriteRules::EmptyRule,
  typename R4 = CoreRewriteRules::EmptyRule,
  typename R5 = CoreRewriteRules::EmptyRule,
  typename R6 = CoreRewriteRules::EmptyRule,
  typename R7 = CoreRewriteRules::EmptyRule
  >
struct LinearRewriteStrategy {
  static Node apply(Node node) {
    Node current = node;
    if (R1::applies(current)) current = R1::apply(current);
    if (R2::applies(current)) current = R2::apply(current);
    if (R3::applies(current)) current = R3::apply(current);
    if (R4::applies(current)) current = R4::apply(current);
    if (R5::applies(current)) current = R5::apply(current);
    if (R6::applies(current)) current = R6::apply(current);
    if (R7::applies(current)) current = R7::apply(current);
    return current;
  }
};

} // End namespace bv
} // End namespace theory
} // End namespace CVC4

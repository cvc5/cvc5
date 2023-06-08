/******************************************************************************
 * Top contributors (to current version):
 *   Dejan Jovanovic, Liana Hadarean, Clark Barrett
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Core rewrite rules of the BV theory.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__THEORY_BV_REWRITE_RULES_CORE_H
#define CVC5__THEORY__BV__THEORY_BV_REWRITE_RULES_CORE_H

#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ConcatFlatten>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_CONCAT);
}

template<> inline
Node RewriteRule<ConcatFlatten>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<ConcatFlatten>(" << node << ")" << std::endl;
  NodeBuilder result(kind::BITVECTOR_CONCAT);
  std::vector<Node> processing_stack;
  processing_stack.push_back(node);
  while (!processing_stack.empty()) {
    Node current = processing_stack.back();
    processing_stack.pop_back();
    if (current.getKind() == kind::BITVECTOR_CONCAT) {
      for (int i = current.getNumChildren() - 1; i >= 0; i--)
        processing_stack.push_back(current[i]);
    } else {
      result << current;
    }
  }
  Node resultNode = result;
  Trace("bv-rewrite") << "RewriteRule<ConcatFlatten>(" << resultNode << ")" << std::endl;
  return resultNode;
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ConcatExtractMerge>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_CONCAT);
}

template<> inline
Node RewriteRule<ConcatExtractMerge>::apply(TNode node) {

  Trace("bv-rewrite") << "RewriteRule<ConcatExtractMerge>(" << node << ")" << std::endl;

  std::vector<Node> mergedExtracts;

  Node current = node[0];
  bool mergeStarted = false;
  unsigned currentHigh = 0;
  unsigned currentLow  = 0;

  for(size_t i = 1, end = node.getNumChildren(); i < end; ++ i) {
    // The next candidate for merging
    Node next = node[i];
    // If the current is not an extract we just go to the next
    if (current.getKind() != kind::BITVECTOR_EXTRACT) {
      mergedExtracts.push_back(current);
      current = next;
      continue;
    }
    // If it is an extract and the first one, get the extract parameters
    else if (!mergeStarted) {
      currentHigh = utils::getExtractHigh(current);
      currentLow = utils::getExtractLow(current);
    }

    // If the next one can be merged, try to merge
    bool merged = false;
    if (next.getKind() == kind::BITVECTOR_EXTRACT && current[0] == next[0]) {
      // x[i : j] @ x[j - 1 : k] -> c x[i : k]
      unsigned nextHigh = utils::getExtractHigh(next);
      unsigned nextLow  = utils::getExtractLow(next);
      if(nextHigh + 1 == currentLow) {
        currentLow = nextLow;
        mergeStarted = true;
        merged = true;
      }
    }
    // If we haven't merged anything, add the previous merge and continue with the next
    if (!merged) {
      if (!mergeStarted) mergedExtracts.push_back(current);
      else mergedExtracts.push_back(utils::mkExtract(current[0], currentHigh, currentLow));
      current = next;
      mergeStarted = false;
    }
  }

  // Add the last child
  if (!mergeStarted) mergedExtracts.push_back(current);
  else mergedExtracts.push_back(utils::mkExtract(current[0], currentHigh, currentLow));

  // Return the result
  return utils::mkConcat(mergedExtracts);
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ConcatConstantMerge>::applies(TNode node) {
  return node.getKind() == kind::BITVECTOR_CONCAT;
}

template<> inline
Node RewriteRule<ConcatConstantMerge>::apply(TNode node) {

  Trace("bv-rewrite") << "RewriteRule<ConcatConstantMerge>(" << node << ")" << std::endl;

  std::vector<Node> mergedConstants;
  for (unsigned i = 0, end = node.getNumChildren(); i < end;) {
    if (node[i].getKind() != kind::CONST_BITVECTOR) {
      // If not a constant, just add it
      mergedConstants.push_back(node[i]);
      ++i;
    } else {
      // Find the longest sequence of constants
      unsigned j = i + 1;
      while (j < end) {
        if (node[j].getKind() != kind::CONST_BITVECTOR) {
          break;
        } else {
          ++ j;
        }
      }
      // Append all the constants
      BitVector current = node[i].getConst<BitVector>();
      for (unsigned k = i + 1; k < j; ++ k) {
        current = current.concat(node[k].getConst<BitVector>());
      }
      // Add the new merged constant
      mergedConstants.push_back(utils::mkConst(current));
      i = j;
    }
  }

  Trace("bv-rewrite") << "RewriteRule<ConcatConstantMerge>(" << node << ") => " << utils::mkConcat(mergedConstants) << std::endl;

  return utils::mkConcat(mergedConstants);
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ExtractWhole>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  unsigned length = utils::getSize(node[0]);
  unsigned extractHigh = utils::getExtractHigh(node);
  if (extractHigh != length - 1) return false;
  unsigned extractLow  = utils::getExtractLow(node);
  if (extractLow != 0) return false;
  return true;
}

template<> inline
Node RewriteRule<ExtractWhole>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<ExtractWhole>(" << node << ")" << std::endl;
  return node[0];
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ExtractConstant>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  if (node[0].getKind() != kind::CONST_BITVECTOR) return false;
  return true;
}

template<> inline
Node RewriteRule<ExtractConstant>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<ExtractConstant>(" << node << ")" << std::endl;
  Node child = node[0];
  BitVector childValue = child.getConst<BitVector>();
  return utils::mkConst(childValue.extract(utils::getExtractHigh(node), utils::getExtractLow(node)));
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ExtractConcat>::applies(TNode node) {
  //Trace("bv-rewrite") << "RewriteRule<ExtractConcat>(" << node << ")" << std::endl;
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  if (node[0].getKind() != kind::BITVECTOR_CONCAT) return false;
  return true;
}

template<> inline
Node RewriteRule<ExtractConcat>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<ExtractConcat>(" << node << ")" << std::endl;
  int extract_high = utils::getExtractHigh(node);
  int extract_low = utils::getExtractLow(node);

  std::vector<Node> resultChildren;

  Node concat = node[0];
  for (int i = concat.getNumChildren() - 1; i >= 0 && extract_high >= 0; i--) {
    Node concatChild = concat[i];
    int concatChildSize = utils::getSize(concatChild);
    if (extract_low < concatChildSize) {
      int extract_start = extract_low < 0 ? 0 : extract_low;
      int extract_end = extract_high < concatChildSize ? extract_high : concatChildSize - 1;
      resultChildren.push_back(utils::mkExtract(concatChild, extract_end, extract_start));
    }
    extract_low -= concatChildSize;
    extract_high -= concatChildSize;
  }

  std::reverse(resultChildren.begin(), resultChildren.end());

  return utils::mkConcat(resultChildren);
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ExtractExtract>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  if (node[0].getKind() != kind::BITVECTOR_EXTRACT) return false;
  return true;
}

template<> inline
Node RewriteRule<ExtractExtract>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<ExtractExtract>(" << node << ")" << std::endl;

  // x[i:j][k:l] ~>  x[k+j:l+j]
  uint32_t j = 0;
  Node child = node[0];
  do
  {
    j += utils::getExtractLow(child);
    child = child[0];
  } while (child.getKind() == kind::BITVECTOR_EXTRACT);

  uint32_t k = utils::getExtractHigh(node);
  uint32_t l = utils::getExtractLow(node);
  Node result = utils::mkExtract(child, k + j, l + j);
  return result;
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<FailEq>::applies(TNode node) {
  //Trace("bv-rewrite") << "RewriteRule<FailEq>(" << node << ")" << std::endl;
  if (node.getKind() != kind::EQUAL) return false;
  if (node[0].getKind() != kind::CONST_BITVECTOR) return false;
  if (node[1].getKind() != kind::CONST_BITVECTOR) return false;
  return node[0] != node[1];
}

template<> inline
Node RewriteRule<FailEq>::apply(TNode node) {
  return utils::mkFalse();
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<SimplifyEq>::applies(TNode node) {
  if (node.getKind() != kind::EQUAL) return false;
  return node[0] == node[1];
}

template<> inline
Node RewriteRule<SimplifyEq>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<SimplifyEq>(" << node << ")" << std::endl;
  return utils::mkTrue();
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ReflexivityEq>::applies(TNode node) {
  return (node.getKind() == kind::EQUAL && node[0] < node[1]);
}

template<> inline
Node RewriteRule<ReflexivityEq>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<ReflexivityEq>(" << node << ")" << std::endl;
  Node res = node[1].eqNode(node[0]);
  return res;
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
#endif

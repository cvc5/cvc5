/*********************                                                        */
/*! \file theory_bv_rewrite_rules_core.h
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

#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace theory {
namespace bv {

template<>
bool RewriteRule<ConcatFlatten>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_CONCAT);
}

template<>
Node RewriteRule<ConcatFlatten>::apply(Node node) {
  NodeBuilder<> result(kind::BITVECTOR_CONCAT);
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
  return resultNode;
}

template<>
bool RewriteRule<ConcatExtractMerge>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_CONCAT);
}

template<>
Node RewriteRule<ConcatExtractMerge>::apply(Node node) {
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
      //x[i : j] @ x[j − 1 : k] -> c x[i : k]
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

template<>
bool RewriteRule<ConcatConstantMerge>::applies(Node node) {
  return node.getKind() == kind::BITVECTOR_CONCAT;
}

template<>
Node RewriteRule<ConcatConstantMerge>::apply(Node node) {
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
      i = j + 1;
    }
  }

  return utils::mkConcat(mergedConstants);
}

template<>
bool RewriteRule<ExtractWhole>::applies(Node node) {
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  unsigned length = utils::getSize(node[0]);
  unsigned extractHigh = utils::getExtractHigh(node);
  if (extractHigh != length - 1) return false;
  unsigned extractLow  = utils::getExtractLow(node);
  if (extractLow != 0) return false;
  return true;
}

template<>
Node RewriteRule<ExtractWhole>::apply(Node node) {
  return node[0];
}

template<>
bool RewriteRule<ExtractConstant>::applies(Node node) {
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  if (node[0].getKind() != kind::CONST_BITVECTOR) return false;
  return true;
}

template<>
Node RewriteRule<ExtractConstant>::apply(Node node) {
  Node child = node[0];
  BitVector childValue = child.getConst<BitVector>();
  return utils::mkConst(childValue.extract(utils::getExtractHigh(node), utils::getExtractLow(node)));
}

template<>
bool RewriteRule<ExtractConcat>::applies(Node node) {
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  if (node[0].getKind() != kind::BITVECTOR_CONCAT) return false;
  return true;
}

template<>
Node RewriteRule<ExtractConcat>::apply(Node node) {
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

template<>
bool RewriteRule<ExtractExtract>::applies(Node node) {
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  if (node[0].getKind() != kind::BITVECTOR_EXTRACT) return false;
  return true;
}

template<>
Node RewriteRule<ExtractExtract>::apply(Node node) {
  // x[i:j][k:l] ~>  x[k+j:l+j]
  Node child = node[0];
  unsigned k = utils::getExtractHigh(node);
  unsigned l = utils::getExtractLow(node);
  unsigned j = utils::getExtractLow(child);

  Node result = utils::mkExtract(child[0], k + j, l + j);
  return result;
}

template<>
bool RewriteRule<FailEq>::applies(Node node) {
  if (node.getKind() != kind::EQUAL) return false;
  if (node[0].getKind() != kind::CONST_BITVECTOR) return false;
  if (node[1].getKind() != kind::CONST_BITVECTOR) return false;
  return node[0] != node[1];
}

template<>
Node RewriteRule<FailEq>::apply(Node node) {
    return utils::mkFalse();
}

template<>
bool RewriteRule<SimplifyEq>::applies(Node node) {
  if (node.getKind() != kind::EQUAL) return false;
  return node[0] == node[1];
}

template<>
Node RewriteRule<SimplifyEq>::apply(Node node) {
  return utils::mkTrue();
}

template<>
bool RewriteRule<ReflexivityEq>::applies(Node node) {
  return (node.getKind() == kind::EQUAL && node[0] < node[1]);
}

template<>
Node RewriteRule<ReflexivityEq>::apply(Node node) {
  return node[1].eqNode(node[0]);;
}

}
}
}

#include <vector>
#include "expr/node_builder.h"
#include "theory_bv_rewrite_rules.h"
#include "theory_bv_utils.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

bool CoreRewriteRules::ConcatFlatten::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_CONCAT);
}

Node CoreRewriteRules::ConcatFlatten::apply(Node node) {
  Assert(applies(node));

  Debug("bitvector") << "ConcatFlatten(" << node << ")" << endl;

  NodeBuilder<> result(kind::BITVECTOR_CONCAT);
  vector<Node> processing_stack;
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

  Debug("bitvector") << "ConcatFlatten(" << node << ") => " << result << endl;

  return result;
}

bool CoreRewriteRules::ConcatExtractMerge::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_CONCAT);
}

Node CoreRewriteRules::ConcatExtractMerge::apply(Node node) {
  Assert(applies(node));

  Debug("bitvector") << "ConcatExtractMerge(" << node << ")" << endl;

  vector<Node> mergedExtracts;

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
      currentHigh = getExtractHigh(current);
      currentLow = getExtractLow(current);
    }

    // If the next one can be merged, try to merge
    bool merged = false;
    if (next.getKind() == kind::BITVECTOR_EXTRACT && current[0] == next[0]) {
      //x[i : j] @ x[j − 1 : k] -> c x[i : k]
      unsigned nextHigh = getExtractHigh(next);
      unsigned nextLow  = getExtractLow(next);
      if(nextHigh + 1 == currentLow) {
        currentLow = nextLow;
        mergeStarted = true;
        merged = true;
      }
    }
    // If we haven't merged anything, add the previous merge and continue with the next
    if (!merged) {
      if (!mergeStarted) mergedExtracts.push_back(current);
      else mergedExtracts.push_back(mkExtract(current[0], currentHigh, currentLow));
      current = next;
      mergeStarted = false;
    }
  }

  // Add the last child
  if (!mergeStarted) mergedExtracts.push_back(current);
  else mergedExtracts.push_back(mkExtract(current[0], currentHigh, currentLow));

  // Create the result
  Node result = mkConcat(mergedExtracts);

  Debug("bitvector") << "ConcatExtractMerge(" << node << ") =>" << result << endl;

  // Return the result
  return result;
}

bool CoreRewriteRules::ConcatConstantMerge::applies(Node node) {
  return node.getKind() == kind::BITVECTOR_CONCAT;
}

Node CoreRewriteRules::ConcatConstantMerge::apply(Node node) {
  Assert(applies(node));

  Debug("bitvector") << "ConcatConstantMerge(" << node << ")" << endl;

  vector<Node> mergedConstants;
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
      mergedConstants.push_back(mkConst(current));
      i = j + 1;
    }
  }

  Node result = mkConcat(mergedConstants);

  Debug("bitvector") << "ConcatConstantMerge(" << node << ") => " << result << endl;

  return result;
}

bool CoreRewriteRules::ExtractWhole::applies(Node node) {
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  unsigned length = getSize(node[0]);
  unsigned extractHigh = getExtractHigh(node);
  if (extractHigh != length - 1) return false;
  unsigned extractLow  = getExtractLow(node);
  if (extractLow != 0) return false;
  return true;
}

Node CoreRewriteRules::ExtractWhole::apply(Node node) {
  Assert(applies(node));

  Debug("bitvector") << "ExtractWhole(" << node << ")" << endl;
  Debug("bitvector") << "ExtractWhole(" << node << ") => " << node[0] << endl;

  return node[0];
}

bool CoreRewriteRules::ExtractConstant::applies(Node node) {
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  if (node[0].getKind() != kind::CONST_BITVECTOR) return false;
  return true;
}

Node CoreRewriteRules::ExtractConstant::apply(Node node) {
  Assert(applies(node));

  Debug("bitvector") << "ExtractConstant(" << node << ")" << endl;

  Node child = node[0];
  BitVector childValue = child.getConst<BitVector>();

  Node result = mkConst(childValue.extract(getExtractHigh(node), getExtractLow(node)));

  Debug("bitvector") << "ExtractConstant(" << node << ") => " << result << endl;

  return result;
}

bool CoreRewriteRules::ExtractConcat::applies(Node node) {
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  if (node[0].getKind() != kind::BITVECTOR_CONCAT) return false;
  return true;
}

Node CoreRewriteRules::ExtractConcat::apply(Node node) {
  Assert(applies(node));

  Debug("bitvector") << "ExtractConcat(" << node << ")" << endl;

  int extract_high = getExtractHigh(node);
  int extract_low = getExtractLow(node);

  vector<Node> resultChildren;

  Node concat = node[0];
  for (int i = concat.getNumChildren() - 1; i >= 0 && extract_high >= 0; i--) {
    Node concatChild = concat[i];
    int concatChildSize = getSize(concatChild);
    if (extract_low < concatChildSize) {
      int extract_start = extract_low < 0 ? 0 : extract_low;
      int extract_end = extract_high < concatChildSize ? extract_high : concatChildSize - 1;
      resultChildren.push_back(mkExtract(concatChild, extract_end, extract_start));
    }
    extract_low -= concatChildSize;
    extract_high -= concatChildSize;
  }

  std::reverse(resultChildren.begin(), resultChildren.end());

  Node result = mkConcat(resultChildren);

  Debug("bitvector") << "ExtractConcat(" << node << ") => " << result << endl;

  return result;
}

bool CoreRewriteRules::ExtractExtract::applies(Node node) {
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  if (node[0].getKind() != kind::BITVECTOR_EXTRACT) return false;
  return true;
}

Node CoreRewriteRules::ExtractExtract::apply(Node node) {
  Assert(applies(node));

  Debug("bitvector") << "ExtractExtract(" << node << ")" << endl;

  // x[i:j][k:l] ~>  x[k+j:l+j]
  Node child = node[0];
  unsigned k = getExtractHigh(node);
  unsigned l = getExtractLow(node);
  unsigned j = getExtractLow(child);

  Node result = mkExtract(child[0], k + j, l + j);

  Debug("bitvector") << "ExtractExtract(" << node << ") => " << result << endl;

  return result;

}

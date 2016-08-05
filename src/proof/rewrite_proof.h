#include "cvc4_private.h"

#pragma once

#include "expr/node.h"
#include "proof/theory_proof.h"
#include "util/proof.h"

namespace CVC4 {

typedef int rewrite_tag_t;

// Theory independent rewrites
enum SharedRewrites {
  ORIGINAL_OP, // Mirror an original operator
  TRUSTED,
  LAST_SHARED,
};

struct Rewrite {
  // The type of the rewrite
  int d_tag;
  // Node before the rewrite
  Node d_original;
  // Subproofs
  std::vector<Rewrite> d_children;

  Rewrite(const Node original) : d_tag(0), d_original(original) {}
  Rewrite(const rewrite_tag_t tag, const Node original)
      : d_tag(tag), d_original(original) {}

  void print(int tab) const;

  bool isLeaf() const { return d_children.size() == 0; }
};

class RewriteProof {
private:
  std::vector<Rewrite> d_rewrites;

public:
  RewriteProof() {}

  void addRewrite(const Rewrite &rewrite) { d_rewrites.push_back(rewrite); }

  // Apply a rewrite rule to the top node
  void rewriteTopNode(const int tag, std::vector<Rewrite> rewrites);
  void attachSubproofToParent();

  const Rewrite getRewrite() const;
  const Rewrite& getTopRewrite() const { return d_rewrites.back(); };
};

class RewriteProofEngine {
public:
  RewriteProofEngine();
  ~RewriteProofEngine();
};

} /* CVC4 namespace */

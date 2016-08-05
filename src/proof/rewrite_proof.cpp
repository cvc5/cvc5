#include "proof/rewrite_proof.h"

#include "proof_manager.h"
#include "theory/rewriter.h"

namespace CVC4 {

RewriteProofEngine::RewriteProofEngine() {}
RewriteProofEngine::~RewriteProofEngine() {}

void Rewrite::print(int tab) const {
  for (int j = 0; j < tab; j++)
    std::cout << " ";
  std::cout << d_tag << " > " << d_original << " < " << std::endl;

  for (size_t i = 0; i < d_children.size(); i++) {
    d_children[i].print(tab + 1);
    std::cout << std::endl;
  }
}

void RewriteProof::rewriteTopNode(const int tag,
                                  std::vector<Rewrite> rewrites) {
  // TODO: pass rewrite to rewrite functions instead of this.
  Rewrite &topRewrite = d_rewrites.back();
  Rewrite newRewrite(tag, topRewrite.d_original);
  newRewrite.d_children = rewrites;
  newRewrite.d_children.push_back(topRewrite);
  d_rewrites.pop_back();
  d_rewrites.push_back(newRewrite);
}

void RewriteProof::attachSubproofToParent() {
  Rewrite &topRewrite = d_rewrites.back();

  // Simplify proof
  if (topRewrite.d_tag == ORIGINAL_OP) {
    bool allChildrenRefl = true;
    for (size_t i = 0; i < topRewrite.d_children.size(); i++) {
      if (topRewrite.d_children[i].d_tag != ORIGINAL_OP) {
        allChildrenRefl = false;
        break;
      }
    }
    if (allChildrenRefl) {
      topRewrite.d_children.clear();
    }
  }
  d_rewrites[d_rewrites.size() - 2].d_children.push_back(d_rewrites.back());
  d_rewrites.pop_back();
}

const Rewrite RewriteProof::getRewrite() const {
  Assert(d_rewrites.size() == 1);
  return d_rewrites[0];
}

} /* CVC4 namespace */

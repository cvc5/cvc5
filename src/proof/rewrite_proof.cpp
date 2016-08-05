#include "proof/rewrite_proof.h"

#include "proof/rewrite_proof_dispatcher.h"
#include "proof_manager.h"
#include "theory/rewriter.h"

namespace CVC4 {

Rewrite::~Rewrite() {
  for (size_t i = 0; i < d_subproofs.size(); i++) {
    delete d_subproofs[i];
  }
}

void Rewrite::deleteUncachedChildren() {
  for (size_t i = 0; i < d_children.size(); i++) {
    if (d_children[i] != NULL) {
      d_children[i]->deleteUncachedChildren();
      if (!d_children[i]->d_cached_version_used) {
        delete d_children[i];
        d_children[i] = NULL;
      }
    }
  }
}

void Rewrite::print(int tab) const {
  for (int j = 0; j < tab; j++)
    std::cout << " ";
  std::cout << d_tag << " > " << d_original << " < " << std::endl;

  for (size_t i = 0; i < d_children.size(); i++) {
    d_children[i]->print(tab + 1);
    std::cout << std::endl;
  }
}

RewriteProof::~RewriteProof() {
  for (ProofCacheIterator iter = preRewriteCache.begin();
       iter != preRewriteCache.end(); ++iter) {
    if (!iter->second->d_cached_version_used) {
      preRewriteCache[iter->first] = NULL;
    }
  }
  /*
  for (ProofCacheIterator iter = postRewriteCache.begin();
       iter != postRewriteCache.end(); ++iter) {
    if (!iter->second->d_cached_version_used) {
      postRewriteCache[iter->first] = NULL;
    }
  }*/

  for (size_t i = 0; i < d_rewrites.size(); i++) {
    d_rewrites[i]->deleteUncachedChildren();
    if (!d_rewrites[i]->d_cached_version_used) {
      delete d_rewrites[i];
    }
  }

  for (ProofCacheIterator iter = preRewriteCache.begin();
       iter != preRewriteCache.end(); ++iter) {
    if (iter->second != NULL) {
      delete iter->second;
    }
  }
  /*
  for (ProofCacheIterator iter = postRewriteCache.begin();
       iter != postRewriteCache.end(); ++iter) {
    if (iter->second != NULL) {
      delete iter->second;
    }
  }*/
}

void RewriteProof::attachSubproofToParent() {
  Rewrite *topRewrite = d_rewrites.back();

  // Simplify proof
  if (topRewrite->d_tag == ORIGINAL_OP) {
    bool allChildrenRefl = true;
    for (size_t i = 0; i < topRewrite->d_children.size(); i++) {
      if (topRewrite->d_children[i]->d_tag != ORIGINAL_OP) {
        allChildrenRefl = false;
        break;
      }
    }
    if (allChildrenRefl) {
      topRewrite->d_children.clear();
    }
  }
  d_rewrites[d_rewrites.size() - 2]->d_children.push_back(d_rewrites.back());
  d_rewrites.pop_back();
}

Rewrite *RewriteProof::getRewrite() const {
  Assert(d_rewrites.size() == 1);
  return d_rewrites[0];
}

void RewriteProof::registerRewrite(const int tag) {
  Rewrite *topRewrite = d_rewrites.back();
  d_rewrites.pop_back();
  Rewrite *newRewrite = new Rewrite(tag, topRewrite->d_original);
  newRewrite->d_children.push_back(topRewrite);
  d_rewrites.push_back(newRewrite);
}

void RewriteProof::replaceRewrite(Rewrite *rewrite) {
  // XXX: make sure that this is always safe
  delete d_rewrites.back();
  d_rewrites.back() = rewrite;
}

Rewrite *RewriteProof::getPreRewriteCache(Node node) {
  return preRewriteCache[node.toExpr()];
}

Rewrite *RewriteProof::getPostRewriteCache(Node node) {
  return postRewriteCache[node.toExpr()];
}

void RewriteProof::setPreRewriteCache(Node node, Rewrite *rewrite) {
  preRewriteCache[node.toExpr()] = rewrite;
}

void RewriteProof::setPostRewriteCache(Node node, Rewrite *rewrite) {
  postRewriteCache[node.toExpr()] = rewrite;
}

void RewriteProof::printCachedProofs(TheoryProofEngine *tp, std::ostream &os,
                                     std::ostream &paren,
                                     ProofLetMap &globalLetMap) const {
  for (ProofCacheIterator iter = preRewriteCache.begin();
       iter != preRewriteCache.end(); ++iter) {
    if (iter->second->d_cached_version_used) {
      os << std::endl;
      os << "(@ let" << iter->second->d_id << " ";
      callPrintRewriteProof(false, tp, iter->second, os, globalLetMap);
      paren << ")";
    }
  }
}

} /* CVC4 namespace */

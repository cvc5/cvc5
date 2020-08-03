/*********************                                                        */
/*! \file theory_preprocessor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory preprocessor.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__THEORY_PREPROCESSOR_H
#define CVC4__THEORY__THEORY_PREPROCESSOR_H

#include <unordered_map>

#include "expr/node.h"
#include "preprocessing/assertion_pipeline.h"

namespace CVC4 {

class LogicInfo;
class TheoryEngine;
class RemoveTermFormulas;
class LazyCDProof;

namespace theory {

/**
 * The preprocessor used in TheoryEngine.
 */
class TheoryPreprocessor
{
  typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;

 public:
  /** Constructs a theory preprocessor */
  TheoryPreprocessor(TheoryEngine& engine, RemoveTermFormulas& tfr);
  /** Destroys a theory preprocessor */
  ~TheoryPreprocessor();
  /** Clear the cache of this class */
  void clearCache();
  /**
   * Preprocesses the given assertion node. It returns a TrustNode of kind
   * TrustNodeKind::REWRITE indicating the preprocessed form of node. It stores
   * additional lemmas in newLemmas, which are trust nodes of kind
   * TrustNodeKind::LEMMA. These correspond to e.g. lemmas corresponding to ITE
   * removal. For each lemma in newLemmas, we add the corresponding skolem that
   * the lemma defines. The flag doTheoryPreprocess is whether we should run
   * theory-specific preprocessing.
   *
   * @param node The assertion to preprocess,
   * @param newLemmas The lemmas to add to the set of assertions,
   * @param newSkolems The skolems that newLemmas correspond to,
   * @param doTheoryPreprocess whether to run theory-specific preprocessing.
   * @return The trust node corresponding to rewriting node via preprocessing.
   */
  TrustNode preprocess(TNode node,
                       std::vector<TrustNode>& newLemmas,
                       std::vector<Node>& newSkolems,
                       bool doTheoryPreprocess);
  /**
   * Runs theory specific preprocessing on the non-Boolean parts of
   * the formula.  This is only called on input assertions, after ITEs
   * have been removed.
   */
  Node theoryPreprocess(TNode node);

 private:
  /** Reference to owning theory engine */
  TheoryEngine& d_engine;
  /** Logic info of theory engine */
  const LogicInfo& d_logicInfo;
  /** Cache for theory-preprocessing of assertions */
  NodeMap d_ppCache;
  /** The term formula remover */
  RemoveTermFormulas& d_tfr;
  /** Helper for theoryPreprocess */
  Node ppTheoryRewrite(TNode term);
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__THEORY_PREPROCESSOR_H */

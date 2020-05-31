/*********************                                                        */
/*! \file theory_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory engine
 **
 ** The theory engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__THEORY_PREPROCESSOR_H
#define CVC4__THEORY__THEORY_PREPROCESSOR_H

#include <unordered_map>

#include "expr/node.h"

namespace CVC4 {

class LogicInfo;
class TheoryEngine;
class RemoveTermFormulas;

/**
 * The preprocessor used in TheoryPreprocessor.
 */
class TheoryPreprocessor {
  typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;
public:
  /** Constructs a theory preprocessor */
  TheoryPreprocessor(TheoryEngine& engine);

  /** Destroys a theory preprocessor */
  ~TheoryPreprocessor();
  /**
   * Signal the start of a new round of assertion preprocessing
   */
  void preprocessStart();

  /**
   * Runs theory specific preprocessing on the non-Boolean parts of
   * the formula.  This is only called on input assertions, after ITEs
   * have been removed.
   */
  Node preprocess(TNode node);
private:
  /** Reference to owning theory engine */
  TheoryEngine& d_engine;
  /** Logic info of theory engine */
  const LogicInfo& d_logicInfo;
    /**Cache for theory-preprocessing of assertions */
  NodeMap d_ppCache;
  /** The term formula remover */
  RemoveTermFormulas& d_tfr;
  /**
   * Helper for preprocess
   */
  Node ppTheoryRewrite(TNode term);
};

}/* CVC4 namespace */

#endif /* CVC4__THEORY__THEORY_PREPROCESSOR_H */

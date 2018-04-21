/*********************                                                        */
/*! \file preprocessing_pass.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass super class
 **
 ** Implementation of the preprocessing pass super class. Preprocessing passes
 ** that inherit from this class, need to pass their name to the constructor to
 ** register the pass appropriately. The core of a preprocessing pass lives
 ** in applyInternal(), which operates on a list of assertions and is called
 ** from apply() in the super class. The apply() method automatically takes
 ** care of the following:
 **
 ** - Dumping assertions before and after the pass
 ** - Initializing the timer
 ** - Tracing and chatting
 **
 ** Optionally, preprocessing passes can overwrite the initInteral() method to
 ** do work that only needs to be done once.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PREPROCESSING_PASS_H
#define __CVC4__PREPROCESSING__PREPROCESSING_PASS_H

#include <string>
#include <vector>

#include "expr/node.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/smt_engine_scope.h"

namespace CVC4 {
namespace preprocessing {

/* Assertion Pipeline stores a list of assertions modified by preprocessing
 * passes. */
class AssertionPipeline {
  std::vector<Node> d_nodes;

 public:
  size_t size() const { return d_nodes.size(); }

  void resize(size_t n) { d_nodes.resize(n); }
  void clear() { d_nodes.clear(); }

  Node& operator[](size_t i) { return d_nodes[i]; }
  const Node& operator[](size_t i) const { return d_nodes[i]; }
  void push_back(Node n) { d_nodes.push_back(n); }

  std::vector<Node>& ref() { return d_nodes; }
  const std::vector<Node>& ref() const { return d_nodes; }

  std::vector<Node>::const_iterator begin() const { return d_nodes.cbegin(); }
  std::vector<Node>::const_iterator end() const { return d_nodes.cend(); }

  /*
   * Replaces assertion i with node n and records the dependency between the
   * original assertion and its replacement.
   */
  void replace(size_t i, Node n);

  /*
   * Replaces assertion i with node n and records that this replacement depends
   * on assertion i and the nodes listed in addnDeps. The dependency
   * information is used for unsat cores and proofs.
   */
  void replace(size_t i, Node n, const std::vector<Node>& addnDeps);

  /*
   * Replaces an assertion with a vector of assertions and records the
   * dependencies.
   */
  void replace(size_t i, const std::vector<Node>& ns);
}; /* class AssertionPipeline */

/**
 * Preprocessing passes return a result which indicates whether a conflict has
 * been detected during preprocessing.
 */
enum PreprocessingPassResult { CONFLICT, NO_CONFLICT };

class PreprocessingPass {
 public:
  /* Preprocesses a list of assertions assertionsToPreprocess */
  PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);

  PreprocessingPass(PreprocessingPassContext* preprocContext,
                    const std::string& name);
  virtual ~PreprocessingPass();

 protected:
  /*
   * Method for dumping assertions within a pass. Also called before and after
   * applying the pass.
   */
  void dumpAssertions(const char* key, const AssertionPipeline& assertionList);

  /*
   * Abstract method that each pass implements to do the actual preprocessing.
   */
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) = 0;

  /* Context for Preprocessing Passes that initializes necessary variables */
  PreprocessingPassContext* d_preprocContext;

 private:
  /* Name of pass */
  std::string d_name;
  /* Timer for registering the preprocessing time of this pass */
  TimerStat d_timer;
};

}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PREPROCESSING_PASS_H */

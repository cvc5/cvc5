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
 ** \brief Implementation for preprocessing pass super class
 **
 ** Implementation for preprocessing pass super class. Includes a generalized
 ** structure for the apply method, which includes dumping assertions before
 ** and after the pass, initializing the Timer, and Tracing and Chatting.
 ** For new classes, a name is necessary to register the pass, and
 ** an apply internal method is necessary that takes in
 ** the AssertionPipeline to perform the pass. An init Internal method
 ** is optional to initialize variables that are not a part of the Context.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PREPROCESSING_PASS_H
#define __CVC4__PREPROCESSING__PREPROCESSING_PASS_H

#include <string>
#include <vector>

#include "expr/expr.h"
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

  void replace(size_t i, Node n);
}; /* class AssertionPipeline */

/* Enumeration of the values returned when applying preprocessing pass */
enum PreprocessingPassResult { CONFLICT, NO_CONFLICT };

class PreprocessingPass {
 public:
  /* Takes a collection of assertions and preprocesses them, modifying
   * assertionsToPreprocess. Supports timing and output of debugging
   * information  */
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

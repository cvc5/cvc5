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
 ** is optional to initialize variables that are not a part of the API.
 **/
#include "cvc4_public.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASS_H
#define __CVC4__PREPROC__PREPROCESSING_PASS_H

#include <iostream>
#include <string>
#include <vector>
#include "expr/node.h"

#include "options/proof_options.h"
#include "preproc/preprocessing_pass_registry.h"
#include "smt/dump.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory_model.h"
using namespace std;

namespace CVC4 {
namespace preproc {

class AssertionPipeline {
  vector<Node> d_nodes;

 public:
  size_t size() const { return d_nodes.size(); }

  void resize(size_t n) { d_nodes.resize(n); }
  void clear() { d_nodes.clear(); }

  Node& operator[](size_t i) { return d_nodes[i]; }
  const Node& operator[](size_t i) const { return d_nodes[i]; }
  void push_back(Node n) { d_nodes.push_back(n); }

  vector<Node>& ref() { return d_nodes; }
  const vector<Node>& ref() const { return d_nodes; }

  void replace(size_t i, Node n) {
    PROOF(ProofManager::currentPM()->addDependence(n, d_nodes[i]););
    d_nodes[i] = n;
  }
}; /* class AssertionPipeline */

/* Data structure for return type of passes */
enum PreprocessingPassResult { CONFLICT, NO_CONFLICT };
/* forward declaration of registry */
class PreprocessingPassRegistry;

class PreprocessingPass {
 public:
  /* Initializes the api and registers the timer for each pass */
  void init(PreprocessingPassAPI* api);
  /* General structure for the apply method for a pass, includes dumping
   * assertions before and after pass and Chat */
  PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);
  /* do dumping before/after any preprocessing pass) */
  void dumpAssertions(const char* key, const AssertionPipeline& assertionList);
  PreprocessingPass(PreprocessingPassRegistry* preprocessingPassRegistry,
                    const std::string& name);

  virtual ~PreprocessingPass();

 protected:
  /* prototype for initInternal method, wh ich may need to be called to
   * initialize stats or variables within passes */
  virtual void initInternal(PreprocessingPassAPI* api) {}
  /* prototype for apply method each individual pass ultimately calls */
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) = 0;
  /* API for Preprocessing Passes that initializes necessary variables */
  PreprocessingPassAPI* d_api;
  /* name of pass */
  std::string d_name;
  /* timer registered for passes */
  TimerStat d_timer;
};

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_H */

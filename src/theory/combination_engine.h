/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Abstract interface for theory combination.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__COMBINATION_ENGINE__H
#define CVC5__THEORY__COMBINATION_ENGINE__H

#include <vector>
#include <memory>

#include "theory/ee_manager.h"
#include "theory/valuation.h"

namespace cvc5 {

class TheoryEngine;
class Env;
class EagerProofGenerator;

namespace theory {

class ModelManager;
class SharedSolver;

/**
 * Manager for doing theory combination. This class is responsible for:
 * (1) Initializing the various components of theory combination (equality
 * engine manager, model manager, shared solver) based on the equality engine
 * mode, and
 * (2) Implementing the main combination method (combineTheories).
 */
class CombinationEngine
{
 public:
  CombinationEngine(TheoryEngine& te,
                    Env& env,
                    const std::vector<Theory*>& paraTheories,
                    ProofNodeManager* pnm);
  virtual ~CombinationEngine();

  /** Finish initialization */
  void finishInit();

  /** Get equality engine theory information for theory with identifier tid. */
  const EeTheoryInfo* getEeTheoryInfo(TheoryId tid) const;
  //-------------------------- model
  /**
   * Reset the model maintained by this class. This resets all local information
   * that is unique to each check.
   */
  void resetModel();
  /**
   * Build the model maintained by this class.
   *
   * @return true if model building was successful.
   */
  virtual bool buildModel() = 0;
  /**
   * Post process the model maintained by this class. This is called after
   * a successful call to buildModel. This does any theory-specific
   * postprocessing of the model.
   *
   * @param incomplete Whether we are answering "unknown" instead of "sat".
   */
  void postProcessModel(bool incomplete);
  /**
   * Get the model object maintained by this class.
   */
  TheoryModel* getModel();
  //-------------------------- end model
  /**
   * Get the shared solver, which is the active component of theory combination
   * that TheoryEngine interacts with prior to calling combineTheories.
   */
  SharedSolver* getSharedSolver();
  /**
   * Called at the beginning of full effort
   */
  virtual void resetRound();
  /**
   * Combine theories, called after FULL effort passes with no lemmas
   * and before LAST_CALL effort is run. This adds necessary lemmas for
   * theory combination (e.g. splitting lemmas) to the parent TheoryEngine.
   */
  virtual void combineTheories() = 0;

 protected:
  /** Is proof enabled? */
  bool isProofEnabled() const;
  /**
   * Get model equality engine notify. Return the notification object for
   * who listens to the model's equality engine (if any).
   */
  virtual eq::EqualityEngineNotify* getModelEqualityEngineNotify();
  /** Send lemma to the theory engine, atomsTo is the theory to send atoms to */
  void sendLemma(TrustNode trn, TheoryId atomsTo);
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Reference to the environment */
  Env& d_env;
  /** Valuation for the engine */
  Valuation d_valuation;
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** Logic info of theory engine (cached) */
  const LogicInfo& d_logicInfo;
  /** List of parametric theories of theory engine */
  const std::vector<Theory*> d_paraTheories;
  /**
   * The equality engine manager we are using. This class is responsible for
   * configuring equality engines for each theory.
   */
  std::unique_ptr<EqEngineManager> d_eemanager;
  /**
   * The model manager we are using. This class is responsible for building the
   * model.
   */
  std::unique_ptr<ModelManager> d_mmanager;
  /**
   * The shared solver. This class is responsible for performing combination
   * tasks (e.g. preregistration) during solving.
   */
  std::unique_ptr<SharedSolver> d_sharedSolver;
  /**
   * An eager proof generator, if proofs are enabled. This proof generator is
   * responsible for proofs of splitting lemmas generated in combineTheories.
   */
  std::unique_ptr<EagerProofGenerator> d_cmbsPg;
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__COMBINATION_DISTRIBUTED__H */

/*********************                                                        */
/*! \file quantifiers_modules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Class for initializing the modules of quantifiers engine
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_MODULES_H
#define CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_MODULES_H

#include "theory/quantifiers/alpha_equivalence.h"
#include "theory/quantifiers/anti_skolem.h"
#include "theory/quantifiers/conjecture_generator.h"
#include "theory/quantifiers/ematching/instantiation_engine.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/quantifiers/fmf/model_engine.h"
#include "theory/quantifiers/inst_strategy_enumerative.h"
#include "theory/quantifiers/quant_conflict_find.h"
#include "theory/quantifiers/quant_split.h"
#include "theory/quantifiers/sygus/synth_engine.h"
#include "theory/quantifiers/sygus_inst.h"

namespace CVC4 {
namespace theory {
  
class QuantifiersEngine;

namespace quantifiers {

/**
 * This class is responsible for constructing the vector of modules to be
 * used by quantifiers engine. It generates this list of modules in its
 * initialize method, which is based on the options.
 */
class QuantifiersModules
{
  friend class ::CVC4::theory::QuantifiersEngine;
 public:
  QuantifiersModules();
  ~QuantifiersModules();
  /** initialize
   *
   * This constructs the above modules based on the current options. It adds
   * a pointer to each module it constructs to modules.
   */
  void initialize(QuantifiersEngine* qe,
                  context::Context* c,
                  std::vector<QuantifiersModule*>& modules);
 private:
  //------------------------------ quantifier utilities
  /** relevant domain */
  std::unique_ptr<quantifiers::RelevantDomain> d_rel_dom;
  //------------------------------ quantifiers modules
  /** alpha equivalence */
  std::unique_ptr<quantifiers::AlphaEquivalence> d_alpha_equiv;
  /** instantiation engine */
  std::unique_ptr<quantifiers::InstantiationEngine> d_inst_engine;
  /** model engine */
  std::unique_ptr<quantifiers::ModelEngine> d_model_engine;
  /** bounded integers utility */
  std::unique_ptr<quantifiers::BoundedIntegers> d_bint;
  /** Conflict find mechanism for quantifiers */
  std::unique_ptr<quantifiers::QuantConflictFind> d_qcf;
  /** subgoal generator */
  std::unique_ptr<quantifiers::ConjectureGenerator> d_sg_gen;
  /** ceg instantiation */
  std::unique_ptr<quantifiers::SynthEngine> d_synth_e;
  /** full saturation */
  std::unique_ptr<quantifiers::InstStrategyEnum> d_fs;
  /** counterexample-based quantifier instantiation */
  std::unique_ptr<quantifiers::InstStrategyCegqi> d_i_cbqi;
  /** quantifiers splitting */
  std::unique_ptr<quantifiers::QuantDSplit> d_qsplit;
  /** quantifiers anti-skolemization */
  std::unique_ptr<quantifiers::QuantAntiSkolem> d_anti_skolem;
  /** SyGuS instantiation engine */
  std::unique_ptr<quantifiers::SygusInst> d_sygus_inst;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_MODULES_H */

/*********************                                                        */
/*! \file preprocessor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessor of the SmtEngine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__PREPROCESSOR_H
#define CVC4__SMT__PREPROCESSOR_H

#include <vector>

#include "theory/booleans/circuit_propagator.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/process_assertions.h"
#include "smt/term_formula_removal.h"

namespace CVC4 {
namespace smt {
  
class AbstractValues;

/**
 * The preprocessor module of an SMT engine.
 */
class Preprocessor
{
 public:
  Preprocessor(SmtEngine& smt, context::UserContext* u, AbstractValues& abs);
  ~Preprocessor();
    
  /**
   * Process the assertions that have been asserted.
   */
  void processAssertions(Assertions& as);
  /** 
   * Get term formula remover 
   */
  RemoveTermFormulas& getTermFormulaRemover();
private:
  /** Reference to the abstract values utility */
  AbstractValues& d_absValues; 
  /** A circuit propagator for non-clausal propositional deduction */
  booleans::CircuitPropagator d_propagator;
  /** Whether any assertions have been processed */
  context::CDO<bool> d_assertionsProcessed;
  /** Cached true value */
  //Node d_true;
  /** The preprocessing pass context */
  std::unique_ptr<PreprocessingPassContext> d_preprocessingPassContext;
  /** Process assertions module */
  ProcessAssertions d_processor;
  /** Instance of the term formula remover */
  RemoveTermFormulas d_rtf;
};

}  // namespace smt
}  // namespace CVC4

#endif

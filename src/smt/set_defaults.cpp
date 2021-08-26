/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of setting default options.
 */

#include "smt/set_defaults.h"

#include <sstream>

#include "base/output.h"
#include "options/arith_options.h"
#include "options/arrays_options.h"
#include "options/base_options.h"
#include "options/booleans_options.h"
#include "options/bv_options.h"
#include "options/datatypes_options.h"
#include "options/decision_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/option_exception.h"
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "options/prop_options.h"
#include "options/quantifiers_options.h"
#include "options/sep_options.h"
#include "options/set_language.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "smt/logic_exception.h"
#include "theory/theory.h"

using namespace cvc5::theory;

namespace cvc5 {
namespace smt {

SetDefaults::SetDefaults(bool isInternalSubsolver)
    : d_isInternalSubsolver(isInternalSubsolver)
{
}

void SetDefaults::setDefaults(LogicInfo& logic, Options& opts)
{
  // initial changes that are independent of logic, and may impact the logic
  setDefaultsPre(opts);
  // now, finalize the logic
  finalizeLogic(logic, opts);
  // further changes to options based on the logic
  setDefaultsPost(logic, opts);
}

void SetDefaults::setDefaultsPre(Options& opts)
{
  // implied options
  if (opts.smt.debugCheckModels)
  {
    opts.smt.checkModels = true;
  }
  if (opts.smt.checkModels || opts.driver.dumpModels)
  {
    opts.smt.produceModels = true;
  }
  if (opts.smt.checkModels)
  {
    opts.smt.produceAssignments = true;
  }
  // unsat cores and proofs shenanigans
  if (opts.driver.dumpUnsatCoresFull)
  {
    opts.driver.dumpUnsatCores = true;
  }
  if (opts.smt.checkUnsatCores || opts.driver.dumpUnsatCores
      || opts.smt.unsatAssumptions || opts.smt.minimalUnsatCores
      || opts.smt.unsatCoresMode != options::UnsatCoresMode::OFF)
  {
    opts.smt.unsatCores = true;
  }
  if (opts.smt.unsatCores
      && opts.smt.unsatCoresMode == options::UnsatCoresMode::OFF)
  {
    if (opts.smt.unsatCoresModeWasSetByUser)
    {
      Notice()
          << "Overriding OFF unsat-core mode since cores were requested.\n";
    }
    opts.smt.unsatCoresMode = options::UnsatCoresMode::ASSUMPTIONS;
  }

  if (opts.smt.checkProofs || opts.driver.dumpProofs)
  {
    opts.smt.produceProofs = true;
  }

  if (opts.smt.produceProofs
      && opts.smt.unsatCoresMode != options::UnsatCoresMode::FULL_PROOF)
  {
    if (opts.smt.unsatCoresModeWasSetByUser)
    {
      Notice() << "Forcing full-proof mode for unsat cores mode since proofs "
                  "were requested.\n";
    }
    // enable unsat cores, because they are available as a consequence of proofs
    opts.smt.unsatCores = true;
    opts.smt.unsatCoresMode = options::UnsatCoresMode::FULL_PROOF;
  }

  // set proofs on if not yet set
  if (opts.smt.unsatCores && !opts.smt.produceProofs)
  {
    if (opts.smt.produceProofsWasSetByUser)
    {
      Notice()
          << "Forcing proof production since new unsat cores were requested.\n";
    }
    opts.smt.produceProofs = true;
  }

  // if unsat cores are disabled, then unsat cores mode should be OFF
  Assert(opts.smt.unsatCores
         == (opts.smt.unsatCoresMode != options::UnsatCoresMode::OFF));

  if (opts.bv.bitvectorAigSimplificationsWasSetByUser)
  {
    Notice() << "SmtEngine: setting bitvectorAig" << std::endl;
    opts.bv.bitvectorAig = true;
  }
  if (opts.bv.bitvectorAlgebraicBudgetWasSetByUser)
  {
    Notice() << "SmtEngine: setting bitvectorAlgebraicSolver" << std::endl;
    opts.bv.bitvectorAlgebraicSolver = true;
  }
}

void SetDefaults::finalizeLogic(LogicInfo& logic, Options& opts) const
{
  if (opts.bv.bitblastMode == options::BitblastMode::EAGER)
  {
    if (opts.smt.produceModels
        && (logic.isTheoryEnabled(THEORY_ARRAYS)
            || logic.isTheoryEnabled(THEORY_UF)))
    {
      if (opts.bv.bitblastModeWasSetByUser
          || opts.smt.produceModelsWasSetByUser)
      {
        throw OptionException(std::string(
            "Eager bit-blasting currently does not support model generation "
            "for the combination of bit-vectors with arrays or uinterpreted "
            "functions. Try --bitblast=lazy"));
      }
      Notice() << "SmtEngine: setting bit-blast mode to lazy to support model"
               << "generation" << std::endl;
      opts.bv.bitblastMode = options::BitblastMode::LAZY;
    }
    else if (!opts.base.incrementalSolving)
    {
      opts.smt.ackermann = true;
    }
  }

  /* Disable bit-level propagation by default for the BITBLAST solver. */
  if (opts.bv.bvSolver == options::BVSolver::BITBLAST)
  {
    opts.bv.bitvectorPropagate = false;
  }

  if (opts.smt.solveIntAsBV > 0)
  {
    // not compatible with incremental
    if (opts.base.incrementalSolving)
    {
      throw OptionException(
          "solving integers as bitvectors is currently not supported "
          "when solving incrementally.");
    }
    // Int to BV currently always eliminates arithmetic completely (or otherwise
    // fails). Thus, it is safe to eliminate arithmetic. Also, bit-vectors
    // are required.
    logic = logic.getUnlockedCopy();
    logic.enableTheory(THEORY_BV);
    logic.disableTheory(THEORY_ARITH);
    logic.lock();
  }

  if (opts.smt.solveBVAsInt != options::SolveBVAsIntMode::OFF)
  {
    if (opts.bv.boolToBitvector != options::BoolToBVMode::OFF)
    {
      throw OptionException(
          "solving bitvectors as integers is incompatible with --bool-to-bv.");
    }
    if (opts.smt.BVAndIntegerGranularity > 8)
    {
      /**
       * The granularity sets the size of the ITE in each element
       * of the sum that is generated for bitwise operators.
       * The size of the ITE is 2^{2*granularity}.
       * Since we don't want to introduce ITEs with unbounded size,
       * we bound the granularity.
       */
      throw OptionException("solve-bv-as-int accepts values from 0 to 8.");
    }
    if (logic.isTheoryEnabled(THEORY_BV))
    {
      logic = logic.getUnlockedCopy();
      logic.enableTheory(THEORY_ARITH);
      logic.arithNonLinear();
      logic.lock();
    }
  }

  // set options about ackermannization
  if (opts.smt.ackermann && opts.smt.produceModels
      && (logic.isTheoryEnabled(THEORY_ARRAYS)
          || logic.isTheoryEnabled(THEORY_UF)))
  {
    if (opts.smt.produceModelsWasSetByUser)
    {
      throw OptionException(std::string(
          "Ackermannization currently does not support model generation."));
    }
    Notice() << "SmtEngine: turn off ackermannization to support model"
             << "generation" << std::endl;
    opts.smt.ackermann = false;
  }

  if (opts.smt.ackermann)
  {
    if (opts.base.incrementalSolving)
    {
      throw OptionException(
          "Incremental Ackermannization is currently not supported.");
    }

    if (logic.isQuantified())
    {
      throw LogicException("Cannot use Ackermannization on quantified formula");
    }

    if (logic.isTheoryEnabled(THEORY_UF))
    {
      logic = logic.getUnlockedCopy();
      logic.disableTheory(THEORY_UF);
      logic.lock();
    }
    if (logic.isTheoryEnabled(THEORY_ARRAYS))
    {
      logic = logic.getUnlockedCopy();
      logic.disableTheory(THEORY_ARRAYS);
      logic.lock();
    }
  }

  // --ite-simp is an experimental option designed for QF_LIA/nec. This
  // technique is experimental. This benchmark set also requires removing ITEs
  // during preprocessing, before repeating simplification. Hence, we enable
  // this by default.
  if (opts.smt.doITESimp)
  {
    if (!opts.smt.earlyIteRemovalWasSetByUser)
    {
      opts.smt.earlyIteRemoval = true;
    }
  }

  // Set default options associated with strings-exp. We also set these options
  // if we are using eager string preprocessing, which may introduce quantified
  // formulas at preprocess time.
  //
  // We don't want to set this option when we are in logics that contain ALL.
  if (!logic.hasEverything() && logic.isTheoryEnabled(THEORY_STRINGS))
  {
    // If the user explicitly set a logic that includes strings, but is not
    // the generic "ALL" logic, then enable stringsExp.
    opts.strings.stringExp = true;
    Trace("smt") << "Turning stringExp on since logic does not have everything "
                    "and string theory is enabled\n";
  }
  if (opts.strings.stringExp || !opts.strings.stringLazyPreproc)
  {
    // We require quantifiers since extended functions reduce using them.
    if (!logic.isQuantified())
    {
      logic = logic.getUnlockedCopy();
      logic.enableQuantifiers();
      logic.lock();
      Trace("smt") << "turning on quantifier logic, for strings-exp"
                   << std::endl;
    }
    // Note we allow E-matching by default to support combinations of sequences
    // and quantifiers. We also do not enable fmfBound here, which would
    // enable bounded integer instantiation for *all* quantifiers. Instead,
    // the bounded integers module will always process internally generated
    // quantifiers (those marked with InternalQuantAttribute).
  }

  // new unsat core specific restrictions for proofs
  if (opts.smt.unsatCores
      && opts.smt.unsatCoresMode != options::UnsatCoresMode::FULL_PROOF)
  {
    // no fine-graininess
    if (!opts.proof.proofGranularityModeWasSetByUser)
    {
      opts.proof.proofGranularityMode = options::ProofGranularityMode::OFF;
    }
  }

  if (opts.arrays.arraysExp)
  {
    if (!logic.isQuantified())
    {
      logic = logic.getUnlockedCopy();
      logic.enableQuantifiers();
      logic.lock();
    }
    // Allows to answer sat more often by default.
    if (!opts.quantifiers.fmfBoundWasSetByUser)
    {
      opts.quantifiers.fmfBound = true;
      Trace("smt") << "turning on fmf-bound, for arrays-exp" << std::endl;
    }
  }

  // We now know whether the input uses sygus. Update the logic to incorporate
  // the theories we need internally for handling sygus problems.
  if (usesSygus(opts))
  {
    logic = logic.getUnlockedCopy();
    logic.enableSygus();
    logic.lock();
  }

  // if we requiring disabling proofs, disable them now
  if (opts.smt.produceProofs)
  {
    std::stringstream reasonNoProofs;
    if (incompatibleWithProofs(opts, reasonNoProofs))
    {
      opts.smt.unsatCores = false;
      opts.smt.unsatCoresMode = options::UnsatCoresMode::OFF;
      Notice() << "SmtEngine: turning off produce-proofs due to "
               << reasonNoProofs.str() << "." << std::endl;
      opts.smt.produceProofs = false;
      opts.smt.checkProofs = false;
      opts.proof.proofEagerChecking = false;
    }
  }

  // sygus core connective requires unsat cores
  if (opts.quantifiers.sygusCoreConnective)
  {
    opts.smt.unsatCores = true;
    if (opts.smt.unsatCoresMode == options::UnsatCoresMode::OFF)
    {
      opts.smt.unsatCoresMode = options::UnsatCoresMode::ASSUMPTIONS;
    }
  }

  if ((opts.smt.checkModels || opts.smt.checkSynthSol || opts.smt.produceAbducts
       || opts.smt.produceInterpols != options::ProduceInterpols::NONE
       || opts.smt.modelCoresMode != options::ModelCoresMode::NONE
       || opts.smt.blockModelsMode != options::BlockModelsMode::NONE
       || opts.smt.produceProofs)
      && !opts.smt.produceAssertions)
  {
    Notice() << "SmtEngine: turning on produce-assertions to support "
             << "option requiring assertions." << std::endl;
    opts.smt.produceAssertions = true;
  }

  if (opts.bv.bvAssertInput && opts.smt.produceProofs)
  {
    Notice() << "Disabling bv-assert-input since it is incompatible with proofs."
             << std::endl;
    opts.bv.bvAssertInput = false;
  }

  // If proofs are required and the user did not specify a specific BV solver,
  // we make sure to use the proof producing BITBLAST_INTERNAL solver.
  if (opts.smt.produceProofs
      && opts.bv.bvSolver != options::BVSolver::BITBLAST_INTERNAL
      && !opts.bv.bvSolverWasSetByUser
      && opts.bv.bvSatSolver == options::SatSolverMode::MINISAT)
  {
    Notice() << "Forcing internal bit-vector solver due to proof production."
             << std::endl;
    opts.bv.bvSolver = options::BVSolver::BITBLAST_INTERNAL;
  }

  if (opts.smt.solveBVAsInt != options::SolveBVAsIntMode::OFF)
  {
    /**
     * Operations on 1 bits are better handled as Boolean operations
     * than as integer operations.
     * Therefore, we enable bv-to-bool, which runs before
     * the translation to integers.
     */
    opts.bv.bitvectorToBool = true;
  }

  // Disable options incompatible with incremental solving, or output an error
  // if enabled explicitly.
  if (opts.base.incrementalSolving)
  {
    std::stringstream reasonNoInc;
    std::stringstream suggestNoInc;
    if (incompatibleWithIncremental(logic, opts, reasonNoInc, suggestNoInc))
    {
      std::stringstream ss;
      ss << reasonNoInc.str() << " not supported with incremental solving. "
         << suggestNoInc.str();
      throw OptionException(ss.str());
    }
  }

  // Disable options incompatible with unsat cores or output an error if enabled
  // explicitly
  if (safeUnsatCores(opts))
  {
    // check if the options are not compatible with unsat cores
    std::stringstream reasonNoUc;
    if (incompatibleWithUnsatCores(opts, reasonNoUc))
    {
      std::stringstream ss;
      ss << reasonNoUc.str() << " not supported with unsat cores";
      throw OptionException(ss.str());
    }
  }
  else
  {
    // Turn on unconstrained simplification for QF_AUFBV
    if (!opts.smt.unconstrainedSimpWasSetByUser
        && !opts.base.incrementalSolving)
    {
      // It is also currently incompatible with arithmetic, force the option
      // off.
      bool uncSimp = !opts.base.incrementalSolving && !logic.isQuantified()
                     && !opts.smt.produceModels && !opts.smt.produceAssignments
                     && !opts.smt.checkModels
                     && logic.isTheoryEnabled(THEORY_ARRAYS)
                     && logic.isTheoryEnabled(THEORY_BV)
                     && !logic.isTheoryEnabled(THEORY_ARITH);
      Trace("smt") << "setting unconstrained simplification to " << uncSimp
                   << std::endl;
      opts.smt.unconstrainedSimp = uncSimp;
    }

    // by default, nonclausal simplification is off for QF_SAT
    if (!opts.smt.simplificationModeWasSetByUser)
    {
      bool qf_sat = logic.isPure(THEORY_BOOL) && !logic.isQuantified();
      Trace("smt") << "setting simplification mode to <"
                   << logic.getLogicString() << "> " << (!qf_sat) << std::endl;
      // simplification=none works better for SMT LIB benchmarks with
      // quantifiers, not others opts.set(options::simplificationMode, qf_sat ||
      // quantifiers ? options::SimplificationMode::NONE :
      // options::SimplificationMode::BATCH);
      opts.smt.simplificationMode = qf_sat ? options::SimplificationMode::NONE
                                           : options::SimplificationMode::BATCH;
    }
  }

  if (opts.quantifiers.cegqiBv && logic.isQuantified())
  {
    if (opts.bv.boolToBitvector != options::BoolToBVMode::OFF)
    {
      if (opts.bv.boolToBitvectorWasSetByUser)
      {
        throw OptionException(
            "bool-to-bv != off not supported with CBQI BV for quantified "
            "logics");
      }
      Notice() << "SmtEngine: turning off bool-to-bitvector to support CBQI BV"
               << std::endl;
      opts.bv.boolToBitvector = options::BoolToBVMode::OFF;
    }
  }

  // cases where we need produce models
  if (!opts.smt.produceModels
      && (opts.smt.produceAssignments || opts.quantifiers.sygusRewSynthCheck
          || usesSygus(opts)))
  {
    Notice() << "SmtEngine: turning on produce-models" << std::endl;
    opts.smt.produceModels = true;
  }

  // widen the logic
  widenLogic(logic, opts);
}

void SetDefaults::setDefaultsPost(const LogicInfo& logic, Options& opts) const
{
  // Set the options for the theoryOf
  if (!opts.theory.theoryOfModeWasSetByUser)
  {
    if (logic.isSharingEnabled() && !logic.isTheoryEnabled(THEORY_BV)
        && !logic.isTheoryEnabled(THEORY_STRINGS)
        && !logic.isTheoryEnabled(THEORY_SETS)
        && !logic.isTheoryEnabled(THEORY_BAGS)
        && !(logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
             && !logic.isQuantified()))
    {
      Trace("smt") << "setting theoryof-mode to term-based" << std::endl;
      opts.theory.theoryOfMode = options::TheoryOfMode::THEORY_OF_TERM_BASED;
    }
  }

  // by default, symmetry breaker is on only for non-incremental QF_UF
  if (!opts.uf.ufSymmetryBreakerWasSetByUser)
  {
    bool qf_uf_noinc = logic.isPure(THEORY_UF) && !logic.isQuantified()
                       && !opts.base.incrementalSolving
                       && !safeUnsatCores(opts);
    Trace("smt") << "setting uf symmetry breaker to " << qf_uf_noinc
                 << std::endl;
    opts.uf.ufSymmetryBreaker = qf_uf_noinc;
  }

  // If in arrays, set the UF handler to arrays
  if (logic.isTheoryEnabled(THEORY_ARRAYS) && !logic.isHigherOrder()
      && !opts.quantifiers.finiteModelFind
      && (!logic.isQuantified()
          || (logic.isQuantified() && !logic.isTheoryEnabled(THEORY_UF))))
  {
    Theory::setUninterpretedSortOwner(THEORY_ARRAYS);
  }
  else
  {
    Theory::setUninterpretedSortOwner(THEORY_UF);
  }

  if (!opts.smt.simplifyWithCareEnabledWasSetByUser)
  {
    bool qf_aufbv =
        !logic.isQuantified() && logic.isTheoryEnabled(THEORY_ARRAYS)
        && logic.isTheoryEnabled(THEORY_UF) && logic.isTheoryEnabled(THEORY_BV);

    bool withCare = qf_aufbv;
    Trace("smt") << "setting ite simplify with care to " << withCare
                 << std::endl;
    opts.smt.simplifyWithCareEnabled = withCare;
  }
  // Turn off array eager index splitting for QF_AUFLIA
  if (!opts.arrays.arraysEagerIndexSplittingWasSetByUser)
  {
    if (not logic.isQuantified() && logic.isTheoryEnabled(THEORY_ARRAYS)
        && logic.isTheoryEnabled(THEORY_UF)
        && logic.isTheoryEnabled(THEORY_ARITH))
    {
      Trace("smt") << "setting array eager index splitting to false"
                   << std::endl;
      opts.arrays.arraysEagerIndexSplitting = false;
    }
  }
  // Turn on multiple-pass non-clausal simplification for QF_AUFBV
  if (!opts.smt.repeatSimpWasSetByUser)
  {
    bool repeatSimp = !logic.isQuantified()
                      && (logic.isTheoryEnabled(THEORY_ARRAYS)
                          && logic.isTheoryEnabled(THEORY_UF)
                          && logic.isTheoryEnabled(THEORY_BV))
                      && !safeUnsatCores(opts);
    Trace("smt") << "setting repeat simplification to " << repeatSimp
                 << std::endl;
    opts.smt.repeatSimp = repeatSimp;
  }

  if (opts.bv.boolToBitvector == options::BoolToBVMode::ALL
      && !logic.isTheoryEnabled(THEORY_BV))
  {
    if (opts.bv.boolToBitvectorWasSetByUser)
    {
      throw OptionException(
          "bool-to-bv=all not supported for non-bitvector logics.");
    }
    Notice() << "SmtEngine: turning off bool-to-bv for non-bv logic: "
             << logic.getLogicString() << std::endl;
    opts.bv.boolToBitvector = options::BoolToBVMode::OFF;
  }

  if (!opts.bv.bvEagerExplanationsWasSetByUser
      && logic.isTheoryEnabled(THEORY_ARRAYS)
      && logic.isTheoryEnabled(THEORY_BV))
  {
    Trace("smt") << "enabling eager bit-vector explanations " << std::endl;
    opts.bv.bvEagerExplanations = true;
  }

  // Turn on arith rewrite equalities only for pure arithmetic
  if (!opts.arith.arithRewriteEqWasSetByUser)
  {
    bool arithRewriteEq =
        logic.isPure(THEORY_ARITH) && logic.isLinear() && !logic.isQuantified();
    Trace("smt") << "setting arith rewrite equalities " << arithRewriteEq
                 << std::endl;
    opts.arith.arithRewriteEq = arithRewriteEq;
  }
  if (!opts.arith.arithHeuristicPivotsWasSetByUser)
  {
    int16_t heuristicPivots = 5;
    if (logic.isPure(THEORY_ARITH) && !logic.isQuantified())
    {
      if (logic.isDifferenceLogic())
      {
        heuristicPivots = -1;
      }
      else if (!logic.areIntegersUsed())
      {
        heuristicPivots = 0;
      }
    }
    Trace("smt") << "setting arithHeuristicPivots  " << heuristicPivots
                 << std::endl;
    opts.arith.arithHeuristicPivots = heuristicPivots;
  }
  if (!opts.arith.arithPivotThresholdWasSetByUser)
  {
    uint16_t pivotThreshold = 2;
    if (logic.isPure(THEORY_ARITH) && !logic.isQuantified())
    {
      if (logic.isDifferenceLogic())
      {
        pivotThreshold = 16;
      }
    }
    Trace("smt") << "setting arith arithPivotThreshold  " << pivotThreshold
                 << std::endl;
    opts.arith.arithPivotThreshold = pivotThreshold;
  }
  if (!opts.arith.arithStandardCheckVarOrderPivotsWasSetByUser)
  {
    int16_t varOrderPivots = -1;
    if (logic.isPure(THEORY_ARITH) && !logic.isQuantified())
    {
      varOrderPivots = 200;
    }
    Trace("smt") << "setting arithStandardCheckVarOrderPivots  "
                 << varOrderPivots << std::endl;
    opts.arith.arithStandardCheckVarOrderPivots = varOrderPivots;
  }
  if (logic.isPure(THEORY_ARITH) && !logic.areRealsUsed())
  {
    if (!opts.arith.nlExtTangentPlanesInterleaveWasSetByUser)
    {
      Trace("smt") << "setting nlExtTangentPlanesInterleave to true"
                   << std::endl;
      opts.arith.nlExtTangentPlanesInterleave = true;
    }
  }

  // set the default decision mode
  setDefaultDecisionMode(logic, opts);

  // set up of central equality engine
  if (opts.theory.eeMode == options::EqEngineMode::CENTRAL)
  {
    if (!opts.arith.arithEqSolverWasSetByUser)
    {
      // use the arithmetic equality solver by default
      opts.arith.arithEqSolver = true;
    }
  }
  if (opts.arith.arithEqSolver)
  {
    if (!opts.arith.arithCongManWasSetByUser)
    {
      // if we are using the arithmetic equality solver, do not use the
      // arithmetic congruence manager by default
      opts.arith.arithCongMan = false;
    }
  }

  if (opts.base.incrementalSolving)
  {
    // disable modes not supported by incremental
    opts.smt.sortInference = false;
    opts.uf.ufssFairnessMonotone = false;
    opts.quantifiers.globalNegate = false;
    opts.quantifiers.cegqiNestedQE = false;
    opts.bv.bvAbstraction = false;
    opts.arith.arithMLTrick = false;
  }

  if (logic.isHigherOrder())
  {
    opts.uf.ufHo = true;
    if (!opts.theory.assignFunctionValues)
    {
      // must assign function values
      opts.theory.assignFunctionValues = true;
    }
  }

  // set all defaults in the quantifiers theory, which includes sygus
  setDefaultsQuantifiers(logic, opts);

  // until bugs 371,431 are fixed
  if (!opts.prop.minisatUseElimWasSetByUser)
  {
    // cannot use minisat elimination for logics where a theory solver
    // introduces new literals into the search. This includes quantifiers
    // (quantifier instantiation), and the lemma schemas used in non-linear
    // and sets. We also can't use it if models are enabled.
    if (logic.isTheoryEnabled(THEORY_SETS) || logic.isTheoryEnabled(THEORY_BAGS)
        || logic.isQuantified() || opts.smt.produceModels
        || opts.smt.produceAssignments || opts.smt.checkModels
        || (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()))
    {
      opts.prop.minisatUseElim = false;
    }
  }

  if (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
      && opts.arith.nlRlvMode != options::NlRlvMode::NONE)
  {
    if (!opts.theory.relevanceFilter)
    {
      if (opts.theory.relevanceFilterWasSetByUser)
      {
        Warning() << "SmtEngine: turning on relevance filtering to support "
                     "--nl-ext-rlv="
                  << opts.arith.nlRlvMode << std::endl;
      }
      // must use relevance filtering techniques
      opts.theory.relevanceFilter = true;
    }
  }

  // For now, these array theory optimizations do not support model-building
  if (opts.smt.produceModels || opts.smt.produceAssignments
      || opts.smt.checkModels)
  {
    opts.arrays.arraysOptimizeLinear = false;
  }

  if (opts.strings.stringFMF && !opts.strings.stringProcessLoopModeWasSetByUser)
  {
    Trace("smt") << "settting stringProcessLoopMode to 'simple' since "
                    "--strings-fmf enabled"
                 << std::endl;
    opts.strings.stringProcessLoopMode = options::ProcessLoopMode::SIMPLE;
  }

  // !!! All options that require disabling models go here
  std::stringstream reasonNoModel;
  if (incompatibleWithModels(opts, reasonNoModel))
  {
    std::string sOptNoModel = reasonNoModel.str();
    if (opts.smt.produceModels)
    {
      if (opts.smt.produceModelsWasSetByUser)
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel << " with model generation.";
        throw OptionException(ss.str());
      }
      Notice() << "SmtEngine: turning off produce-models to support "
               << sOptNoModel << std::endl;
      opts.smt.produceModels = false;
    }
    if (opts.smt.produceAssignments)
    {
      if (opts.smt.produceAssignmentsWasSetByUser)
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel
           << " with model generation (produce-assignments).";
        throw OptionException(ss.str());
      }
      Notice() << "SmtEngine: turning off produce-assignments to support "
               << sOptNoModel << std::endl;
      opts.smt.produceAssignments = false;
    }
    if (opts.smt.checkModels)
    {
      if (opts.smt.checkModelsWasSetByUser)
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel
           << " with model generation (check-models).";
        throw OptionException(ss.str());
      }
      Notice() << "SmtEngine: turning off check-models to support "
               << sOptNoModel << std::endl;
      opts.smt.checkModels = false;
    }
  }

  if (opts.bv.bitblastMode == options::BitblastMode::EAGER
      && !logic.isPure(THEORY_BV) && logic.getLogicString() != "QF_UFBV"
      && logic.getLogicString() != "QF_ABV")
  {
    throw OptionException(
        "Eager bit-blasting does not currently support theory combination. "
        "Note that in a QF_BV problem UF symbols can be introduced for "
        "division. "
        "Try --bv-div-zero-const to interpret division by zero as a constant.");
  }

#ifdef CVC5_USE_POLY
  if (logic == LogicInfo("QF_UFNRA"))
  {
    if (!opts.arith.nlCad && !opts.arith.nlCadWasSetByUser)
    {
      opts.arith.nlCad = true;
      if (!opts.arith.nlExtWasSetByUser)
      {
        opts.arith.nlExt = options::NlExtMode::LIGHT;
      }
      if (!opts.arith.nlRlvModeWasSetByUser)
      {
        opts.arith.nlRlvMode = options::NlRlvMode::INTERLEAVE;
      }
    }
  }
#else
  if (opts.arith.nlCad)
  {
    if (opts.arith.nlCadWasSetByUser)
    {
      std::stringstream ss;
      ss << "Cannot use " << options::arith::nlCad__name
         << " without configuring with --poly.";
      throw OptionException(ss.str());
    }
    else
    {
      Notice() << "Cannot use --" << options::arith::nlCad__name
               << " without configuring with --poly." << std::endl;
      opts.arith.nlCad = false;
      opts.arith.nlExt = options::NlExtMode::FULL;
    }
  }
#endif
}

bool SetDefaults::isSygus(const Options& opts) const
{
  if (language::isLangSygus(opts.base.inputLanguage))
  {
    return true;
  }
  if (!d_isInternalSubsolver)
  {
    if (opts.smt.produceAbducts
        || opts.smt.produceInterpols != options::ProduceInterpols::NONE
        || opts.quantifiers.sygusInference
        || opts.quantifiers.sygusRewSynthInput)
    {
      // since we are trying to recast as sygus, we assume the input is sygus
      return true;
    }
  }
  return false;
}

bool SetDefaults::usesSygus(const Options& opts) const
{
  if (isSygus(opts))
  {
    return true;
  }
  if (!d_isInternalSubsolver && opts.quantifiers.sygusInst)
  {
    // sygus instantiation uses sygus, but it is not a sygus problem
    return true;
  }
  return false;
}

bool SetDefaults::incompatibleWithProofs(const Options& opts,
                                         std::ostream& reason) const
{
  if (opts.quantifiers.globalNegate)
  {
    // When global negate answers "unsat", it is not due to showing a set of
    // formulas is unsat. Thus, proofs do not apply.
    reason << "global-negate";
    return true;
  }
  if (isSygus(opts))
  {
    // When sygus answers "unsat", it is not due to showing a set of
    // formulas is unsat in the standard way. Thus, proofs do not apply.
    reason << "sygus";
    return true;
  }
  return false;
}

bool SetDefaults::incompatibleWithModels(const Options& opts,
                                         std::ostream& reason) const
{
  if (opts.smt.unconstrainedSimpWasSetByUser && opts.smt.unconstrainedSimp)
  {
    reason << "unconstrained-simp";
    return true;
  }
  else if (opts.smt.sortInference)
  {
    reason << "sort-inference";
    return true;
  }
  else if (opts.prop.minisatUseElim)
  {
    reason << "minisat-elimination";
    return true;
  }
  else if (opts.quantifiers.globalNegate)
  {
    reason << "global-negate";
    return true;
  }
  return false;
}

bool SetDefaults::incompatibleWithIncremental(const LogicInfo& logic,
                                              Options& opts,
                                              std::ostream& reason,
                                              std::ostream& suggest) const
{
  if (opts.smt.unconstrainedSimp)
  {
    if (opts.smt.unconstrainedSimpWasSetByUser)
    {
      reason << "unconstrained simplification";
      return true;
    }
    Notice() << "SmtEngine: turning off unconstrained simplification to "
                "support incremental solving"
             << std::endl;
    opts.smt.unconstrainedSimp = false;
  }
  if (opts.bv.bitblastMode == options::BitblastMode::EAGER
      && !logic.isPure(THEORY_BV))
  {
    reason << "eager bit-blasting in non-QF_BV logic";
    suggest << "Try --bitblast=lazy.";
    return true;
  }
  if (opts.quantifiers.sygusInference)
  {
    if (opts.quantifiers.sygusInferenceWasSetByUser)
    {
      reason << "sygus inference";
      return true;
    }
    Notice() << "SmtEngine: turning off sygus inference to support "
                "incremental solving"
             << std::endl;
    opts.quantifiers.sygusInference = false;
  }
  return false;
}

bool SetDefaults::incompatibleWithUnsatCores(Options& opts,
                                             std::ostream& reason) const
{
  if (opts.smt.simplificationMode != options::SimplificationMode::NONE)
  {
    if (opts.smt.simplificationModeWasSetByUser)
    {
      reason << "simplification";
      return true;
    }
    Notice() << "SmtEngine: turning off simplification to support unsat "
                "cores"
             << std::endl;
    opts.smt.simplificationMode = options::SimplificationMode::NONE;
  }

  if (opts.smt.learnedRewrite)
  {
    if (opts.smt.learnedRewriteWasSetByUser)
    {
      reason << "learned rewrites";
      return true;
    }
    Notice() << "SmtEngine: turning off learned rewrites to support "
                "unsat cores\n";
    opts.smt.learnedRewrite = false;
  }

  if (opts.arith.pbRewrites)
  {
    if (opts.arith.pbRewritesWasSetByUser)
    {
      reason << "pseudoboolean rewrites";
      return true;
    }
    Notice() << "SmtEngine: turning off pseudoboolean rewrites to support "
                "unsat cores\n";
    opts.arith.pbRewrites = false;
  }

  if (opts.smt.sortInference)
  {
    if (opts.smt.sortInferenceWasSetByUser)
    {
      reason << "sort inference";
      return true;
    }
    Notice() << "SmtEngine: turning off sort inference to support unsat "
                "cores\n";
    opts.smt.sortInference = false;
  }

  if (opts.quantifiers.preSkolemQuant)
  {
    if (opts.quantifiers.preSkolemQuantWasSetByUser)
    {
      reason << "pre-skolemization";
      return true;
    }
    Notice() << "SmtEngine: turning off pre-skolemization to support "
                "unsat cores\n";
    opts.quantifiers.preSkolemQuant = false;
  }

  if (opts.bv.bitvectorToBool)
  {
    if (opts.bv.bitvectorToBoolWasSetByUser)
    {
      reason << "bv-to-bool";
      return true;
    }
    Notice() << "SmtEngine: turning off bitvector-to-bool to support "
                "unsat cores\n";
    opts.bv.bitvectorToBool = false;
  }

  if (opts.bv.boolToBitvector != options::BoolToBVMode::OFF)
  {
    if (opts.bv.boolToBitvectorWasSetByUser)
    {
      reason << "bool-to-bv != off";
      return true;
    }
    Notice() << "SmtEngine: turning off bool-to-bv to support unsat cores\n";
    opts.bv.boolToBitvector = options::BoolToBVMode::OFF;
  }

  if (opts.bv.bvIntroducePow2)
  {
    if (opts.bv.bvIntroducePow2WasSetByUser)
    {
      reason << "bv-intro-pow2";
      return true;
    }
    Notice() << "SmtEngine: turning off bv-intro-pow2 to support unsat cores";
    opts.bv.bvIntroducePow2 = false;
  }

  if (opts.smt.repeatSimp)
  {
    if (opts.smt.repeatSimpWasSetByUser)
    {
      reason << "repeat-simp";
      return true;
    }
    Notice() << "SmtEngine: turning off repeat-simp to support unsat cores\n";
    opts.smt.repeatSimp = false;
  }

  if (opts.quantifiers.globalNegate)
  {
    if (opts.quantifiers.globalNegateWasSetByUser)
    {
      reason << "global-negate";
      return true;
    }
    Notice() << "SmtEngine: turning off global-negate to support unsat "
                "cores\n";
    opts.quantifiers.globalNegate = false;
  }

  if (opts.bv.bitvectorAig)
  {
    reason << "bitblast-aig";
    return true;
  }

  if (opts.smt.doITESimp)
  {
    reason << "ITE simp";
    return true;
  }
  if (opts.smt.unconstrainedSimp)
  {
    if (opts.smt.unconstrainedSimpWasSetByUser)
    {
      reason << "unconstrained simplification";
      return true;
    }
    Notice() << "SmtEngine: turning off unconstrained simplification to "
                "support unsat cores"
             << std::endl;
    opts.smt.unconstrainedSimp = false;
  }
  return false;
}

bool SetDefaults::safeUnsatCores(const Options& opts) const
{
  // whether we want to force safe unsat cores, i.e., if we are in the default
  // ASSUMPTIONS mode, since other ones are experimental
  return opts.smt.unsatCoresMode == options::UnsatCoresMode::ASSUMPTIONS;
}

void SetDefaults::widenLogic(LogicInfo& logic, Options& opts) const
{
  bool needsUf = false;
  // strings require LIA, UF; widen the logic
  if (logic.isTheoryEnabled(THEORY_STRINGS))
  {
    LogicInfo log(logic.getUnlockedCopy());
    // Strings requires arith for length constraints, and also UF
    needsUf = true;
    if (!logic.isTheoryEnabled(THEORY_ARITH) || logic.isDifferenceLogic())
    {
      Notice()
          << "Enabling linear integer arithmetic because strings are enabled"
          << std::endl;
      log.enableTheory(THEORY_ARITH);
      log.enableIntegers();
      log.arithOnlyLinear();
    }
    else if (!logic.areIntegersUsed())
    {
      Notice() << "Enabling integer arithmetic because strings are enabled"
               << std::endl;
      log.enableIntegers();
    }
    logic = log;
    logic.lock();
  }
  if (opts.bv.bvAbstraction)
  {
    // bv abstraction may require UF
    Notice() << "Enabling UF because bvAbstraction requires it." << std::endl;
    needsUf = true;
  }
  else if (opts.quantifiers.preSkolemQuantNested
           && opts.quantifiers.preSkolemQuantNestedWasSetByUser)
  {
    // if pre-skolem nested is explictly set, then we require UF. If it is
    // not explicitly set, it is disabled below if UF is not present.
    Notice() << "Enabling UF because preSkolemQuantNested requires it."
             << std::endl;
    needsUf = true;
  }
  if (needsUf
      // Arrays, datatypes and sets permit Boolean terms and thus require UF
      || logic.isTheoryEnabled(THEORY_ARRAYS)
      || logic.isTheoryEnabled(THEORY_DATATYPES)
      || logic.isTheoryEnabled(THEORY_SETS)
      || logic.isTheoryEnabled(THEORY_BAGS)
      // Non-linear arithmetic requires UF to deal with division/mod because
      // their expansion introduces UFs for the division/mod-by-zero case.
      // If we are eliminating non-linear arithmetic via solve-int-as-bv,
      // then this is not required, since non-linear arithmetic will be
      // eliminated altogether (or otherwise fail at preprocessing).
      || (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
          && opts.smt.solveIntAsBV == 0)
      // FP requires UF since there are multiple operators that are partially
      // defined (see http://smtlib.cs.uiowa.edu/papers/BTRW15.pdf for more
      // details).
      || logic.isTheoryEnabled(THEORY_FP))
  {
    if (!logic.isTheoryEnabled(THEORY_UF))
    {
      LogicInfo log(logic.getUnlockedCopy());
      if (!needsUf)
      {
        Notice() << "Enabling UF because " << logic << " requires it."
                 << std::endl;
      }
      log.enableTheory(THEORY_UF);
      logic = log;
      logic.lock();
    }
  }
  if (opts.arith.arithMLTrick)
  {
    if (!logic.areIntegersUsed())
    {
      // enable integers
      LogicInfo log(logic.getUnlockedCopy());
      Notice() << "Enabling integers because arithMLTrick requires it."
               << std::endl;
      log.enableIntegers();
      logic = log;
      logic.lock();
    }
  }
}

void SetDefaults::setDefaultsQuantifiers(const LogicInfo& logic,
                                         Options& opts) const
{
  if (logic.hasCardinalityConstraints())
  {
    // must have finite model finding on
    opts.quantifiers.finiteModelFind = true;
  }

  if (opts.quantifiers.instMaxLevel != -1)
  {
    Notice() << "SmtEngine: turning off cbqi to support instMaxLevel"
             << std::endl;
    opts.quantifiers.cegqi = false;
  }

  if ((opts.quantifiers.fmfBoundLazyWasSetByUser
       && opts.quantifiers.fmfBoundLazy)
      || (opts.quantifiers.fmfBoundIntWasSetByUser
          && opts.quantifiers.fmfBoundInt))
  {
    opts.quantifiers.fmfBound = true;
    Trace("smt")
        << "turning on fmf-bound, for fmf-bound-int or fmf-bound-lazy\n";
  }
  // now have determined whether fmfBound is on/off
  // apply fmfBound options
  if (opts.quantifiers.fmfBound)
  {
    if (!opts.quantifiers.mbqiModeWasSetByUser
        || (opts.quantifiers.mbqiMode != options::MbqiMode::NONE
            && opts.quantifiers.mbqiMode != options::MbqiMode::FMC))
    {
      // if bounded integers are set, use no MBQI by default
      opts.quantifiers.mbqiMode = options::MbqiMode::NONE;
    }
    if (!opts.quantifiers.prenexQuantUserWasSetByUser)
    {
      opts.quantifiers.prenexQuant = options::PrenexQuantMode::NONE;
    }
  }
  if (logic.isHigherOrder())
  {
    // if higher-order, then current variants of model-based instantiation
    // cannot be used
    if (opts.quantifiers.mbqiMode != options::MbqiMode::NONE)
    {
      opts.quantifiers.mbqiMode = options::MbqiMode::NONE;
    }
    if (!opts.quantifiers.hoElimStoreAxWasSetByUser)
    {
      // by default, use store axioms only if --ho-elim is set
      opts.quantifiers.hoElimStoreAx = opts.quantifiers.hoElim;
    }
    // Cannot use macros, since lambda lifting and macro elimination are inverse
    // operations.
    if (opts.quantifiers.macrosQuant)
    {
      opts.quantifiers.macrosQuant = false;
    }
    // HOL is incompatible with fmfBound
    if (opts.quantifiers.fmfBound)
    {
      if (opts.quantifiers.fmfBoundWasSetByUser
          || opts.quantifiers.fmfBoundLazyWasSetByUser
          || opts.quantifiers.fmfBoundIntWasSetByUser)
      {
        Notice() << "Disabling bound finite-model finding since it is "
                    "incompatible with HOL.\n";
      }

      opts.quantifiers.fmfBound = false;
      Trace("smt") << "turning off fmf-bound, since HOL\n";
    }
  }
  if (opts.quantifiers.fmfFunWellDefinedRelevant)
  {
    if (!opts.quantifiers.fmfFunWellDefinedWasSetByUser)
    {
      opts.quantifiers.fmfFunWellDefined = true;
    }
  }
  if (opts.quantifiers.fmfFunWellDefined)
  {
    if (!opts.quantifiers.finiteModelFindWasSetByUser)
    {
      opts.quantifiers.finiteModelFind = true;
    }
  }

  // now, have determined whether finite model find is on/off
  // apply finite model finding options
  if (opts.quantifiers.finiteModelFind)
  {
    // apply conservative quantifiers splitting
    if (!opts.quantifiers.quantDynamicSplitWasSetByUser)
    {
      opts.quantifiers.quantDynamicSplit = options::QuantDSplitMode::DEFAULT;
    }
    if (!opts.quantifiers.eMatchingWasSetByUser)
    {
      opts.quantifiers.eMatching = opts.quantifiers.fmfInstEngine;
    }
    if (!opts.quantifiers.instWhenModeWasSetByUser)
    {
      // instantiate only on last call
      if (opts.quantifiers.eMatching)
      {
        opts.quantifiers.instWhenMode = options::InstWhenMode::LAST_CALL;
      }
    }
  }

  // apply sygus options
  // if we are attempting to rewrite everything to SyGuS, use sygus()
  if (usesSygus(opts))
  {
    setDefaultsSygus(opts);
  }
  // counterexample-guided instantiation for non-sygus
  // enable if any possible quantifiers with arithmetic, datatypes or bitvectors
  if ((logic.isQuantified()
       && (logic.isTheoryEnabled(THEORY_ARITH)
           || logic.isTheoryEnabled(THEORY_DATATYPES)
           || logic.isTheoryEnabled(THEORY_BV)
           || logic.isTheoryEnabled(THEORY_FP)))
      || opts.quantifiers.cegqiAll)
  {
    if (!opts.quantifiers.cegqiWasSetByUser)
    {
      opts.quantifiers.cegqi = true;
    }
    // check whether we should apply full cbqi
    if (logic.isPure(THEORY_BV))
    {
      if (!opts.quantifiers.cegqiFullEffortWasSetByUser)
      {
        opts.quantifiers.cegqiFullEffort = true;
      }
    }
  }
  if (opts.quantifiers.cegqi)
  {
    if (logic.isPure(THEORY_ARITH) || logic.isPure(THEORY_BV))
    {
      if (!opts.quantifiers.quantConflictFindWasSetByUser)
      {
        opts.quantifiers.quantConflictFind = false;
      }
      if (!opts.quantifiers.instNoEntailWasSetByUser)
      {
        opts.quantifiers.instNoEntail = false;
      }
      if (!opts.quantifiers.instWhenModeWasSetByUser
          && opts.quantifiers.cegqiModel)
      {
        // only instantiation should happen at last call when model is avaiable
        opts.quantifiers.instWhenMode = options::InstWhenMode::LAST_CALL;
      }
    }
    else
    {
      // only supported in pure arithmetic or pure BV
      opts.quantifiers.cegqiNestedQE = false;
    }
    if (opts.quantifiers.globalNegate)
    {
      if (!opts.quantifiers.prenexQuantWasSetByUser)
      {
        opts.quantifiers.prenexQuant = options::PrenexQuantMode::NONE;
      }
    }
  }
  // implied options...
  if (opts.quantifiers.qcfModeWasSetByUser || opts.quantifiers.qcfTConstraint)
  {
    opts.quantifiers.quantConflictFind = true;
  }
  if (opts.quantifiers.cegqiNestedQE)
  {
    opts.quantifiers.prenexQuantUser = true;
    if (!opts.quantifiers.preSkolemQuantWasSetByUser)
    {
      opts.quantifiers.preSkolemQuant = true;
    }
  }
  // for induction techniques
  if (opts.quantifiers.quantInduction)
  {
    if (!opts.quantifiers.dtStcInductionWasSetByUser)
    {
      opts.quantifiers.dtStcInduction = true;
    }
    if (!opts.quantifiers.intWfInductionWasSetByUser)
    {
      opts.quantifiers.intWfInduction = true;
    }
  }
  if (opts.quantifiers.dtStcInduction)
  {
    // try to remove ITEs from quantified formulas
    if (!opts.quantifiers.iteDtTesterSplitQuantWasSetByUser)
    {
      opts.quantifiers.iteDtTesterSplitQuant = true;
    }
    if (!opts.quantifiers.iteLiftQuantWasSetByUser)
    {
      opts.quantifiers.iteLiftQuant = options::IteLiftQuantMode::ALL;
    }
  }
  if (opts.quantifiers.intWfInduction)
  {
    if (!opts.quantifiers.purifyTriggersWasSetByUser)
    {
      opts.quantifiers.purifyTriggers = true;
    }
  }
  if (opts.quantifiers.conjectureNoFilter)
  {
    if (!opts.quantifiers.conjectureFilterActiveTermsWasSetByUser)
    {
      opts.quantifiers.conjectureFilterActiveTerms = false;
    }
    if (!opts.quantifiers.conjectureFilterCanonicalWasSetByUser)
    {
      opts.quantifiers.conjectureFilterCanonical = false;
    }
    if (!opts.quantifiers.conjectureFilterModelWasSetByUser)
    {
      opts.quantifiers.conjectureFilterModel = false;
    }
  }
  if (opts.quantifiers.conjectureGenPerRoundWasSetByUser)
  {
    if (opts.quantifiers.conjectureGenPerRound > 0)
    {
      opts.quantifiers.conjectureGen = true;
    }
    else
    {
      opts.quantifiers.conjectureGen = false;
    }
  }
  // can't pre-skolemize nested quantifiers without UF theory
  if (!logic.isTheoryEnabled(THEORY_UF) && opts.quantifiers.preSkolemQuant)
  {
    if (!opts.quantifiers.preSkolemQuantNestedWasSetByUser)
    {
      opts.quantifiers.preSkolemQuantNested = false;
    }
  }
  if (!logic.isTheoryEnabled(THEORY_DATATYPES))
  {
    opts.quantifiers.quantDynamicSplit = options::QuantDSplitMode::NONE;
  }
}

void SetDefaults::setDefaultsSygus(Options& opts) const
{
  if (!opts.quantifiers.sygus)
  {
    Trace("smt") << "turning on sygus" << std::endl;
  }
  opts.quantifiers.sygus = true;
  // must use Ferrante/Rackoff for real arithmetic
  if (!opts.quantifiers.cegqiMidpointWasSetByUser)
  {
    opts.quantifiers.cegqiMidpoint = true;
  }
  // must disable cegqi-bv since it may introduce witness terms, which
  // cannot appear in synthesis solutions
  if (!opts.quantifiers.cegqiBvWasSetByUser)
  {
    opts.quantifiers.cegqiBv = false;
  }
  if (opts.quantifiers.sygusRepairConst)
  {
    if (!opts.quantifiers.cegqiWasSetByUser)
    {
      opts.quantifiers.cegqi = true;
    }
  }
  if (opts.quantifiers.sygusInference)
  {
    // optimization: apply preskolemization, makes it succeed more often
    if (!opts.quantifiers.preSkolemQuantWasSetByUser)
    {
      opts.quantifiers.preSkolemQuant = true;
    }
    if (!opts.quantifiers.preSkolemQuantNestedWasSetByUser)
    {
      opts.quantifiers.preSkolemQuantNested = true;
    }
  }
  // counterexample-guided instantiation for sygus
  if (!opts.quantifiers.cegqiSingleInvModeWasSetByUser)
  {
    opts.quantifiers.cegqiSingleInvMode = options::CegqiSingleInvMode::USE;
  }
  if (!opts.quantifiers.quantConflictFindWasSetByUser)
  {
    opts.quantifiers.quantConflictFind = false;
  }
  if (!opts.quantifiers.instNoEntailWasSetByUser)
  {
    opts.quantifiers.instNoEntail = false;
  }
  if (!opts.quantifiers.cegqiFullEffortWasSetByUser)
  {
    // should use full effort cbqi for single invocation and repair const
    opts.quantifiers.cegqiFullEffort = true;
  }
  if (opts.quantifiers.sygusRew)
  {
    opts.quantifiers.sygusRewSynth = true;
    opts.quantifiers.sygusRewVerify = true;
  }
  if (opts.quantifiers.sygusRewSynthInput)
  {
    // If we are using synthesis rewrite rules from input, we use
    // sygusRewSynth after preprocessing. See passes/synth_rew_rules.h for
    // details on this technique.
    opts.quantifiers.sygusRewSynth = true;
    // we should not use the extended rewriter, since we are interested
    // in rewrites that are not in the main rewriter
    if (!opts.quantifiers.sygusExtRewWasSetByUser)
    {
      opts.quantifiers.sygusExtRew = false;
    }
  }
  // Whether we must use "basic" sygus algorithms. A non-basic sygus algorithm
  // is one that is specialized for returning a single solution. Non-basic
  // sygus algorithms currently include the PBE solver, UNIF+PI, static
  // template inference for invariant synthesis, and single invocation
  // techniques.
  bool reqBasicSygus = false;
  if (opts.smt.produceAbducts)
  {
    // if doing abduction, we should filter strong solutions
    if (!opts.quantifiers.sygusFilterSolModeWasSetByUser)
    {
      opts.quantifiers.sygusFilterSolMode = options::SygusFilterSolMode::STRONG;
    }
    // we must use basic sygus algorithms, since e.g. we require checking
    // a sygus side condition for consistency with axioms.
    reqBasicSygus = true;
  }
  if (opts.quantifiers.sygusRewSynth || opts.quantifiers.sygusRewVerify
      || opts.quantifiers.sygusQueryGen)
  {
    // rewrite rule synthesis implies that sygus stream must be true
    opts.quantifiers.sygusStream = true;
  }
  if (opts.quantifiers.sygusStream || opts.base.incrementalSolving)
  {
    // Streaming and incremental mode are incompatible with techniques that
    // focus the search towards finding a single solution.
    reqBasicSygus = true;
  }
  // Now, disable options for non-basic sygus algorithms, if necessary.
  if (reqBasicSygus)
  {
    if (!opts.quantifiers.sygusUnifPbeWasSetByUser)
    {
      opts.quantifiers.sygusUnifPbe = false;
    }
    if (opts.quantifiers.sygusUnifPiWasSetByUser)
    {
      opts.quantifiers.sygusUnifPi = options::SygusUnifPiMode::NONE;
    }
    if (!opts.quantifiers.sygusInvTemplModeWasSetByUser)
    {
      opts.quantifiers.sygusInvTemplMode = options::SygusInvTemplMode::NONE;
    }
    if (!opts.quantifiers.cegqiSingleInvModeWasSetByUser)
    {
      opts.quantifiers.cegqiSingleInvMode = options::CegqiSingleInvMode::NONE;
    }
  }
  // do not miniscope
  if (!opts.quantifiers.miniscopeQuantWasSetByUser)
  {
    opts.quantifiers.miniscopeQuant = false;
  }
  if (!opts.quantifiers.miniscopeQuantFreeVarWasSetByUser)
  {
    opts.quantifiers.miniscopeQuantFreeVar = false;
  }
  if (!opts.quantifiers.quantSplitWasSetByUser)
  {
    opts.quantifiers.quantSplit = false;
  }
  // do not do macros
  if (!opts.quantifiers.macrosQuantWasSetByUser)
  {
    opts.quantifiers.macrosQuant = false;
  }
}
void SetDefaults::setDefaultDecisionMode(const LogicInfo& logic,
                                         Options& opts) const
{
  // Set decision mode based on logic (if not set by user)
  if (opts.decision.decisionModeWasSetByUser)
  {
    return;
  }
  options::DecisionMode decMode =
      // anything that uses sygus uses internal
      usesSygus(opts) ? options::DecisionMode::INTERNAL :
                      // ALL or its supersets
          logic.hasEverything()
              ? options::DecisionMode::JUSTIFICATION
              : (  // QF_BV
                    (not logic.isQuantified() && logic.isPure(THEORY_BV)) ||
                            // QF_AUFBV or QF_ABV or QF_UFBV
                            (not logic.isQuantified()
                             && (logic.isTheoryEnabled(THEORY_ARRAYS)
                                 || logic.isTheoryEnabled(THEORY_UF))
                             && logic.isTheoryEnabled(THEORY_BV))
                            ||
                            // QF_AUFLIA (and may be ends up enabling
                            // QF_AUFLRA?)
                            (not logic.isQuantified()
                             && logic.isTheoryEnabled(THEORY_ARRAYS)
                             && logic.isTheoryEnabled(THEORY_UF)
                             && logic.isTheoryEnabled(THEORY_ARITH))
                            ||
                            // QF_LRA
                            (not logic.isQuantified()
                             && logic.isPure(THEORY_ARITH) && logic.isLinear()
                             && !logic.isDifferenceLogic()
                             && !logic.areIntegersUsed())
                            ||
                            // Quantifiers
                            logic.isQuantified() ||
                            // Strings
                            logic.isTheoryEnabled(THEORY_STRINGS)
                        ? options::DecisionMode::JUSTIFICATION
                        : options::DecisionMode::INTERNAL);

  bool stoponly =
      // ALL or its supersets
      logic.hasEverything() || logic.isTheoryEnabled(THEORY_STRINGS)
          ? false
          : (  // QF_AUFLIA
                (not logic.isQuantified()
                 && logic.isTheoryEnabled(THEORY_ARRAYS)
                 && logic.isTheoryEnabled(THEORY_UF)
                 && logic.isTheoryEnabled(THEORY_ARITH))
                        ||
                        // QF_LRA
                        (not logic.isQuantified() && logic.isPure(THEORY_ARITH)
                         && logic.isLinear() && !logic.isDifferenceLogic()
                         && !logic.areIntegersUsed())
                    ? true
                    : false);

  opts.decision.decisionMode = decMode;
  if (stoponly)
  {
    if (opts.decision.decisionMode == options::DecisionMode::JUSTIFICATION)
    {
      opts.decision.decisionMode = options::DecisionMode::STOPONLY;
    }
    else
    {
      Assert(opts.decision.decisionMode == options::DecisionMode::INTERNAL);
    }
  }
  Trace("smt") << "setting decision mode to " << opts.decision.decisionMode
               << std::endl;
}

}  // namespace smt
}  // namespace cvc5

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
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "smt/logic_exception.h"
#include "theory/theory.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

SetDefaults::SetDefaults(Env& env, bool isInternalSubsolver)
    : EnvObj(env), d_isInternalSubsolver(isInternalSubsolver)
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
  if (opts.driver.dumpDifficulty)
  {
    opts.smt.produceDifficulty = true;
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
      notifyModifyOption(
          "unsatCoresMode", "assumptions", "enabling unsat cores");
    }
    opts.smt.unsatCoresMode = options::UnsatCoresMode::ASSUMPTIONS;
  }
  // if check-proofs, dump-proofs, or proof-mode=full, then proofs being fully
  // enabled is implied
  if (opts.smt.checkProofs || opts.driver.dumpProofs
      || opts.smt.proofMode == options::ProofMode::FULL)
  {
    opts.smt.produceProofs = true;
  }

  // this check assumes the user has requested *full* proofs
  if (opts.smt.produceProofs)
  {
    // if the user requested proofs, proof mode is full
    opts.smt.proofMode = options::ProofMode::FULL;
    // unsat cores are available due to proofs being enabled
    if (opts.smt.unsatCoresMode != options::UnsatCoresMode::SAT_PROOF)
    {
      if (opts.smt.unsatCoresModeWasSetByUser)
      {
        notifyModifyOption("unsatCoresMode", "sat-proof", "enabling proofs");
      }
      opts.smt.unsatCores = true;
      opts.smt.unsatCoresMode = options::UnsatCoresMode::SAT_PROOF;
    }
  }
  if (!opts.smt.produceProofs)
  {
    if (opts.smt.proofMode != options::ProofMode::OFF)
    {
      // if (expert) user set proof mode to something other than off, enable
      // proofs
      opts.smt.produceProofs = true;
    }
    // if proofs weren't enabled by user, and we are producing difficulty
    if (opts.smt.produceDifficulty)
    {
      opts.smt.produceProofs = true;
      // ensure at least preprocessing proofs are enabled
      if (opts.smt.proofMode == options::ProofMode::OFF)
      {
        opts.smt.proofMode = options::ProofMode::PP_ONLY;
      }
    }
    // if proofs weren't enabled by user, and we are producing unsat cores
    if (opts.smt.unsatCores)
    {
      opts.smt.produceProofs = true;
      if (opts.smt.unsatCoresMode == options::UnsatCoresMode::SAT_PROOF)
      {
        // if requested to be based on proofs, we produce (preprocessing +) SAT
        // proofs
        opts.smt.proofMode = options::ProofMode::SAT;
      }
      else if (opts.smt.proofMode == options::ProofMode::OFF)
      {
        // otherwise, we always produce preprocessing proofs
        opts.smt.proofMode = options::ProofMode::PP_ONLY;
      }
    }
  }

  // if unsat cores are disabled, then unsat cores mode should be OFF. Similarly
  // for proof mode.
  Assert(opts.smt.unsatCores
         == (opts.smt.unsatCoresMode != options::UnsatCoresMode::OFF));
  Assert(opts.smt.produceProofs
         == (opts.smt.proofMode != options::ProofMode::OFF));

  // if we requiring disabling proofs, disable them now
  if (opts.smt.produceProofs)
  {
    std::stringstream reasonNoProofs;
    if (incompatibleWithProofs(opts, reasonNoProofs))
    {
      std::stringstream ss;
      ss << reasonNoProofs.str() << " not supported with proofs or unsat cores";
      throw OptionException(ss.str());
    }
  }
  if (d_isInternalSubsolver)
  {
    // these options must be disabled on internal subsolvers, as they are
    // used by the user to rephrase the input.
    opts.quantifiers.sygusInference = false;
    opts.quantifiers.sygusRewSynthInput = false;
  }
}

void SetDefaults::finalizeLogic(LogicInfo& logic, Options& opts) const
{
  if (opts.quantifiers.sygusInstWasSetByUser)
  {
    if (isSygus(opts))
    {
      throw OptionException(std::string(
          "SyGuS instantiation quantifiers module cannot be enabled "
          "for SyGuS inputs."));
    }
  }
  else if (!isSygus(opts) && logic.isQuantified()
           && (logic.isPure(THEORY_FP)
               || (logic.isPure(THEORY_ARITH) && !logic.isLinear()
                   && logic.areIntegersUsed()))
           && !opts.base.incrementalSolving)
  {
    opts.quantifiers.sygusInst = true;
  }

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
      notifyModifyOption("bitblastMode", "lazy", "model generation");
      opts.bv.bitblastMode = options::BitblastMode::LAZY;
    }
    else if (!opts.base.incrementalSolving)
    {
      opts.smt.ackermann = true;
    }
  }

  if (opts.smt.solveIntAsBV > 0)
  {
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
    notifyModifyOption("ackermann", "false", "model generation");
    opts.smt.ackermann = false;
  }

  if (opts.smt.ackermann)
  {
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

  // Set default options associated with strings-exp. We also set these options
  // if we are using eager string preprocessing, which may introduce quantified
  // formulas at preprocess time.
  //
  // We don't want to set this option when we are in logics that contain ALL.
  //
  // We also must enable stringExp if reElim is aggressive, since this
  // introduces bounded quantifiers during preprocessing.
  if ((!logic.hasEverything() && logic.isTheoryEnabled(THEORY_STRINGS))
      || opts.strings.regExpElim == options::RegExpElimMode::AGG)
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

  if (opts.arrays.arraysExp)
  {
    if (!logic.isQuantified())
    {
      logic = logic.getUnlockedCopy();
      logic.enableQuantifiers();
      logic.lock();
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

  // widen the logic
  widenLogic(logic, opts);

  // check if we have any options that are not supported with quantified logics
  if (logic.isQuantified())
  {
    std::stringstream reasonNoQuant;
    if (incompatibleWithQuantifiers(opts, reasonNoQuant))
    {
      std::stringstream ss;
      ss << reasonNoQuant.str() << " not supported in quantified logics.";
      throw OptionException(ss.str());
    }
  }
}

void SetDefaults::setDefaultsPost(const LogicInfo& logic, Options& opts) const
{
  if (!opts.smt.produceAssertions)
  {
    verbose(1) << "SolverEngine: turning on produce-assertions." << std::endl;
    opts.smt.produceAssertions = true;
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
      verbose(1)
          << "SolverEngine: turning off bool-to-bitvector to support CBQI BV"
          << std::endl;
      opts.bv.boolToBitvector = options::BoolToBVMode::OFF;
    }
  }

  // cases where we need produce models
  if (!opts.smt.produceModels
      && (opts.smt.produceAssignments || usesSygus(opts)))
  {
    verbose(1) << "SolverEngine: turning on produce-models" << std::endl;
    opts.smt.produceModels = true;
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
    d_env.setUninterpretedSortOwner(THEORY_ARRAYS);
  }
  else
  {
    d_env.setUninterpretedSortOwner(THEORY_UF);
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

  /* Disable bit-level propagation by default for the BITBLAST solver. */
  if (opts.bv.bvSolver == options::BVSolver::BITBLAST)
  {
    opts.bv.bitvectorPropagate = false;
  }

  if (opts.bv.boolToBitvector == options::BoolToBVMode::ALL
      && !logic.isTheoryEnabled(THEORY_BV))
  {
    if (opts.bv.boolToBitvectorWasSetByUser)
    {
      throw OptionException(
          "bool-to-bv=all not supported for non-bitvector logics.");
    }
    verbose(1) << "SolverEngine: turning off bool-to-bv for non-bv logic: "
               << logic.getLogicString() << std::endl;
    opts.bv.boolToBitvector = options::BoolToBVMode::OFF;
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
  if (!opts.arith.nlRlvAssertBoundsWasSetByUser)
  {
    // use bound inference to determine when bounds are irrelevant only when
    // the logic is quantifier-free
    opts.arith.nlRlvAssertBounds = !logic.isQuantified();
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

  if (logic.isHigherOrder())
  {
    if (!opts.theory.assignFunctionValues)
    {
      // must assign function values
      opts.theory.assignFunctionValues = true;
    }
  }

  // set all defaults in the quantifiers theory, which includes sygus
  setDefaultsQuantifiers(logic, opts);

  // shared selectors are generally not good to combine with standard
  // quantifier techniques e.g. E-matching
  if (!opts.datatypes.dtSharedSelectorsWasSetByUser)
  {
    if (logic.isQuantified() && !usesSygus(opts))
    {
      Trace("smt")
          << "Disabling shared selectors for quantified logic without SyGuS"
          << std::endl;
      opts.datatypes.dtSharedSelectors = false;
    }
  }

  if (!opts.prop.minisatSimpModeWasSetByUser
      && opts.prop.minisatSimpMode == options::MinisatSimpMode::ALL)
  {
    // cannot use minisat variable elimination for logics where a theory solver
    // introduces new literals into the search. This includes quantifiers
    // (quantifier instantiation), and the lemma schemas used in non-linear
    // and sets. We also can't use it if models are enabled.
    if (logic.isTheoryEnabled(THEORY_SETS) || logic.isTheoryEnabled(THEORY_BAGS)
        || logic.isQuantified() || opts.smt.produceModels
        || opts.smt.produceAssignments || opts.smt.checkModels
        || (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()))
    {
      opts.prop.minisatSimpMode = options::MinisatSimpMode::CLAUSE_ELIM;
    }
  }

  if (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
      && opts.arith.nlRlvMode != options::NlRlvMode::NONE)
  {
    if (!opts.theory.relevanceFilter)
    {
      if (opts.theory.relevanceFilterWasSetByUser)
      {
        Trace("smt") << "SolverEngine: turning on relevance filtering to support "
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
      verbose(1) << "SolverEngine: turning off produce-models to support "
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
      verbose(1) << "SolverEngine: turning off produce-assignments to support "
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
      verbose(1) << "SolverEngine: turning off check-models to support "
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
    if (!opts.arith.nlCov && !opts.arith.nlCovWasSetByUser)
    {
      opts.arith.nlCov = true;
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
  else if (logic.isQuantified() && logic.isTheoryEnabled(theory::THEORY_ARITH)
           && logic.areRealsUsed() && !logic.areIntegersUsed())
  {
    if (!opts.arith.nlCov && !opts.arith.nlCovWasSetByUser)
    {
      opts.arith.nlCov = true;
      if (!opts.arith.nlExtWasSetByUser)
      {
        opts.arith.nlExt = options::NlExtMode::LIGHT;
      }
    }
  }
#else
  if (opts.arith.nlCov)
  {
    if (opts.arith.nlCovWasSetByUser)
    {
      throw OptionException(
          "Cannot use --nl-cov without configuring with --poly.");
    }
    else
    {
      verbose(1) << "Cannot use --nl-cov without configuring with --poly."
                 << std::endl;
      opts.arith.nlCov = false;
      opts.arith.nlExt = options::NlExtMode::FULL;
    }
  }
#endif
  if (logic.isTheoryEnabled(theory::THEORY_ARITH) && logic.areTranscendentalsUsed())
  {
      if (!opts.arith.nlExtWasSetByUser)
      {
        opts.arith.nlExt = options::NlExtMode::FULL;
      }
  }
}

bool SetDefaults::isSygus(const Options& opts) const
{
  if (opts.quantifiers.sygus)
  {
    return true;
  }
  if (!d_isInternalSubsolver)
  {
    if (opts.smt.produceAbducts || opts.smt.interpolants
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

bool SetDefaults::usesInputConversion(const Options& opts,
                                      std::ostream& reason) const
{
  if (opts.smt.solveBVAsInt != options::SolveBVAsIntMode::OFF)
  {
    reason << "solveBVAsInt";
    return true;
  }
  if (opts.smt.solveIntAsBV > 0)
  {
    reason << "solveIntAsBV";
    return true;
  }
  if (opts.smt.solveRealAsInt)
  {
    reason << "solveRealAsInt";
    return true;
  }
  return false;
}

bool SetDefaults::incompatibleWithProofs(Options& opts,
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
    // we don't support proofs with SyGuS. One issue is that SyGuS evaluation
    // functions are incompatible with our equality proofs. Moreover, enabling
    // proofs for sygus (sub)solvers is irrelevant, since they are not given
    // check-sat queries.
    reason << "sygus";
    return true;
  }
  // options that are automatically set to support proofs
  if (opts.bv.bvAssertInput)
  {
    verbose(1)
        << "Disabling bv-assert-input since it is incompatible with proofs."
        << std::endl;
    opts.bv.bvAssertInput = false;
  }
  // If proofs are required and the user did not specify a specific BV solver,
  // we make sure to use the proof producing BITBLAST_INTERNAL solver.
  if (opts.bv.bvSolver != options::BVSolver::BITBLAST_INTERNAL
      && !opts.bv.bvSolverWasSetByUser)
  {
    verbose(1) << "Forcing internal bit-vector solver due to proof production."
               << std::endl;
    opts.bv.bvSolver = options::BVSolver::BITBLAST_INTERNAL;
  }
  if (opts.arith.nlCovVarElim && !opts.arith.nlCovVarElimWasSetByUser)
  {
    verbose(1)
        << "Disabling nl-cov-var-elim since it is incompatible with proofs."
        << std::endl;
    opts.arith.nlCovVarElim = false;
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
  else if (opts.prop.minisatSimpMode == options::MinisatSimpMode::ALL)
  {
    reason << "minisat-simplification";
    return true;
  }
  else if (opts.quantifiers.globalNegate)
  {
    reason << "global-negate";
    return true;
  }
  else if (opts.arrays.arraysWeakEquivalence)
  {
    reason << "arrays-weak-equiv";
    return true;
  }
  return false;
}

bool SetDefaults::incompatibleWithIncremental(const LogicInfo& logic,
                                              Options& opts,
                                              std::ostream& reason,
                                              std::ostream& suggest) const
{
  if (opts.smt.ackermann)
  {
    reason << "ackermann";
    return true;
  }
  if (opts.smt.unconstrainedSimp)
  {
    if (opts.smt.unconstrainedSimpWasSetByUser)
    {
      reason << "unconstrained simplification";
      return true;
    }
    notifyModifyOption("unconstrainedSimp", "false", "incremental solving");
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
    notifyModifyOption("sygusInference", "false", "incremental solving");
    opts.quantifiers.sygusInference = false;
  }
  if (opts.quantifiers.sygusInst)
  {
    if (opts.quantifiers.sygusInstWasSetByUser)
    {
      reason << "sygus inst";
      return true;
    }
    notifyModifyOption("sygusInst", "false", "incremental solving");
    opts.quantifiers.sygusInst = false;
  }
  if (opts.smt.solveIntAsBV > 0)
  {
    reason << "solveIntAsBV";
    return true;
  }

  // disable modes not supported by incremental
  notifyModifyOption("sortInference", "false", "incremental solving");
  opts.smt.sortInference = false;
  opts.uf.ufssFairnessMonotone = false;
  notifyModifyOption("globalNegate", "false", "incremental solving");
  opts.quantifiers.globalNegate = false;
  notifyModifyOption("cegqiNestedQE", "false", "incremental solving");
  opts.quantifiers.cegqiNestedQE = false;
  opts.arith.arithMLTrick = false;

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
    notifyModifyOption("simplificationMode", "none", "unsat cores");
    opts.smt.simplificationMode = options::SimplificationMode::NONE;
  }

  if (opts.smt.learnedRewrite)
  {
    if (opts.smt.learnedRewriteWasSetByUser)
    {
      reason << "learned rewrites";
      return true;
    }
    notifyModifyOption("learnedRewrite", "false", "unsat cores");
    opts.smt.learnedRewrite = false;
  }

  if (opts.arith.pbRewrites)
  {
    if (opts.arith.pbRewritesWasSetByUser)
    {
      reason << "pseudoboolean rewrites";
      return true;
    }
    notifyModifyOption("pbRewrites", "false", "unsat cores");
    opts.arith.pbRewrites = false;
  }

  if (opts.smt.sortInference)
  {
    if (opts.smt.sortInferenceWasSetByUser)
    {
      reason << "sort inference";
      return true;
    }
    notifyModifyOption("sortInference", "false", "unsat cores");
    opts.smt.sortInference = false;
  }

  if (opts.quantifiers.preSkolemQuant != options::PreSkolemQuantMode::OFF)
  {
    if (opts.quantifiers.preSkolemQuantWasSetByUser)
    {
      reason << "pre-skolemization";
      return true;
    }
    notifyModifyOption("preSkolemQuant", "off", "unsat cores");
    opts.quantifiers.preSkolemQuant = options::PreSkolemQuantMode::OFF;
  }

  if (opts.bv.bitvectorToBool)
  {
    if (opts.bv.bitvectorToBoolWasSetByUser)
    {
      reason << "bv-to-bool";
      return true;
    }
    notifyModifyOption("bitvectorToBool", "false", "unsat cores");
    opts.bv.bitvectorToBool = false;
  }

  if (opts.bv.boolToBitvector != options::BoolToBVMode::OFF)
  {
    if (opts.bv.boolToBitvectorWasSetByUser)
    {
      reason << "bool-to-bv != off";
      return true;
    }
    notifyModifyOption("boolToBitvector", "off", "unsat cores");
    opts.bv.boolToBitvector = options::BoolToBVMode::OFF;
  }

  if (opts.bv.bvIntroducePow2)
  {
    if (opts.bv.bvIntroducePow2WasSetByUser)
    {
      reason << "bv-intro-pow2";
      return true;
    }
    notifyModifyOption("bvIntroducePow2", "false", "unsat cores");
    opts.bv.bvIntroducePow2 = false;
  }

  if (opts.smt.repeatSimp)
  {
    if (opts.smt.repeatSimpWasSetByUser)
    {
      reason << "repeat-simp";
      return true;
    }
    notifyModifyOption("repeatSimp", "false", "unsat cores");
    opts.smt.repeatSimp = false;
  }

  if (opts.quantifiers.globalNegate)
  {
    if (opts.quantifiers.globalNegateWasSetByUser)
    {
      reason << "global-negate";
      return true;
    }
    notifyModifyOption("globalNegate", "false", "unsat cores");
    opts.quantifiers.globalNegate = false;
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
    notifyModifyOption("unconstrainedSimp", "false", "unsat cores");
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

bool SetDefaults::incompatibleWithSygus(Options& opts,
                                        std::ostream& reason) const
{
  // sygus should not be combined with preprocessing passes that convert the
  // input
  if (usesInputConversion(opts, reason))
  {
    return true;
  }
  return false;
}

bool SetDefaults::incompatibleWithQuantifiers(Options& opts,
                                              std::ostream& reason) const
{
  if (opts.smt.ackermann)
  {
    reason << "ackermann";
    return true;
  }
  if (opts.arith.nlRlvMode != options::NlRlvMode::NONE)
  {
    // Theory relevance is incompatible with CEGQI and SyQI, since there is no
    // appropriate policy for the relevance of counterexample lemmas (when their
    // guard is entailed to be false, the entire lemma is relevant, not just the
    // guard). Hence, we throw an option exception if quantifiers are enabled.
    reason << "--nl-ext-rlv";
    return true;
  }
  return false;
}

void SetDefaults::widenLogic(LogicInfo& logic, const Options& opts) const
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
      verbose(1)
          << "Enabling linear integer arithmetic because strings are enabled"
          << std::endl;
      log.enableTheory(THEORY_ARITH);
      log.enableIntegers();
      log.arithOnlyLinear();
    }
    else if (!logic.areIntegersUsed())
    {
      verbose(1) << "Enabling integer arithmetic because strings are enabled"
                 << std::endl;
      log.enableIntegers();
    }
    logic = log;
    logic.lock();
  }
  if (opts.quantifiers.preSkolemQuantNested
      && opts.quantifiers.preSkolemQuantNestedWasSetByUser)
  {
    // if pre-skolem nested is explictly set, then we require UF. If it is
    // not explicitly set, it is disabled below if UF is not present.
    verbose(1) << "Enabling UF because preSkolemQuantNested requires it."
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
        verbose(1) << "Enabling UF because " << logic << " requires it."
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
      verbose(1) << "Enabling integers because arithMLTrick requires it."
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
  if (opts.quantifiers.fullSaturateQuant)
  {
    Trace("smt") << "enabling enum-inst for full-saturate-quant" << std::endl;
    opts.quantifiers.enumInst = true;
  }
  if (opts.arrays.arraysExp)
  {
    // Allows to answer sat more often by default.
    if (!opts.quantifiers.fmfBoundWasSetByUser)
    {
      notifyModifyOption("fmfBound", "true", "arrays-exp");
      opts.quantifiers.fmfBound = true;
    }
  }
  if (logic.hasCardinalityConstraints())
  {
    // must have finite model finding on
    opts.quantifiers.finiteModelFind = true;
  }

  if (opts.quantifiers.instMaxLevel != -1)
  {
    verbose(1) << "SolverEngine: turning off cbqi to support instMaxLevel"
               << std::endl;
    opts.quantifiers.cegqi = false;
  }

  if (opts.quantifiers.fmfBoundLazyWasSetByUser
       && opts.quantifiers.fmfBoundLazy)
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
      // do not use E-matching by default. For E-matching + FMF, the user should
      // specify --finite-model-find --e-matching.
      opts.quantifiers.eMatching = false;
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
  if (isSygus(opts))
  {
    std::stringstream reasonNoSygus;
    if (incompatibleWithSygus(opts, reasonNoSygus))
    {
      std::stringstream ss;
      ss << reasonNoSygus.str() << " not supported in sygus.";
      throw OptionException(ss.str());
    }
    // now, set defaults based on sygus
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
      if (!opts.quantifiers.conflictBasedInstWasSetByUser)
      {
        opts.quantifiers.conflictBasedInst = false;
      }
      if (!opts.quantifiers.instNoEntailWasSetByUser)
      {
        opts.quantifiers.instNoEntail = false;
      }
      if (!opts.quantifiers.instWhenModeWasSetByUser)
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
  if (opts.quantifiers.cbqiModeWasSetByUser || opts.quantifiers.cbqiTConstraint)
  {
    opts.quantifiers.conflictBasedInst = true;
  }
  if (opts.quantifiers.cegqiNestedQE)
  {
    opts.quantifiers.prenexQuantUser = true;
    if (!opts.quantifiers.preSkolemQuantWasSetByUser)
    {
      opts.quantifiers.preSkolemQuant = options::PreSkolemQuantMode::ON;
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
  if (!logic.isTheoryEnabled(THEORY_UF)
      && opts.quantifiers.preSkolemQuant != options::PreSkolemQuantMode::OFF)
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
    notifyModifyOption("sygus", "true", "");
    opts.quantifiers.sygus = true;
  }
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
      opts.quantifiers.preSkolemQuant = options::PreSkolemQuantMode::ON;
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
  if (!opts.quantifiers.conflictBasedInstWasSetByUser)
  {
    opts.quantifiers.conflictBasedInst = false;
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
  if (opts.quantifiers.sygusRewSynthInput)
  {
    // If we are using synthesis rewrite rules from input, we use
    // sygusRewSynth after preprocessing. See passes/synth_rew_rules.h for
    // details on this technique.
    opts.quantifiers.sygusRewSynth = true;
    // we should not use the extended rewriter, since we are interested
    // in rewrites that are not in the main rewriter
    if (!opts.datatypes.sygusRewriterWasSetByUser)
    {
      opts.datatypes.sygusRewriter = options::SygusRewriterMode::BASIC;
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
      || opts.quantifiers.sygusQueryGen != options::SygusQueryGenMode::NONE)
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
    opts.quantifiers.miniscopeQuant = options::MiniscopeQuantMode::OFF;
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

void SetDefaults::notifyModifyOption(const std::string& x,
                                     const std::string& val,
                                     const std::string& reason) const
{
  verbose(1) << "SetDefaults: setting " << x << " to " << val;
  if (!reason.empty())
  {
    verbose(1) << " due to " << reason;
  }
  verbose(1) << std::endl;
}

}  // namespace smt
}  // namespace cvc5::internal

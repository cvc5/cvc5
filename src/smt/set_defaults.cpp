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
#include "options/open_ostream.h"
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

void setDefaults(LogicInfo& logic, bool isInternalSubsolver)
{
  // implied options
  if (options::debugCheckModels())
  {
    Notice() << "SmtEngine: setting checkModel" << std::endl;
    Options::current()->set(options::checkModels, true);
  }
  if (options::checkModels() || options::dumpModels())
  {
    Notice() << "SmtEngine: setting produceModels" << std::endl;
    Options::current()->set(options::produceModels, true);
  }
  if (options::checkModels())
  {
    Notice() << "SmtEngine: setting produceAssignments" << std::endl;
    Options::current()->set(options::produceAssignments, true);
  }
  if (options::dumpUnsatCoresFull())
  {
    Notice() << "SmtEngine: setting dumpUnsatCores" << std::endl;
    Options::current()->set(options::dumpUnsatCores, true);
  }
  if ((options::unsatCores() && options::unsatCoresNew())
      || (options::checkUnsatCores() && options::checkUnsatCoresNew()))
  {
    AlwaysAssert(false) << "Can't have both unsat cores modes, pick one.\n";
  }
  if (options::checkUnsatCores())
  {
    Options::current()->set(options::unsatCores, true);
  }
  if (options::checkUnsatCoresNew())
  {
    Options::current()->set(options::unsatCoresNew, true);
  }
  if (options::dumpUnsatCores() || options::unsatAssumptions())
  {
    if (!options::unsatCoresNew())
    {
      Notice() << "SmtEngine: setting unsatCores" << std::endl;
      Options::current()->set(options::unsatCores, true);
    }
  }
  if (options::unsatCoresNew()
      && ((options::produceProofs() && Options::current()->wasSetByUser(options::produceProofs))
          || (options::checkProofs() && Options::current()->wasSetByUser(options::checkProofs))
          || (options::dumpProofs() && Options::current()->wasSetByUser(options::dumpProofs))))
  {
    AlwaysAssert(false) << "Can't properly produce proofs and have the new "
                           "unsat cores simultaneously.\n";
  }
  if (options::checkProofs() || options::unsatCoresNew()
      || options::dumpProofs())
  {
    Notice() << "SmtEngine: setting proof" << std::endl;
    Options::current()->set(options::produceProofs, true);
  }
  if (Options::current()->wasSetByUser(options::bitvectorAigSimplifications))
  {
    Notice() << "SmtEngine: setting bitvectorAig" << std::endl;
    Options::current()->set(options::bitvectorAig, true);
  }
  if (Options::current()->wasSetByUser(options::bitvectorAlgebraicBudget))
  {
    Notice() << "SmtEngine: setting bitvectorAlgebraicSolver" << std::endl;
    Options::current()->set(options::bitvectorAlgebraicSolver, true);
  }

  bool isSygus = language::isInputLangSygus(options::inputLanguage());
  bool usesSygus = isSygus;

  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    if (options::produceModels()
        && (logic.isTheoryEnabled(THEORY_ARRAYS)
            || logic.isTheoryEnabled(THEORY_UF)))
    {
      if (Options::current()->wasSetByUser(options::bitblastMode)
          || Options::current()->wasSetByUser(options::produceModels))
      {
        throw OptionException(std::string(
            "Eager bit-blasting currently does not support model generation "
            "for the combination of bit-vectors with arrays or uinterpreted "
            "functions. Try --bitblast=lazy"));
      }
      Notice() << "SmtEngine: setting bit-blast mode to lazy to support model"
               << "generation" << std::endl;
      Options::current()->set(options::bitblastMode, options::BitblastMode::LAZY);
    }
    else if (!options::incrementalSolving())
    {
      Options::current()->set(options::ackermann, true);
    }

    if (options::incrementalSolving() && !logic.isPure(THEORY_BV))
    {
      throw OptionException(
          "Incremental eager bit-blasting is currently "
          "only supported for QF_BV. Try --bitblast=lazy.");
    }

    // Force lazy solver since we don't handle EAGER_ATOMS in the
    // BVSolver::BITBLAST solver.
    Options::current()->set(options::bvSolver, options::BVSolver::LAZY);
  }

  /* Only BVSolver::LAZY natively supports int2bv and nat2bv, for other solvers
   * we need to eagerly eliminate the operators. */
  if (options::bvSolver() == options::BVSolver::SIMPLE
      || options::bvSolver() == options::BVSolver::BITBLAST)
  {
    Options::current()->set(options::bvLazyReduceExtf, false);
    Options::current()->set(options::bvLazyRewriteExtf, false);
  }

  /* Disable bit-level propagation by default for the BITBLAST solver. */
  if (options::bvSolver() == options::BVSolver::BITBLAST)
  {
    Options::current()->set(options::bitvectorPropagate, false);
  }

  if (options::solveIntAsBV() > 0)
  {
    // not compatible with incremental
    if (options::incrementalSolving())
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

  if (options::solveBVAsInt() != options::SolveBVAsIntMode::OFF)
  {
    if (options::boolToBitvector() != options::BoolToBVMode::OFF)
    {
      throw OptionException(
          "solving bitvectors as integers is incompatible with --bool-to-bv.");
    }
    if (options::BVAndIntegerGranularity() > 8)
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
  if (options::ackermann() && options::produceModels()
      && (logic.isTheoryEnabled(THEORY_ARRAYS)
          || logic.isTheoryEnabled(THEORY_UF)))
  {
    if (Options::current()->wasSetByUser(options::produceModels))
    {
      throw OptionException(std::string(
          "Ackermannization currently does not support model generation."));
    }
    Notice() << "SmtEngine: turn off ackermannization to support model"
             << "generation" << std::endl;
    Options::current()->set(options::ackermann, false);
  }

  if (options::ackermann())
  {
    if (options::incrementalSolving())
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
  if (options::doITESimp())
  {
    if (!Options::current()->wasSetByUser(options::earlyIteRemoval))
    {
      Options::current()->set(options::earlyIteRemoval, true);
    }
  }

  // Set default options associated with strings-exp. We also set these options
  // if we are using eager string preprocessing, which may introduce quantified
  // formulas at preprocess time.
  if (options::stringExp() || !options::stringLazyPreproc())
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
    // We require bounded quantifier handling.
    if (!Options::current()->wasSetByUser(options::fmfBound))
    {
      Options::current()->set(options::fmfBound, true);
      Trace("smt") << "turning on fmf-bound-int, for strings-exp" << std::endl;
    }
    // Note we allow E-matching by default to support combinations of sequences
    // and quantifiers.
  }
  // whether we must disable proofs
  bool disableProofs = false;
  if (options::globalNegate())
  {
    // When global negate answers "unsat", it is not due to showing a set of
    // formulas is unsat. Thus, proofs do not apply.
    disableProofs = true;
  }
  // !!! must disable proofs if using the old unsat core infrastructure
  // TODO (#project 37) remove this
  if (options::unsatCores())
  {
    disableProofs = true;
  }

  // new unsat core specific restrictions for proofs
  if (options::unsatCoresNew())
  {
    // no fine-graininess
    if (!Options::current()->wasSetByUser(options::proofGranularityMode))
    {
      Options::current()->set(options::proofGranularityMode, options::ProofGranularityMode::OFF);
    }
  }

  if (options::arraysExp())
  {
    if (!logic.isQuantified())
    {
      logic = logic.getUnlockedCopy();
      logic.enableQuantifiers();
      logic.lock();
    }
    // Allows to answer sat more often by default.
    if (!Options::current()->wasSetByUser(options::fmfBound))
    {
      Options::current()->set(options::fmfBound, true);
      Trace("smt") << "turning on fmf-bound, for arrays-exp" << std::endl;
    }
  }

  // sygus inference may require datatypes
  if (!isInternalSubsolver)
  {
    if (options::produceAbducts()
        || options::produceInterpols() != options::ProduceInterpols::NONE
        || options::sygusInference() || options::sygusRewSynthInput())
    {
      // since we are trying to recast as sygus, we assume the input is sygus
      isSygus = true;
      usesSygus = true;
    }
    else if (options::sygusInst())
    {
      // sygus instantiation uses sygus, but it is not a sygus problem
      usesSygus = true;
    }
  }

  // We now know whether the input uses sygus. Update the logic to incorporate
  // the theories we need internally for handling sygus problems.
  if (usesSygus)
  {
    logic = logic.getUnlockedCopy();
    logic.enableSygus();
    logic.lock();
    if (isSygus)
    {
      // When sygus answers "unsat", it is not due to showing a set of
      // formulas is unsat in the standard way. Thus, proofs do not apply.
      disableProofs = true;
    }
  }

  // if we requiring disabling proofs, disable them now
  if (disableProofs && options::produceProofs())
  {
    if (options::unsatCoresNew())
    {
      Notice() << "SmtEngine: turning off new unsat cores." << std::endl;
    }
    Options::current()->set(options::unsatCoresNew, false);
    Options::current()->set(options::checkUnsatCoresNew, false);
    if (options::produceProofs())
    {
      Notice() << "SmtEngine: turning off produce-proofs." << std::endl;
    }
    Options::current()->set(options::produceProofs, false);
    Options::current()->set(options::checkProofs, false);
    Options::current()->set(options::proofEagerChecking, false);
  }

  // sygus core connective requires unsat cores
  if (options::sygusCoreConnective())
  {
    Options::current()->set(options::unsatCores, true);
  }

  if ((options::checkModels() || options::checkSynthSol()
       || options::produceAbducts()
       || options::produceInterpols() != options::ProduceInterpols::NONE
       || options::modelCoresMode() != options::ModelCoresMode::NONE
       || options::blockModelsMode() != options::BlockModelsMode::NONE
       || options::produceProofs())
      && !options::produceAssertions())
  {
    Notice() << "SmtEngine: turning on produce-assertions to support "
             << "option requiring assertions." << std::endl;
    Options::current()->set(options::produceAssertions, true);
  }

  // Disable options incompatible with incremental solving, unsat cores or
  // output an error if enabled explicitly. It is also currently incompatible
  // with arithmetic, force the option off.
  if (options::incrementalSolving() || options::unsatCores()
      || options::unsatCoresNew())
  {
    if (options::unconstrainedSimp())
    {
      if (Options::current()->wasSetByUser(options::unconstrainedSimp))
      {
        throw OptionException(
            "unconstrained simplification not supported with unsat "
            "cores/incremental solving");
      }
      Notice() << "SmtEngine: turning off unconstrained simplification to "
                  "support unsat cores/incremental solving"
               << std::endl;
      Options::current()->set(options::unconstrainedSimp, false);
    }
  }
  else
  {
    // Turn on unconstrained simplification for QF_AUFBV
    if (!Options::current()->wasSetByUser(options::unconstrainedSimp))
    {
      bool uncSimp = !logic.isQuantified() && !options::produceModels()
                     && !options::produceAssignments()
                     && !options::checkModels()
                     && logic.isTheoryEnabled(THEORY_ARRAYS)
                     && logic.isTheoryEnabled(THEORY_BV)
                     && !logic.isTheoryEnabled(THEORY_ARITH);
      Trace("smt") << "setting unconstrained simplification to " << uncSimp
                   << std::endl;
      Options::current()->set(options::unconstrainedSimp, uncSimp);
    }
  }

  if (options::incrementalSolving())
  {
    if (options::sygusInference())
    {
      if (Options::current()->wasSetByUser(options::sygusInference))
      {
        throw OptionException(
            "sygus inference not supported with incremental solving");
      }
      Notice() << "SmtEngine: turning off sygus inference to support "
                  "incremental solving"
               << std::endl;
      Options::current()->set(options::sygusInference, false);
    }
  }

  if (options::solveBVAsInt() != options::SolveBVAsIntMode::OFF)
  {
    /**
     * Operations on 1 bits are better handled as Boolean operations
     * than as integer operations.
     * Therefore, we enable bv-to-bool, which runs before
     * the translation to integers.
     */
    Options::current()->set(options::bitvectorToBool, true);
  }

  // Disable options incompatible with unsat cores or output an error if enabled
  // explicitly
  if (options::unsatCores() || options::unsatCoresNew())
  {
    if (options::simplificationMode() != options::SimplificationMode::NONE)
    {
      if (Options::current()->wasSetByUser(options::simplificationMode))
      {
        throw OptionException("simplification not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off simplification to support unsat "
                  "cores"
               << std::endl;
      Options::current()->set(options::simplificationMode, options::SimplificationMode::NONE);
    }

    if (options::pbRewrites())
    {
      if (Options::current()->wasSetByUser(options::pbRewrites))
      {
        throw OptionException(
            "pseudoboolean rewrites not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off pseudoboolean rewrites to support "
                  "unsat cores"
               << std::endl;
      Options::current()->set(options::pbRewrites, false);
    }

    if (options::sortInference())
    {
      if (Options::current()->wasSetByUser(options::sortInference))
      {
        throw OptionException("sort inference not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off sort inference to support unsat "
                  "cores"
               << std::endl;
      Options::current()->set(options::sortInference, false);
    }

    if (options::preSkolemQuant())
    {
      if (Options::current()->wasSetByUser(options::preSkolemQuant))
      {
        throw OptionException(
            "pre-skolemization not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off pre-skolemization to support unsat "
                  "cores"
               << std::endl;
      Options::current()->set(options::preSkolemQuant, false);
    }


    if (options::bitvectorToBool())
    {
      if (Options::current()->wasSetByUser(options::bitvectorToBool))
      {
        throw OptionException("bv-to-bool not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off bitvector-to-bool to support unsat "
                  "cores"
               << std::endl;
      Options::current()->set(options::bitvectorToBool, false);
    }

    if (options::boolToBitvector() != options::BoolToBVMode::OFF)
    {
      if (Options::current()->wasSetByUser(options::boolToBitvector))
      {
        throw OptionException(
            "bool-to-bv != off not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off bool-to-bv to support unsat "
                  "cores"
               << std::endl;
      Options::current()->set(options::boolToBitvector, options::BoolToBVMode::OFF);
    }

    if (options::bvIntroducePow2())
    {
      if (Options::current()->wasSetByUser(options::bvIntroducePow2))
      {
        throw OptionException("bv-intro-pow2 not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off bv-intro-pow2 to support "
                  "unsat-cores"
               << std::endl;
      Options::current()->set(options::bvIntroducePow2, false);
    }

    if (options::repeatSimp())
    {
      if (Options::current()->wasSetByUser(options::repeatSimp))
      {
        throw OptionException("repeat-simp not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off repeat-simp to support unsat "
                  "cores"
               << std::endl;
      Options::current()->set(options::repeatSimp, false);
    }

    if (options::globalNegate())
    {
      if (Options::current()->wasSetByUser(options::globalNegate))
      {
        throw OptionException("global-negate not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off global-negate to support unsat "
                  "cores"
               << std::endl;
      Options::current()->set(options::globalNegate, false);
    }

    if (options::bitvectorAig())
    {
      throw OptionException("bitblast-aig not supported with unsat cores");
    }

    if (options::doITESimp())
    {
      throw OptionException("ITE simp not supported with unsat cores");
    }
  }
  else
  {
    // by default, nonclausal simplification is off for QF_SAT
    if (!Options::current()->wasSetByUser(options::simplificationMode))
    {
      bool qf_sat = logic.isPure(THEORY_BOOL) && !logic.isQuantified();
      Trace("smt") << "setting simplification mode to <"
                   << logic.getLogicString() << "> " << (!qf_sat) << std::endl;
      // simplification=none works better for SMT LIB benchmarks with
      // quantifiers, not others Options::current()->set(options::simplificationMode, qf_sat ||
      // quantifiers ? options::SimplificationMode::NONE :
      // options::SimplificationMode::BATCH);
      Options::current()->set(options::simplificationMode, qf_sat
                                          ? options::SimplificationMode::NONE
                                          : options::SimplificationMode::BATCH);
    }
  }

  if (options::cegqiBv() && logic.isQuantified())
  {
    if (options::boolToBitvector() != options::BoolToBVMode::OFF)
    {
      if (Options::current()->wasSetByUser(options::boolToBitvector))
      {
        throw OptionException(
            "bool-to-bv != off not supported with CBQI BV for quantified "
            "logics");
      }
      Notice() << "SmtEngine: turning off bool-to-bitvector to support CBQI BV"
               << std::endl;
      Options::current()->set(options::boolToBitvector, options::BoolToBVMode::OFF);
    }
  }

  // cases where we need produce models
  if (!options::produceModels()
      && (options::produceAssignments() || options::sygusRewSynthCheck()
          || usesSygus))
  {
    Notice() << "SmtEngine: turning on produce-models" << std::endl;
    Options::current()->set(options::produceModels, true);
  }

  /////////////////////////////////////////////////////////////////////////////
  // Theory widening
  //
  // Some theories imply the use of other theories to handle certain operators,
  // e.g. UF to handle partial functions.
  /////////////////////////////////////////////////////////////////////////////
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
  if (options::bvAbstraction())
  {
    // bv abstraction may require UF
    Notice() << "Enabling UF because bvAbstraction requires it." << std::endl;
    needsUf = true;
  }
  else if (options::preSkolemQuantNested()
           && Options::current()->wasSetByUser(options::preSkolemQuantNested))
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
          && options::solveIntAsBV() == 0)
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
  if (options::arithMLTrick())
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
  /////////////////////////////////////////////////////////////////////////////

  // Set the options for the theoryOf
  if (!Options::current()->wasSetByUser(options::theoryOfMode))
  {
    if (logic.isSharingEnabled() && !logic.isTheoryEnabled(THEORY_BV)
        && !logic.isTheoryEnabled(THEORY_STRINGS)
        && !logic.isTheoryEnabled(THEORY_SETS)
        && !logic.isTheoryEnabled(THEORY_BAGS)
        && !(logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
             && !logic.isQuantified()))
    {
      Trace("smt") << "setting theoryof-mode to term-based" << std::endl;
      Options::current()->set(options::theoryOfMode, options::TheoryOfMode::THEORY_OF_TERM_BASED);
    }
  }

  // by default, symmetry breaker is on only for non-incremental QF_UF
  if (!Options::current()->wasSetByUser(options::ufSymmetryBreaker))
  {
    bool qf_uf_noinc = logic.isPure(THEORY_UF) && !logic.isQuantified()
                       && !options::incrementalSolving()
                       && !options::unsatCores() && !options::unsatCoresNew();
    Trace("smt") << "setting uf symmetry breaker to " << qf_uf_noinc
                 << std::endl;
    Options::current()->set(options::ufSymmetryBreaker, qf_uf_noinc);
  }

  // If in arrays, set the UF handler to arrays
  if (logic.isTheoryEnabled(THEORY_ARRAYS) && !options::ufHo()
      && !options::finiteModelFind()
      && (!logic.isQuantified()
          || (logic.isQuantified() && !logic.isTheoryEnabled(THEORY_UF))))
  {
    Theory::setUninterpretedSortOwner(THEORY_ARRAYS);
  }
  else
  {
    Theory::setUninterpretedSortOwner(THEORY_UF);
  }

  if (!Options::current()->wasSetByUser(options::simplifyWithCareEnabled))
  {
    bool qf_aufbv =
        !logic.isQuantified() && logic.isTheoryEnabled(THEORY_ARRAYS)
        && logic.isTheoryEnabled(THEORY_UF) && logic.isTheoryEnabled(THEORY_BV);

    bool withCare = qf_aufbv;
    Trace("smt") << "setting ite simplify with care to " << withCare
                 << std::endl;
    Options::current()->set(options::simplifyWithCareEnabled, withCare);
  }
  // Turn off array eager index splitting for QF_AUFLIA
  if (!Options::current()->wasSetByUser(options::arraysEagerIndexSplitting))
  {
    if (not logic.isQuantified() && logic.isTheoryEnabled(THEORY_ARRAYS)
        && logic.isTheoryEnabled(THEORY_UF)
        && logic.isTheoryEnabled(THEORY_ARITH))
    {
      Trace("smt") << "setting array eager index splitting to false"
                   << std::endl;
      Options::current()->set(options::arraysEagerIndexSplitting, false);
    }
  }
  // Turn on multiple-pass non-clausal simplification for QF_AUFBV
  if (!Options::current()->wasSetByUser(options::repeatSimp))
  {
    bool repeatSimp = !logic.isQuantified()
                      && (logic.isTheoryEnabled(THEORY_ARRAYS)
                          && logic.isTheoryEnabled(THEORY_UF)
                          && logic.isTheoryEnabled(THEORY_BV))
                      && !options::unsatCores() && !options::unsatCoresNew();
    Trace("smt") << "setting repeat simplification to " << repeatSimp
                 << std::endl;
    Options::current()->set(options::repeatSimp, repeatSimp);
  }

  if (options::boolToBitvector() == options::BoolToBVMode::ALL
      && !logic.isTheoryEnabled(THEORY_BV))
  {
    if (Options::current()->wasSetByUser(options::boolToBitvector))
    {
      throw OptionException(
          "bool-to-bv=all not supported for non-bitvector logics.");
    }
    Notice() << "SmtEngine: turning off bool-to-bv for non-bv logic: "
             << logic.getLogicString() << std::endl;
    Options::current()->set(options::boolToBitvector, options::BoolToBVMode::OFF);
  }

  if (!Options::current()->wasSetByUser(options::bvEagerExplanations)
      && logic.isTheoryEnabled(THEORY_ARRAYS)
      && logic.isTheoryEnabled(THEORY_BV))
  {
    Trace("smt") << "enabling eager bit-vector explanations " << std::endl;
    Options::current()->set(options::bvEagerExplanations, true);
  }

  // Turn on arith rewrite equalities only for pure arithmetic
  if (!Options::current()->wasSetByUser(options::arithRewriteEq))
  {
    bool arithRewriteEq =
        logic.isPure(THEORY_ARITH) && logic.isLinear() && !logic.isQuantified();
    Trace("smt") << "setting arith rewrite equalities " << arithRewriteEq
                 << std::endl;
    Options::current()->set(options::arithRewriteEq, arithRewriteEq);
  }
  if (!Options::current()->wasSetByUser(options::arithHeuristicPivots))
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
    Options::current()->set(options::arithHeuristicPivots, heuristicPivots);
  }
  if (!Options::current()->wasSetByUser(options::arithPivotThreshold))
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
    Options::current()->set(options::arithPivotThreshold, pivotThreshold);
  }
  if (!Options::current()->wasSetByUser(options::arithStandardCheckVarOrderPivots))
  {
    int16_t varOrderPivots = -1;
    if (logic.isPure(THEORY_ARITH) && !logic.isQuantified())
    {
      varOrderPivots = 200;
    }
    Trace("smt") << "setting arithStandardCheckVarOrderPivots  "
                 << varOrderPivots << std::endl;
    Options::current()->set(options::arithStandardCheckVarOrderPivots, varOrderPivots);
  }
  if (logic.isPure(THEORY_ARITH) && !logic.areRealsUsed())
  {
    if (!Options::current()->wasSetByUser(options::nlExtTangentPlanesInterleave))
    {
      Trace("smt") << "setting nlExtTangentPlanesInterleave to true"
                   << std::endl;
      Options::current()->set(options::nlExtTangentPlanesInterleave, true);
    }
  }

  // Set decision mode based on logic (if not set by user)
  if (!Options::current()->wasSetByUser(options::decisionMode))
  {
    options::DecisionMode decMode =
        // anything that uses sygus uses internal
        usesSygus ? options::DecisionMode::INTERNAL :
                  // ALL
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
        // ALL
        logic.hasEverything() || logic.isTheoryEnabled(THEORY_STRINGS)
            ? false
            : (  // QF_AUFLIA
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
                      ? true
                      : false);

    Trace("smt") << "setting decision mode to " << decMode << std::endl;
    Options::current()->set(options::decisionMode, decMode);
    Options::current()->set(options::decisionStopOnly, stoponly);
  }
  if (options::incrementalSolving())
  {
    // disable modes not supported by incremental
    Options::current()->set(options::sortInference, false);
    Options::current()->set(options::ufssFairnessMonotone, false);
    Options::current()->set(options::globalNegate, false);
    Options::current()->set(options::bvAbstraction, false);
    Options::current()->set(options::arithMLTrick, false);
  }
  if (logic.hasCardinalityConstraints())
  {
    // must have finite model finding on
    Options::current()->set(options::finiteModelFind, true);
  }

  if (options::instMaxLevel() != -1)
  {
    Notice() << "SmtEngine: turning off cbqi to support instMaxLevel"
             << std::endl;
    Options::current()->set(options::cegqi, false);
  }

  if ((Options::current()->wasSetByUser(options::fmfBoundLazy) && options::fmfBoundLazy())
      || (Options::current()->wasSetByUser(options::fmfBoundInt) && options::fmfBoundInt()))
  {
    Options::current()->set(options::fmfBound, true);
  }
  // now have determined whether fmfBoundInt is on/off
  // apply fmfBoundInt options
  if (options::fmfBound())
  {
    if (!Options::current()->wasSetByUser(options::mbqiMode)
        || (options::mbqiMode() != options::MbqiMode::NONE
            && options::mbqiMode() != options::MbqiMode::FMC))
    {
      // if bounded integers are set, use no MBQI by default
      Options::current()->set(options::mbqiMode, options::MbqiMode::NONE);
    }
    if (!Options::current()->wasSetByUser(options::prenexQuant))
    {
      Options::current()->set(options::prenexQuant, options::PrenexQuantMode::NONE);
    }
  }
  if (options::ufHo())
  {
    // if higher-order, then current variants of model-based instantiation
    // cannot be used
    if (options::mbqiMode() != options::MbqiMode::NONE)
    {
      Options::current()->set(options::mbqiMode, options::MbqiMode::NONE);
    }
    if (!Options::current()->wasSetByUser(options::hoElimStoreAx))
    {
      // by default, use store axioms only if --ho-elim is set
      Options::current()->set(options::hoElimStoreAx, options::hoElim());
    }
    if (!options::assignFunctionValues())
    {
      // must assign function values
      Options::current()->set(options::assignFunctionValues, true);
    }
    // Cannot use macros, since lambda lifting and macro elimination are inverse
    // operations.
    if (options::macrosQuant())
    {
      Options::current()->set(options::macrosQuant, false);
    }
  }
  if (options::fmfFunWellDefinedRelevant())
  {
    if (!Options::current()->wasSetByUser(options::fmfFunWellDefined))
    {
      Options::current()->set(options::fmfFunWellDefined, true);
    }
  }
  if (options::fmfFunWellDefined())
  {
    if (!Options::current()->wasSetByUser(options::finiteModelFind))
    {
      Options::current()->set(options::finiteModelFind, true);
    }
  }

  // now, have determined whether finite model find is on/off
  // apply finite model finding options
  if (options::finiteModelFind())
  {
    // apply conservative quantifiers splitting
    if (!Options::current()->wasSetByUser(options::quantDynamicSplit))
    {
      Options::current()->set(options::quantDynamicSplit, options::QuantDSplitMode::DEFAULT);
    }
    if (!Options::current()->wasSetByUser(options::eMatching))
    {
      Options::current()->set(options::eMatching, options::fmfInstEngine());
    }
    if (!Options::current()->wasSetByUser(options::instWhenMode))
    {
      // instantiate only on last call
      if (options::eMatching())
      {
        Options::current()->set(options::instWhenMode, options::InstWhenMode::LAST_CALL);
      }
    }
  }

  // apply sygus options
  // if we are attempting to rewrite everything to SyGuS, use sygus()
  if (usesSygus)
  {
    if (!options::sygus())
    {
      Trace("smt") << "turning on sygus" << std::endl;
    }
    Options::current()->set(options::sygus, true);
    // must use Ferrante/Rackoff for real arithmetic
    if (!Options::current()->wasSetByUser(options::cegqiMidpoint))
    {
      Options::current()->set(options::cegqiMidpoint, true);
    }
    // must disable cegqi-bv since it may introduce witness terms, which
    // cannot appear in synthesis solutions
    if (!Options::current()->wasSetByUser(options::cegqiBv))
    {
      Options::current()->set(options::cegqiBv, false);
    }
    if (options::sygusRepairConst())
    {
      if (!Options::current()->wasSetByUser(options::cegqi))
      {
        Options::current()->set(options::cegqi, true);
      }
    }
    if (options::sygusInference())
    {
      // optimization: apply preskolemization, makes it succeed more often
      if (!Options::current()->wasSetByUser(options::preSkolemQuant))
      {
        Options::current()->set(options::preSkolemQuant, true);
      }
      if (!Options::current()->wasSetByUser(options::preSkolemQuantNested))
      {
        Options::current()->set(options::preSkolemQuantNested, true);
      }
    }
    // counterexample-guided instantiation for sygus
    if (!Options::current()->wasSetByUser(options::cegqiSingleInvMode))
    {
      Options::current()->set(options::cegqiSingleInvMode, options::CegqiSingleInvMode::USE);
    }
    if (!Options::current()->wasSetByUser(options::quantConflictFind))
    {
      Options::current()->set(options::quantConflictFind, false);
    }
    if (!Options::current()->wasSetByUser(options::instNoEntail))
    {
      Options::current()->set(options::instNoEntail, false);
    }
    if (!Options::current()->wasSetByUser(options::cegqiFullEffort))
    {
      // should use full effort cbqi for single invocation and repair const
      Options::current()->set(options::cegqiFullEffort, true);
    }
    if (options::sygusRew())
    {
      Options::current()->set(options::sygusRewSynth, true);
      Options::current()->set(options::sygusRewVerify, true);
    }
    if (options::sygusRewSynthInput())
    {
      // If we are using synthesis rewrite rules from input, we use
      // sygusRewSynth after preprocessing. See passes/synth_rew_rules.h for
      // details on this technique.
      Options::current()->set(options::sygusRewSynth, true);
      // we should not use the extended rewriter, since we are interested
      // in rewrites that are not in the main rewriter
      if (!Options::current()->wasSetByUser(options::sygusExtRew))
      {
        Options::current()->set(options::sygusExtRew, false);
      }
    }
    // Whether we must use "basic" sygus algorithms. A non-basic sygus algorithm
    // is one that is specialized for returning a single solution. Non-basic
    // sygus algorithms currently include the PBE solver, UNIF+PI, static
    // template inference for invariant synthesis, and single invocation
    // techniques.
    bool reqBasicSygus = false;
    if (options::produceAbducts())
    {
      // if doing abduction, we should filter strong solutions
      if (!Options::current()->wasSetByUser(options::sygusFilterSolMode))
      {
        Options::current()->set(options::sygusFilterSolMode, options::SygusFilterSolMode::STRONG);
      }
      // we must use basic sygus algorithms, since e.g. we require checking
      // a sygus side condition for consistency with axioms.
      reqBasicSygus = true;
    }
    if (options::sygusRewSynth() || options::sygusRewVerify()
        || options::sygusQueryGen())
    {
      // rewrite rule synthesis implies that sygus stream must be true
      Options::current()->set(options::sygusStream, true);
    }
    if (options::sygusStream() || options::incrementalSolving())
    {
      // Streaming and incremental mode are incompatible with techniques that
      // focus the search towards finding a single solution.
      reqBasicSygus = true;
    }
    // Now, disable options for non-basic sygus algorithms, if necessary.
    if (reqBasicSygus)
    {
      if (!Options::current()->wasSetByUser(options::sygusUnifPbe))
      {
        Options::current()->set(options::sygusUnifPbe, false);
      }
      if (Options::current()->wasSetByUser(options::sygusUnifPi))
      {
        Options::current()->set(options::sygusUnifPi, options::SygusUnifPiMode::NONE);
      }
      if (!Options::current()->wasSetByUser(options::sygusInvTemplMode))
      {
        Options::current()->set(options::sygusInvTemplMode, options::SygusInvTemplMode::NONE);
      }
      if (!Options::current()->wasSetByUser(options::cegqiSingleInvMode))
      {
        Options::current()->set(options::cegqiSingleInvMode, options::CegqiSingleInvMode::NONE);
      }
    }
    if (!Options::current()->wasSetByUser(options::dtRewriteErrorSel))
    {
      Options::current()->set(options::dtRewriteErrorSel, true);
    }
    // do not miniscope
    if (!Options::current()->wasSetByUser(options::miniscopeQuant))
    {
      Options::current()->set(options::miniscopeQuant, false);
    }
    if (!Options::current()->wasSetByUser(options::miniscopeQuantFreeVar))
    {
      Options::current()->set(options::miniscopeQuantFreeVar, false);
    }
    if (!Options::current()->wasSetByUser(options::quantSplit))
    {
      Options::current()->set(options::quantSplit, false);
    }
    // do not do macros
    if (!Options::current()->wasSetByUser(options::macrosQuant))
    {
      Options::current()->set(options::macrosQuant, false);
    }
    // use tangent planes by default, since we want to put effort into
    // the verification step for sygus queries with non-linear arithmetic
    if (!Options::current()->wasSetByUser(options::nlExtTangentPlanes))
    {
      Options::current()->set(options::nlExtTangentPlanes, true);
    }
  }
  // counterexample-guided instantiation for non-sygus
  // enable if any possible quantifiers with arithmetic, datatypes or bitvectors
  if ((logic.isQuantified()
       && (logic.isTheoryEnabled(THEORY_ARITH)
           || logic.isTheoryEnabled(THEORY_DATATYPES)
           || logic.isTheoryEnabled(THEORY_BV)
           || logic.isTheoryEnabled(THEORY_FP)))
      || options::cegqiAll())
  {
    if (!Options::current()->wasSetByUser(options::cegqi))
    {
      Options::current()->set(options::cegqi, true);
    }
    // check whether we should apply full cbqi
    if (logic.isPure(THEORY_BV))
    {
      if (!Options::current()->wasSetByUser(options::cegqiFullEffort))
      {
        Options::current()->set(options::cegqiFullEffort, true);
      }
    }
  }
  if (options::cegqi())
  {
    if (options::incrementalSolving())
    {
      // cannot do nested quantifier elimination in incremental mode
      Options::current()->set(options::cegqiNestedQE, false);
    }
    if (logic.isPure(THEORY_ARITH) || logic.isPure(THEORY_BV))
    {
      if (!Options::current()->wasSetByUser(options::quantConflictFind))
      {
        Options::current()->set(options::quantConflictFind, false);
      }
      if (!Options::current()->wasSetByUser(options::instNoEntail))
      {
        Options::current()->set(options::instNoEntail, false);
      }
      if (!Options::current()->wasSetByUser(options::instWhenMode) && options::cegqiModel())
      {
        // only instantiation should happen at last call when model is avaiable
        Options::current()->set(options::instWhenMode, options::InstWhenMode::LAST_CALL);
      }
    }
    else
    {
      // only supported in pure arithmetic or pure BV
      Options::current()->set(options::cegqiNestedQE, false);
    }
    if (options::globalNegate())
    {
      if (!Options::current()->wasSetByUser(options::prenexQuant))
      {
        Options::current()->set(options::prenexQuant, options::PrenexQuantMode::NONE);
      }
    }
  }
  // implied options...
  if (options::strictTriggers())
  {
    if (!Options::current()->wasSetByUser(options::userPatternsQuant))
    {
      Options::current()->set(options::userPatternsQuant, options::UserPatMode::TRUST);
    }
  }
  if (Options::current()->wasSetByUser(options::qcfMode) || options::qcfTConstraint())
  {
    Options::current()->set(options::quantConflictFind, true);
  }
  if (options::cegqiNestedQE())
  {
    Options::current()->set(options::prenexQuantUser, true);
    if (!Options::current()->wasSetByUser(options::preSkolemQuant))
    {
      Options::current()->set(options::preSkolemQuant, true);
    }
  }
  // for induction techniques
  if (options::quantInduction())
  {
    if (!Options::current()->wasSetByUser(options::dtStcInduction))
    {
      Options::current()->set(options::dtStcInduction, true);
    }
    if (!Options::current()->wasSetByUser(options::intWfInduction))
    {
      Options::current()->set(options::intWfInduction, true);
    }
  }
  if (options::dtStcInduction())
  {
    // try to remove ITEs from quantified formulas
    if (!Options::current()->wasSetByUser(options::iteDtTesterSplitQuant))
    {
      Options::current()->set(options::iteDtTesterSplitQuant, true);
    }
    if (!Options::current()->wasSetByUser(options::iteLiftQuant))
    {
      Options::current()->set(options::iteLiftQuant, options::IteLiftQuantMode::ALL);
    }
  }
  if (options::intWfInduction())
  {
    if (!Options::current()->wasSetByUser(options::purifyTriggers))
    {
      Options::current()->set(options::purifyTriggers, true);
    }
  }
  if (options::conjectureNoFilter())
  {
    if (!Options::current()->wasSetByUser(options::conjectureFilterActiveTerms))
    {
      Options::current()->set(options::conjectureFilterActiveTerms, false);
    }
    if (!Options::current()->wasSetByUser(options::conjectureFilterCanonical))
    {
      Options::current()->set(options::conjectureFilterCanonical, false);
    }
    if (!Options::current()->wasSetByUser(options::conjectureFilterModel))
    {
      Options::current()->set(options::conjectureFilterModel, false);
    }
  }
  if (Options::current()->wasSetByUser(options::conjectureGenPerRound))
  {
    if (options::conjectureGenPerRound() > 0)
    {
      Options::current()->set(options::conjectureGen, true);
    }
    else
    {
      Options::current()->set(options::conjectureGen, false);
    }
  }
  // can't pre-skolemize nested quantifiers without UF theory
  if (!logic.isTheoryEnabled(THEORY_UF) && options::preSkolemQuant())
  {
    if (!Options::current()->wasSetByUser(options::preSkolemQuantNested))
    {
      Options::current()->set(options::preSkolemQuantNested, false);
    }
  }
  if (!logic.isTheoryEnabled(THEORY_DATATYPES))
  {
    Options::current()->set(options::quantDynamicSplit, options::QuantDSplitMode::NONE);
  }

  // until bugs 371,431 are fixed
  if (!Options::current()->wasSetByUser(options::minisatUseElim))
  {
    // cannot use minisat elimination for logics where a theory solver
    // introduces new literals into the search. This includes quantifiers
    // (quantifier instantiation), and the lemma schemas used in non-linear
    // and sets. We also can't use it if models are enabled.
    if (logic.isTheoryEnabled(THEORY_SETS)
        || logic.isTheoryEnabled(THEORY_BAGS)
        || logic.isQuantified()
        || options::produceModels() || options::produceAssignments()
        || options::checkModels()
        || (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()))
    {
      Options::current()->set(options::minisatUseElim, false);
    }
  }

  if (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
      && options::nlRlvMode() != options::NlRlvMode::NONE)
  {
    if (!options::relevanceFilter())
    {
      if (Options::current()->wasSetByUser(options::relevanceFilter))
      {
        Warning() << "SmtEngine: turning on relevance filtering to support "
                     "--nl-ext-rlv="
                  << options::nlRlvMode() << std::endl;
      }
      // must use relevance filtering techniques
      Options::current()->set(options::relevanceFilter, true);
    }
  }

  // For now, these array theory optimizations do not support model-building
  if (options::produceModels() || options::produceAssignments()
      || options::checkModels())
  {
    Options::current()->set(options::arraysOptimizeLinear, false);
  }

  if (!options::bitvectorEqualitySolver())
  {
    if (options::bvLazyRewriteExtf())
    {
      if (Options::current()->wasSetByUser(options::bvLazyRewriteExtf))
      {
        throw OptionException(
            "--bv-lazy-rewrite-extf requires --bv-eq-solver to be set");
      }
    }
    Trace("smt")
        << "disabling bvLazyRewriteExtf since equality solver is disabled"
        << std::endl;
    Options::current()->set(options::bvLazyRewriteExtf, false);
  }

  if (options::stringFMF() && !Options::current()->wasSetByUser(options::stringProcessLoopMode))
  {
    Trace("smt") << "settting stringProcessLoopMode to 'simple' since "
                    "--strings-fmf enabled"
                 << std::endl;
    Options::current()->set(options::stringProcessLoopMode, options::ProcessLoopMode::SIMPLE);
  }

  // !!! All options that require disabling models go here
  bool disableModels = false;
  std::string sOptNoModel;
  if (Options::current()->wasSetByUser(options::unconstrainedSimp) && options::unconstrainedSimp())
  {
    disableModels = true;
    sOptNoModel = "unconstrained-simp";
  }
  else if (options::sortInference())
  {
    disableModels = true;
    sOptNoModel = "sort-inference";
  }
  else if (options::minisatUseElim())
  {
    disableModels = true;
    sOptNoModel = "minisat-elimination";
  }
  else if (options::globalNegate())
  {
    disableModels = true;
    sOptNoModel = "global-negate";
  }
  if (disableModels)
  {
    if (options::produceModels())
    {
      if (Options::current()->wasSetByUser(options::produceModels))
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel << " with model generation.";
        throw OptionException(ss.str());
      }
      Notice() << "SmtEngine: turning off produce-models to support "
               << sOptNoModel << std::endl;
      Options::current()->set(options::produceModels, false);
    }
    if (options::produceAssignments())
    {
      if (Options::current()->wasSetByUser(options::produceAssignments))
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel
           << " with model generation (produce-assignments).";
        throw OptionException(ss.str());
      }
      Notice() << "SmtEngine: turning off produce-assignments to support "
               << sOptNoModel << std::endl;
      Options::current()->set(options::produceAssignments, false);
    }
    if (options::checkModels())
    {
      if (Options::current()->wasSetByUser(options::checkModels))
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel
           << " with model generation (check-models).";
        throw OptionException(ss.str());
      }
      Notice() << "SmtEngine: turning off check-models to support "
               << sOptNoModel << std::endl;
      Options::current()->set(options::checkModels, false);
    }
  }

  if (options::bitblastMode() == options::BitblastMode::EAGER
      && !logic.isPure(THEORY_BV) && logic.getLogicString() != "QF_UFBV"
      && logic.getLogicString() != "QF_ABV")
  {
    throw OptionException(
        "Eager bit-blasting does not currently support theory combination. "
        "Note that in a QF_BV problem UF symbols can be introduced for "
        "division. "
        "Try --bv-div-zero-const to interpret division by zero as a constant.");
  }

  if (logic == LogicInfo("QF_UFNRA"))
  {
#ifdef CVC5_USE_POLY
    if (!options::nlCad() && !Options::current()->wasSetByUser(options::nlCad))
    {
      Options::current()->set(options::nlCad, true);
      if (!Options::current()->wasSetByUser(options::nlExt))
      {
        Options::current()->set(options::nlExt, false);
      }
      if (!Options::current()->wasSetByUser(options::nlRlvMode))
      {
        Options::current()->set(options::nlRlvMode, options::NlRlvMode::INTERLEAVE);
      }
    }
#endif
  }
#ifndef CVC5_USE_POLY
  if (options::nlCad())
  {
    if (Options::current()->wasSetByUser(options::nlCad))
    {
      std::stringstream ss;
      ss << "Cannot use " << options::nlCad.name << " without configuring with --poly.";
      throw OptionException(ss.str());
    }
    else
    {
      Notice() << "Cannot use --" << options::nlCad.name
               << " without configuring with --poly." << std::endl;
      Options::current()->set(options::nlCad, false);
      Options::current()->set(options::nlExt, true);
    }
  }
#endif
}

}  // namespace smt
}  // namespace cvc5

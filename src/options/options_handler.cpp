/*********************                                                        */
/*! \file options_handler.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Interface for custom handlers and predicates options.
 **
 ** Interface for custom handlers and predicates options.
 **/

#include "options/options_handler.h"

#include <ostream>
#include <string>
#include <cerrno>

#include "cvc4autoconfig.h"

#include "base/configuration.h"
#include "base/configuration_private.h"
#include "base/cvc4_assert.h"
#include "base/exception.h"
#include "base/modal_exception.h"
#include "base/output.h"
#include "lib/strtok_r.h"
#include "options/arith_heuristic_pivot_rule.h"
#include "options/arith_propagation_mode.h"
#include "options/arith_unate_lemma_mode.h"
#include "options/base_options.h"
#include "options/bv_bitblast_mode.h"
#include "options/bv_options.h"
#include "options/decision_mode.h"
#include "options/decision_options.h"
#include "options/datatypes_modes.h"
#include "options/didyoumean.h"
#include "options/language.h"
#include "options/option_exception.h"
#include "options/printer_modes.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "options/theoryof_mode.h"
#include "options/ufss_mode.h"

namespace CVC4 {
namespace options {

// helper functions
namespace {

void throwLazyBBUnsupported(theory::bv::SatSolverMode m)
{
  std::string sat_solver;
  if (m == theory::bv::SAT_SOLVER_CADICAL)
  {
    sat_solver = "CaDiCaL";
  }
  else
  {
    Assert(m == theory::bv::SAT_SOLVER_CRYPTOMINISAT);
    sat_solver = "CryptoMiniSat";
  }
  std::string indent(25, ' ');
  throw OptionException(sat_solver + " does not support lazy bit-blasting.\n"
                        + indent + "Try --bv-sat-solver=minisat");
}

}  // namespace

OptionsHandler::OptionsHandler(Options* options) : d_options(options) { }

void OptionsHandler::notifyBeforeSearch(const std::string& option)
{
  try{
    d_options->d_beforeSearchListeners.notify();
  } catch (ModalException&){
    std::stringstream ss;
    ss << "cannot change option `" << option << "' after final initialization";
    throw ModalException(ss.str());
  }
}


void OptionsHandler::notifyTlimit(const std::string& option) {
  d_options->d_tlimitListeners.notify();
}

void OptionsHandler::notifyTlimitPer(const std::string& option) {
  d_options->d_tlimitPerListeners.notify();
}

void OptionsHandler::notifyRlimit(const std::string& option) {
  d_options->d_rlimitListeners.notify();
}

void OptionsHandler::notifyRlimitPer(const std::string& option) {
  d_options->d_rlimitPerListeners.notify();
}

unsigned long OptionsHandler::limitHandler(std::string option,
                                           std::string optarg)
{
  unsigned long ms;
  std::istringstream convert(optarg);
  if (!(convert >> ms))
  {
    throw OptionException("option `" + option
                          + "` requires a number as an argument");
  }
  return ms;
}

/* options/base_options_handlers.h */
void OptionsHandler::notifyPrintSuccess(std::string option) {
  d_options->d_setPrintSuccessListeners.notify();
}

// theory/arith/options_handlers.h
const std::string OptionsHandler::s_arithUnateLemmasHelp = "\
Unate lemmas are generated before SAT search begins using the relationship\n\
of constant terms and polynomials.\n\
Modes currently supported by the --unate-lemmas option:\n\
+ none \n\
+ ineqs \n\
  Outputs lemmas of the general form (<= p c) implies (<= p d) for c < d.\n\
+ eqs \n\
  Outputs lemmas of the general forms\n\
  (= p c) implies (<= p d) for c < d, or\n\
  (= p c) implies (not (= p d)) for c != d.\n\
+ all \n\
  A combination of inequalities and equalities.\n\
";

const std::string OptionsHandler::s_arithPropagationModeHelp = "\
This decides on kind of propagation arithmetic attempts to do during the search.\n\
+ none\n\
+ unate\n\
 use constraints to do unate propagation\n\
+ bi (Bounds Inference)\n\
  infers bounds on basic variables using the upper and lower bounds of the\n\
  non-basic variables in the tableau.\n\
+both\n\
";

const std::string OptionsHandler::s_errorSelectionRulesHelp = "\
This decides on the rule used by simplex during heuristic rounds\n\
for deciding the next basic variable to select.\n\
Heuristic pivot rules available:\n\
+min\n\
  The minimum abs() value of the variable's violation of its bound. (default)\n\
+max\n\
  The maximum violation the bound\n\
+varord\n\
  The variable order\n\
";

ArithUnateLemmaMode OptionsHandler::stringToArithUnateLemmaMode(
    std::string option, std::string optarg)
{
  if(optarg == "all") {
    return ALL_PRESOLVE_LEMMAS;
  } else if(optarg == "none") {
    return NO_PRESOLVE_LEMMAS;
  } else if(optarg == "ineqs") {
    return INEQUALITY_PRESOLVE_LEMMAS;
  } else if(optarg == "eqs") {
    return EQUALITY_PRESOLVE_LEMMAS;
  } else if(optarg == "help") {
    puts(s_arithUnateLemmasHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --unate-lemmas: `") +
                          optarg + "'.  Try --unate-lemmas help.");
  }
}

ArithPropagationMode OptionsHandler::stringToArithPropagationMode(
    std::string option, std::string optarg)
{
  if(optarg == "none") {
    return NO_PROP;
  } else if(optarg == "unate") {
    return UNATE_PROP;
  } else if(optarg == "bi") {
    return BOUND_INFERENCE_PROP;
  } else if(optarg == "both") {
    return BOTH_PROP;
  } else if(optarg == "help") {
    puts(s_arithPropagationModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --arith-prop: `") +
                          optarg + "'.  Try --arith-prop help.");
  }
}

ErrorSelectionRule OptionsHandler::stringToErrorSelectionRule(
    std::string option, std::string optarg)
{
  if(optarg == "min") {
    return MINIMUM_AMOUNT;
  } else if(optarg == "varord") {
    return VAR_ORDER;
  } else if(optarg == "max") {
    return MAXIMUM_AMOUNT;
  } else if(optarg == "help") {
    puts(s_errorSelectionRulesHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --heuristic-pivot-rule: `") +
                          optarg + "'.  Try --heuristic-pivot-rule help.");
  }
}
// theory/quantifiers/options_handlers.h

const std::string OptionsHandler::s_instWhenHelp = "\
Instantiation modes currently supported by the --inst-when option:\n\
\n\
full-last-call (default)\n\
+ Alternate running instantiation rounds at full effort and last\n\
  call.  In other words, interleave instantiation and theory combination.\n\
\n\
full\n\
+ Run instantiation round at full effort, before theory combination.\n\
\n\
full-delay \n\
+ Run instantiation round at full effort, before theory combination, after\n\
  all other theories have finished.\n\
\n\
full-delay-last-call \n\
+ Alternate running instantiation rounds at full effort after all other\n\
  theories have finished, and last call.  \n\
\n\
last-call\n\
+ Run instantiation at last call effort, after theory combination and\n\
  and theories report sat.\n\
\n\
";

const std::string OptionsHandler::s_literalMatchHelp = "\
Literal match modes currently supported by the --literal-match option:\n\
\n\
none \n\
+ Do not use literal matching.\n\
\n\
use (default)\n\
+ Consider phase requirements of triggers conservatively. For example, the\n\
  trigger P( x ) in forall( x ). ( P( x ) V ~Q( x ) ) will not be matched with\n\
  terms in the equivalence class of true, and likewise Q( x ) will not be matched\n\
  terms in the equivalence class of false. Extends to equality.\n\
\n\
agg-predicate \n\
+ Consider phase requirements aggressively for predicates. In the above example,\n\
  only match P( x ) with terms that are in the equivalence class of false.\n\
\n\
agg \n\
+ Consider the phase requirements aggressively for all triggers.\n\
\n\
";

const std::string OptionsHandler::s_mbqiModeHelp =
    "\
Model-based quantifier instantiation modes currently supported by the --mbqi option:\n\
\n\
default \n\
+ Use algorithm from Section 5.4.2 of thesis Finite Model Finding in Satisfiability \n\
  Modulo Theories.\n\
\n\
none \n\
+ Disable model-based quantifier instantiation.\n\
\n\
trust \n\
+ Do not instantiate quantified formulas (incomplete technique).\n\
\n\
";

const std::string OptionsHandler::s_qcfWhenModeHelp = "\
Quantifier conflict find modes currently supported by the --quant-cf-when option:\n\
\n\
default \n\
+ Default, apply conflict finding at full effort.\n\
\n\
last-call \n\
+ Apply conflict finding at last call, after theory combination and \n\
  and all theories report sat. \n\
\n\
std \n\
+ Apply conflict finding at standard effort.\n\
\n\
std-h \n\
+ Apply conflict finding at standard effort when heuristic says to. \n\
\n\
";

const std::string OptionsHandler::s_qcfModeHelp = "\
Quantifier conflict find modes currently supported by the --quant-cf option:\n\
\n\
prop-eq \n\
+ Default, apply QCF algorithm to propagate equalities as well as conflicts. \n\
\n\
conflict \n\
+ Apply QCF algorithm to find conflicts only.\n\
\n\
";

const std::string OptionsHandler::s_userPatModeHelp = "\
User pattern modes currently supported by the --user-pat option:\n\
\n\
trust \n\
+ When provided, use only user-provided patterns for a quantified formula.\n\
\n\
use \n\
+ Use both user-provided and auto-generated patterns when patterns\n\
  are provided for a quantified formula.\n\
\n\
resort \n\
+ Use user-provided patterns only after auto-generated patterns saturate.\n\
\n\
ignore \n\
+ Ignore user-provided patterns. \n\
\n\
interleave \n\
+ Alternate between use/resort. \n\
\n\
";

const std::string OptionsHandler::s_triggerSelModeHelp = "\
Trigger selection modes currently supported by the --trigger-sel option:\n\
\n\
min | default \n\
+ Consider only minimal subterms that meet criteria for triggers.\n\
\n\
max \n\
+ Consider only maximal subterms that meet criteria for triggers. \n\
\n\
all \n\
+ Consider all subterms that meet criteria for triggers. \n\
\n\
min-s-max \n\
+ Consider only minimal subterms that meet criteria for single triggers, maximal otherwise. \n\
\n\
min-s-all \n\
+ Consider only minimal subterms that meet criteria for single triggers, all otherwise. \n\
\n\
";
const std::string OptionsHandler::s_triggerActiveSelModeHelp = "\
Trigger active selection modes currently supported by the \
--trigger-active-sel option:\n\
\n\
all \n\
+ Make all triggers active. \n\
\n\
min \n\
+ Activate triggers with minimal ground terms.\n\
\n\
max \n\
+ Activate triggers with maximal ground terms. \n\
\n\
";
const std::string OptionsHandler::s_prenexQuantModeHelp = "\
Prenex quantifiers modes currently supported by the --prenex-quant option:\n\
\n\
none \n\
+ Do no prenex nested quantifiers. \n\
\n\
default | simple \n\
+ Default, do simple prenexing of same sign quantifiers.\n\
\n\
dnorm \n\
+ Prenex to disjunctive prenex normal form.\n\
\n\
norm \n\
+ Prenex to prenex normal form.\n\
\n\
";

const std::string OptionsHandler::s_cegqiFairModeHelp = "\
Modes for enforcing fairness for counterexample guided quantifier instantion, supported by --sygus-fair:\n\
\n\
uf-dt-size \n\
+ Enforce fairness using an uninterpreted function for datatypes size.\n\
\n\
direct \n\
+ Enforce fairness using direct conflict lemmas.\n\
\n\
default | dt-size \n\
+ Default, enforce fairness using size operator.\n\
\n\
dt-height-bound \n\
+ Enforce fairness by height bound predicate.\n\
\n\
none \n\
+ Do not enforce fairness. \n\
\n\
";

const std::string OptionsHandler::s_termDbModeHelp = "\
Modes for terms included in the quantifiers term database, supported by\
--term-db-mode:\n\
\n\
all  \n\
+ Quantifiers module considers all ground terms.\n\
\n\
relevant \n\
+ Quantifiers module considers only ground terms connected to current assertions. \n\
\n\
";

const std::string OptionsHandler::s_iteLiftQuantHelp = "\
Modes for term database, supported by --ite-lift-quant:\n\
\n\
none  \n\
+ Do not lift if-then-else in quantified formulas.\n\
\n\
simple  \n\
+ Lift if-then-else in quantified formulas if results in smaller term size.\n\
\n\
all \n\
+ Lift if-then-else in quantified formulas. \n\
\n\
";

const std::string OptionsHandler::s_cbqiBvIneqModeHelp =
    "\
Modes for handling bit-vector inequalities in counterexample-guided\
instantiation, supported by --cbqi-bv-ineq:\n\
\n\
eq-slack (default)  \n\
+ Solve for the inequality using the slack value in the model, e.g.,\
  t > s becomes t = s + ( t-s )^M.\n\
\n\
eq-boundary \n\
+ Solve for the boundary point of the inequality, e.g.,\
  t > s becomes t = s+1.\n\
\n\
keep  \n\
+ Solve for the inequality directly using side conditions for invertibility.\n\
\n\
";

const std::string OptionsHandler::s_cegqiSingleInvHelp = "\
Modes for single invocation techniques, supported by --cegqi-si:\n\
\n\
none  \n\
+ Do not use single invocation techniques.\n\
\n\
use (default) \n\
+ Use single invocation techniques only if grammar is not restrictive.\n\
\n\
all-abort  \n\
+ Always use single invocation techniques, abort if solution reconstruction will likely fail,\
  for instance, when the grammar does not have ITE and solution requires it.\n\
\n\
all \n\
+ Always use single invocation techniques. \n\
\n\
";

const std::string OptionsHandler::s_cegqiSingleInvRconsHelp =
    "\
Modes for reconstruction solutions while using single invocation techniques,\
supported by --cegqi-si-rcons:\n\
\n\
none \n\
+ Do not try to reconstruct solutions in the original (user-provided) grammar\
  when using single invocation techniques. In this mode, solutions produced by\
  CVC4 may violate grammar restrictions.\n\
\n\
try \n\
+ Try to reconstruct solutions in the original grammar when using single\
  invocation techniques in an incomplete (fail-fast) manner.\n\
\n\
all-limit \n\
+ Try to reconstruct solutions in the original grammar, but termintate if a\
  maximum number of rounds for reconstruction is exceeded.\n\
\n\
all \n\
+ Try to reconstruct solutions in the original grammar. In this mode,\
  we do not terminate until a solution is successfully reconstructed. \n\
\n\
";

const std::string OptionsHandler::s_cegisSampleHelp =
    "\
Modes for sampling with counterexample-guided inductive synthesis (CEGIS),\
supported by --cegis-sample:\n\
\n\
none (default) \n\
+ Do not use sampling with CEGIS.\n\
\n\
use \n\
+ Use sampling to accelerate CEGIS. This will rule out solutions for a\
  conjecture when they are not satisfied by a sample point.\n\
\n\
trust  \n\
+ Trust that when a solution for a conjecture is always true under sampling,\
  then it is indeed a solution. Note this option may print out spurious\
  solutions for synthesis conjectures.\n\
\n\
";

const std::string OptionsHandler::s_sygusQueryDumpFileHelp =
    "\
Query file options supported by --sygus-query-gen-dump-files:\n\
\n\
none (default) \n\
+ Do not dump query files when using --sygus-query-gen.\n\
\n\
all \n\
+ Dump all query files.\n\
\n\
unsolved \n\
+ Dump query files that the subsolver did not solve.\n\
\n\
";

const std::string OptionsHandler::s_sygusFilterSolHelp =
    "\
Modes for filtering sygus solutions supported by --sygus-filter-sol:\n\
\n\
none (default) \n\
+ Do not filter sygus solutions.\n\
\n\
strong \n\
+ Filter solutions that are logically stronger than others.\n\
\n\
weak \n\
+ Filter solutions that are logically weaker than others.\n\
\n\
";

const std::string OptionsHandler::s_sygusInvTemplHelp = "\
Template modes for sygus invariant synthesis, supported by --sygus-inv-templ:\n\
\n\
none  \n\
+ Synthesize invariant directly.\n\
\n\
pre  \n\
+ Synthesize invariant based on weakening of precondition .\n\
\n\
post \n\
+ Synthesize invariant based on strengthening of postcondition. \n\
\n\
";

const std::string OptionsHandler::s_sygusActiveGenHelp =
    "\
Modes for actively-generated sygus enumerators, supported by --sygus-active-gen:\n\
\n\
none  \n\
+ Do not use actively-generated sygus enumerators.\n\
\n\
basic  \n\
+ Use basic type enumerator for actively-generated sygus enumerators.\n\
\n\
enum  \n\
+ Use optimized enumerator for actively-generated sygus enumerators.\n\
\n\
var-agnostic \n\
+ Use sygus solver to enumerate terms that are agnostic to variables. \n\
\n\
auto (default) \n\
+ Internally decide the best policy for each enumerator. \n\
\n\
";

const std::string OptionsHandler::s_macrosQuantHelp = "\
Modes for quantifiers macro expansion, supported by --macros-quant-mode:\n\
\n\
all \n\
+ Infer definitions for functions, including those containing quantified formulas.\n\
\n\
ground (default) \n\
+ Only infer ground definitions for functions.\n\
\n\
ground-uf \n\
+ Only infer ground definitions for functions that result in triggers for all free variables.\n\
\n\
";

const std::string OptionsHandler::s_quantDSplitHelp = "\
Modes for quantifiers splitting, supported by --quant-dsplit-mode:\n\
\n\
none \n\
+ Never split quantified formulas.\n\
\n\
default \n\
+ Split quantified formulas over some finite datatypes when finite model finding is enabled.\n\
\n\
agg \n\
+ Aggressively split quantified formulas.\n\
\n\
";

const std::string OptionsHandler::s_quantRepHelp = "\
Modes for quantifiers representative selection, supported by --quant-rep-mode:\n\
\n\
ee \n\
+ Let equality engine choose representatives.\n\
\n\
first (default) \n\
+ Choose terms that appear first.\n\
\n\
depth \n\
+ Choose terms that are of minimal depth.\n\
\n\
";

theory::quantifiers::InstWhenMode OptionsHandler::stringToInstWhenMode(
    std::string option, std::string optarg)
{
  if(optarg == "pre-full") {
    return theory::quantifiers::INST_WHEN_PRE_FULL;
  } else if(optarg == "full") {
    return theory::quantifiers::INST_WHEN_FULL;
  } else if(optarg == "full-delay") {
    return theory::quantifiers::INST_WHEN_FULL_DELAY;
  } else if(optarg == "full-last-call") {
    return theory::quantifiers::INST_WHEN_FULL_LAST_CALL;
  } else if(optarg == "full-delay-last-call") {
    return theory::quantifiers::INST_WHEN_FULL_DELAY_LAST_CALL;
  } else if(optarg == "last-call") {
    return theory::quantifiers::INST_WHEN_LAST_CALL;
  } else if(optarg == "help") {
    puts(s_instWhenHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --inst-when: `") +
                          optarg + "'.  Try --inst-when help.");
  }
}

void OptionsHandler::checkInstWhenMode(std::string option,
                                       theory::quantifiers::InstWhenMode mode)
{
  if(mode == theory::quantifiers::INST_WHEN_PRE_FULL) {
    throw OptionException(std::string("Mode pre-full for ") + option + " is not supported in this release.");
  }
}

theory::quantifiers::LiteralMatchMode OptionsHandler::stringToLiteralMatchMode(
    std::string option, std::string optarg)
{
  if(optarg ==  "none") {
    return theory::quantifiers::LITERAL_MATCH_NONE;
  } else if(optarg ==  "use") {
    return theory::quantifiers::LITERAL_MATCH_USE;
  } else if(optarg ==  "agg-predicate") {
    return theory::quantifiers::LITERAL_MATCH_AGG_PREDICATE;
  } else if(optarg ==  "agg") {
    return theory::quantifiers::LITERAL_MATCH_AGG;
  } else if(optarg ==  "help") {
    puts(s_literalMatchHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --literal-matching: `") +
                          optarg + "'.  Try --literal-matching help.");
  }
}

void OptionsHandler::checkLiteralMatchMode(
    std::string option, theory::quantifiers::LiteralMatchMode mode)
{
}

theory::quantifiers::MbqiMode OptionsHandler::stringToMbqiMode(
    std::string option, std::string optarg)
{
  if (optarg == "none")
  {
    return theory::quantifiers::MBQI_NONE;
  } else if(optarg == "default" || optarg ==  "fmc") {
    return theory::quantifiers::MBQI_FMC;
  } else if(optarg == "trust") {
    return theory::quantifiers::MBQI_TRUST;
  } else if(optarg == "help") {
    puts(s_mbqiModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --mbqi: `") +
                          optarg + "'.  Try --mbqi help.");
  }
}

void OptionsHandler::checkMbqiMode(std::string option,
                                   theory::quantifiers::MbqiMode mode)
{
}

theory::quantifiers::QcfWhenMode OptionsHandler::stringToQcfWhenMode(
    std::string option, std::string optarg)
{
  if(optarg ==  "default") {
    return theory::quantifiers::QCF_WHEN_MODE_DEFAULT;
  } else if(optarg ==  "last-call") {
    return theory::quantifiers::QCF_WHEN_MODE_LAST_CALL;
  } else if(optarg ==  "std") {
    return theory::quantifiers::QCF_WHEN_MODE_STD;
  } else if(optarg ==  "std-h") {
    return theory::quantifiers::QCF_WHEN_MODE_STD_H;
  } else if(optarg ==  "help") {
    puts(s_qcfWhenModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --quant-cf-when: `") +
                          optarg + "'.  Try --quant-cf-when help.");
  }
}

theory::quantifiers::QcfMode OptionsHandler::stringToQcfMode(std::string option,
                                                             std::string optarg)
{
  if(optarg ==  "conflict") {
    return theory::quantifiers::QCF_CONFLICT_ONLY;
  } else if(optarg ==  "default" || optarg == "prop-eq") {
    return theory::quantifiers::QCF_PROP_EQ;
  } else if(optarg ==  "help") {
    puts(s_qcfModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --quant-cf-mode: `") +
                          optarg + "'.  Try --quant-cf-mode help.");
  }
}

theory::quantifiers::UserPatMode OptionsHandler::stringToUserPatMode(
    std::string option, std::string optarg)
{
  if(optarg == "use") {
    return theory::quantifiers::USER_PAT_MODE_USE;
  } else if(optarg ==  "default" || optarg == "trust") {
    return theory::quantifiers::USER_PAT_MODE_TRUST;
  } else if(optarg == "resort") {
    return theory::quantifiers::USER_PAT_MODE_RESORT;
  } else if(optarg == "ignore") {
    return theory::quantifiers::USER_PAT_MODE_IGNORE;
  } else if(optarg == "interleave") {
    return theory::quantifiers::USER_PAT_MODE_INTERLEAVE;
  } else if(optarg ==  "help") {
    puts(s_userPatModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --user-pat: `") +
                          optarg + "'.  Try --user-pat help.");
  }
}

theory::quantifiers::TriggerSelMode OptionsHandler::stringToTriggerSelMode(
    std::string option, std::string optarg)
{
  if(optarg ==  "default" || optarg == "min") {
    return theory::quantifiers::TRIGGER_SEL_MIN;
  } else if(optarg == "max") {
    return theory::quantifiers::TRIGGER_SEL_MAX;
  } else if(optarg == "min-s-max") {
    return theory::quantifiers::TRIGGER_SEL_MIN_SINGLE_MAX;
  } else if(optarg == "min-s-all") {
    return theory::quantifiers::TRIGGER_SEL_MIN_SINGLE_ALL;
  } else if(optarg == "all") {
    return theory::quantifiers::TRIGGER_SEL_ALL;
  } else if(optarg ==  "help") {
    puts(s_triggerSelModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --trigger-sel: `") +
                          optarg + "'.  Try --trigger-sel help.");
  }
}

theory::quantifiers::TriggerActiveSelMode
OptionsHandler::stringToTriggerActiveSelMode(std::string option,
                                             std::string optarg)
{
  if(optarg ==  "default" || optarg == "all") {
    return theory::quantifiers::TRIGGER_ACTIVE_SEL_ALL;
  } else if(optarg == "min") {
    return theory::quantifiers::TRIGGER_ACTIVE_SEL_MIN;
  } else if(optarg == "max") {
    return theory::quantifiers::TRIGGER_ACTIVE_SEL_MAX;
  } else if(optarg ==  "help") {
    puts(s_triggerActiveSelModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --trigger-active-sel: `") +
                          optarg + "'.  Try --trigger-active-sel help.");
  }
}

theory::quantifiers::PrenexQuantMode OptionsHandler::stringToPrenexQuantMode(
    std::string option, std::string optarg)
{
  if(optarg== "default" || optarg== "simple" ) {
    return theory::quantifiers::PRENEX_QUANT_SIMPLE;
  } else if(optarg == "none") {
    return theory::quantifiers::PRENEX_QUANT_NONE;
  } else if(optarg == "dnorm") {
    return theory::quantifiers::PRENEX_QUANT_DISJ_NORMAL;
  } else if(optarg == "norm") {
    return theory::quantifiers::PRENEX_QUANT_NORMAL;
  } else if(optarg ==  "help") {
    puts(s_prenexQuantModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --prenex-quant: `") +
                          optarg + "'.  Try --prenex-quant help.");
  }
}

theory::SygusFairMode OptionsHandler::stringToSygusFairMode(std::string option,
                                                            std::string optarg)
{
  if(optarg == "direct") {
    return theory::SYGUS_FAIR_DIRECT;
  } else if(optarg == "default" || optarg == "dt-size") {
    return theory::SYGUS_FAIR_DT_SIZE;
  } else if(optarg == "dt-height-bound" ){
    return theory::SYGUS_FAIR_DT_HEIGHT_PRED;
  } else if(optarg == "dt-size-bound" ){
    return theory::SYGUS_FAIR_DT_SIZE_PRED;
  } else if(optarg == "none") {
    return theory::SYGUS_FAIR_NONE;
  } else if(optarg ==  "help") {
    puts(s_cegqiFairModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --cegqi-fair: `") +
                          optarg + "'.  Try --cegqi-fair help.");
  }
}

theory::quantifiers::TermDbMode OptionsHandler::stringToTermDbMode(
    std::string option, std::string optarg)
{
  if(optarg == "all" ) {
    return theory::quantifiers::TERM_DB_ALL;
  } else if(optarg == "relevant") {
    return theory::quantifiers::TERM_DB_RELEVANT;
  } else if(optarg ==  "help") {
    puts(s_termDbModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --term-db-mode: `") +
                          optarg + "'.  Try --term-db-mode help.");
  }
}

theory::quantifiers::IteLiftQuantMode OptionsHandler::stringToIteLiftQuantMode(
    std::string option, std::string optarg)
{
  if(optarg == "all" ) {
    return theory::quantifiers::ITE_LIFT_QUANT_MODE_ALL;
  } else if(optarg == "simple") {
    return theory::quantifiers::ITE_LIFT_QUANT_MODE_SIMPLE;
  } else if(optarg == "none") {
    return theory::quantifiers::ITE_LIFT_QUANT_MODE_NONE;
  } else if(optarg ==  "help") {
    puts(s_iteLiftQuantHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --ite-lift-quant: `") +
                          optarg + "'.  Try --ite-lift-quant help.");
  }
}

theory::quantifiers::CbqiBvIneqMode OptionsHandler::stringToCbqiBvIneqMode(
    std::string option, std::string optarg)
{
  if (optarg == "eq-slack")
  {
    return theory::quantifiers::CBQI_BV_INEQ_EQ_SLACK;
  }
  else if (optarg == "eq-boundary")
  {
    return theory::quantifiers::CBQI_BV_INEQ_EQ_BOUNDARY;
  }
  else if (optarg == "keep")
  {
    return theory::quantifiers::CBQI_BV_INEQ_KEEP;
  }
  else if (optarg == "help")
  {
    puts(s_cbqiBvIneqModeHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(std::string("unknown option for --cbqi-bv-ineq: `")
                          + optarg
                          + "'.  Try --cbqi-bv-ineq help.");
  }
}

theory::quantifiers::CegqiSingleInvMode
OptionsHandler::stringToCegqiSingleInvMode(std::string option,
                                           std::string optarg)
{
  if(optarg == "none" ) {
    return theory::quantifiers::CEGQI_SI_MODE_NONE;
  } else if(optarg == "use" || optarg == "default") {
    return theory::quantifiers::CEGQI_SI_MODE_USE;
  } else if(optarg == "all") {
    return theory::quantifiers::CEGQI_SI_MODE_ALL;
  } else if(optarg ==  "help") {
    puts(s_cegqiSingleInvHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --cegqi-si: `") +
                          optarg + "'.  Try --cegqi-si help.");
  }
}

theory::quantifiers::CegqiSingleInvRconsMode
OptionsHandler::stringToCegqiSingleInvRconsMode(std::string option,
                                                std::string optarg)
{
  if (optarg == "none")
  {
    return theory::quantifiers::CEGQI_SI_RCONS_MODE_NONE;
  }
  else if (optarg == "try")
  {
    return theory::quantifiers::CEGQI_SI_RCONS_MODE_TRY;
  }
  else if (optarg == "all")
  {
    return theory::quantifiers::CEGQI_SI_RCONS_MODE_ALL;
  }
  else if (optarg == "all-limit")
  {
    return theory::quantifiers::CEGQI_SI_RCONS_MODE_ALL_LIMIT;
  }
  else if (optarg == "help")
  {
    puts(s_cegqiSingleInvRconsHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(std::string("unknown option for --cegqi-si-rcons: `")
                          + optarg + "'.  Try --cegqi-si-rcons help.");
  }
}

theory::quantifiers::CegisSampleMode OptionsHandler::stringToCegisSampleMode(
    std::string option, std::string optarg)
{
  if (optarg == "none")
  {
    return theory::quantifiers::CEGIS_SAMPLE_NONE;
  }
  else if (optarg == "use")
  {
    return theory::quantifiers::CEGIS_SAMPLE_USE;
  }
  else if (optarg == "trust")
  {
    return theory::quantifiers::CEGIS_SAMPLE_TRUST;
  }
  else if (optarg == "help")
  {
    puts(s_cegisSampleHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(std::string("unknown option for --cegis-sample: `")
                          + optarg
                          + "'.  Try --cegis-sample help.");
  }
}

theory::quantifiers::SygusQueryDumpFilesMode
OptionsHandler::stringToSygusQueryDumpFilesMode(std::string option,
                                                std::string optarg)
{
  if (optarg == "none")
  {
    return theory::quantifiers::SYGUS_QUERY_DUMP_NONE;
  }
  else if (optarg == "all")
  {
    return theory::quantifiers::SYGUS_QUERY_DUMP_ALL;
  }
  else if (optarg == "unsolved")
  {
    return theory::quantifiers::SYGUS_QUERY_DUMP_UNSOLVED;
  }
  else if (optarg == "help")
  {
    puts(s_sygusQueryDumpFileHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(
        std::string("unknown option for --sygus-query-gen-dump-files: `")
        + optarg + "'.  Try --sygus-query-gen-dump-files help.");
  }
}
theory::quantifiers::SygusFilterSolMode
OptionsHandler::stringToSygusFilterSolMode(std::string option,
                                           std::string optarg)
{
  if (optarg == "none")
  {
    return theory::quantifiers::SYGUS_FILTER_SOL_NONE;
  }
  else if (optarg == "strong")
  {
    return theory::quantifiers::SYGUS_FILTER_SOL_STRONG;
  }
  else if (optarg == "weak")
  {
    return theory::quantifiers::SYGUS_FILTER_SOL_WEAK;
  }
  else if (optarg == "help")
  {
    puts(s_sygusFilterSolHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(
        std::string("unknown option for --sygus-filter-sol: `") + optarg
        + "'.  Try --sygus-filter-sol help.");
  }
}

theory::quantifiers::SygusInvTemplMode
OptionsHandler::stringToSygusInvTemplMode(std::string option,
                                          std::string optarg)
{
  if(optarg == "none" ) {
    return theory::quantifiers::SYGUS_INV_TEMPL_MODE_NONE;
  } else if(optarg == "pre") {
    return theory::quantifiers::SYGUS_INV_TEMPL_MODE_PRE;
  } else if(optarg == "post") {
    return theory::quantifiers::SYGUS_INV_TEMPL_MODE_POST;
  } else if(optarg ==  "help") {
    puts(s_sygusInvTemplHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --sygus-inv-templ: `") +
                          optarg + "'.  Try --sygus-inv-templ help.");
  }
}

theory::quantifiers::SygusActiveGenMode
OptionsHandler::stringToSygusActiveGenMode(std::string option,
                                           std::string optarg)
{
  if (optarg == "none")
  {
    return theory::quantifiers::SYGUS_ACTIVE_GEN_NONE;
  }
  else if (optarg == "basic")
  {
    return theory::quantifiers::SYGUS_ACTIVE_GEN_ENUM_BASIC;
  }
  else if (optarg == "enum")
  {
    return theory::quantifiers::SYGUS_ACTIVE_GEN_ENUM;
  }
  else if (optarg == "var-agnostic")
  {
    return theory::quantifiers::SYGUS_ACTIVE_GEN_VAR_AGNOSTIC;
  }
  else if (optarg == "auto")
  {
    return theory::quantifiers::SYGUS_ACTIVE_GEN_AUTO;
  }
  else if (optarg == "help")
  {
    puts(s_sygusActiveGenHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(std::string("unknown option for --sygus-inv-templ: `")
                          + optarg + "'.  Try --sygus-inv-templ help.");
  }
}

theory::quantifiers::MacrosQuantMode OptionsHandler::stringToMacrosQuantMode(
    std::string option, std::string optarg)
{
  if(optarg == "all" ) {
    return theory::quantifiers::MACROS_QUANT_MODE_ALL;
  } else if(optarg == "ground") {
    return theory::quantifiers::MACROS_QUANT_MODE_GROUND;
  } else if(optarg == "ground-uf") {
    return theory::quantifiers::MACROS_QUANT_MODE_GROUND_UF;
  } else if(optarg ==  "help") {
    puts(s_macrosQuantHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --macros-quant-mode: `") +
                          optarg + "'.  Try --macros-quant-mode help.");
  }
}

theory::quantifiers::QuantDSplitMode OptionsHandler::stringToQuantDSplitMode(
    std::string option, std::string optarg)
{
  if(optarg == "none" ) {
    return theory::quantifiers::QUANT_DSPLIT_MODE_NONE;
  } else if(optarg == "default") {
    return theory::quantifiers::QUANT_DSPLIT_MODE_DEFAULT;
  } else if(optarg == "agg") {
    return theory::quantifiers::QUANT_DSPLIT_MODE_AGG;
  } else if(optarg ==  "help") {
    puts(s_quantDSplitHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --quant-dsplit-mode: `") +
                          optarg + "'.  Try --quant-dsplit-mode help.");
  }
}

theory::quantifiers::QuantRepMode OptionsHandler::stringToQuantRepMode(
    std::string option, std::string optarg)
{
  if(optarg == "none" ) {
    return theory::quantifiers::QUANT_REP_MODE_EE;
  } else if(optarg == "first" || optarg == "default") {
    return theory::quantifiers::QUANT_REP_MODE_FIRST;
  } else if(optarg == "depth") {
    return theory::quantifiers::QUANT_REP_MODE_DEPTH;
  } else if(optarg ==  "help") {
    puts(s_quantRepHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --quant-rep-mode: `") +
                          optarg + "'.  Try --quant-rep-mode help.");
  }
}

// theory/bv/options_handlers.h
void OptionsHandler::abcEnabledBuild(std::string option, bool value)
{
#ifndef CVC4_USE_ABC
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an abc-enabled build of CVC4; this binary was not built with abc support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_ABC */
}

void OptionsHandler::abcEnabledBuild(std::string option, std::string value)
{
#ifndef CVC4_USE_ABC
  if(!value.empty()) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an abc-enabled build of CVC4; this binary was not built with abc support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_ABC */
}

void OptionsHandler::satSolverEnabledBuild(std::string option, bool value)
{
#if !defined(CVC4_USE_CRYPTOMINISAT) && !defined(CVC4_USE_CADICAL)
  if (value)
  {
    std::stringstream ss;
    ss << "option `" << option
       << "' requires a CVC4 to be built with CryptoMiniSat or CaDiCaL";
    throw OptionException(ss.str());
  }
#endif
}

void OptionsHandler::satSolverEnabledBuild(std::string option,
                                           std::string value)
{
#if !defined(CVC4_USE_CRYPTOMINISAT) && !defined(CVC4_USE_CADICAL)
  if (!value.empty())
  {
    std::stringstream ss;
    ss << "option `" << option
       << "' requires a CVC4 to be built with CryptoMiniSat or CaDiCaL";
    throw OptionException(ss.str());
  }
#endif
}

const std::string OptionsHandler::s_bvSatSolverHelp = "\
Sat solvers currently supported by the --bv-sat-solver option:\n\
\n\
minisat (default)\n\
\n\
cadical\n\
\n\
cryptominisat\n\
";

theory::bv::SatSolverMode OptionsHandler::stringToSatSolver(std::string option,
                                                            std::string optarg)
{
  if(optarg == "minisat") {
    return theory::bv::SAT_SOLVER_MINISAT;
  } else if(optarg == "cryptominisat") {
    if (options::bitblastMode() == theory::bv::BITBLAST_MODE_LAZY &&
        options::bitblastMode.wasSetByUser()) {
      throwLazyBBUnsupported(theory::bv::SAT_SOLVER_CRYPTOMINISAT);
    }
    if (!options::bitvectorToBool.wasSetByUser()) {
      options::bitvectorToBool.set(true);
    }
    return theory::bv::SAT_SOLVER_CRYPTOMINISAT;
  }
  else if (optarg == "cadical")
  {
    if (options::bitblastMode() == theory::bv::BITBLAST_MODE_LAZY
        && options::bitblastMode.wasSetByUser())
    {
      throwLazyBBUnsupported(theory::bv::SAT_SOLVER_CADICAL);
    }
    if (!options::bitvectorToBool.wasSetByUser())
    {
      options::bitvectorToBool.set(true);
    }
    return theory::bv::SAT_SOLVER_CADICAL;
  } else if(optarg == "help") {
    puts(s_bvSatSolverHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --bv-sat-solver: `") +
                          optarg + "'.  Try --bv-sat-solver=help.");
  }
}

const std::string OptionsHandler::s_bvProofFormatHelp =
    "\
Proof formats currently supported by the --bv-proof-format option:\n\
\n\
  lrat : DRAT with unit propagation hints to accelerate checking (default)\n\
\n\
  drat : Deletion and Resolution Asymmetric Tautology Additions \n\
\n\
  er : Extended Resolution, i.e. resolution with new variable definitions\n\
\n\
This option controls which underlying UNSAT proof format is used in BV proofs.\n\
\n\
Note: Currently this option does nothing. BV proofs are a work in progress!\
";

theory::bv::BvProofFormat OptionsHandler::stringToBvProofFormat(
    std::string option, std::string optarg)
{
  if (optarg == "er")
  {
    return theory::bv::BITVECTOR_PROOF_ER;
  }
  else if (optarg == "lrat")
  {
    return theory::bv::BITVECTOR_PROOF_LRAT;
  }
  else if (optarg == "drat")
  {
    return theory::bv::BITVECTOR_PROOF_DRAT;
  }
  else if (optarg == "help")
  {
    puts(s_bvProofFormatHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(std::string("unknown option for --bv-proof-format: `")
                          + optarg + "'.  Try --bv-proof-format=help.");
  }
}

const std::string OptionsHandler::s_bvOptimizeSatProofHelp =
    "\
Optimization levels currently supported by the --bv-optimize-sat-proof option:\n\
\n\
  none    : Do not optimize the SAT proof\n\
\n\
  proof   : Use drat-trim to shrink the SAT proof\n\
\n\
  formula : Use drat-trim to shrink the SAT proof and formula (default)\
";

theory::bv::BvOptimizeSatProof OptionsHandler::stringToBvOptimizeSatProof(
    std::string option, std::string optarg)
{
  if (optarg == "none")
  {
    return theory::bv::BITVECTOR_OPTIMIZE_SAT_PROOF_NONE;
  }
  else if (optarg == "proof")
  {
    return theory::bv::BITVECTOR_OPTIMIZE_SAT_PROOF_PROOF;
  }
  else if (optarg == "formula")
  {
    return theory::bv::BITVECTOR_OPTIMIZE_SAT_PROOF_FORMULA;
  }
  else if (optarg == "help")
  {
    puts(s_bvOptimizeSatProofHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(std::string("unknown option for --bv-optimize-sat-proof: `")
                          + optarg + "'.  Try --bv-optimize-sat-proof=help.");
  }
}


const std::string OptionsHandler::s_bitblastingModeHelp = "\
Bit-blasting modes currently supported by the --bitblast option:\n\
\n\
lazy (default)\n\
+ Separate boolean structure and term reasoning between the core\n\
  SAT solver and the bv SAT solver\n\
\n\
eager\n\
+ Bitblast eagerly to bv SAT solver\n\
";

theory::bv::BitblastMode OptionsHandler::stringToBitblastMode(
    std::string option, std::string optarg)
{
  if (optarg == "lazy")
  {
    if (!options::bitvectorPropagate.wasSetByUser())
    {
      options::bitvectorPropagate.set(true);
    }
    if (!options::bitvectorEqualitySolver.wasSetByUser())
    {
      options::bitvectorEqualitySolver.set(true);
    }
    if (!options::bitvectorEqualitySlicer.wasSetByUser())
    {
      if (options::incrementalSolving() || options::produceModels())
      {
        options::bitvectorEqualitySlicer.set(theory::bv::BITVECTOR_SLICER_OFF);
      }
      else
      {
        options::bitvectorEqualitySlicer.set(theory::bv::BITVECTOR_SLICER_AUTO);
      }
    }

    if (!options::bitvectorInequalitySolver.wasSetByUser())
    {
      options::bitvectorInequalitySolver.set(true);
    }
    if (!options::bitvectorAlgebraicSolver.wasSetByUser())
    {
      options::bitvectorAlgebraicSolver.set(true);
    }
    if (options::bvSatSolver() != theory::bv::SAT_SOLVER_MINISAT)
    {
      throwLazyBBUnsupported(options::bvSatSolver());
    }
    return theory::bv::BITBLAST_MODE_LAZY;
  }
  else if (optarg == "eager")
  {
    if (!options::bitvectorToBool.wasSetByUser())
    {
      options::bitvectorToBool.set(true);
    }
    return theory::bv::BITBLAST_MODE_EAGER;
  }
  else if (optarg == "help")
  {
    puts(s_bitblastingModeHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(std::string("unknown option for --bitblast: `")
                          + optarg + "'.  Try --bitblast=help.");
  }
}

const std::string OptionsHandler::s_bvSlicerModeHelp = "\
Bit-vector equality slicer modes supported by the --bv-eq-slicer option:\n\
\n\
auto (default)\n\
+ Turn slicer on if input has only equalities over core symbols\n\
\n\
on\n\
+ Turn slicer on\n\
\n\
off\n\
+ Turn slicer off\n\
";

theory::bv::BvSlicerMode OptionsHandler::stringToBvSlicerMode(
    std::string option, std::string optarg)
{
  if(optarg == "auto") {
    return theory::bv::BITVECTOR_SLICER_AUTO;
  } else if(optarg == "on") {
    return theory::bv::BITVECTOR_SLICER_ON;
  } else if(optarg == "off") {
    return theory::bv::BITVECTOR_SLICER_OFF;
  } else if(optarg == "help") {
    puts(s_bvSlicerModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --bv-eq-slicer: `") +
                          optarg + "'.  Try --bv-eq-slicer=help.");
  }
}

const std::string OptionsHandler::s_stringsProcessLoopModeHelp =
    "Loop processing modes supported by the --strings-process-loop-mode "
    "option:\n"
    "\n"
    "full (default)\n"
    "+ Perform full processing of looping word equations\n"
    "\n"
    "simple (default with --strings-fmf)\n"
    "+ Omit normal loop breaking\n"
    "\n"
    "simple-abort\n"
    "+ Abort when normal loop breaking is required\n"
    "\n"
    "none\n"
    "+ Omit loop processing\n"
    "\n"
    "abort\n"
    "+ Abort if looping word equations are encountered\n";

theory::strings::ProcessLoopMode OptionsHandler::stringToStringsProcessLoopMode(
    std::string option, std::string optarg)
{
  if (optarg == "full")
  {
    return theory::strings::ProcessLoopMode::FULL;
  }
  else if (optarg == "simple")
  {
    return theory::strings::ProcessLoopMode::SIMPLE;
  }
  else if (optarg == "simple-abort")
  {
    return theory::strings::ProcessLoopMode::SIMPLE_ABORT;
  }
  else if (optarg == "none")
  {
    return theory::strings::ProcessLoopMode::NONE;
  }
  else if (optarg == "abort")
  {
    return theory::strings::ProcessLoopMode::ABORT;
  }
  else if (optarg == "help")
  {
    puts(s_stringsProcessLoopModeHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(
        std::string("unknown option for --strings-process-loop-mode: `")
        + optarg + "'.  Try --strings-process-loop-mode=help.");
  }
}

const std::string OptionsHandler::s_regExpInterModeHelp =
    "\
Regular expression intersection modes supported by the --re-inter-mode option\
\n\
\n\
all \n\
+ Compute intersections for all regular expressions.\n\
\n\
constant (default)\n\
+ Compute intersections only between regular expressions that do not contain\
re.allchar or re.range\n\
\n\
one-constant\n\
+ Compute intersections only between regular expressions such that at least one\
side does not contain re.allchar or re.range\n\
\n\
none\n\
+ Do not compute intersections for regular expressions\n\
";

theory::strings::RegExpInterMode OptionsHandler::stringToRegExpInterMode(
    std::string option, std::string optarg)
{
  if (optarg == "all")
  {
    return theory::strings::RegExpInterMode::RE_INTER_ALL;
  }
  else if (optarg == "constant")
  {
    return theory::strings::RegExpInterMode::RE_INTER_CONSTANT;
  }
  else if (optarg == "one-constant")
  {
    return theory::strings::RegExpInterMode::RE_INTER_ONE_CONSTANT;
  }
  else if (optarg == "none")
  {
    return theory::strings::RegExpInterMode::RE_INTER_NONE;
  }
  else if (optarg == "help")
  {
    puts(s_regExpInterModeHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(std::string("unknown option for --re-inter-mode: `")
                          + optarg + "'.  Try --re-inter-mode=help.");
  }
}

const std::string OptionsHandler::s_boolToBVModeHelp =
    "\
BoolToBV pass modes supported by the --bool-to-bv option:\n\
\n\
off (default)\n\
+ Don't push any booleans to width one bit-vectors\n\
\n\
ite\n\
+ Try to turn ITEs into BITVECTOR_ITE when possible. It can fail per-formula \n\
  if not all sub-formulas can be turned to bit-vectors\n\
\n\
all\n\
+ Force all booleans to be bit-vectors of width one except at the top level.\n\
  Most aggressive mode\n\
";

preprocessing::passes::BoolToBVMode OptionsHandler::stringToBoolToBVMode(
    std::string option, std::string optarg)
{
  if (optarg == "off")
  {
    return preprocessing::passes::BOOL_TO_BV_OFF;
  }
  else if (optarg == "ite")
  {
    return preprocessing::passes::BOOL_TO_BV_ITE;
  }
  else if (optarg == "all")
  {
    return preprocessing::passes::BOOL_TO_BV_ALL;
  }
  else if (optarg == "help")
  {
    puts(s_boolToBVModeHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(std::string("unknown option for --bool-to-bv: `")
                          + optarg
                          + "'. Try --bool-to-bv=help");
  }
}

void OptionsHandler::setBitblastAig(std::string option, bool arg)
{
  if(arg) {
    if(options::bitblastMode.wasSetByUser()) {
      if(options::bitblastMode() != theory::bv::BITBLAST_MODE_EAGER) {
        throw OptionException("bitblast-aig must be used with eager bitblaster");
      }
    } else {
      theory::bv::BitblastMode mode = stringToBitblastMode("", "eager");
      options::bitblastMode.set(mode);
    }
    if(!options::bitvectorAigSimplifications.wasSetByUser()) {
      options::bitvectorAigSimplifications.set("balance;drw");
    }
  }
}

// theory/uf/options_handlers.h
const std::string OptionsHandler::s_ufssModeHelp = "\
UF with cardinality options currently supported by the --uf-ss option when\n\
combined with finite model finding:\n\
\n\
full \n\
+ Default, use UF with cardinality to find minimal models for uninterpreted\n\
sorts.\n\
\n\
no-minimal \n\
+ Use UF with cardinality to shrink models, but do no enforce minimality.\n\
\n\
none \n\
+ Do not use UF with cardinality to shrink model sizes. \n\
\n\
";

theory::uf::UfssMode OptionsHandler::stringToUfssMode(std::string option,
                                                      std::string optarg)
{
  if(optarg ==  "default" || optarg == "full" ) {
    return theory::uf::UF_SS_FULL;
  } else if(optarg == "no-minimal") {
    return theory::uf::UF_SS_NO_MINIMAL;
  } else if(optarg == "none") {
    return theory::uf::UF_SS_NONE;
  } else if(optarg ==  "help") {
    puts(s_ufssModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --uf-ss: `") +
                          optarg + "'.  Try --uf-ss help.");
  }
}



// theory/options_handlers.h
const std::string OptionsHandler::s_theoryOfModeHelp = "\
TheoryOf modes currently supported by the --theoryof-mode option:\n\
\n\
type (default) \n\
+ type variables, constants and equalities by type\n\
\n\
term \n\
+ type variables as uninterpreted, equalities by the parametric theory\n\
";

theory::TheoryOfMode OptionsHandler::stringToTheoryOfMode(std::string option, std::string optarg) {
  if(optarg == "type") {
    return theory::THEORY_OF_TYPE_BASED;
  } else if(optarg == "term") {
    return theory::THEORY_OF_TERM_BASED;
  } else if(optarg == "help") {
    puts(s_theoryOfModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --theoryof-mode: `") +
                          optarg + "'.  Try --theoryof-mode help.");
  }
}

// theory/options_handlers.h
std::string OptionsHandler::handleUseTheoryList(std::string option, std::string optarg) {
  std::string currentList = options::useTheoryList();
  if(currentList.empty()){
    return optarg;
  } else {
    return currentList +','+ optarg;
  }
}

void OptionsHandler::notifyUseTheoryList(std::string option) {
  d_options->d_useTheoryListListeners.notify();
}



// printer/options_handlers.h
const std::string OptionsHandler::s_modelFormatHelp = "\
Model format modes currently supported by the --model-format option:\n\
\n\
default \n\
+ Print model as expressions in the output language format.\n\
\n\
table\n\
+ Print functional expressions over finite domains in a table format.\n\
";

const std::string OptionsHandler::s_instFormatHelp = "\
Inst format modes currently supported by the --inst-format option:\n\
\n\
default \n\
+ Print instantiations as a list in the output language format.\n\
\n\
szs\n\
+ Print instantiations as SZS compliant proof.\n\
";

ModelFormatMode OptionsHandler::stringToModelFormatMode(std::string option,
                                                        std::string optarg)
{
  if(optarg == "default") {
    return MODEL_FORMAT_MODE_DEFAULT;
  } else if(optarg == "table") {
    return MODEL_FORMAT_MODE_TABLE;
  } else if(optarg == "help") {
    puts(s_modelFormatHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --model-format: `") +
                          optarg + "'.  Try --model-format help.");
  }
}

InstFormatMode OptionsHandler::stringToInstFormatMode(std::string option,
                                                      std::string optarg)
{
  if(optarg == "default") {
    return INST_FORMAT_MODE_DEFAULT;
  } else if(optarg == "szs") {
    return INST_FORMAT_MODE_SZS;
  } else if(optarg == "help") {
    puts(s_instFormatHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --inst-format: `") +
                          optarg + "'.  Try --inst-format help.");
  }
}


// decision/options_handlers.h
const std::string OptionsHandler::s_decisionModeHelp = "\
Decision modes currently supported by the --decision option:\n\
\n\
internal (default)\n\
+ Use the internal decision heuristics of the SAT solver\n\
\n\
justification\n\
+ An ATGP-inspired justification heuristic\n\
\n\
justification-stoponly\n\
+ Use the justification heuristic only to stop early, not for decisions\n\
";

decision::DecisionMode OptionsHandler::stringToDecisionMode(std::string option,
                                                            std::string optarg)
{
  options::decisionStopOnly.set(false);

  if(optarg == "internal") {
    return decision::DECISION_STRATEGY_INTERNAL;
  } else if(optarg == "justification") {
    return decision::DECISION_STRATEGY_JUSTIFICATION;
  } else if(optarg == "justification-stoponly") {
    options::decisionStopOnly.set(true);
    return decision::DECISION_STRATEGY_JUSTIFICATION;
  } else if(optarg == "help") {
    puts(s_decisionModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --decision: `") +
                          optarg + "'.  Try --decision help.");
  }
}

decision::DecisionWeightInternal OptionsHandler::stringToDecisionWeightInternal(
    std::string option, std::string optarg)
{
  if(optarg == "off")
    return decision::DECISION_WEIGHT_INTERNAL_OFF;
  else if(optarg == "max")
    return decision::DECISION_WEIGHT_INTERNAL_MAX;
  else if(optarg == "sum")
    return decision::DECISION_WEIGHT_INTERNAL_SUM;
  else if(optarg == "usr1")
    return decision::DECISION_WEIGHT_INTERNAL_USR1;
  else
    throw OptionException(std::string("--decision-weight-internal must be off, max or sum."));
}


// smt/options_handlers.h
const std::string OptionsHandler::s_simplificationHelp = "\
Simplification modes currently supported by the --simplification option:\n\
\n\
batch (default) \n\
+ save up all ASSERTions; run nonclausal simplification and clausal\n\
  (MiniSat) propagation for all of them only after reaching a querying command\n\
  (CHECKSAT or QUERY or predicate SUBTYPE declaration)\n\
\n\
none\n\
+ do not perform nonclausal simplification\n\
";

SimplificationMode OptionsHandler::stringToSimplificationMode(
    std::string option, std::string optarg)
{
  if(optarg == "batch") {
    return SIMPLIFICATION_MODE_BATCH;
  } else if(optarg == "none") {
    return SIMPLIFICATION_MODE_NONE;
  } else if(optarg == "help") {
    puts(s_simplificationHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --simplification: `") +
                          optarg + "'.  Try --simplification help.");
  }
}

const std::string OptionsHandler::s_modelCoresHelp =
    "\
Model cores modes currently supported by the --model-cores option:\n\
\n\
none (default) \n\
+ do not compute model cores\n\
\n\
simple\n\
+ only include a subset of variables whose values are sufficient to show the\n\
input formula is satisfied by the given model\n\
\n\
non-implied\n\
+ only include a subset of variables whose values, in addition to the values\n\
of variables whose values are implied, are sufficient to show the input\n\
formula is satisfied by the given model\n\
\n\
";

ModelCoresMode OptionsHandler::stringToModelCoresMode(std::string option,
                                                      std::string optarg)
{
  if (optarg == "none")
  {
    return MODEL_CORES_NONE;
  }
  else if (optarg == "simple")
  {
    return MODEL_CORES_SIMPLE;
  }
  else if (optarg == "non-implied")
  {
    return MODEL_CORES_NON_IMPLIED;
  }
  else if (optarg == "help")
  {
    puts(s_modelCoresHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(std::string("unknown option for --model-cores: `")
                          + optarg + "'.  Try --model-cores help.");
  }
}

const std::string OptionsHandler::s_blockModelsHelp =
    "\
Blocking models modes are currently supported by the --block-models option:\n\
\n\
none (default) \n\
+ do not block models\n\
\n\
literals\n\
+ block models based on the SAT skeleton\n\
\n\
values\n\
+ block models based on the concrete model values for the free variables.\n\
\n\
";

BlockModelsMode OptionsHandler::stringToBlockModelsMode(std::string option,
                                                        std::string optarg)
{
  if (optarg == "none")
  {
    return BLOCK_MODELS_NONE;
  }
  else if (optarg == "literals")
  {
    return BLOCK_MODELS_LITERALS;
  }
  else if (optarg == "values")
  {
    return BLOCK_MODELS_VALUES;
    ;
  }
  else if (optarg == "help")
  {
    puts(s_blockModelsHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(std::string("unknown option for --block-models: `")
                          + optarg + "'.  Try --block-models help.");
  }
}

const std::string OptionsHandler::s_sygusSolutionOutModeHelp =
    "\
Modes for sygus solution output, supported by --sygus-out:\n\
\n\
status \n\
+ Print only status for check-synth calls.\n\
\n\
status-and-def (default) \n\
+ Print status followed by definition corresponding to solution.\n\
\n\
status-or-def \n\
+ Print status if infeasible, or definition corresponding to\n\
  solution if feasible.\n\
\n\
sygus-standard \n\
+ Print based on SyGuS standard.\n\
\n\
";

SygusSolutionOutMode OptionsHandler::stringToSygusSolutionOutMode(
    std::string option, std::string optarg)
{
  if (optarg == "status")
  {
    return SYGUS_SOL_OUT_STATUS;
  }
  else if (optarg == "status-and-def")
  {
    return SYGUS_SOL_OUT_STATUS_AND_DEF;
  }
  else if (optarg == "status-or-def")
  {
    return SYGUS_SOL_OUT_STATUS_OR_DEF;
  }
  else if (optarg == "sygus-standard")
  {
    return SYGUS_SOL_OUT_STANDARD;
  }
  else if (optarg == "help")
  {
    puts(s_sygusSolutionOutModeHelp.c_str());
    exit(1);
  }
  else
  {
    throw OptionException(std::string("unknown option for --sygus-out: `")
                          + optarg
                          + "'.  Try --sygus-out help.");
  }
}

void OptionsHandler::setProduceAssertions(std::string option, bool value)
{
  options::produceAssertions.set(value);
  options::interactiveMode.set(value);
}

void OptionsHandler::proofEnabledBuild(std::string option, bool value)
{
#ifdef CVC4_PROOF
  if (value && options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER
      && options::bvSatSolver() != theory::bv::SAT_SOLVER_MINISAT
      && options::bvSatSolver() != theory::bv::SAT_SOLVER_CRYPTOMINISAT)
  {
    throw OptionException(
        "Eager BV proofs only supported when MiniSat or CryptoMiniSat is used");
  }
#else
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires a proofs-enabled build of CVC4; this binary was not built with proof support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_PROOF */
}

void OptionsHandler::LFSCEnabledBuild(std::string option, bool value) {
#ifndef CVC4_USE_LFSC
  if (value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires a build of CVC4 with integrated "
                                  "LFSC; this binary was not built with LFSC";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_LFSC */
}

void OptionsHandler::notifyDumpToFile(std::string option) {
  d_options->d_dumpToFileListeners.notify();
}


void OptionsHandler::notifySetRegularOutputChannel(std::string option) {
  d_options->d_setRegularChannelListeners.notify();
}

void OptionsHandler::notifySetDiagnosticOutputChannel(std::string option) {
  d_options->d_setDiagnosticChannelListeners.notify();
}


std::string OptionsHandler::checkReplayFilename(std::string option, std::string optarg) {
#ifdef CVC4_REPLAY
  if(optarg == "") {
    throw OptionException (std::string("Bad file name for --replay"));
  } else {
    return optarg;
  }
#else /* CVC4_REPLAY */
  throw OptionException("The replay feature was disabled in this build of CVC4.");
#endif /* CVC4_REPLAY */
}

void OptionsHandler::notifySetReplayLogFilename(std::string option) {
  d_options->d_setReplayFilenameListeners.notify();
}

void OptionsHandler::statsEnabledBuild(std::string option, bool value)
{
#ifndef CVC4_STATISTICS_ON
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires a statistics-enabled build of CVC4; this binary was not built with statistics support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_STATISTICS_ON */
}

void OptionsHandler::threadN(std::string option) {
  throw OptionException(option + " is not a real option by itself.  Use e.g. --thread0=\"--random-seed=10 --random-freq=0.02\" --thread1=\"--random-seed=20 --random-freq=0.05\"");
}

void OptionsHandler::notifyDumpMode(std::string option)
{
  d_options->d_setDumpModeListeners.notify();
}


// expr/options_handlers.h
void OptionsHandler::setDefaultExprDepthPredicate(std::string option, int depth) {
  if(depth < -1) {
    throw OptionException("--default-expr-depth requires a positive argument, or -1.");
  }
}

void OptionsHandler::setDefaultDagThreshPredicate(std::string option, int dag) {
  if(dag < 0) {
    throw OptionException("--default-dag-thresh requires a nonnegative argument.");
  }
}

void OptionsHandler::notifySetDefaultExprDepth(std::string option) {
  d_options->d_setDefaultExprDepthListeners.notify();
}

void OptionsHandler::notifySetDefaultDagThresh(std::string option) {
  d_options->d_setDefaultDagThreshListeners.notify();
}

void OptionsHandler::notifySetPrintExprTypes(std::string option) {
  d_options->d_setPrintExprTypesListeners.notify();
}


// main/options_handlers.h

static void print_config (const char * str, std::string config) {
  std::string s(str);
  unsigned sz = 14;
  if (s.size() < sz) s.resize(sz, ' ');
  std::cout << s << ": " << config << std::endl;
}

static void print_config_cond (const char * str, bool cond = false) {
  print_config(str, cond ? "yes" : "no");
}

void OptionsHandler::copyright(std::string option) {
  std::cout << Configuration::copyright() << std::endl;
  exit(0);
}

void OptionsHandler::showConfiguration(std::string option) {
  std::cout << Configuration::about() << std::endl;

  print_config ("version", Configuration::getVersionString());

  if(Configuration::isGitBuild()) {
    const char* branchName = Configuration::getGitBranchName();
    if(*branchName == '\0')  { branchName = "-"; }
    std::stringstream ss;
    ss << "git ["
       << branchName << " "
       << std::string(Configuration::getGitCommit()).substr(0, 8)
       << (Configuration::hasGitModifications() ? " (with modifications)" : "")
       << "]";
    print_config("scm", ss.str());
  } else {
    print_config_cond("scm", false);
  }
  
  std::cout << std::endl;

  std::stringstream ss;
  ss << Configuration::getVersionMajor() << "."
     << Configuration::getVersionMinor() << "."
     << Configuration::getVersionRelease();
  print_config("library", ss.str());
  
  std::cout << std::endl;

  print_config_cond("debug code", Configuration::isDebugBuild());
  print_config_cond("statistics", Configuration::isStatisticsBuild());
  print_config_cond("replay", Configuration::isReplayBuild());
  print_config_cond("tracing", Configuration::isTracingBuild());
  print_config_cond("dumping", Configuration::isDumpingBuild());
  print_config_cond("muzzled", Configuration::isMuzzledBuild());
  print_config_cond("assertions", Configuration::isAssertionBuild());
  print_config_cond("proof", Configuration::isProofBuild());
  print_config_cond("coverage", Configuration::isCoverageBuild());
  print_config_cond("profiling", Configuration::isProfilingBuild());
  print_config_cond("asan", Configuration::isAsanBuild());
  print_config_cond("competition", Configuration::isCompetitionBuild());
  
  std::cout << std::endl;
  
  print_config_cond("abc", Configuration::isBuiltWithAbc());
  print_config_cond("cln", Configuration::isBuiltWithCln());
  print_config_cond("glpk", Configuration::isBuiltWithGlpk());
  print_config_cond("cadical", Configuration::isBuiltWithCadical());
  print_config_cond("cryptominisat", Configuration::isBuiltWithCryptominisat());
  print_config_cond("drat2er", Configuration::isBuiltWithDrat2Er());
  print_config_cond("gmp", Configuration::isBuiltWithGmp());
  print_config_cond("lfsc", Configuration::isBuiltWithLfsc());
  print_config_cond("readline", Configuration::isBuiltWithReadline());
  print_config_cond("symfpu", Configuration::isBuiltWithSymFPU());
  
  exit(0);
}

static void printTags(unsigned ntags, char const* const* tags)
{
  std::cout << "available tags:";
  for (unsigned i = 0; i < ntags; ++ i)
  {
    std::cout << "  " << tags[i] << std::endl;
  }
  std::cout << std::endl;
}

void OptionsHandler::showDebugTags(std::string option)
{
  if (!Configuration::isDebugBuild())
  {
    throw OptionException("debug tags not available in non-debug builds");
  }
  else if (!Configuration::isTracingBuild())
  {
    throw OptionException("debug tags not available in non-tracing builds");
  }
  printTags(Configuration::getNumDebugTags(),Configuration::getDebugTags());
  exit(0);
}

void OptionsHandler::showTraceTags(std::string option)
{
  if (!Configuration::isTracingBuild())
  {
    throw OptionException("trace tags not available in non-tracing build");
  }
  printTags(Configuration::getNumTraceTags(), Configuration::getTraceTags());
  exit(0);
}

static std::string suggestTags(char const* const* validTags,
                               std::string inputTag,
                               char const* const* additionalTags)
{
  DidYouMean didYouMean;

  const char* opt;
  for (size_t i = 0; (opt = validTags[i]) != nullptr; ++i)
  {
    didYouMean.addWord(validTags[i]);
  }
  if (additionalTags != nullptr)
  {
    for (size_t i = 0; (opt = additionalTags[i]) != nullptr; ++i)
    {
      didYouMean.addWord(additionalTags[i]);
    }
  }

  return didYouMean.getMatchAsString(inputTag);
}

void OptionsHandler::enableTraceTag(std::string option, std::string optarg)
{
  if(!Configuration::isTracingBuild())
  {
    throw OptionException("trace tags not available in non-tracing builds");
  }
  else if(!Configuration::isTraceTag(optarg.c_str()))
  {
    if (optarg == "help")
    {
      printTags(
          Configuration::getNumTraceTags(), Configuration::getTraceTags());
      exit(0);
    }

    throw OptionException(
        std::string("trace tag ") + optarg + std::string(" not available.")
        + suggestTags(Configuration::getTraceTags(), optarg, nullptr));
  }
  Trace.on(optarg);
}

void OptionsHandler::enableDebugTag(std::string option, std::string optarg)
{
  if (!Configuration::isDebugBuild())
  {
    throw OptionException("debug tags not available in non-debug builds");
  }
  else if (!Configuration::isTracingBuild())
  {
    throw OptionException("debug tags not available in non-tracing builds");
  }

  if (!Configuration::isDebugTag(optarg.c_str())
      && !Configuration::isTraceTag(optarg.c_str()))
  {
    if (optarg == "help")
    {
      printTags(
          Configuration::getNumDebugTags(), Configuration::getDebugTags());
      exit(0);
    }

    throw OptionException(std::string("debug tag ") + optarg
                          + std::string(" not available.")
                          + suggestTags(Configuration::getDebugTags(),
                                        optarg,
                                        Configuration::getTraceTags()));
  }
  Debug.on(optarg);
  Trace.on(optarg);
}

OutputLanguage OptionsHandler::stringToOutputLanguage(std::string option,
                                                      std::string optarg)
{
  if(optarg == "help") {
    options::languageHelp.set(true);
    return language::output::LANG_AUTO;
  }

  try {
    return language::toOutputLanguage(optarg);
  } catch(OptionException& oe) {
    throw OptionException("Error in " + option + ": " + oe.getMessage() +
                          "\nTry --output-language help");
  }

  Unreachable();
}

InputLanguage OptionsHandler::stringToInputLanguage(std::string option,
                                                    std::string optarg)
{
  if(optarg == "help") {
    options::languageHelp.set(true);
    return language::input::LANG_AUTO;
  }

  try {
    return language::toInputLanguage(optarg);
  } catch(OptionException& oe) {
    throw OptionException("Error in " + option + ": " + oe.getMessage() + "\nTry --language help");
  }

  Unreachable();
}

/* options/base_options_handlers.h */
void OptionsHandler::setVerbosity(std::string option, int value)
{
  if(Configuration::isMuzzledBuild()) {
    DebugChannel.setStream(&CVC4::null_os);
    TraceChannel.setStream(&CVC4::null_os);
    NoticeChannel.setStream(&CVC4::null_os);
    ChatChannel.setStream(&CVC4::null_os);
    MessageChannel.setStream(&CVC4::null_os);
    WarningChannel.setStream(&CVC4::null_os);
  } else {
    if(value < 2) {
      ChatChannel.setStream(&CVC4::null_os);
    } else {
      ChatChannel.setStream(&std::cout);
    }
    if(value < 1) {
      NoticeChannel.setStream(&CVC4::null_os);
    } else {
      NoticeChannel.setStream(&std::cout);
    }
    if(value < 0) {
      MessageChannel.setStream(&CVC4::null_os);
      WarningChannel.setStream(&CVC4::null_os);
    } else {
      MessageChannel.setStream(&std::cout);
      WarningChannel.setStream(&std::cerr);
    }
  }
}

void OptionsHandler::increaseVerbosity(std::string option) {
  options::verbosity.set(options::verbosity() + 1);
  setVerbosity(option, options::verbosity());
}

void OptionsHandler::decreaseVerbosity(std::string option) {
  options::verbosity.set(options::verbosity() - 1);
  setVerbosity(option, options::verbosity());
}


}/* CVC4::options namespace */
}/* CVC4 namespace */

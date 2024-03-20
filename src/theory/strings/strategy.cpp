/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the strategy of the theory of strings.
 */

#include "theory/strings/strategy.h"

#include "options/strings_options.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

std::ostream& operator<<(std::ostream& out, InferStep s)
{
  switch (s)
  {
    case InferStep::NONE: out << "none"; break;
    case InferStep::BREAK: out << "break"; break;
    case InferStep::CHECK_INIT: out << "check_init"; break;
    case InferStep::CHECK_CONST_EQC: out << "check_const_eqc"; break;
    case InferStep::CHECK_EXTF_EVAL: out << "check_extf_eval"; break;
    case InferStep::CHECK_CYCLES: out << "check_cycles"; break;
    case InferStep::CHECK_FLAT_FORMS: out << "check_flat_forms"; break;
    case InferStep::CHECK_NORMAL_FORMS_EQ_PROP:
      out << "check_normal_forms_eq_prop";
      break;
    case InferStep::CHECK_NORMAL_FORMS_EQ:
      out << "check_normal_forms_eq";
      break;
    case InferStep::CHECK_NORMAL_FORMS_DEQ:
      out << "check_normal_forms_deq";
      break;
    case InferStep::CHECK_CODES: out << "check_codes"; break;
    case InferStep::CHECK_LENGTH_EQC: out << "check_length_eqc"; break;
    case InferStep::CHECK_REGISTER_TERMS_NF:
      out << "check_register_terms_nf";
      break;
    case InferStep::CHECK_EXTF_REDUCTION_EAGER:
      out << "check_extf_reduction_eager";
      break;
    case InferStep::CHECK_EXTF_REDUCTION: out << "check_extf_reduction"; break;
    case InferStep::CHECK_MEMBERSHIP_EAGER:
      out << "check_membership_eager";
      break;
    case InferStep::CHECK_MEMBERSHIP: out << "check_membership"; break;
    case InferStep::CHECK_CARDINALITY: out << "check_cardinality"; break;
    case InferStep::CHECK_SEQUENCES_ARRAY_CONCAT:
      out << "check_sequences_update_concat_terms";
      break;
    case InferStep::CHECK_SEQUENCES_ARRAY:
      out << "check_sequences_array";
      break;
    case InferStep::CHECK_SEQUENCES_ARRAY_EAGER:
      out << "check_sequences_array_eager";
      break;
    case InferStep::UNKNOWN: out << "?"; break;
    default:
      Unreachable();
      out << "?unhandled";
      break;
  }
  return out;
}

Strategy::Strategy(Env& env) : EnvObj(env), d_strategy_init(false) {}

Strategy::~Strategy() {}

bool Strategy::isStrategyInit() const { return d_strategy_init; }

bool Strategy::hasStrategyEffort(Theory::Effort e) const
{
  return d_strat_steps.find(e) != d_strat_steps.end();
}

std::vector<std::pair<InferStep, int> >::iterator Strategy::stepBegin(
    Theory::Effort e)
{
  std::map<Theory::Effort, std::pair<unsigned, unsigned> >::const_iterator it =
      d_strat_steps.find(e);
  Assert(it != d_strat_steps.end());
  return d_infer_steps.begin() + it->second.first;
}

std::vector<std::pair<InferStep, int> >::iterator Strategy::stepEnd(
    Theory::Effort e)
{
  std::map<Theory::Effort, std::pair<unsigned, unsigned> >::const_iterator it =
      d_strat_steps.find(e);
  Assert(it != d_strat_steps.end());
  return d_infer_steps.begin() + it->second.second;
}

void Strategy::addStrategyStep(InferStep s, int effort, bool addBreak)
{
  // must run check init first
  Assert((s == InferStep::CHECK_INIT) == d_infer_steps.empty());
  d_infer_steps.push_back(std::pair<InferStep, int>(s, effort));
  if (addBreak)
  {
    d_infer_steps.push_back(std::pair<InferStep, int>(InferStep::BREAK, 0));
  }
}

void Strategy::initializeStrategy()
{
  // initialize the strategy if not already done so
  if (!d_strategy_init)
  {
    std::map<Theory::Effort, unsigned> step_begin;
    std::map<Theory::Effort, unsigned> step_end;
    d_strategy_init = true;
    // beginning indices
    step_begin[Theory::EFFORT_FULL] = 0;
    // add the inference steps
    addStrategyStep(InferStep::CHECK_INIT);
    addStrategyStep(InferStep::CHECK_CONST_EQC);
    addStrategyStep(InferStep::CHECK_EXTF_EVAL, 0);
    if (options().strings.seqArray == options::SeqArrayMode::EAGER)
    {
      addStrategyStep(InferStep::CHECK_SEQUENCES_ARRAY_EAGER);
    }
    // we must check cycles before using flat forms
    addStrategyStep(InferStep::CHECK_CYCLES);
    if (options().strings.stringFlatForms)
    {
      addStrategyStep(InferStep::CHECK_FLAT_FORMS);
    }
    addStrategyStep(InferStep::CHECK_EXTF_REDUCTION_EAGER);
    addStrategyStep(InferStep::CHECK_MEMBERSHIP_EAGER);
    addStrategyStep(InferStep::CHECK_NORMAL_FORMS_EQ_PROP);
    addStrategyStep(InferStep::CHECK_NORMAL_FORMS_EQ);
    addStrategyStep(InferStep::CHECK_EXTF_EVAL, 1);
    addStrategyStep(InferStep::CHECK_NORMAL_FORMS_DEQ);
    addStrategyStep(InferStep::CHECK_CODES);
    if (options().strings.stringLenNorm)
    {
      addStrategyStep(InferStep::CHECK_LENGTH_EQC);
    }
    if (options().strings.seqArray != options::SeqArrayMode::NONE)
    {
      addStrategyStep(InferStep::CHECK_SEQUENCES_ARRAY_CONCAT);
      addStrategyStep(InferStep::CHECK_SEQUENCES_ARRAY);
    }
    if (options().strings.stringExp)
    {
      addStrategyStep(InferStep::CHECK_EXTF_REDUCTION);
    }
    addStrategyStep(InferStep::CHECK_MEMBERSHIP);
    addStrategyStep(InferStep::CHECK_CARDINALITY);
    step_end[Theory::EFFORT_FULL] = d_infer_steps.size() - 1;
    if (options().strings.stringModelBasedReduction)
    {
      step_begin[Theory::EFFORT_LAST_CALL] = d_infer_steps.size();
      addStrategyStep(InferStep::CHECK_EXTF_EVAL, 3);
      if (options().strings.stringExp)
      {
        addStrategyStep(InferStep::CHECK_EXTF_REDUCTION);
      }
      addStrategyStep(InferStep::CHECK_MEMBERSHIP);
      step_end[Theory::EFFORT_LAST_CALL] = d_infer_steps.size() - 1;
    }
    // set the beginning/ending ranges
    for (const std::pair<const Theory::Effort, unsigned>& it_begin : step_begin)
    {
      Theory::Effort e = it_begin.first;
      std::map<Theory::Effort, unsigned>::iterator it_end = step_end.find(e);
      Assert(it_end != step_end.end());
      d_strat_steps[e] =
          std::pair<unsigned, unsigned>(it_begin.second, it_end->second);
    }
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

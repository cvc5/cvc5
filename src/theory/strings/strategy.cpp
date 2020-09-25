/*********************                                                        */
/*! \file strategy.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the strategy of the theory of strings.
 **/

#include "theory/strings/strategy.h"

#include "options/strings_options.h"

namespace CVC4 {
namespace theory {
namespace strings {

std::ostream& operator<<(std::ostream& out, InferStep s)
{
  switch (s)
  {
    case BREAK: out << "break"; break;
    case CHECK_INIT: out << "check_init"; break;
    case CHECK_CONST_EQC: out << "check_const_eqc"; break;
    case CHECK_EXTF_EVAL: out << "check_extf_eval"; break;
    case CHECK_CYCLES: out << "check_cycles"; break;
    case CHECK_FLAT_FORMS: out << "check_flat_forms"; break;
    case CHECK_NORMAL_FORMS_EQ: out << "check_normal_forms_eq"; break;
    case CHECK_NORMAL_FORMS_DEQ: out << "check_normal_forms_deq"; break;
    case CHECK_CODES: out << "check_codes"; break;
    case CHECK_LENGTH_EQC: out << "check_length_eqc"; break;
    case CHECK_EXTF_REDUCTION: out << "check_extf_reduction"; break;
    case CHECK_MEMBERSHIP: out << "check_membership"; break;
    case CHECK_CARDINALITY: out << "check_cardinality"; break;
    default: out << "?"; break;
  }
  return out;
}

Strategy::Strategy() : d_strategy_init(false) {}

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
  Assert((s == CHECK_INIT) == d_infer_steps.empty());
  d_infer_steps.push_back(std::pair<InferStep, int>(s, effort));
  if (addBreak)
  {
    d_infer_steps.push_back(std::pair<InferStep, int>(BREAK, 0));
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
    if (options::stringEager())
    {
      step_begin[Theory::EFFORT_STANDARD] = 0;
    }
    // add the inference steps
    addStrategyStep(CHECK_INIT);
    addStrategyStep(CHECK_CONST_EQC);
    addStrategyStep(CHECK_EXTF_EVAL, 0);
    // we must check cycles before using flat forms
    addStrategyStep(CHECK_CYCLES);
    if (options::stringFlatForms())
    {
      addStrategyStep(CHECK_FLAT_FORMS);
    }
    addStrategyStep(CHECK_EXTF_REDUCTION, 1);
    if (options::stringEager())
    {
      // do only the above inferences at standard effort, if applicable
      step_end[Theory::EFFORT_STANDARD] = d_infer_steps.size() - 1;
    }
    if (!options::stringEagerLen())
    {
      addStrategyStep(CHECK_REGISTER_TERMS_PRE_NF);
    }
    addStrategyStep(CHECK_NORMAL_FORMS_EQ);
    addStrategyStep(CHECK_EXTF_EVAL, 1);
    if (!options::stringEagerLen() && options::stringLenNorm())
    {
      addStrategyStep(CHECK_LENGTH_EQC, 0, false);
      addStrategyStep(CHECK_REGISTER_TERMS_NF);
    }
    addStrategyStep(CHECK_NORMAL_FORMS_DEQ);
    addStrategyStep(CHECK_CODES);
    if (options::stringEagerLen() && options::stringLenNorm())
    {
      addStrategyStep(CHECK_LENGTH_EQC);
    }
    if (options::stringExp() && !options::stringGuessModel())
    {
      addStrategyStep(CHECK_EXTF_REDUCTION, 2);
    }
    addStrategyStep(CHECK_MEMBERSHIP);
    addStrategyStep(CHECK_CARDINALITY);
    step_end[Theory::EFFORT_FULL] = d_infer_steps.size() - 1;
    if (options::stringExp() && options::stringGuessModel())
    {
      step_begin[Theory::EFFORT_LAST_CALL] = d_infer_steps.size();
      // these two steps are run in parallel
      addStrategyStep(CHECK_EXTF_REDUCTION, 2, false);
      addStrategyStep(CHECK_EXTF_EVAL, 3);
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
}  // namespace CVC4

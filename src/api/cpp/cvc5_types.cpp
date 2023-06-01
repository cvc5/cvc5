/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common cvc5 types. These types are used internally as well as externally and
 * the language bindings are generated automatically.
 */

#include <cvc5/cvc5_types.h>

#include <iostream>

#include "base/check.h"

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, UnknownExplanation e)
{
  switch (e)
  {
    case UnknownExplanation::REQUIRES_FULL_CHECK:
      out << "REQUIRES_FULL_CHECK";
      break;
    case UnknownExplanation::INCOMPLETE: out << "INCOMPLETE"; break;
    case UnknownExplanation::TIMEOUT: out << "TIMEOUT"; break;
    case UnknownExplanation::RESOURCEOUT: out << "RESOURCEOUT"; break;
    case UnknownExplanation::MEMOUT: out << "MEMOUT"; break;
    case UnknownExplanation::INTERRUPTED: out << "INTERRUPTED"; break;
    case UnknownExplanation::UNSUPPORTED: out << "UNSUPPORTED"; break;
    case UnknownExplanation::OTHER: out << "OTHER"; break;
    case UnknownExplanation::REQUIRES_CHECK_AGAIN:
      out << "REQUIRES_CHECK_AGAIN";
      break;
    case UnknownExplanation::UNKNOWN_REASON: out << "UNKNOWN_REASON"; break;
    default: Unhandled() << e;
  }
  return out;
}

}  // namespace cvc5

namespace cvc5::modes {

std::ostream& operator<<(std::ostream& out, BlockModelsMode bmode)
{
  switch (bmode)
  {
    case BlockModelsMode::LITERALS: out << "literals"; break;
    case BlockModelsMode::VALUES: out << "values"; break;
    default: out << "?";
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, LearnedLitType ltype)
{
  switch (ltype)
  {
    case LearnedLitType::LEARNED_LIT_PREPROCESS_SOLVED:
      out << "preprocess_solved";
      break;
    case LearnedLitType::LEARNED_LIT_PREPROCESS: out << "preprocess"; break;
    case LearnedLitType::LEARNED_LIT_INPUT: out << "input"; break;
    case LearnedLitType::LEARNED_LIT_SOLVABLE: out << "solvable"; break;
    case LearnedLitType::LEARNED_LIT_CONSTANT_PROP:
      out << "constant_prop";
      break;
    case LearnedLitType::LEARNED_LIT_INTERNAL: out << "internal"; break;
    case LearnedLitType::LEARNED_LIT_UNKNOWN: out << "unknown"; break;
    default: out << "?";
  }
  return out;
}
std::ostream& operator<<(std::ostream& out, ProofComponent pc)
{
  switch (pc)
  {
    case ProofComponent::PROOF_COMPONENT_RAW_PREPROCESS:
      out << "raw_preprocess";
      break;
    case ProofComponent::PROOF_COMPONENT_PREPROCESS: out << "preprocess"; break;
    case ProofComponent::PROOF_COMPONENT_SAT: out << "sat"; break;
    case ProofComponent::PROOF_COMPONENT_THEORY_LEMMAS:
      out << "theory_lemmas";
      break;
    case ProofComponent::PROOF_COMPONENT_FULL: out << "full"; break;
    default: out << "?";
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, FindSynthTarget fst)
{
  switch (fst)
  {
    case FindSynthTarget::FIND_SYNTH_TARGET_ENUM: out << "enum"; break;
    case FindSynthTarget::FIND_SYNTH_TARGET_REWRITE: out << "rewrite"; break;
    case FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_UNSOUND:
      out << "rewrite_unsound";
      break;
    case FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_INPUT:
      out << "rewrite_input";
      break;
    case FindSynthTarget::FIND_SYNTH_TARGET_QUERY: out << "query"; break;
    default: out << "?";
  }
  return out;
}

}  // namespace cvc5::modes

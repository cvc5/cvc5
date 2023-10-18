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
    case LearnedLitType::PREPROCESS_SOLVED: out << "preprocess_solved"; break;
    case LearnedLitType::PREPROCESS: out << "preprocess"; break;
    case LearnedLitType::INPUT: out << "input"; break;
    case LearnedLitType::SOLVABLE: out << "solvable"; break;
    case LearnedLitType::CONSTANT_PROP: out << "constant_prop"; break;
    case LearnedLitType::INTERNAL: out << "internal"; break;
    case LearnedLitType::UNKNOWN: out << "unknown"; break;
    default: out << "?";
  }
  return out;
}
std::ostream& operator<<(std::ostream& out, ProofComponent pc)
{
  switch (pc)
  {
    case ProofComponent::RAW_PREPROCESS: out << "raw_preprocess"; break;
    case ProofComponent::PREPROCESS: out << "preprocess"; break;
    case ProofComponent::SAT: out << "sat"; break;
    case ProofComponent::THEORY_LEMMAS: out << "theory_lemmas"; break;
    case ProofComponent::FULL: out << "full"; break;
    default: out << "?";
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, ProofFormat pc)
{
  switch (pc)
  {
    case ProofFormat::NONE: out << "none"; break;
    case ProofFormat::DOT: out << "dot"; break;
    case ProofFormat::LFSC: out << "lfsc"; break;
    case ProofFormat::ALETHE: out << "alethe"; break;
    case ProofFormat::DEFAULT: out << "default"; break;
    default: out << "?";
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, FindSynthTarget fst)
{
  switch (fst)
  {
    case FindSynthTarget::ENUM: out << "enum"; break;
    case FindSynthTarget::REWRITE: out << "rewrite"; break;
    case FindSynthTarget::REWRITE_UNSOUND: out << "rewrite_unsound"; break;
    case FindSynthTarget::REWRITE_INPUT: out << "rewrite_input"; break;
    case FindSynthTarget::QUERY: out << "query"; break;
    default: out << "?";
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, InputLanguage lang)
{
  switch (lang)
  {
    case InputLanguage::SMT_LIB_2_6: out << "SMT_LIB_2_6"; break;
    case InputLanguage::SYGUS_2_1: out << "SYGUS_2_1"; break;
    case InputLanguage::UNKNOWN: out << "UNKNOWN"; break;
    default: out << "?";
  }
  return out;
}

}  // namespace cvc5::modes

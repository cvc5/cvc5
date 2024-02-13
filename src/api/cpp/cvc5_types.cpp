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

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_types.h>

#include <iostream>
#include <sstream>

#include "base/check.h"

namespace cvc5 {
std::ostream& operator<<(std::ostream& out, RoundingMode rm)
{
  switch (rm)
  {
    case RoundingMode::ROUND_NEAREST_TIES_TO_EVEN:
      out << "ROUND_NEAREST_TIES_TO_EVEN";
      break;
    case RoundingMode::ROUND_TOWARD_POSITIVE:
      out << "ROUND_TOWARD_POSITIVE";
      break;
    case RoundingMode::ROUND_TOWARD_NEGATIVE:
      out << "ROUND_TOWARD_NEGATIVE";
      break;
    case RoundingMode::ROUND_TOWARD_ZERO: out << "ROUND_TOWARD_ZERO"; break;
    case RoundingMode::ROUND_NEAREST_TIES_TO_AWAY:
      out << "ROUND_NEAREST_TIES_TO_AWAY";
      break;
    default:
      throw CVC5ApiException("unhandled enum value '"
                             + std::to_string(static_cast<int32_t>(rm))
                             + "' encountered");
  }
  return out;
}
}  // namespace cvc5

namespace std {
std::string to_string(cvc5::RoundingMode rm)
{
  std::stringstream ss;
  ss << rm;
  return ss.str();
}
}  // namespace std

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
    default:
      throw CVC5ApiException("unhandled enum value '"
                             + std::to_string(static_cast<int32_t>(e))
                             + "' encountered");
  }
  return out;
}
}  // namespace cvc5

namespace std {
std::string to_string(cvc5::UnknownExplanation exp)
{
  std::stringstream ss;
  ss << exp;
  return ss.str();
}
}  // namespace std

namespace cvc5::modes {
std::ostream& operator<<(std::ostream& out, BlockModelsMode mode)
{
  switch (mode)
  {
    case BlockModelsMode::LITERALS: out << "LITERALS"; break;
    case BlockModelsMode::VALUES: out << "VALUES"; break;
    default: out << "?";
  }
  return out;
}

}  // namespace cvc5::modes

namespace std {
std::string to_string(cvc5::modes::BlockModelsMode mode)
{
  std::stringstream ss;
  ss << mode;
  return ss.str();
}
}  // namespace std

namespace cvc5::modes {
std::ostream& operator<<(std::ostream& out, LearnedLitType ltype)
{
  switch (ltype)
  {
    case LearnedLitType::PREPROCESS_SOLVED: out << "PREPROCESS_SOLVED"; break;
    case LearnedLitType::PREPROCESS: out << "PREPROCESS"; break;
    case LearnedLitType::INPUT: out << "INPUT"; break;
    case LearnedLitType::SOLVABLE: out << "SOLVABLE"; break;
    case LearnedLitType::CONSTANT_PROP: out << "CONSTANT_PROP"; break;
    case LearnedLitType::INTERNAL: out << "INTERNAL"; break;
    case LearnedLitType::UNKNOWN: out << "UNKNOWN"; break;
    default: out << "?";
  }
  return out;
}
}  // namespace cvc5::modes

namespace std {
std::string to_string(cvc5::modes::LearnedLitType type)
{
  std::stringstream ss;
  ss << type;
  return ss.str();
}
}  // namespace std

namespace cvc5::modes {
std::ostream& operator<<(std::ostream& out, ProofComponent pc)
{
  switch (pc)
  {
    case ProofComponent::RAW_PREPROCESS: out << "RAW_PREPROCESS"; break;
    case ProofComponent::PREPROCESS: out << "PREPROCESS"; break;
    case ProofComponent::SAT: out << "SAT"; break;
    case ProofComponent::THEORY_LEMMAS: out << "THEORY_LEMMAS"; break;
    case ProofComponent::FULL: out << "FULL"; break;
    default: out << "?";
  }
  return out;
}
}  // namespace cvc5::modes

namespace std {
std::string to_string(cvc5::modes::ProofComponent pc)
{
  std::stringstream ss;
  ss << pc;
  return ss.str();
}
}  // namespace std

namespace cvc5::modes {
std::ostream& operator<<(std::ostream& out, ProofFormat format)
{
  switch (format)
  {
    case ProofFormat::NONE: out << "NONE"; break;
    case ProofFormat::DOT: out << "DOT"; break;
    case ProofFormat::LFSC: out << "LFSC"; break;
    case ProofFormat::ALETHE: out << "ALETHE"; break;
    case ProofFormat::DEFAULT: out << "DEFAULT"; break;
    default: out << "?";
  }
  return out;
}
}  // namespace cvc5::modes

namespace std {
std::string to_string(cvc5::modes::ProofFormat format)
{
  std::stringstream ss;
  ss << format;
  return ss.str();
}
}  // namespace std

namespace cvc5::modes {
std::ostream& operator<<(std::ostream& out, FindSynthTarget target)
{
  switch (target)
  {
    case FindSynthTarget::ENUM: out << "ENUM"; break;
    case FindSynthTarget::REWRITE: out << "REWRITE"; break;
    case FindSynthTarget::REWRITE_UNSOUND: out << "REWRITE_UNSOUND"; break;
    case FindSynthTarget::REWRITE_INPUT: out << "REWRITE_INPUT"; break;
    case FindSynthTarget::QUERY: out << "QUERY"; break;
    default: out << "?";
  }
  return out;
}
}  // namespace cvc5::modes

namespace std {
std::string to_string(cvc5::modes::FindSynthTarget target)
{
  std::stringstream ss;
  ss << target;
  return ss.str();
}
}  // namespace std

namespace cvc5::modes {
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

namespace std {
std::string to_string(cvc5::modes::InputLanguage lang)
{
  std::stringstream ss;
  ss << lang;
  return ss.str();
}
}  // namespace std

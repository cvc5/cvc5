/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include <cvc5/cvc5.h>

#include <iostream>

#include "api/c/cvc5_checks.h"

/* -------------------------------------------------------------------------- */
/* Cvc5Kind                                                                   */
/* -------------------------------------------------------------------------- */

size_t cvc5_kind_hash(Cvc5Kind kind)
{
  return std::hash<cvc5::Kind>{}(static_cast<cvc5::Kind>(kind));
}

const char* cvc5_kind_to_string(Cvc5Kind kind)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_KIND(kind);
  str = "CVC5_KIND_" + std::to_string(static_cast<cvc5::Kind>(kind));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* Cvc5SortKind                                                               */
/* -------------------------------------------------------------------------- */

size_t cvc5_sort_kind_hash(Cvc5SortKind kind)
{
  return std::hash<cvc5::SortKind>{}(static_cast<cvc5::SortKind>(kind));
}

const char* cvc5_sort_kind_to_string(Cvc5SortKind kind)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT_KIND(kind);
  str = "CVC5_SORT_KIND_" + std::to_string(static_cast<cvc5::SortKind>(kind));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* Cvc5RoundingMode                                                           */
/* -------------------------------------------------------------------------- */

const char* cvc5_rm_to_string(Cvc5RoundingMode rm)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_RM(rm);
  str = std::to_string(static_cast<cvc5::RoundingMode>(rm));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* Cvc5UnknownExplanation                                                     */
/* -------------------------------------------------------------------------- */

const char* cvc5_unknown_explanation_to_string(Cvc5UnknownExplanation exp)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_UNKNOWN_EXPLANATION(exp);
  str = std::to_string(static_cast<cvc5::UnknownExplanation>(exp));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* Cvc5LearnedLitType                                                         */
/* -------------------------------------------------------------------------- */

const char* cvc5_modes_learned_lit_type_to_string(Cvc5LearnedLitType type)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_LEARNED_LIT_TYPE(type);
  str = std::to_string(static_cast<cvc5::modes::LearnedLitType>(type));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* Cvc5BlockedModelsMode                                                      */
/* -------------------------------------------------------------------------- */

const char* cvc5_modes_block_models_mode_to_string(Cvc5BlockModelsMode mode)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_BLOCK_MODELS_MODE(mode);
  str = std::to_string(static_cast<cvc5::modes::BlockModelsMode>(mode));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* Cvc5ProofComponent                                                         */
/* -------------------------------------------------------------------------- */

const char* cvc5_modes_proof_component_to_string(Cvc5ProofComponent pc)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_PROOF_COMPONENT(pc);
  str = std::to_string(static_cast<cvc5::modes::ProofComponent>(pc));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* Cvc5ProofFormat                                                            */
/* -------------------------------------------------------------------------- */

const char* cvc5_modes_proof_format_to_string(Cvc5ProofFormat format)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_PROOF_FORMAT(format);
  str = std::to_string(static_cast<cvc5::modes::ProofFormat>(format));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* Cvc5FindSynthTarget                                                        */
/* -------------------------------------------------------------------------- */

const char* cvc5_modes_find_synthesis_target_to_string(
    Cvc5FindSynthTarget target)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_FIND_SYNTH_TARGET(target);
  str = std::to_string(static_cast<cvc5::modes::FindSynthTarget>(target));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* Cvc5InputLanguage                                                          */
/* -------------------------------------------------------------------------- */

const char* cvc5_modes_input_language_to_string(Cvc5InputLanguage lang)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_INPUT_LANGUAGE(lang);
  str = std::to_string(static_cast<cvc5::modes::InputLanguage>(lang));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

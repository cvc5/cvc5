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

#include <cstring>
#include <fstream>
#include <iostream>
#include <variant>

#include "api/c/cvc5_c_structs.h"
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
/* Cvc5ProofRule                                                              */
/* -------------------------------------------------------------------------- */

const char* cvc5_proof_rule_to_string(Cvc5ProofRule rule)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_PROOF_RULE(rule);
  str = std::to_string(static_cast<cvc5::ProofRule>(rule));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_proof_rule_hash(Cvc5ProofRule rule)
{
  return std::hash<cvc5::ProofRule>{}(static_cast<cvc5::ProofRule>(rule));
}

/* -------------------------------------------------------------------------- */
/* Cvc5ProofRewriteRule                                                       */
/* -------------------------------------------------------------------------- */

const char* cvc5_proof_rewrite_rule_to_string(Cvc5ProofRewriteRule rule)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_PROOF_REWRITE_RULE(rule);
  str = std::to_string(static_cast<cvc5::ProofRewriteRule>(rule));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_proof_rewrite_rule_hash(Cvc5ProofRewriteRule rule)
{
  return std::hash<cvc5::ProofRewriteRule>{}(
      static_cast<cvc5::ProofRewriteRule>(rule));
}

/* -------------------------------------------------------------------------- */
/* Cvc5FindSynthTarget                                                        */
/* -------------------------------------------------------------------------- */

const char* cvc5_modes_find_synth_target_to_string(Cvc5FindSynthTarget target)
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

/* -------------------------------------------------------------------------- */
/* Cvc5Skolemid                                                               */
/* -------------------------------------------------------------------------- */

const char* cvc5_skolem_id_to_string(Cvc5SkolemId id)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SKOLEM_ID(id);
  str = std::to_string(static_cast<cvc5::SkolemId>(id));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_skolem_id_hash(Cvc5SkolemId id)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SKOLEM_ID(id);
  res = std::hash<cvc5::SkolemId>{}(static_cast<cvc5::SkolemId>(id));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* -------------------------------------------------------------------------- */
/* Cvc5Sort                                                                   */
/* -------------------------------------------------------------------------- */

Cvc5Sort cvc5_sort_copy(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->copy(sort);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_sort_release(Cvc5Sort sort)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  sort->d_tm->release(sort);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_sort_is_equal(Cvc5Sort a, Cvc5Sort b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a == b;
  }
  else
  {
    res = a->d_sort == b->d_sort;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_disequal(Cvc5Sort a, Cvc5Sort b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    printf("1\n");
    res = a != b;
  }
  else
  {
    printf("2\n");
    res = a->d_sort != b->d_sort;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

int64_t cvc5_sort_compare(Cvc5Sort a, Cvc5Sort b)
{
  int64_t res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(a);
  CVC5_CAPI_CHECK_SORT(b);
  res = a->d_sort < b->d_sort ? -1 : (a->d_sort > b->d_sort ? 1 : 0);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5SortKind cvc5_sort_get_kind(Cvc5Sort sort)
{
  Cvc5SortKind res = CVC5_SORT_KIND_INTERNAL_SORT_KIND;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = static_cast<Cvc5SortKind>(sort->d_sort.getKind());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_has_symbol(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.hasSymbol();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_sort_get_symbol(Cvc5Sort sort)
{
  const char* res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_API_CHECK(cvc5_sort_has_symbol(sort))
      << "cannot get symbol of sort that has no symbol";
  static thread_local std::string str;
  if (sort->d_sort.hasSymbol())
  {
    str = sort->d_sort.getSymbol();
    res = str.c_str();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_boolean(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isBoolean();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_integer(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isInteger();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_real(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isReal();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_string(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isString();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_regexp(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isRegExp();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_rm(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isRoundingMode();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_bv(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isBitVector();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_fp(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isFloatingPoint();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_dt(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isDatatype();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_dt_constructor(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isDatatypeConstructor();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_dt_selector(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isDatatypeSelector();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_dt_tester(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isDatatypeTester();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_dt_updater(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isDatatypeUpdater();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_fun(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isFunction();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_predicate(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isPredicate();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_tuple(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isTuple();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_nullable(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isNullable();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_record(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isRecord();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_array(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isArray();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_ff(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isFiniteField();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_set(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isSet();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_bag(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isBag();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_sequence(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isSequence();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_abstract(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isAbstract();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_uninterpreted_sort(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isUninterpretedSort();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_uninterpreted_sort_constructor(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isUninterpretedSortConstructor();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_sort_is_instantiated(Cvc5Sort sort)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (sort)
  {
    res = sort->d_sort.isInstantiated();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_sort_get_uninterpreted_sort_constructor(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(sort->d_sort.getUninterpretedSortConstructor());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Datatype cvc5_sort_get_datatype(Cvc5Sort sort)
{
  Cvc5Datatype res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_dt(sort->d_sort.getDatatype());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_sort_instantiate(Cvc5Sort sort,
                               size_t size,
                               const Cvc5Sort params[])
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_NOT_NULL(params);
  std::vector<cvc5::Sort> cparams;
  for (uint32_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_SORT_AT_IDX(params, i);
    cparams.push_back(params[i]->d_sort);
  }
  res = sort->d_tm->export_sort(sort->d_sort.instantiate(cparams));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Sort* cvc5_sort_get_instantiated_parameters(Cvc5Sort sort,
                                                      size_t* size)
{
  static thread_local std::vector<Cvc5Sort> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto sorts = sort->d_sort.getInstantiatedParameters();
  auto tm = sort->d_tm;
  for (auto& s : sorts)
  {
    res.push_back(tm->export_sort(s));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

Cvc5Sort cvc5_sort_substitute(Cvc5Sort sort, Cvc5Sort s, Cvc5Sort replacement)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_SORT(s);
  CVC5_CAPI_CHECK_SORT(replacement);
  res = sort->d_tm->export_sort(
      sort->d_sort.substitute(s->d_sort, replacement->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_sort_substitute_sorts(Cvc5Sort sort,
                                    size_t size,
                                    const Cvc5Sort sorts[],
                                    const Cvc5Sort replacements[])
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_NOT_NULL(sorts);
  CVC5_CAPI_CHECK_NOT_NULL(replacements);
  std::vector<cvc5::Sort> csorts;
  for (uint32_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_SORT_AT_IDX(sorts, i);
    csorts.push_back(sorts[i]->d_sort);
  }
  std::vector<cvc5::Sort> creplacements;
  for (uint32_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_SORT_AT_IDX(replacements, i);
    creplacements.push_back(replacements[i]->d_sort);
  }
  res = sort->d_tm->export_sort(sort->d_sort.substitute(csorts, creplacements));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_sort_to_string(Cvc5Sort sort)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  str = sort->d_sort.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_sort_hash(Cvc5Sort sort)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = std::hash<cvc5::Sort>{}(sort->d_sort);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Datatype constructor sort ------------------------------------------- */

size_t cvc5_sort_dt_constructor_get_arity(Cvc5Sort sort)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_sort.getDatatypeConstructorArity();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Sort* cvc5_sort_dt_constructor_get_domain(Cvc5Sort sort, size_t* size)
{
  static thread_local std::vector<Cvc5Sort> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto sorts = sort->d_sort.getDatatypeConstructorDomainSorts();
  auto tm = sort->d_tm;
  for (auto& s : sorts)
  {
    res.push_back(tm->export_sort(s));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

Cvc5Sort cvc5_sort_dt_constructor_get_codomain(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(
      sort->d_sort.getDatatypeConstructorCodomainSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Dataype Selector sort ------------------------------------------------ */

Cvc5Sort cvc5_sort_dt_selector_get_domain(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(sort->d_sort.getDatatypeSelectorDomainSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_sort_dt_selector_get_codomain(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(sort->d_sort.getDatatypeSelectorCodomainSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Datatype Tester sort ------------------------------------------------ */

Cvc5Sort cvc5_sort_dt_tester_get_domain(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(sort->d_sort.getDatatypeTesterDomainSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_sort_dt_tester_get_codomain(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(sort->d_sort.getDatatypeTesterCodomainSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Function sort ------------------------------------------------------- */

size_t cvc5_sort_fun_get_arity(Cvc5Sort sort)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_sort.getFunctionArity();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Sort* cvc5_sort_fun_get_domain(Cvc5Sort sort, size_t* size)
{
  static thread_local std::vector<Cvc5Sort> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto sorts = sort->d_sort.getFunctionDomainSorts();
  auto tm = sort->d_tm;
  for (auto& s : sorts)
  {
    res.push_back(tm->export_sort(s));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

Cvc5Sort cvc5_sort_fun_get_codomain(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(sort->d_sort.getFunctionCodomainSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Array sort ---------------------------------------------------------- */

Cvc5Sort cvc5_sort_array_get_index_sort(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(sort->d_sort.getArrayIndexSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_sort_array_get_element_sort(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(sort->d_sort.getArrayElementSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Set sort ------------------------------------------------------------ */

Cvc5Sort cvc5_sort_set_get_element_sort(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(sort->d_sort.getSetElementSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Bag sort ------------------------------------------------------------ */

Cvc5Sort cvc5_sort_bag_get_element_sort(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(sort->d_sort.getBagElementSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Sequence sort ------------------------------------------------------- */

Cvc5Sort cvc5_sort_sequence_get_element_sort(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(sort->d_sort.getSequenceElementSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Abstract sort ------------------------------------------------------- */

Cvc5SortKind cvc5_sort_abstract_get_kind(Cvc5Sort sort)
{
  Cvc5SortKind res = CVC5_SORT_KIND_INTERNAL_SORT_KIND;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = static_cast<Cvc5SortKind>(sort->d_sort.getAbstractedKind());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Uninterpreted sort constructor sort --------------------------------- */

size_t cvc5_sort_uninterpreted_sort_constructor_get_arity(Cvc5Sort sort)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_sort.getUninterpretedSortConstructorArity();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Bit-vector sort ----------------------------------------------------- */

uint32_t cvc5_sort_bv_get_size(Cvc5Sort sort)
{
  uint32_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_sort.getBitVectorSize();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Finite field sort --------------------------------------------------- */

const char* cvc5_sort_ff_get_size(Cvc5Sort sort)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  str = sort->d_sort.getFiniteFieldSize();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* Floating-point sort ------------------------------------------------- */

uint32_t cvc5_sort_fp_get_exp_size(Cvc5Sort sort)
{
  uint32_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_sort.getFloatingPointExponentSize();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

uint32_t cvc5_sort_fp_get_sig_size(Cvc5Sort sort)
{
  uint32_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_sort.getFloatingPointSignificandSize();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Datatype sort ------------------------------------------------------- */

size_t cvc5_sort_dt_get_arity(Cvc5Sort sort)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_sort.getDatatypeArity();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Tuple sort ---------------------------------------------------------- */

size_t cvc5_sort_tuple_get_length(Cvc5Sort sort)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_sort.getTupleLength();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Sort* cvc5_sort_tuple_get_element_sorts(Cvc5Sort sort, size_t* size)
{
  static thread_local std::vector<Cvc5Sort> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto sorts = sort->d_sort.getTupleSorts();
  auto tm = sort->d_tm;
  for (auto& s : sorts)
  {
    res.push_back(tm->export_sort(s));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

Cvc5Sort cvc5_sort_nullable_get_element_sort(Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(sort->d_sort.getNullableElementSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* -------------------------------------------------------------------------- */
/* Cvc5Datatype                                                               */
/* -------------------------------------------------------------------------- */

/* Cvc5DatatypeConstructorDecl ----------------------------------------- */

Cvc5DatatypeConstructorDecl cvc5_dt_cons_decl_copy(
    Cvc5DatatypeConstructorDecl decl)
{
  Cvc5DatatypeConstructorDecl res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS_DECL(decl);
  res = decl->d_tm->copy(decl);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_dt_cons_decl_release(Cvc5DatatypeConstructorDecl decl)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS_DECL(decl);
  decl->d_tm->release(decl);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_dt_cons_decl_is_equal(Cvc5DatatypeConstructorDecl a,
                                Cvc5DatatypeConstructorDecl b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a == b;
  }
  else
  {
    res = a->d_decl == b->d_decl;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_dt_cons_decl_add_selector(Cvc5DatatypeConstructorDecl decl,
                                    const char* name,
                                    Cvc5Sort sort)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS_DECL(decl);
  CVC5_CAPI_CHECK_NOT_NULL(name);
  CVC5_CAPI_CHECK_SORT(sort);
  decl->d_decl.addSelector(name, sort->d_sort);
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_dt_cons_decl_add_selector_self(Cvc5DatatypeConstructorDecl decl,
                                         const char* name)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS_DECL(decl);
  CVC5_CAPI_CHECK_NOT_NULL(name);
  decl->d_decl.addSelectorSelf(name);
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_dt_cons_decl_add_selector_unresolved(Cvc5DatatypeConstructorDecl decl,
                                               const char* name,
                                               const char* unres_name)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS_DECL(decl);
  CVC5_CAPI_CHECK_NOT_NULL(name);
  CVC5_CAPI_CHECK_NOT_NULL(unres_name);
  decl->d_decl.addSelectorUnresolved(name, unres_name);
  CVC5_CAPI_TRY_CATCH_END;
}

const char* cvc5_dt_cons_decl_to_string(Cvc5DatatypeConstructorDecl decl)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS_DECL(decl);
  str = decl->d_decl.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_dt_cons_decl_hash(Cvc5DatatypeConstructorDecl decl)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS_DECL(decl);
  res = std::hash<cvc5::DatatypeConstructorDecl>{}(decl->d_decl);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Cvc5DatatypeDecl ---------------------------------------------------- */

Cvc5DatatypeDecl cvc5_dt_decl_copy(Cvc5DatatypeDecl decl)
{
  Cvc5DatatypeDecl res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_DECL(decl);
  res = decl->d_tm->copy(decl);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_dt_decl_release(Cvc5DatatypeDecl decl)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_DECL(decl);
  decl->d_tm->release(decl);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_dt_decl_is_equal(Cvc5DatatypeDecl a, Cvc5DatatypeDecl b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a == b;
  }
  else
  {
    res = a->d_decl == b->d_decl;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_dt_decl_add_constructor(Cvc5DatatypeDecl decl,
                                  Cvc5DatatypeConstructorDecl cdecl)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_DECL(decl);
  CVC5_CAPI_CHECK_NOT_NULL(cdecl);
  decl->d_decl.addConstructor(cdecl->d_decl);
  CVC5_CAPI_TRY_CATCH_END;
}

size_t cvc5_dt_decl_get_num_constructors(Cvc5DatatypeDecl decl)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_DECL(decl);
  res = decl->d_decl.getNumConstructors();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_dt_decl_is_parametric(Cvc5DatatypeDecl decl)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_DECL(decl);
  res = decl->d_decl.isParametric();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_dt_decl_is_resolved(Cvc5DatatypeDecl decl)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_DECL(decl);
  res = decl->d_decl.isResolved();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_dt_decl_to_string(Cvc5DatatypeDecl decl)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_DECL(decl);
  str = decl->d_decl.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

const char* cvc5_dt_decl_get_name(Cvc5DatatypeDecl decl)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_DECL(decl);
  str = decl->d_decl.getName();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_dt_decl_hash(Cvc5DatatypeDecl decl)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_DECL(decl);
  res = std::hash<cvc5::DatatypeDecl>{}(decl->d_decl);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Cvc5DatatypeSelector ------------------------------------------------ */

Cvc5DatatypeSelector cvc5_dt_sel_copy(Cvc5DatatypeSelector sel)
{
  Cvc5DatatypeSelector res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_SEL(sel);
  res = sel->d_tm->copy(sel);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_dt_sel_release(Cvc5DatatypeSelector sel)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_SEL(sel);
  sel->d_tm->release(sel);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_dt_sel_is_equal(Cvc5DatatypeSelector a, Cvc5DatatypeSelector b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a == b;
  }
  else
  {
    res = a->d_dt_sel == b->d_dt_sel;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_dt_sel_get_name(Cvc5DatatypeSelector sel)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_SEL(sel);
  str = sel->d_dt_sel.getName();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

Cvc5Term cvc5_dt_sel_get_term(Cvc5DatatypeSelector sel)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_SEL(sel);
  res = sel->d_tm->export_term(sel->d_dt_sel.getTerm());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_dt_sel_get_updater_term(Cvc5DatatypeSelector sel)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_SEL(sel);
  res = sel->d_tm->export_term(sel->d_dt_sel.getUpdaterTerm());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_dt_sel_get_codomain_sort(Cvc5DatatypeSelector sel)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_SEL(sel);
  res = sel->d_tm->export_sort(sel->d_dt_sel.getCodomainSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_dt_sel_to_string(Cvc5DatatypeSelector sel)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_SEL(sel);
  str = sel->d_dt_sel.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_dt_sel_hash(Cvc5DatatypeSelector sel)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_SEL(sel);
  res = std::hash<cvc5::DatatypeSelector>{}(sel->d_dt_sel);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Cvc5DatatypeConstructor --------------------------------------------- */

Cvc5DatatypeConstructor cvc5_dt_cons_copy(Cvc5DatatypeConstructor cons)
{
  Cvc5DatatypeConstructor res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS(cons);
  res = cons->d_tm->copy(cons);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_dt_cons_release(Cvc5DatatypeConstructor cons)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS(cons);
  cons->d_tm->release(cons);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_dt_cons_is_equal(Cvc5DatatypeConstructor a, Cvc5DatatypeConstructor b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a == b;
  }
  else
  {
    res = a->d_dt_cons == b->d_dt_cons;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_dt_cons_get_name(Cvc5DatatypeConstructor cons)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS(cons);
  str = cons->d_dt_cons.getName();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

Cvc5Term cvc5_dt_cons_get_term(Cvc5DatatypeConstructor cons)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS(cons);
  res = cons->d_tm->export_term(cons->d_dt_cons.getTerm());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_dt_cons_get_instantiated_term(Cvc5DatatypeConstructor cons,
                                            Cvc5Sort sort)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS(cons);
  CVC5_CAPI_CHECK_SORT(sort);
  res = cons->d_tm->export_term(
      cons->d_dt_cons.getInstantiatedTerm(sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_dt_cons_get_tester_term(Cvc5DatatypeConstructor cons)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS(cons);
  res = cons->d_tm->export_term(cons->d_dt_cons.getTesterTerm());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

size_t cvc5_dt_cons_get_num_selectors(Cvc5DatatypeConstructor cons)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS(cons);
  res = cons->d_dt_cons.getNumSelectors();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5DatatypeSelector cvc5_dt_cons_get_selector(Cvc5DatatypeConstructor cons,
                                               size_t index)
{
  Cvc5DatatypeSelector res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS(cons);
  res = cons->d_tm->export_dt_sel(cons->d_dt_cons[index]);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5DatatypeSelector cvc5_dt_cons_get_selector_by_name(
    Cvc5DatatypeConstructor cons, const char* name)
{
  Cvc5DatatypeSelector res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS(cons);
  CVC5_CAPI_CHECK_NOT_NULL(name);
  res = cons->d_tm->export_dt_sel(cons->d_dt_cons.getSelector(name));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_dt_cons_to_string(Cvc5DatatypeConstructor cons)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS(cons);
  str = cons->d_dt_cons.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_dt_cons_hash(Cvc5DatatypeConstructor cons)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT_CONS(cons);
  res = std::hash<cvc5::DatatypeConstructor>{}(cons->d_dt_cons);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Cvc5Datatype -------------------------------------------------------- */

Cvc5Datatype cvc5_dt_copy(Cvc5Datatype dt)
{
  Cvc5Datatype res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  res = dt->d_tm->copy(dt);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_dt_release(Cvc5Datatype dt)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  dt->d_tm->release(dt);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_dt_is_equal(Cvc5Datatype a, Cvc5Datatype b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a == b;
  }
  else
  {
    res = a->d_dt == b->d_dt;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5DatatypeConstructor cvc5_dt_get_constructor(Cvc5Datatype dt, size_t idx)
{
  Cvc5DatatypeConstructor res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  res = dt->d_tm->export_dt_cons(dt->d_dt[idx]);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5DatatypeConstructor cvc5_dt_get_constructor_by_name(Cvc5Datatype dt,
                                                        const char* name)
{
  Cvc5DatatypeConstructor res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  CVC5_CAPI_CHECK_NOT_NULL(name);
  res = dt->d_tm->export_dt_cons(dt->d_dt.getConstructor(name));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5DatatypeSelector cvc5_dt_get_selector(Cvc5Datatype dt, const char* name)
{
  Cvc5DatatypeSelector res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  CVC5_CAPI_CHECK_NOT_NULL(name);
  res = dt->d_tm->export_dt_sel(dt->d_dt.getSelector(name));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_dt_get_name(Cvc5Datatype dt)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  str = dt->d_dt.getName();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_dt_get_num_constructors(Cvc5Datatype dt)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  res = dt->d_dt.getNumConstructors();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Sort* cvc5_dt_get_parameters(Cvc5Datatype dt, size_t* size)
{
  static thread_local std::vector<Cvc5Sort> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto sorts = dt->d_dt.getParameters();
  auto tm = dt->d_tm;
  for (auto& s : sorts)
  {
    res.push_back(tm->export_sort(s));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

bool cvc5_dt_is_parametric(Cvc5Datatype dt)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  res = dt->d_dt.isParametric();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_dt_is_codatatype(Cvc5Datatype dt)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  res = dt->d_dt.isCodatatype();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_dt_is_tuple(Cvc5Datatype dt)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  res = dt->d_dt.isTuple();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_dt_is_record(Cvc5Datatype dt)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  res = dt->d_dt.isRecord();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_dt_is_finite(Cvc5Datatype dt)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  res = dt->d_dt.isFinite();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_dt_is_well_founded(Cvc5Datatype dt)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  res = dt->d_dt.isWellFounded();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_dt_to_string(Cvc5Datatype dt)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  str = dt->d_dt.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_dt_hash(Cvc5Datatype dt)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_DT(dt);
  res = std::hash<cvc5::Datatype>{}(dt->d_dt);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* -------------------------------------------------------------------------- */
/* Cvc5Term                                                                   */
/* -------------------------------------------------------------------------- */

Cvc5Term cvc5_term_copy(Cvc5Term term)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_tm->copy(term);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_term_release(Cvc5Term term)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  term->d_tm->release(term);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_term_is_equal(Cvc5Term a, Cvc5Term b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a == b;
  }
  else
  {
    res = a->d_term == b->d_term;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_disequal(Cvc5Term a, Cvc5Term b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a != b;
  }
  else
  {
    res = a->d_term != b->d_term;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

int64_t cvc5_term_compare(Cvc5Term a, Cvc5Term b)
{
  int64_t res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(a);
  CVC5_CAPI_CHECK_TERM(b);
  res = a->d_term < b->d_term ? -1 : (a->d_term > b->d_term ? 1 : 0);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

size_t cvc5_term_get_num_children(Cvc5Term term)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getNumChildren();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_term_get_child(Cvc5Term term, size_t index)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_tm->export_term(term->d_term[index]);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

uint64_t cvc5_term_get_id(Cvc5Term term)
{
  uint64_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getId();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Kind cvc5_term_get_kind(Cvc5Term term)
{
  Cvc5Kind res = CVC5_KIND_INTERNAL_KIND;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = static_cast<Cvc5Kind>(term->d_term.getKind());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_term_get_sort(Cvc5Term term)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_tm->export_sort(term->d_term.getSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_term_substitute_term(Cvc5Term term,
                                   Cvc5Term t,
                                   Cvc5Term replacement)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  CVC5_CAPI_CHECK_TERM(t);
  CVC5_CAPI_CHECK_TERM(replacement);
  res = term->d_tm->export_term(
      term->d_term.substitute(t->d_term, replacement->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_term_substitute_terms(Cvc5Term term,
                                    size_t size,
                                    const Cvc5Term terms[],
                                    const Cvc5Term replacements[])
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  CVC5_CAPI_CHECK_NOT_NULL(terms);
  CVC5_CAPI_CHECK_NOT_NULL(replacements);
  std::vector<cvc5::Term> cterms;
  for (uint32_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(terms, i);
    cterms.push_back(terms[i]->d_term);
  }
  std::vector<cvc5::Term> creplacements;
  for (uint32_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(replacements, i);
    creplacements.push_back(replacements[i]->d_term);
  }
  res = term->d_tm->export_term(term->d_term.substitute(cterms, creplacements));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_has_op(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.hasOp();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Op cvc5_term_get_op(Cvc5Term term)
{
  Cvc5Op res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_tm->export_op(term->d_term.getOp());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_has_symbol(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.hasSymbol();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_term_get_symbol(Cvc5Term term)
{
  const char* res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  CVC5_API_CHECK(cvc5_term_has_symbol(term))
      << "cannot get symbol of term that has no symbol";
  static thread_local std::string str;
  if (term->d_term.hasSymbol())
  {
    str = term->d_term.getSymbol();
    res = str.c_str();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_term_to_string(Cvc5Term term)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  str = term->d_term.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

int32_t cvc5_term_get_real_or_integer_value_sign(Cvc5Term term)
{
  int32_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getRealOrIntegerValueSign();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_int32_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isInt32Value();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

int32_t cvc5_term_get_int32_value(Cvc5Term term)
{
  int32_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getInt32Value();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_uint32_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isUInt32Value();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

uint32_t cvc5_term_get_uint32_value(Cvc5Term term)
{
  uint32_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getUInt32Value();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_int64_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isInt64Value();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

int64_t cvc5_term_get_int64_value(Cvc5Term term)
{
  int64_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getInt64Value();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_uint64_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isUInt64Value();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

uint64_t cvc5_term_get_uint64_value(Cvc5Term term)
{
  uint64_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getUInt64Value();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_integer_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isIntegerValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_term_get_integer_value(Cvc5Term term)
{
  static thread_local std::string res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getIntegerValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res.c_str();
}

bool cvc5_term_is_string_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isStringValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const wchar_t* cvc5_term_get_string_value(Cvc5Term term)
{
  static thread_local std::wstring res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getStringValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res.c_str();
}

bool cvc5_term_is_real32_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isReal32Value();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_term_get_real32_value(Cvc5Term term, int32_t* num, uint32_t* den)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  CVC5_CAPI_CHECK_NOT_NULL(num);
  CVC5_CAPI_CHECK_NOT_NULL(den);
  std::tie(*num, *den) = term->d_term.getReal32Value();
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_term_is_real64_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isReal64Value();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_term_get_real64_value(Cvc5Term term, int64_t* num, uint64_t* den)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  CVC5_CAPI_CHECK_NOT_NULL(num);
  CVC5_CAPI_CHECK_NOT_NULL(den);
  std::tie(*num, *den) = term->d_term.getReal64Value();
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_term_is_real_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isRealValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_term_get_real_value(Cvc5Term term)
{
  static thread_local std::string res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getRealValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res.c_str();
}

bool cvc5_term_is_const_array(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isConstArray();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_term_get_const_array_base(Cvc5Term term)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_tm->export_term(term->d_term.getConstArrayBase());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_boolean_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isBooleanValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_get_boolean_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getBooleanValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_bv_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isBitVectorValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_term_get_bv_value(Cvc5Term term, uint32_t base)
{
  static thread_local std::string res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getBitVectorValue(base);
  CVC5_CAPI_TRY_CATCH_END;
  return res.c_str();
}

bool cvc5_term_is_ff_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isFiniteFieldValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_term_get_ff_value(Cvc5Term term)
{
  static thread_local std::string res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getFiniteFieldValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res.c_str();
}

bool cvc5_term_is_uninterpreted_sort_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isUninterpretedSortValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_term_get_uninterpreted_sort_value(Cvc5Term term)
{
  static thread_local std::string res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.getUninterpretedSortValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res.c_str();
}

bool cvc5_term_is_tuple_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isTupleValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Term* cvc5_term_get_tuple_value(Cvc5Term term, size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto terms = term->d_term.getTupleValue();
  for (auto& t : terms)
  {
    res.push_back(term->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

bool cvc5_term_is_rm_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isRoundingModeValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5RoundingMode cvc5_term_get_rm_value(Cvc5Term term)
{
  Cvc5RoundingMode res = CVC5_RM_ROUND_NEAREST_TIES_TO_AWAY;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = static_cast<Cvc5RoundingMode>(term->d_term.getRoundingModeValue());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_fp_pos_zero(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isFloatingPointPosZero();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_fp_neg_zero(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isFloatingPointNegZero();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_fp_pos_inf(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isFloatingPointPosInf();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_fp_neg_inf(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isFloatingPointNegInf();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_fp_nan(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isFloatingPointNaN();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_fp_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isFloatingPointValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_term_get_fp_value(Cvc5Term term,
                            uint32_t* ew,
                            uint32_t* sw,
                            Cvc5Term* val)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  CVC5_CAPI_CHECK_NOT_NULL(ew);
  CVC5_CAPI_CHECK_NOT_NULL(sw);
  CVC5_CAPI_CHECK_NOT_NULL(val);
  cvc5::Term res;
  std::tie(*ew, *sw, res) = term->d_term.getFloatingPointValue();
  *val = term->d_tm->export_term(res);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_term_is_set_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isSetValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Term* cvc5_term_get_set_value(Cvc5Term term, size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto terms = term->d_term.getSetValue();
  for (auto& t : terms)
  {
    res.push_back(term->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

bool cvc5_term_is_sequence_value(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isSequenceValue();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Term* cvc5_term_get_sequence_value(Cvc5Term term, size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto terms = term->d_term.getSequenceValue();
  for (auto& t : terms)
  {
    res.push_back(term->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

bool cvc5_term_is_cardinality_constraint(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isCardinalityConstraint();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_term_get_cardinality_constraint(Cvc5Term term,
                                          Cvc5Sort* sort,
                                          uint32_t* upper)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  CVC5_CAPI_CHECK_NOT_NULL(sort);
  CVC5_CAPI_CHECK_NOT_NULL(upper);
  cvc5::Sort res;
  std::tie(res, *upper) = term->d_term.getCardinalityConstraint();
  *sort = term->d_tm->export_sort(res);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_term_is_real_algebraic_number(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isRealAlgebraicNumber();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_term_get_real_algebraic_number_defining_polynomial(Cvc5Term term,
                                                                 Cvc5Term v)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  CVC5_CAPI_CHECK_TERM(v);
  res = term->d_tm->export_term(
      term->d_term.getRealAlgebraicNumberDefiningPolynomial(v->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_term_get_real_algebraic_number_lower_bound(Cvc5Term term)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res =
      term->d_tm->export_term(term->d_term.getRealAlgebraicNumberLowerBound());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_term_get_real_algebraic_number_upper_bound(Cvc5Term term)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res =
      term->d_tm->export_term(term->d_term.getRealAlgebraicNumberUpperBound());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_term_is_skolem(Cvc5Term term)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_term.isSkolem();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5SkolemId cvc5_term_get_skolem_id(Cvc5Term term)
{
  Cvc5SkolemId res = CVC5_SKOLEM_ID_NONE;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = static_cast<Cvc5SkolemId>(term->d_term.getSkolemId());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Term* cvc5_term_get_skolem_indices(Cvc5Term term, size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto terms = term->d_term.getSkolemIndices();
  for (auto& t : terms)
  {
    res.push_back(term->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

size_t cvc5_term_hash(Cvc5Term term)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = std::hash<cvc5::Term>{}(term->d_term);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* -------------------------------------------------------------------------- */
/* Cvc5Op                                                                     */
/* -------------------------------------------------------------------------- */

bool cvc5_op_is_equal(Cvc5Op a, Cvc5Op b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a == b;
  }
  else
  {
    res = a->d_op == b->d_op;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_op_is_disequal(Cvc5Op a, Cvc5Op b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a != b;
  }
  else
  {
    res = a->d_op != b->d_op;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Kind cvc5_op_get_kind(Cvc5Op op)
{
  Cvc5Kind res = CVC5_KIND_INTERNAL_KIND;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_OP(op);
  res = static_cast<Cvc5Kind>(op->d_op.getKind());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_op_is_indexed(Cvc5Op op)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_OP(op);
  res = op->d_op.isIndexed();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

size_t cvc5_op_get_num_indices(Cvc5Op op)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_OP(op);
  res = op->d_op.getNumIndices();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_op_get_index(Cvc5Op op, size_t i)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_OP(op);
  res = op->d_tm->export_term(op->d_op[i]);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_op_to_string(Cvc5Op op)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_OP(op);
  str = op->d_op.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_op_hash(Cvc5Op op)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_OP(op);
  res = std::hash<cvc5::Op>{}(op->d_op);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Op cvc5_op_copy(Cvc5Op op)
{
  Cvc5Op res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_OP(op);
  res = op->d_tm->copy(op);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_op_release(Cvc5Op op)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_OP(op);
  op->d_tm->release(op);
  CVC5_CAPI_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* Cvc5TermManager                                                            */
/* -------------------------------------------------------------------------- */

Cvc5TermManager* cvc5_term_manager_new()
{
  Cvc5TermManager* res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  res = new Cvc5TermManager();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_term_manager_delete(Cvc5TermManager* tm)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  delete tm;
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_term_manager_release(Cvc5TermManager* tm)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  tm->release();
  CVC5_CAPI_TRY_CATCH_END;
}

Cvc5Statistics cvc5_term_manager_get_statistics(Cvc5TermManager* tm)
{
  Cvc5Statistics res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_stats(tm->d_tm.getStatistics());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_term_manager_print_stats_safe(Cvc5TermManager* tm, int fd)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  tm->d_tm.printStatisticsSafe(fd);
  CVC5_CAPI_TRY_CATCH_END;
}

/* Sorts Handling ----------------------------------------------------------- */

Cvc5Sort cvc5_get_boolean_sort(Cvc5TermManager* tm)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_sort(tm->d_tm.getBooleanSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_get_integer_sort(Cvc5TermManager* tm)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_sort(tm->d_tm.getIntegerSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_get_real_sort(Cvc5TermManager* tm)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_sort(tm->d_tm.getRealSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_get_regexp_sort(Cvc5TermManager* tm)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_sort(tm->d_tm.getRegExpSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_get_rm_sort(Cvc5TermManager* tm)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_sort(tm->d_tm.getRoundingModeSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_get_string_sort(Cvc5TermManager* tm)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_sort(tm->d_tm.getStringSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_array_sort(Cvc5TermManager* tm, Cvc5Sort index, Cvc5Sort elem)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(index);
  CVC5_CAPI_CHECK_SORT(elem);
  res = tm->export_sort(tm->d_tm.mkArraySort(index->d_sort, elem->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_bv_sort(Cvc5TermManager* tm, uint32_t size)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_sort(tm->d_tm.mkBitVectorSort(size));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_fp_sort(Cvc5TermManager* tm, uint32_t exp, uint32_t sig)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_sort(tm->d_tm.mkFloatingPointSort(exp, sig));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_ff_sort(Cvc5TermManager* tm, const char* size, uint32_t base)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res = tm->export_sort(tm->d_tm.mkFiniteFieldSort(size, base));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_dt_sort(Cvc5TermManager* tm, Cvc5DatatypeDecl decl)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_DT_DECL(decl);
  res = tm->export_sort(tm->d_tm.mkDatatypeSort(decl->d_decl));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Sort* cvc5_mk_dt_sorts(Cvc5TermManager* tm,
                                 size_t size,
                                 const Cvc5DatatypeDecl decls[])
{
  static thread_local std::vector<Cvc5Sort> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(decls);
  res.clear();
  std::vector<cvc5::DatatypeDecl> cdecls;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_DT_DECL_AT_IDX(decls, i);
    cdecls.push_back(decls[i]->d_decl);
  }
  auto sorts = tm->d_tm.mkDatatypeSorts(cdecls);
  for (auto& s : sorts)
  {
    res.push_back(tm->export_sort(s));
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

Cvc5Sort cvc5_mk_fun_sort(Cvc5TermManager* tm,
                          size_t size,
                          const Cvc5Sort sorts[],
                          Cvc5Sort codomain)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(sorts);
  std::vector<cvc5::Sort> csorts;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_SORT_AT_IDX(sorts, i);
    csorts.push_back(sorts[i]->d_sort);
  }
  res = tm->export_sort(tm->d_tm.mkFunctionSort(csorts, codomain->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_param_sort(Cvc5TermManager* tm, const char* symbol)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(symbol);
  res = tm->export_sort(tm->d_tm.mkParamSort(symbol));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_predicate_sort(Cvc5TermManager* tm,
                                size_t size,
                                const Cvc5Sort sorts[])
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(sorts);
  std::vector<cvc5::Sort> csorts;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_SORT_AT_IDX(sorts, i);
    csorts.push_back(sorts[i]->d_sort);
  }
  res = tm->export_sort(tm->d_tm.mkPredicateSort(csorts));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_record_sort(Cvc5TermManager* tm,
                             size_t size,
                             const char* names[],
                             const Cvc5Sort sorts[])
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  if (names != NULL)
  {
    CVC5_CAPI_CHECK_NOT_NULL(sorts);
    std::vector<std::pair<std::string, cvc5::Sort>> cfields;
    for (size_t i = 0; i < size; ++i)
    {
      CVC5_CAPI_CHECK_NOT_NULL_AT_IDX(names, i);
      CVC5_CAPI_CHECK_SORT_AT_IDX(sorts, i);
      cfields.emplace_back(names[i], sorts[i]->d_sort);
    }
    res = tm->export_sort(tm->d_tm.mkRecordSort(cfields));
  }
  else
  {
    res = tm->export_sort(tm->d_tm.mkRecordSort({}));
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_set_sort(Cvc5TermManager* tm, Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  res = tm->export_sort(tm->d_tm.mkSetSort(sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_bag_sort(Cvc5TermManager* tm, Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  res = tm->export_sort(tm->d_tm.mkBagSort(sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_sequence_sort(Cvc5TermManager* tm, Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  res = tm->export_sort(tm->d_tm.mkSequenceSort(sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_abstract_sort(Cvc5TermManager* tm, Cvc5SortKind k)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res =
      tm->export_sort(tm->d_tm.mkAbstractSort(static_cast<cvc5::SortKind>(k)));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_uninterpreted_sort(Cvc5TermManager* tm, const char* symbol)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  if (symbol)
  {
    res = tm->export_sort(tm->d_tm.mkUninterpretedSort(symbol));
  }
  else
  {
    res = tm->export_sort(tm->d_tm.mkUninterpretedSort());
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_unresolved_dt_sort(Cvc5TermManager* tm,
                                    const char* symbol,
                                    size_t arity)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(symbol);
  res = tm->export_sort(tm->d_tm.mkUnresolvedDatatypeSort(symbol, arity));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_uninterpreted_sort_constructor_sort(Cvc5TermManager* tm,
                                                     size_t arity,
                                                     const char* symbol)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  if (symbol)
  {
    res = tm->export_sort(
        tm->d_tm.mkUninterpretedSortConstructorSort(arity, symbol));
  }
  else
  {
    res = tm->export_sort(tm->d_tm.mkUninterpretedSortConstructorSort(arity));
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_tuple_sort(Cvc5TermManager* tm,
                            size_t size,
                            const Cvc5Sort sorts[])
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(sorts);
  std::vector<cvc5::Sort> csorts;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_SORT_AT_IDX(sorts, i);
    csorts.push_back(sorts[i]->d_sort);
  }
  res = tm->export_sort(tm->d_tm.mkTupleSort(csorts));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_mk_nullable_sort(Cvc5TermManager* tm, Cvc5Sort sort)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  res = tm->export_sort(tm->d_tm.mkNullableSort(sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Datatype constructor declaration ------------------------------------ */

Cvc5DatatypeConstructorDecl cvc5_mk_dt_cons_decl(Cvc5TermManager* tm,
                                                 const char* name)
{
  Cvc5DatatypeConstructorDecl res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(name);
  res = tm->export_dt_cons_decl(tm->d_tm.mkDatatypeConstructorDecl(name));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Datatype declaration ------------------------------------------------ */

Cvc5DatatypeDecl cvc5_mk_dt_decl(Cvc5TermManager* tm,
                                 const char* name,
                                 bool is_codt)
{
  Cvc5DatatypeDecl res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(name);
  res = tm->export_dt_decl(tm->d_tm.mkDatatypeDecl(name, is_codt));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5DatatypeDecl cvc5_mk_dt_decl_with_params(Cvc5TermManager* tm,
                                             const char* name,
                                             size_t size,
                                             const Cvc5Sort* params,
                                             bool is_codt)
{
  Cvc5DatatypeDecl res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(name);
  std::vector<cvc5::Sort> cparams;
  if (params)
  {
    for (size_t i = 0; i < size; ++i)
    {
      CVC5_CAPI_CHECK_SORT_AT_IDX(params, i);
      cparams.push_back(params[i]->d_sort);
    }
  }
  res = tm->export_dt_decl(tm->d_tm.mkDatatypeDecl(name, cparams, is_codt));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Create Terms --------------------------------------------------------- */

Cvc5Term cvc5_mk_term(Cvc5TermManager* tm,
                      Cvc5Kind kind,
                      size_t size,
                      const Cvc5Term children[])
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_KIND(kind);
  CVC5_API_CHECK(children || size == 0)
      << "unexpected NULL argument for 'children'";
  std::vector<cvc5::Term> cchildren;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(children, i);
    cchildren.push_back(children[i]->d_term);
  }
  res = tm->export_term(
      tm->d_tm.mkTerm(static_cast<cvc5::Kind>(kind), cchildren));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_term_from_op(Cvc5TermManager* tm,
                              Cvc5Op op,
                              size_t size,
                              const Cvc5Term children[])
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(op);
  CVC5_API_CHECK(children || size == 0)
      << "unexpected NULL argument for 'children'";
  std::vector<cvc5::Term> cchildren;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(children, i);
    cchildren.push_back(children[i]->d_term);
  }
  res = tm->export_term(tm->d_tm.mkTerm(op->d_op, cchildren));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_tuple(Cvc5TermManager* tm, size_t size, const Cvc5Term terms[])
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(terms);
  std::vector<cvc5::Term> cterms;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(terms, i);
    cterms.push_back(terms[i]->d_term);
  }
  res = tm->export_term(tm->d_tm.mkTuple(cterms));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_nullable_some(Cvc5TermManager* tm, Cvc5Term term)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_TERM(term);
  res = tm->export_term(tm->d_tm.mkNullableSome(term->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_nullable_val(Cvc5TermManager* tm, Cvc5Term term)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_TERM(term);
  res = tm->export_term(tm->d_tm.mkNullableVal(term->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_nullable_is_null(Cvc5TermManager* tm, Cvc5Term term)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_TERM(term);
  res = tm->export_term(tm->d_tm.mkNullableIsNull(term->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_nullable_is_some(Cvc5TermManager* tm, Cvc5Term term)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_TERM(term);
  res = tm->export_term(tm->d_tm.mkNullableIsSome(term->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_nullable_null(Cvc5TermManager* tm, Cvc5Sort sort)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  res = tm->export_term(tm->d_tm.mkNullableNull(sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_nullable_lift(Cvc5TermManager* tm,
                               Cvc5Kind kind,
                               size_t size,
                               const Cvc5Term args[])
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_KIND(kind);
  CVC5_CAPI_CHECK_NOT_NULL(args);
  std::vector<cvc5::Term> cargs;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(args, i);
    cargs.push_back(args[i]->d_term);
  }
  res = tm->export_term(
      tm->d_tm.mkNullableLift(static_cast<cvc5::Kind>(kind), cargs));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_skolem(Cvc5TermManager* tm,
                        Cvc5SkolemId id,
                        size_t size,
                        const Cvc5Term indices[])
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SKOLEM_ID(id);
  std::vector<cvc5::Term> cindices;
  if (indices)
  {
    for (size_t i = 0; i < size; ++i)
    {
      CVC5_CAPI_CHECK_TERM_AT_IDX(indices, i);
      cindices.push_back(indices[i]->d_term);
    }
  }
  res = tm->export_term(
      tm->d_tm.mkSkolem(static_cast<cvc5::SkolemId>(id), cindices));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

size_t cvc5_get_num_idxs_for_skolem_id(Cvc5TermManager* tm, Cvc5SkolemId id)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SKOLEM_ID(id);
  res = tm->d_tm.getNumIndicesForSkolemId(static_cast<cvc5::SkolemId>(id));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Create Operators ---------------------------------------------------- */

Cvc5Op cvc5_mk_op(Cvc5TermManager* tm,
                  Cvc5Kind kind,
                  size_t size,
                  const uint32_t idxs[])
{
  Cvc5Op res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_KIND(kind);
  CVC5_API_CHECK(idxs || size == 0) << "unexpected NULL argument for 'idxs'";
  std::vector<uint32_t> cidxs;
  for (size_t i = 0; i < size; ++i)
  {
    cidxs.push_back(idxs[i]);
  }
  res = tm->export_op(tm->d_tm.mkOp(static_cast<cvc5::Kind>(kind), cidxs));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Op cvc5_mk_op_from_str(Cvc5TermManager* tm, Cvc5Kind kind, const char* arg)
{
  Cvc5Op res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_KIND(kind);
  CVC5_CAPI_CHECK_NOT_NULL(arg);
  res = tm->export_op(tm->d_tm.mkOp(static_cast<cvc5::Kind>(kind), arg));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Create Constants ---------------------------------------------------- */

Cvc5Term cvc5_mk_true(Cvc5TermManager* tm)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkTrue());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_false(Cvc5TermManager* tm)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkFalse());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_boolean(Cvc5TermManager* tm, bool val)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkBoolean(val));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_pi(Cvc5TermManager* tm)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkPi());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_integer(Cvc5TermManager* tm, const char* s)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(s);
  res = tm->export_term(tm->d_tm.mkInteger(s));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_integer_int64(Cvc5TermManager* tm, int64_t val)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkInteger(val));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_real(Cvc5TermManager* tm, const char* s)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(s);
  res = tm->export_term(tm->d_tm.mkReal(s));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_real_int64(Cvc5TermManager* tm, int64_t val)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkReal(val));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_real_num_den(Cvc5TermManager* tm, int64_t num, int64_t den)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkReal(num, den));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_regexp_all(Cvc5TermManager* tm)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkRegexpAll());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_regexp_allchar(Cvc5TermManager* tm)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkRegexpAllchar());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_regexp_none(Cvc5TermManager* tm)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkRegexpNone());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_empty_set(Cvc5TermManager* tm, Cvc5Sort sort)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  res = tm->export_term(tm->d_tm.mkEmptySet(sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_empty_bag(Cvc5TermManager* tm, Cvc5Sort sort)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  res = tm->export_term(tm->d_tm.mkEmptyBag(sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_sep_emp(Cvc5TermManager* tm)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkSepEmp());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_sep_nil(Cvc5TermManager* tm, Cvc5Sort sort)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  res = tm->export_term(tm->d_tm.mkSepNil(sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_string(Cvc5TermManager* tm, const char* s, bool use_esc_seq)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(s);
  res = tm->export_term(tm->d_tm.mkString(s, use_esc_seq));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_string_from_wchar(Cvc5TermManager* tm, const wchar_t* s)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(s);
  res = tm->export_term(tm->d_tm.mkString(s));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_empty_sequence(Cvc5TermManager* tm, Cvc5Sort sort)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  res = tm->export_term(tm->d_tm.mkEmptySequence(sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_universe_set(Cvc5TermManager* tm, Cvc5Sort sort)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  res = tm->export_term(tm->d_tm.mkUniverseSet(sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_bv_uint64(Cvc5TermManager* tm, uint32_t size, uint64_t val)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkBitVector(size, val));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_bv(Cvc5TermManager* tm,
                    uint32_t size,
                    const char* s,
                    uint32_t base)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(s);
  res = tm->export_term(tm->d_tm.mkBitVector(size, s, base));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_ff_elem(Cvc5TermManager* tm,
                         const char* value,
                         Cvc5Sort sort,
                         uint32_t base)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_NOT_NULL(value);
  CVC5_CAPI_CHECK_SORT(sort);
  res = tm->export_term(tm->d_tm.mkFiniteFieldElem(value, sort->d_sort, base));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_const_array(Cvc5TermManager* tm, Cvc5Sort sort, Cvc5Term val)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_TERM(val);
  res = tm->export_term(tm->d_tm.mkConstArray(sort->d_sort, val->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_fp_pos_inf(Cvc5TermManager* tm, uint32_t exp, uint32_t sig)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkFloatingPointPosInf(exp, sig));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_fp_neg_inf(Cvc5TermManager* tm, uint32_t exp, uint32_t sig)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkFloatingPointNegInf(exp, sig));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_fp_nan(Cvc5TermManager* tm, uint32_t exp, uint32_t sig)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkFloatingPointNaN(exp, sig));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_fp_pos_zero(Cvc5TermManager* tm, uint32_t exp, uint32_t sig)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkFloatingPointPosZero(exp, sig));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_fp_neg_zero(Cvc5TermManager* tm, uint32_t exp, uint32_t sig)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mkFloatingPointNegZero(exp, sig));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_rm(Cvc5TermManager* tm, Cvc5RoundingMode rm)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = tm->export_term(
      tm->d_tm.mkRoundingMode(static_cast<cvc5::RoundingMode>(rm)));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_fp(Cvc5TermManager* tm,
                    uint32_t exp,
                    uint32_t sig,
                    Cvc5Term val)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_TERM(val);
  res = tm->export_term(tm->d_tm.mkFloatingPoint(exp, sig, val->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_fp_from_ieee(Cvc5TermManager* tm,
                              Cvc5Term sign,
                              Cvc5Term exp,
                              Cvc5Term sig)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_TERM(sign);
  CVC5_CAPI_CHECK_TERM(exp);
  CVC5_CAPI_CHECK_TERM(sig);
  res = tm->export_term(
      tm->d_tm.mkFloatingPoint(sign->d_term, exp->d_term, sig->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_cardinality_constraint(Cvc5TermManager* tm,
                                        Cvc5Sort sort,
                                        uint32_t upperBound)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  res = tm->export_term(
      tm->d_tm.mkCardinalityConstraint(sort->d_sort, upperBound));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* Create Variables ----------------------------------------------------- */

Cvc5Term cvc5_mk_const(Cvc5TermManager* tm, Cvc5Sort sort, const char* symbol)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  if (symbol)
  {
    res = tm->export_term(tm->d_tm.mkConst(sort->d_sort, symbol));
  }
  else
  {
    res = tm->export_term(tm->d_tm.mkConst(sort->d_sort));
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_mk_var(Cvc5TermManager* tm, Cvc5Sort sort, const char* symbol)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  CVC5_CAPI_CHECK_SORT(sort);
  if (symbol)
  {
    res = tm->export_term(tm->d_tm.mkVar(sort->d_sort, symbol));
  }
  else
  {
    res = tm->export_term(tm->d_tm.mkVar(sort->d_sort));
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* -------------------------------------------------------------------------- */
/* Cvc5Result                                                                 */
/* -------------------------------------------------------------------------- */

Cvc5Result cvc5_result_copy(Cvc5Result result)
{
  Cvc5Result res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_RESULT(result);
  res = result->d_cvc5->copy(result);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_result_release(Cvc5Result result)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_RESULT(result);
  result->d_cvc5->release(result);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_result_is_null(const Cvc5Result result)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_RESULT(result);
  res = result->d_result.isNull();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_result_is_sat(const Cvc5Result result)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_RESULT(result);
  res = result->d_result.isSat();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_result_is_unsat(const Cvc5Result result)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_RESULT(result);
  res = result->d_result.isUnsat();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_result_is_unknown(const Cvc5Result result)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_RESULT(result);
  res = result->d_result.isUnknown();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_result_is_equal(const Cvc5Result a, const Cvc5Result b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a == b;
  }
  else
  {
    res = a->d_result == b->d_result;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_result_is_disequal(const Cvc5Result a, const Cvc5Result b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a != b;
  }
  else
  {
    res = a->d_result != b->d_result;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5UnknownExplanation cvc5_result_get_unknown_explanation(
    const Cvc5Result result)
{
  Cvc5UnknownExplanation res = CVC5_UNKNOWN_EXPLANATION_LAST;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_RESULT(result);
  res = static_cast<Cvc5UnknownExplanation>(
      result->d_result.getUnknownExplanation());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_result_to_string(const Cvc5Result result)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_RESULT(result);
  str = result->d_result.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_result_hash(Cvc5Result result)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_RESULT(result);
  res = std::hash<cvc5::Result>{}(result->d_result);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* -------------------------------------------------------------------------- */
/* Cvc5SynthResult                                                            */
/* -------------------------------------------------------------------------- */

Cvc5SynthResult cvc5_synth_result_copy(Cvc5SynthResult result)
{
  Cvc5SynthResult res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SYNTH_RESULT(result);
  res = result->d_cvc5->copy(result);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_synth_result_release(Cvc5SynthResult result)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SYNTH_RESULT(result);
  result->d_cvc5->release(result);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_synth_result_is_null(const Cvc5SynthResult result)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SYNTH_RESULT(result);
  res = result->d_result.isNull();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_synth_result_has_solution(const Cvc5SynthResult result)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SYNTH_RESULT(result);
  res = result->d_result.hasSolution();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_synth_result_has_no_solution(const Cvc5SynthResult result)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SYNTH_RESULT(result);
  res = result->d_result.hasNoSolution();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_synth_result_is_unknown(const Cvc5SynthResult result)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SYNTH_RESULT(result);
  res = result->d_result.isUnknown();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_synth_result_is_equal(const Cvc5SynthResult a,
                                const Cvc5SynthResult b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a == b;
  }
  else
  {
    res = a->d_result == b->d_result;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_synth_result_is_disequal(const Cvc5SynthResult a,
                                   const Cvc5SynthResult b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a != b;
  }
  else
  {
    res = a->d_result != b->d_result;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_synth_result_to_string(const Cvc5SynthResult result)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SYNTH_RESULT(result);
  str = result->d_result.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

size_t cvc5_synth_result_hash(Cvc5SynthResult result)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SYNTH_RESULT(result);
  res = std::hash<cvc5::SynthResult>{}(result->d_result);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* -------------------------------------------------------------------------- */
/* Cvc5Proof                                                                  */
/* -------------------------------------------------------------------------- */

Cvc5ProofRule cvc5_proof_get_rule(Cvc5Proof proof)
{
  Cvc5ProofRule res = CVC5_PROOF_RULE_LAST;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_PROOF(proof);
  res = static_cast<Cvc5ProofRule>(proof->d_proof.getRule());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5ProofRewriteRule cvc5_proof_get_rewrite_rule(Cvc5Proof proof)
{
  Cvc5ProofRewriteRule res = CVC5_PROOF_REWRITE_RULE_LAST;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_PROOF(proof);
  res = static_cast<Cvc5ProofRewriteRule>(proof->d_proof.getRewriteRule());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_proof_get_result(Cvc5Proof proof)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_PROOF(proof);
  res = proof->d_cvc5->d_tm->export_term(proof->d_proof.getResult());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Proof* cvc5_proof_get_children(Cvc5Proof proof, size_t* size)
{
  static thread_local std::vector<Cvc5Proof> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_PROOF(proof);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto children = proof->d_proof.getChildren();
  for (auto& p : children)
  {
    res.push_back(proof->d_cvc5->export_proof(p));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

const Cvc5Term* cvc5_proof_get_arguments(Cvc5Proof proof, size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_PROOF(proof);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto args = proof->d_proof.getArguments();
  for (auto& t : args)
  {
    res.push_back(proof->d_cvc5->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

bool cvc5_proof_is_equal(Cvc5Proof a, Cvc5Proof b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a == b;
  }
  else
  {
    res = a->d_proof == b->d_proof;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_proof_is_disequal(Cvc5Proof a, Cvc5Proof b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a != b;
  }
  else
  {
    res = a->d_proof != b->d_proof;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

size_t cvc5_proof_hash(Cvc5Proof proof)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_PROOF(proof);
  res = std::hash<cvc5::Proof>{}(proof->d_proof);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Proof cvc5_proof_copy(Cvc5Proof proof)
{
  Cvc5Proof res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_PROOF(proof);
  res = proof->d_cvc5->copy(proof);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_proof_release(Cvc5Proof proof)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_PROOF(proof);
  proof->d_cvc5->release(proof);
  CVC5_CAPI_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* Cvc5Grammar                                                                */
/* -------------------------------------------------------------------------- */

void cvc5_grammar_add_rule(Cvc5Grammar grammar, Cvc5Term symbol, Cvc5Term rule)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_GRAMMAR(grammar);
  CVC5_CAPI_CHECK_TERM(symbol);
  CVC5_CAPI_CHECK_TERM(rule);
  grammar->d_grammar.addRule(symbol->d_term, rule->d_term);
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_grammar_add_rules(Cvc5Grammar grammar,
                            Cvc5Term symbol,
                            size_t size,
                            const Cvc5Term rules[])
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_GRAMMAR(grammar);
  CVC5_CAPI_CHECK_TERM(symbol);
  CVC5_CAPI_CHECK_NOT_NULL(rules);
  std::vector<cvc5::Term> crules;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(rules, i);
    crules.push_back(rules[i]->d_term);
  }
  grammar->d_grammar.addRules(symbol->d_term, crules);
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_grammar_add_any_constant(Cvc5Grammar grammar, Cvc5Term symbol)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_GRAMMAR(grammar);
  CVC5_CAPI_CHECK_TERM(symbol);
  grammar->d_grammar.addAnyConstant(symbol->d_term);
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_grammar_add_any_variable(Cvc5Grammar grammar, Cvc5Term symbol)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_GRAMMAR(grammar);
  CVC5_CAPI_CHECK_TERM(symbol);
  grammar->d_grammar.addAnyVariable(symbol->d_term);
  CVC5_CAPI_TRY_CATCH_END;
}

const char* cvc5_grammar_to_string(const Cvc5Grammar grammar)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_GRAMMAR(grammar);
  str = grammar->d_grammar.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

bool cvc5_grammar_is_equal(Cvc5Grammar a, Cvc5Grammar b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a == b;
  }
  else
  {
    res = a->d_grammar == b->d_grammar;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_grammar_is_disequal(Cvc5Grammar a, Cvc5Grammar b)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  if (a == nullptr || b == nullptr)
  {
    res = a != b;
  }
  else
  {
    res = a->d_grammar != b->d_grammar;
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

size_t cvc5_grammar_hash(Cvc5Grammar grammar)
{
  size_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_GRAMMAR(grammar);
  res = std::hash<cvc5::Grammar>{}(grammar->d_grammar);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Grammar cvc5_grammar_copy(Cvc5Grammar grammar)
{
  Cvc5Grammar res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_GRAMMAR(grammar);
  res = grammar->d_cvc5->copy(grammar);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_grammar_release(Cvc5Grammar grammar)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_GRAMMAR(grammar);
  grammar->d_cvc5->release(grammar);
  CVC5_CAPI_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* Cvc5Stat                                                                   */
/* -------------------------------------------------------------------------- */

bool cvc5_stat_is_internal(Cvc5Stat stat)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STAT(stat);
  res = stat->d_stat.isInternal();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_stat_is_default(Cvc5Stat stat)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STAT(stat);
  res = stat->d_stat.isDefault();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_stat_is_int(Cvc5Stat stat)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STAT(stat);
  res = stat->d_stat.isInt();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

int64_t cvc5_stat_get_int(Cvc5Stat stat)
{
  int64_t res = 0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STAT(stat);
  res = stat->d_stat.getInt();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_stat_is_double(Cvc5Stat stat)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STAT(stat);
  res = stat->d_stat.isDouble();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

double cvc5_stat_get_double(Cvc5Stat stat)
{
  double res = 0.0;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STAT(stat);
  res = stat->d_stat.getDouble();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_stat_is_string(Cvc5Stat stat)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STAT(stat);
  res = stat->d_stat.isString();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_stat_get_string(Cvc5Stat stat)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STAT(stat);
  str = stat->d_stat.getString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

bool cvc5_stat_is_histogram(Cvc5Stat stat)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STAT(stat);
  res = stat->d_stat.isHistogram();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_stat_get_histogram(Cvc5Stat stat,
                             const char** keys[],
                             uint64_t* values[],
                             size_t* size)
{
  static thread_local std::vector<const char*> rkeys;
  static thread_local std::vector<uint64_t> rvalues;
  static thread_local cvc5::Stat::HistogramData histo;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STAT(stat);
  CVC5_CAPI_CHECK_NOT_NULL(keys);
  CVC5_CAPI_CHECK_NOT_NULL(values);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  rkeys.clear();
  rvalues.clear();
  histo = stat->d_stat.getHistogram();
  for (auto& h : histo)
  {
    rkeys.push_back(h.first.c_str());
    rvalues.push_back(h.second);
  }
  *size = rkeys.size();
  *keys = rkeys.data();
  *values = rvalues.data();
  CVC5_CAPI_TRY_CATCH_END;
}

const char* cvc5_stat_to_string(Cvc5Stat stat)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STAT(stat);
  str = stat->d_stat.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* Cvc5Statistics                                                             */
/* -------------------------------------------------------------------------- */

void cvc5_stats_iter_init(Cvc5Statistics stat, bool internal, bool dflt)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STATS(stat);
  stat->d_iter.reset(
      new cvc5::Statistics::iterator(stat->d_stat.begin(internal, dflt)));
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_stats_iter_has_next(Cvc5Statistics stat)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STATS(stat);
  CVC5_API_CHECK(stat->d_iter != nullptr) << "iterator not initialized";
  res = *stat->d_iter != stat->d_stat.end();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Stat cvc5_stats_iter_next(Cvc5Statistics stat, const char** name)
{
  static thread_local std::string str;
  Cvc5Stat res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STATS(stat);
  CVC5_API_CHECK(stat->d_iter != nullptr) << "iterator not initialized";
  cvc5::Stat rstat;
  std::tie(str, rstat) = **stat->d_iter;
  if (name)
  {
    *name = str.c_str();
  }
  res = stat->d_tm->export_stat(rstat);
  (*stat->d_iter)++;
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Stat cvc5_stats_get(Cvc5Statistics stat, const char* name)
{
  Cvc5Stat res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STATS(stat);
  CVC5_CAPI_CHECK_NOT_NULL(name);
  res = stat->d_tm->export_stat(stat->d_stat.get(name));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_stats_to_string(Cvc5Statistics stat)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_STATS(stat);
  str = stat->d_stat.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* Cvc5                                                                       */
/* -------------------------------------------------------------------------- */

Cvc5* cvc5_new(Cvc5TermManager* tm)
{
  Cvc5* res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  res = new Cvc5(tm);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_delete(Cvc5* cvc5)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  delete cvc5;
  CVC5_CAPI_TRY_CATCH_END;
}

Cvc5TermManager* cvc5_get_tm(Cvc5* cvc5)
{
  Cvc5TermManager* tm = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  tm = cvc5->d_tm;
  CVC5_CAPI_TRY_CATCH_END;
  return tm;
}

void cvc5_set_info(Cvc5* cvc5, const char* keyword, const char* value)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(keyword);
  CVC5_CAPI_CHECK_NOT_NULL(value);
  cvc5->d_solver.setInfo(keyword, value);
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_set_logic(Cvc5* cvc5, const char* logic)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(logic);
  cvc5->d_solver.setLogic(logic);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_is_logic_set(Cvc5* cvc5)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  res = cvc5->d_solver.isLogicSet();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_get_logic(Cvc5* cvc5)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  str = cvc5->d_solver.getLogic();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

void cvc5_set_option(Cvc5* cvc5, const char* option, const char* value)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(option);
  CVC5_CAPI_CHECK_NOT_NULL(value);
  cvc5->d_solver.setOption(option, value);
  CVC5_CAPI_TRY_CATCH_END;
}

Cvc5Statistics cvc5_get_statistics(Cvc5* cvc5)
{
  Cvc5Statistics res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  res = cvc5->d_tm->export_stats(cvc5->d_solver.getStatistics());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_print_stats_safe(Cvc5* cvc5, int fd)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  cvc5->d_solver.printStatisticsSafe(fd);
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_is_output_on(Cvc5* cvc5, const char* tag)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(tag);
  res = cvc5->d_solver.isOutputOn(tag);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_get_output(Cvc5* cvc5, const char* tag, const char* filename)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(tag);
  CVC5_CAPI_CHECK_NOT_NULL(filename);
  if (cvc5->d_solver.isOutputOn(tag))
  {
    std::ostream* out;
    if (filename != std::string("<stdout>"))
    {
      if (cvc5->d_output_tag_file_stream.is_open())
      {
        cvc5->d_output_tag_file_stream.close();
      }
      cvc5->d_output_tag_file_stream.open(filename);
      out = &cvc5->d_output_tag_file_stream;
    }
    else
    {
      out = &std::cout;
    }
    cvc5->d_output_tag_stream = &cvc5->d_solver.getOutput(tag);
    cvc5->d_output_tag_streambuf = cvc5->d_output_tag_stream->rdbuf();
    cvc5->d_output_tag_stream->rdbuf(out->rdbuf());
  }
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_close_output(Cvc5* cvc5, const char* filename)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(filename);
  if (cvc5->d_output_tag_file_stream.is_open())
  {
    cvc5->d_output_tag_file_stream.close();
  }
  // reset redirected output stream returned by Solver::getOutput()
  if (cvc5->d_output_tag_stream)
  {
    Assert(cvc5->d_output_tag_streambuf);
    cvc5->d_output_tag_stream->rdbuf(cvc5->d_output_tag_streambuf);
  }
  CVC5_CAPI_TRY_CATCH_END;
}

const char* cvc5_get_version(Cvc5* cvc5)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  str = cvc5->d_solver.getVersion();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* .................................................................... */
/* SMT-LIB-style Term/Sort Creation                                     */
/* .................................................................... */

Cvc5Sort cvc5_declare_dt(Cvc5* cvc5,
                         const char* symbol,
                         size_t size,
                         const Cvc5DatatypeConstructorDecl ctors[])
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(symbol);
  CVC5_CAPI_CHECK_NOT_NULL(ctors);
  std::vector<cvc5::DatatypeConstructorDecl> cctors;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_DT_CONS_DECL_AT_IDX(ctors, i);
    cctors.push_back(ctors[i]->d_decl);
  }
  res = cvc5->d_tm->export_sort(cvc5->d_solver.declareDatatype(symbol, cctors));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_declare_fun(Cvc5* cvc5,
                          const char* symbol,
                          size_t size,
                          const Cvc5Sort sorts[],
                          Cvc5Sort sort,
                          bool fresh)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(symbol);
  CVC5_CAPI_CHECK_SORT(sort);
  std::vector<cvc5::Sort> csorts;
  if (sorts != nullptr)
  {
    for (size_t i = 0; i < size; ++i)
    {
      CVC5_CAPI_CHECK_SORT_AT_IDX(sorts, i);
      csorts.push_back(sorts[i]->d_sort);
    }
  }
  res = cvc5->d_tm->export_term(
      cvc5->d_solver.declareFun(symbol, csorts, sort->d_sort, fresh));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Sort cvc5_declare_sort(Cvc5* cvc5,
                           const char* symbol,
                           uint32_t arity,
                           bool fresh)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(symbol);
  res =
      cvc5->d_tm->export_sort(cvc5->d_solver.declareSort(symbol, arity, fresh));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

/* .................................................................... */
/* Formula Handling                                                     */
/* .................................................................... */

Cvc5Term cvc5_define_fun(Cvc5* cvc5,
                         const char* symbol,
                         size_t size,
                         const Cvc5Term vars[],
                         const Cvc5Sort sort,
                         const Cvc5Term term,
                         bool global)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(symbol);
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_TERM(term);
  std::vector<cvc5::Term> cvars;
  if (vars != nullptr)
  {
    for (size_t i = 0; i < size; ++i)
    {
      CVC5_CAPI_CHECK_TERM_AT_IDX(vars, i);
      cvars.push_back(vars[i]->d_term);
    }
  }
  res = cvc5->d_tm->export_term(cvc5->d_solver.defineFun(
      symbol, cvars, sort->d_sort, term->d_term, global));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_define_fun_rec(Cvc5* cvc5,
                             const char* symbol,
                             size_t size,
                             const Cvc5Term vars[],
                             const Cvc5Sort sort,
                             const Cvc5Term term,
                             bool global)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(symbol);
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_TERM(term);
  std::vector<cvc5::Term> cvars;
  if (vars != nullptr)
  {
    for (size_t i = 0; i < size; ++i)
    {
      CVC5_CAPI_CHECK_TERM_AT_IDX(vars, i);
      cvars.push_back(vars[i]->d_term);
    }
  }
  res = cvc5->d_tm->export_term(cvc5->d_solver.defineFunRec(
      symbol, cvars, sort->d_sort, term->d_term, global));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_define_fun_rec_from_const(Cvc5* cvc5,
                                        Cvc5Term fun,
                                        size_t size,
                                        const Cvc5Term vars[],
                                        const Cvc5Term term,
                                        bool global)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(fun);
  CVC5_CAPI_CHECK_TERM(term);
  std::vector<cvc5::Term> cvars;
  if (vars != nullptr)
  {
    for (size_t i = 0; i < size; ++i)
    {
      CVC5_CAPI_CHECK_TERM_AT_IDX(vars, i);
      cvars.push_back(vars[i]->d_term);
    }
  }
  res = cvc5->d_tm->export_term(
      cvc5->d_solver.defineFunRec(fun->d_term, cvars, term->d_term, global));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_define_funs_rec(Cvc5* cvc5,
                          size_t nfuns,
                          const Cvc5Term funs[],
                          size_t nvars[],
                          const Cvc5Term* vars[],
                          const Cvc5Term terms[],
                          bool global)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(funs);
  CVC5_CAPI_CHECK_NOT_NULL(nvars);
  CVC5_CAPI_CHECK_NOT_NULL(vars);
  CVC5_CAPI_CHECK_NOT_NULL(terms);
  std::vector<cvc5::Term> cfuns;
  for (size_t i = 0; i < nfuns; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(funs, i);
    cfuns.push_back(funs[i]->d_term);
  }
  std::vector<std::vector<cvc5::Term>> cvars;
  for (size_t i = 0; i < nfuns; ++i)
  {
    std::vector<cvc5::Term> cv;
    for (size_t j = 0; j < nvars[i]; ++j)
    {
      CVC5_CAPI_CHECK_TERM_AT_IDX(vars[i], j);
      cv.push_back(vars[i][j]->d_term);
    }
    cvars.push_back(cv);
  }
  std::vector<cvc5::Term> cterms;
  for (size_t i = 0; i < nfuns; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(terms, i);
    cterms.push_back(terms[i]->d_term);
  }
  cvc5->d_solver.defineFunsRec(cfuns, cvars, cterms, global);
  CVC5_CAPI_TRY_CATCH_END;
}

Cvc5Term cvc5_simplify(Cvc5* cvc5, Cvc5Term term, bool apply_subs)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(term);
  res = cvc5->d_tm->export_term(
      cvc5->d_solver.simplify(term->d_term, apply_subs));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_assert_formula(Cvc5* cvc5, Cvc5Term term)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(term);
  cvc5->d_solver.assertFormula(term->d_term);
  CVC5_CAPI_TRY_CATCH_END;
}

Cvc5Result cvc5_check_sat(Cvc5* cvc5)
{
  Cvc5Result res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  res = cvc5->export_result(cvc5->d_solver.checkSat());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Result cvc5_check_sat_assuming(Cvc5* cvc5,
                                   size_t size,
                                   const Cvc5Term assumptions[])
{
  Cvc5Result res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(assumptions);
  std::vector<cvc5::Term> cassumptions;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(assumptions, i);
    cassumptions.push_back(assumptions[i]->d_term);
  }
  res = cvc5->export_result(cvc5->d_solver.checkSatAssuming(cassumptions));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Term* cvc5_get_assertions(Cvc5* cvc5, size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto assertions = cvc5->d_solver.getAssertions();
  for (auto& t : assertions)
  {
    res.push_back(cvc5->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

const char* cvc5_get_info(Cvc5* cvc5, const char* flag)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(flag);
  str = cvc5->d_solver.getInfo(flag);
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

const char* cvc5_get_option(Cvc5* cvc5, const char* option)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(option);
  str = cvc5->d_solver.getOption(option);
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

const char** cvc5_get_option_names(Cvc5* cvc5, size_t* size)
{
  static thread_local std::vector<const char*> res;
  static thread_local std::vector<std::string> names;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  names = cvc5->d_solver.getOptionNames();
  for (auto& s : names)
  {
    res.push_back(s.c_str());
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

template <class... Ts>
struct overloaded : Ts...
{
  using Ts::operator()...;
};
template <class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

void cvc5_get_option_info(Cvc5* cvc5, const char* option, Cvc5OptionInfo* info)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(option);
  CVC5_CAPI_CHECK_NOT_NULL(info);

  static thread_local cvc5::OptionInfo cpp_info;
  cpp_info = cvc5->d_solver.getOptionInfo(option);

  std::memset(info, 0, sizeof(*info));

  info->name = cpp_info.name.c_str();

  info->num_aliases = cpp_info.aliases.size();
  static thread_local std::vector<const char*> c_aliases;
  c_aliases.clear();
  for (const auto& a : cpp_info.aliases)
  {
    c_aliases.push_back(a.c_str());
  }
  info->aliases = c_aliases.data();

  info->is_set_by_user = cpp_info.setByUser;
  info->is_expert = cpp_info.isExpert;
  info->is_regular = cpp_info.isRegular;

  std::visit(
      overloaded{
          [info](const cvc5::OptionInfo::VoidInfo& vi) {
            (void)vi;
            info->kind = CVC5_OPTION_INFO_VOID;
          },
          [info](const cvc5::OptionInfo::ValueInfo<bool>& vi) {
            info->kind = CVC5_OPTION_INFO_BOOL;
            info->info_bool.dflt = vi.defaultValue;
            info->info_bool.cur = vi.currentValue;
          },
          [info](const cvc5::OptionInfo::ValueInfo<std::string>& vi) {
            info->kind = CVC5_OPTION_INFO_STR;
            info->info_str.dflt = vi.defaultValue.c_str();
            info->info_str.cur = vi.currentValue.c_str();
          },
          [info](const cvc5::OptionInfo::NumberInfo<int64_t>& vi) {
            info->kind = CVC5_OPTION_INFO_INT64;
            info->info_int.dflt = vi.defaultValue;
            info->info_int.cur = vi.currentValue;
            if (vi.minimum)
            {
              info->info_int.min = *vi.minimum;
              info->info_int.has_min = true;
            }
            if (vi.maximum)
            {
              info->info_int.max = *vi.maximum;
              info->info_int.has_max = true;
            }
          },
          [info](const cvc5::OptionInfo::NumberInfo<uint64_t>& vi) {
            info->kind = CVC5_OPTION_INFO_UINT64;
            info->info_uint.dflt = vi.defaultValue;
            info->info_uint.cur = vi.currentValue;
            if (vi.minimum)
            {
              info->info_uint.min = *vi.minimum;
              info->info_uint.has_min = true;
            }
            if (vi.maximum)
            {
              info->info_uint.max = *vi.maximum;
              info->info_uint.has_max = true;
            }
          },
          [info](const cvc5::OptionInfo::NumberInfo<double>& vi) {
            info->kind = CVC5_OPTION_INFO_DOUBLE;
            info->info_double.dflt = vi.defaultValue;
            info->info_double.cur = vi.currentValue;
            if (vi.minimum)
            {
              info->info_double.min = *vi.minimum;
              info->info_double.has_min = true;
            }
            if (vi.maximum)
            {
              info->info_double.max = *vi.maximum;
              info->info_double.has_max = true;
            }
          },
          [info](const cvc5::OptionInfo::ModeInfo& vi) {
            info->kind = CVC5_OPTION_INFO_MODES;
            info->info_mode.cur =
                std::get<cvc5::OptionInfo::ModeInfo>(cpp_info.valueInfo)
                    .currentValue.c_str();
            info->info_mode.dflt =
                std::get<cvc5::OptionInfo::ModeInfo>(cpp_info.valueInfo)
                    .defaultValue.c_str();
            info->info_mode.num_modes =
                std::get<cvc5::OptionInfo::ModeInfo>(cpp_info.valueInfo)
                    .modes.size();
            static thread_local std::vector<const char*> c_modes;
            c_modes.clear();
            for (const auto& m :
                 std::get<cvc5::OptionInfo::ModeInfo>(cpp_info.valueInfo).modes)
            {
              c_modes.push_back(m.c_str());
            }
            info->info_mode.modes = c_modes.data();
          },
      },
      cpp_info.valueInfo);

  info->d_cpp_info = &cpp_info;
  CVC5_CAPI_TRY_CATCH_END;
}

const char* cvc5_option_info_to_string(const Cvc5OptionInfo* info)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(info);
  Assert(info->d_cpp_info);
  str = static_cast<cvc5::OptionInfo*>(info->d_cpp_info)->toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

const Cvc5Term* cvc5_get_unsat_assumptions(Cvc5* cvc5, size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto assumptions = cvc5->d_solver.getUnsatAssumptions();
  for (auto& t : assumptions)
  {
    res.push_back(cvc5->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

const Cvc5Term* cvc5_get_unsat_core(Cvc5* cvc5, size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto assertions = cvc5->d_solver.getUnsatCore();
  for (auto& t : assertions)
  {
    res.push_back(cvc5->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

const Cvc5Term* cvc5_get_unsat_core_lemmas(Cvc5* cvc5, size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto assertions = cvc5->d_solver.getUnsatCoreLemmas();
  for (auto& t : assertions)
  {
    res.push_back(cvc5->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

void cvc5_get_difficulty(Cvc5* cvc5,
                         size_t* size,
                         Cvc5Term* inputs[],
                         Cvc5Term* values[])
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  CVC5_CAPI_CHECK_NOT_NULL(inputs);
  CVC5_CAPI_CHECK_NOT_NULL(values);
  auto res = cvc5->d_solver.getDifficulty();
  static thread_local std::vector<Cvc5Term> rinputs;
  static thread_local std::vector<Cvc5Term> rvalues;
  rinputs.clear();
  rvalues.clear();
  for (const auto& p : res)
  {
    rinputs.push_back(cvc5->d_tm->export_term(p.first));
    rvalues.push_back(cvc5->d_tm->export_term(p.second));
  }
  *size = rinputs.size();
  *inputs = rinputs.data();
  *values = rvalues.data();
  CVC5_CAPI_TRY_CATCH_END;
}

const Cvc5Term* cvc5_get_timeout_core(Cvc5* cvc5,
                                      Cvc5Result* result,
                                      size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(result);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto ccore = cvc5->d_solver.getTimeoutCore();
  *result = cvc5->export_result(ccore.first);
  for (const auto& t : ccore.second)
  {
    res.push_back(cvc5->d_tm->export_term(t));
  }
  *size = ccore.second.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

const Cvc5Term* cvc5_get_timeout_core_assuming(Cvc5* cvc5,
                                               size_t size,
                                               const Cvc5Term assumptions[],
                                               Cvc5Result* result,
                                               size_t* rsize)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(assumptions);
  std::vector<cvc5::Term> cassumptions;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(assumptions, i);
    cassumptions.push_back(assumptions[i]->d_term);
  }
  CVC5_CAPI_CHECK_NOT_NULL(result);
  CVC5_CAPI_CHECK_NOT_NULL(rsize);
  res.clear();
  auto ccore = cvc5->d_solver.getTimeoutCoreAssuming(cassumptions);
  *result = cvc5->export_result(ccore.first);
  for (const auto& t : ccore.second)
  {
    res.push_back(cvc5->d_tm->export_term(t));
  }
  *rsize = ccore.second.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

const Cvc5Proof* cvc5_get_proof(Cvc5* cvc5, Cvc5ProofComponent c, size_t* size)
{
  static thread_local std::vector<Cvc5Proof> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto proofs =
      cvc5->d_solver.getProof(static_cast<cvc5::modes::ProofComponent>(c));
  for (const auto& p : proofs)
  {
    res.push_back(cvc5->export_proof(p));
  }
  *size = proofs.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

const Cvc5Term* cvc5_get_learned_literals(Cvc5* cvc5,
                                          Cvc5LearnedLitType type,
                                          size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto lits = cvc5->d_solver.getLearnedLiterals(
      static_cast<cvc5::modes::LearnedLitType>(type));
  for (const auto& t : lits)
  {
    res.push_back(cvc5->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

Cvc5Term cvc5_get_value(Cvc5* cvc5, Cvc5Term term)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(term);
  res = cvc5->d_tm->export_term(cvc5->d_solver.getValue(term->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Term* cvc5_get_values(Cvc5* cvc5,
                                size_t size,
                                const Cvc5Term terms[],
                                size_t* rsize)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(terms);
  CVC5_CAPI_CHECK_NOT_NULL(rsize);
  res.clear();
  std::vector<cvc5::Term> cterms;
  for (size_t i = 0; i < size; ++i)
  {
    cterms.push_back(terms[i]->d_term);
  }
  auto values = cvc5->d_solver.getValue(cterms);
  for (const auto& t : values)
  {
    res.push_back(cvc5->d_tm->export_term(t));
  }
  *rsize = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

const Cvc5Term* cvc5_get_model_domain_elements(Cvc5* cvc5,
                                               Cvc5Sort sort,
                                               size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto elems = cvc5->d_solver.getModelDomainElements(sort->d_sort);
  for (const auto& t : elems)
  {
    res.push_back(cvc5->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

bool cvc5_is_model_core_symbol(Cvc5* cvc5, Cvc5Term v)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  if (v)
  {
    res = cvc5->d_solver.isModelCoreSymbol(v->d_term);
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_get_model(Cvc5* cvc5,
                           size_t nsorts,
                           const Cvc5Sort sorts[],
                           size_t nconsts,
                           const Cvc5Term consts[])
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(sorts);
  CVC5_CAPI_CHECK_NOT_NULL(consts);
  std::vector<cvc5::Sort> csorts;
  for (size_t i = 0; i < nsorts; ++i)
  {
    csorts.push_back(sorts[i]->d_sort);
  }
  std::vector<cvc5::Term> cconsts;
  for (size_t i = 0; i < nconsts; ++i)
  {
    cconsts.push_back(consts[i]->d_term);
  }
  str = cvc5->d_solver.getModel(csorts, cconsts);
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

Cvc5Term cvc5_get_quantifier_elimination(Cvc5* cvc5, Cvc5Term q)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(q);
  res = cvc5->d_tm->export_term(
      cvc5->d_solver.getQuantifierElimination(q->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_get_quantifier_elimination_disjunct(Cvc5* cvc5, Cvc5Term q)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(q);
  res = cvc5->d_tm->export_term(
      cvc5->d_solver.getQuantifierEliminationDisjunct(q->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_declare_sep_heap(Cvc5* cvc5, Cvc5Sort loc, Cvc5Sort data)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_SORT(loc);
  CVC5_CAPI_CHECK_SORT(data);
  cvc5->d_solver.declareSepHeap(loc->d_sort, data->d_sort);
  CVC5_CAPI_TRY_CATCH_END;
}

Cvc5Term cvc5_get_value_sep_heap(Cvc5* cvc5)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  res = cvc5->d_tm->export_term(cvc5->d_solver.getValueSepHeap());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_get_value_sep_nil(Cvc5* cvc5)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  res = cvc5->d_tm->export_term(cvc5->d_solver.getValueSepNil());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_declare_pool(Cvc5* cvc5,
                           const char* symbol,
                           Cvc5Sort sort,
                           size_t size,
                           const Cvc5Term init_value[])
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(symbol);
  CVC5_CAPI_CHECK_SORT(sort);
  std::vector<cvc5::Term> cinit_value;
  if (init_value != nullptr)
  {
    for (size_t i = 0; i < size; ++i)
    {
      CVC5_CAPI_CHECK_TERM_AT_IDX(init_value, i);
      cinit_value.push_back(init_value[i]->d_term);
    }
  }
  res = cvc5->d_tm->export_term(
      cvc5->d_solver.declarePool(symbol, sort->d_sort, cinit_value));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

namespace {
cvc5::Term call_oracle(Cvc5* cvc5,
                       Cvc5Term (*fun)(size_t, const Cvc5Term*, void*),
                       const std::vector<cvc5::Term>& terms,
                       void* state)
{
  std::vector<Cvc5Term> cterms;
  for (auto& t : terms)
  {
    cterms.push_back(cvc5->d_tm->export_term(t));
  }
  return fun(cterms.size(), cterms.data(), state)->d_term;
}
}  // namespace

Cvc5Term cvc5_declare_oracle_fun(Cvc5* cvc5,
                                 const char* symbol,
                                 size_t size,
                                 const Cvc5Sort sorts[],
                                 Cvc5Sort sort,
                                 void* state,
                                 Cvc5Term (*fun)(size_t,
                                                 const Cvc5Term*,
                                                 void*))
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(symbol);
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_NOT_NULL(fun);
  std::vector<cvc5::Sort> csorts;
  if (sorts != nullptr)
  {
    for (size_t i = 0; i < size; ++i)
    {
      CVC5_CAPI_CHECK_SORT_AT_IDX(sorts, i);
      csorts.push_back(sorts[i]->d_sort);
    }
  }
  std::function<cvc5::Term(const std::vector<cvc5::Term>&)> cfun =
      [cvc5, state, fun](const std::vector<cvc5::Term>& terms) {
        cvc5::Term term = call_oracle(cvc5, fun, terms, state);
        return term;
      };
  res = cvc5->d_tm->export_term(
      cvc5->d_solver.declareOracleFun(symbol, csorts, sort->d_sort, cfun));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_add_plugin(Cvc5* cvc5, Cvc5Plugin* plugin)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(plugin);
  cvc5->d_plugin.reset(new Cvc5::PluginCpp(cvc5->d_tm->d_tm, cvc5, plugin));
  cvc5->d_solver.addPlugin(*cvc5->d_plugin);
  CVC5_CAPI_TRY_CATCH_END;
}

Cvc5Term cvc5_get_interpolant(Cvc5* cvc5, Cvc5Term conj)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(conj);
  cvc5::Term cres = cvc5->d_solver.getInterpolant(conj->d_term);
  res = cres.isNull() ? nullptr : cvc5->d_tm->export_term(cres);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_get_interpolant_with_grammar(Cvc5* cvc5,
                                           Cvc5Term conj,
                                           Cvc5Grammar grammar)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(conj);
  CVC5_CAPI_CHECK_GRAMMAR(grammar);
  cvc5::Term cres =
      cvc5->d_solver.getInterpolant(conj->d_term, grammar->d_grammar);
  res = cres.isNull() ? nullptr : cvc5->d_tm->export_term(cres);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_get_interpolant_next(Cvc5* cvc5)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  cvc5::Term cres = cvc5->d_solver.getInterpolantNext();
  res = cres.isNull() ? nullptr : cvc5->d_tm->export_term(cres);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_get_abduct(Cvc5* cvc5, Cvc5Term conj)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(conj);
  cvc5::Term cres = cvc5->d_solver.getAbduct(conj->d_term);
  res = cres.isNull() ? nullptr : cvc5->d_tm->export_term(cres);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_get_abduct_with_grammar(Cvc5* cvc5,
                                      Cvc5Term conj,
                                      Cvc5Grammar grammar)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(conj);
  CVC5_CAPI_CHECK_GRAMMAR(grammar);
  cvc5::Term cres = cvc5->d_solver.getAbduct(conj->d_term, grammar->d_grammar);
  res = cres.isNull() ? nullptr : cvc5->d_tm->export_term(cres);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_get_abduct_next(Cvc5* cvc5)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  cvc5::Term cres = cvc5->d_solver.getAbductNext();
  res = cres.isNull() ? nullptr : cvc5->d_tm->export_term(cres);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_block_model(Cvc5* cvc5, Cvc5BlockModelsMode mode)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  cvc5->d_solver.blockModel(static_cast<cvc5::modes::BlockModelsMode>(mode));
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_block_model_values(Cvc5* cvc5, size_t size, const Cvc5Term terms[])
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(terms);
  std::vector<cvc5::Term> cterms;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(terms, i);
    cterms.push_back(terms[i]->d_term);
  }
  cvc5->d_solver.blockModelValues(cterms);
  CVC5_CAPI_TRY_CATCH_END;
}

const char* cvc5_get_instantiations(Cvc5* cvc5)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  str = cvc5->d_solver.getInstantiations();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

void cvc5_push(Cvc5* cvc5, uint32_t nscopes)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  cvc5->d_solver.push(nscopes);
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_pop(Cvc5* cvc5, uint32_t nscopes)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  cvc5->d_solver.pop(nscopes);
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_reset_assertions(Cvc5* cvc5)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  cvc5->d_solver.resetAssertions();
  CVC5_CAPI_TRY_CATCH_END;
}

const char* cvc5_proof_to_string(Cvc5* cvc5,
                                 Cvc5Proof proof,
                                 Cvc5ProofFormat format,
                                 size_t size,
                                 const Cvc5Term assertions[],
                                 const char* names[])
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_PROOF(proof);
  CVC5_API_CHECK(assertions || names == nullptr) << "unexpected NULL argument";
  std::map<cvc5::Term, std::string> cassertion_names;
  if (assertions)
  {
    for (size_t i = 0; i < size; ++i)
    {
      cassertion_names.emplace(assertions[i]->d_term, names[i]);
    }
  }
  str = proof->d_cvc5->d_solver.proofToString(
      proof->d_proof,
      static_cast<cvc5::modes::ProofFormat>(format),
      cassertion_names);
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

Cvc5Term cvc5_declare_sygus_var(Cvc5* cvc5, const char* symbol, Cvc5Sort sort)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(symbol);
  CVC5_CAPI_CHECK_SORT(sort);
  res = cvc5->d_tm->export_term(
      cvc5->d_solver.declareSygusVar(symbol, sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Grammar cvc5_mk_grammar(Cvc5* cvc5,
                            size_t nbound_vars,
                            const Cvc5Term bound_vars[],
                            size_t nsymbols,
                            const Cvc5Term symbols[])
{
  Cvc5Grammar res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(symbols);
  std::vector<cvc5::Term> cbound_vars;
  if (nbound_vars)
  {
    for (size_t i = 0; i < nbound_vars; ++i)
    {
      cbound_vars.push_back(bound_vars[i]->d_term);
    }
  }
  std::vector<cvc5::Term> csymbols;
  for (size_t i = 0; i < nsymbols; ++i)
  {
    csymbols.push_back(symbols[i]->d_term);
  }
  res = cvc5->export_grammar(cvc5->d_solver.mkGrammar(cbound_vars, csymbols));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_synth_fun(Cvc5* cvc5,
                        const char* symbol,
                        size_t size,
                        const Cvc5Term bound_vars[],
                        Cvc5Sort sort)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(symbol);
  CVC5_CAPI_CHECK_SORT(sort);
  std::vector<cvc5::Term> cbound_vars;
  if (size)
  {
    for (size_t i = 0; i < size; ++i)
    {
      cbound_vars.push_back(bound_vars[i]->d_term);
    }
  }
  res = cvc5->d_tm->export_term(
      cvc5->d_solver.synthFun(symbol, cbound_vars, sort->d_sort));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_synth_fun_with_grammar(Cvc5* cvc5,
                                     const char* symbol,
                                     size_t size,
                                     const Cvc5Term bound_vars[],
                                     Cvc5Sort sort,
                                     Cvc5Grammar grammar)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(symbol);
  CVC5_CAPI_CHECK_SORT(sort);
  CVC5_CAPI_CHECK_GRAMMAR(grammar);
  std::vector<cvc5::Term> cbound_vars;
  if (size)
  {
    for (size_t i = 0; i < size; ++i)
    {
      cbound_vars.push_back(bound_vars[i]->d_term);
    }
  }
  res = cvc5->d_tm->export_term(cvc5->d_solver.synthFun(
      symbol, cbound_vars, sort->d_sort, grammar->d_grammar));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_add_sygus_constraint(Cvc5* cvc5, Cvc5Term term)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(term);
  cvc5->d_solver.addSygusConstraint(term->d_term);
  CVC5_CAPI_TRY_CATCH_END;
}

const Cvc5Term* cvc5_get_sygus_constraints(Cvc5* cvc5, size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto terms = cvc5->d_solver.getSygusConstraints();
  for (auto& t : terms)
  {
    res.push_back(cvc5->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

void cvc5_add_sygus_assume(Cvc5* cvc5, Cvc5Term term)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(term);
  cvc5->d_solver.addSygusAssume(term->d_term);
  CVC5_CAPI_TRY_CATCH_END;
}

const Cvc5Term* cvc5_get_sygus_assumptions(Cvc5* cvc5, size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto terms = cvc5->d_solver.getSygusAssumptions();
  for (auto& t : terms)
  {
    res.push_back(cvc5->d_tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

void cvc5_add_sygus_inv_constraint(
    Cvc5* cvc5, Cvc5Term inv, Cvc5Term pre, Cvc5Term trans, Cvc5Term post)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(inv);
  CVC5_CAPI_CHECK_TERM(pre);
  CVC5_CAPI_CHECK_TERM(trans);
  CVC5_CAPI_CHECK_TERM(post);
  cvc5->d_solver.addSygusInvConstraint(
      inv->d_term, pre->d_term, trans->d_term, post->d_term);
  CVC5_CAPI_TRY_CATCH_END;
}

Cvc5SynthResult cvc5_check_synth(Cvc5* cvc5)
{
  Cvc5SynthResult res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  res = cvc5->export_synth_result(cvc5->d_solver.checkSynth());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5SynthResult cvc5_check_synth_next(Cvc5* cvc5)
{
  Cvc5SynthResult res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  res = cvc5->export_synth_result(cvc5->d_solver.checkSynthNext());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_get_synth_solution(Cvc5* cvc5, Cvc5Term term)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_TERM(term);
  res = cvc5->d_tm->export_term(cvc5->d_solver.getSynthSolution(term->d_term));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const Cvc5Term* cvc5_get_synth_solutions(Cvc5* cvc5,
                                         size_t size,
                                         const Cvc5Term terms[])
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(terms);
  res.clear();
  std::vector<cvc5::Term> cterms;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_TERM_AT_IDX(terms, i);
    cterms.push_back(terms[i]->d_term);
  }
  auto rterms = cvc5->d_solver.getSynthSolutions(cterms);
  for (auto& t : rterms)
  {
    res.push_back(cvc5->d_tm->export_term(t));
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res.data();
}

Cvc5Term cvc5_find_synth(Cvc5* cvc5, Cvc5FindSynthTarget target)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_FIND_SYNTH_TARGET(target);
  cvc5::Term cres = cvc5->d_solver.findSynth(
      static_cast<cvc5::modes::FindSynthTarget>(target));
  res = cres.isNull() ? nullptr : cvc5->d_tm->export_term(cres);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_find_synth_with_grammar(Cvc5* cvc5,
                                      Cvc5FindSynthTarget target,
                                      Cvc5Grammar grammar)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_FIND_SYNTH_TARGET(target);
  CVC5_CAPI_CHECK_GRAMMAR(grammar);
  cvc5::Term cres = cvc5->d_solver.findSynth(
      static_cast<cvc5::modes::FindSynthTarget>(target), grammar->d_grammar);
  res = cres.isNull() ? nullptr : cvc5->d_tm->export_term(cres);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_find_synth_next(Cvc5* cvc5)
{
  Cvc5Term res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  cvc5::Term cres = cvc5->d_solver.findSynthNext();
  res = cres.isNull() ? nullptr : cvc5->d_tm->export_term(cres);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

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

/* -------------------------------------------------------------------------- */
/* Wrapper structs                                                            */
/* -------------------------------------------------------------------------- */

/** Wrapper for cvc5 C++ terms. */
struct cvc5_term_t
{
  /**
   * Constructor.
   * @param term The wrapped C++ term.
   * @param tm   The associated term manager.
   */
  cvc5_term_t(Cvc5TermManager* tm, const cvc5::Term& term)
      : d_term(term), d_tm(tm)
  {
  }
  /** The wrapped C++ term. */
  cvc5::Term d_term;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated term manager. */
  Cvc5TermManager* d_tm = nullptr;
};

/** Wrapper for cvc5 C++ sorts. */
struct cvc5_sort_t
{
  /**
   * Constructor.
   * @param sort The wrapped C++ sort.
   * @param tm   The associated term manager.
   */
  cvc5_sort_t(Cvc5TermManager* tm, const cvc5::Sort& sort)
      : d_sort(sort), d_tm(tm)
  {
  }
  /** The wrapped C++ sort. */
  cvc5::Sort d_sort;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated term manager. */
  Cvc5TermManager* d_tm = nullptr;
};

/** Wrapper for cvc5 C++ datatypes. */
struct cvc5_dt_t
{
  /**
   * Constructor.
   * @param tm The associated term manager.
   * @param dt The wrapped C++ datatype.
   */
  cvc5_dt_t(Cvc5TermManager* tm, const cvc5::Datatype& dt) : d_dt(dt), d_tm(tm)
  {
  }
  /** The wrapped C++ datatype. */
  cvc5::Datatype d_dt;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated term manager. */
  Cvc5TermManager* d_tm = nullptr;
};

/** Wrapper for cvc5 C++ datatype constructors. */
struct cvc5_dt_cons_t
{
  /**
   * Constructor.
   * @param tm The associated term manager.
   * @param dt The wrapped C++ datatype constructor.
   */
  cvc5_dt_cons_t(Cvc5TermManager* tm, const cvc5::DatatypeConstructor& cons)
      : d_dt_cons(cons), d_tm(tm)
  {
  }
  /** The wrapped C++ datatype constructor. */
  cvc5::DatatypeConstructor d_dt_cons;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated term manager. */
  Cvc5TermManager* d_tm = nullptr;
};

/** Wrapper for cvc5 C++ datatype selectors. */
struct cvc5_dt_sel_t
{
  /**
   * Constructor.
   * @param tm The associated term manager.
   * @param dt The wrapped C++ datatype selector.
   */
  cvc5_dt_sel_t(Cvc5TermManager* tm, const cvc5::DatatypeSelector& sel)
      : d_dt_sel(sel), d_tm(tm)
  {
  }
  /** The wrapped C++ datatype selector. */
  cvc5::DatatypeSelector d_dt_sel;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated term manager. */
  Cvc5TermManager* d_tm = nullptr;
};

/** Wrapper for cvc5 C++ datatype declarations. */
struct cvc5_dt_decl_t
{
  /**
   * Constructor.
   * @param decl The wrapped C++ datatype declaration.
   * @param tm   The associated term manager.
   */
  cvc5_dt_decl_t(Cvc5TermManager* tm, const cvc5::DatatypeDecl& decl)
      : d_decl(decl), d_tm(tm)
  {
  }
  /** The wrapped C++ datatype declaration. */
  cvc5::DatatypeDecl d_decl;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated term manager. */
  Cvc5TermManager* d_tm = nullptr;
};

/** Wrapper for cvc5 C++ datatype constructor declarations. */
struct cvc5_dt_cons_decl_t
{
  /**
   * Constructor.
   * @param decl The wrapped C++ datatype constructor declaration.
   * @param tm   The associated term manager.
   */
  cvc5_dt_cons_decl_t(Cvc5TermManager* tm,
                      const cvc5::DatatypeConstructorDecl& decl)
      : d_decl(decl), d_tm(tm)
  {
  }
  /** The wrapped C++ datatype constructor declaration. */
  cvc5::DatatypeConstructorDecl d_decl;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated term manager. */
  Cvc5TermManager* d_tm = nullptr;
};

/* -------------------------------------------------------------------------- */
/* Cvc5TermManager struct                                                     */
/* -------------------------------------------------------------------------- */

/** Wrapper for cvc5 C++ term manager. */
struct Cvc5TermManager
{
  /**
   * Export C++ sort to C API.
   * @param sort The sort to export.
   */
  Cvc5Sort export_sort(const cvc5::Sort& sort);
  /**
   * Export C++ term to C API.
   * @param term The term to export.
   */
  Cvc5Term export_term(const cvc5::Term& term);
  /**
   * Export C++ datatype to C API.
   * @param dt The datatype to export.
   */
  Cvc5Datatype export_dt(const cvc5::Datatype& dt);
  /**
   * Export C++ datatype constructor to C API.
   * @param cons The datatype constructor to export.
   */
  Cvc5DatatypeConstructor export_dt_cons(const cvc5::DatatypeConstructor& cons);
  /**
   * Export C++ datatype selector to C API.
   * @param sel The datatype selector to export.
   */
  Cvc5DatatypeSelector export_dt_sel(const cvc5::DatatypeSelector& sel);
  /**
   * Export C++ datatype declaration to C API.
   * @param decl The datatype declaration to export.
   */
  Cvc5DatatypeDecl export_dt_decl(const cvc5::DatatypeDecl& decl);
  /**
   * Export C++ datatype constructor declaration to C API.
   * @param decl The datatype constructor declaration to export.
   */
  Cvc5DatatypeConstructorDecl export_dt_cons_decl(
      const cvc5::DatatypeConstructorDecl& decl);

  /* Manual memory management for sorts and terms. ------ */

  /**
   * Decrement the external ref count of a term. If the ref count reaches zero,
   * the term is release (freed).
   * @param term The term to release.
   */
  void release(cvc5_term_t* term);
  /**
   * Increment the external ref count of a term.
   * @param term The term to copy.
   * @return The copied term.
   */
  cvc5_term_t* copy(cvc5_term_t* term);
  /**
   * Decrement the external ref count of a sort. If the ref count reaches zero,
   * the sort is release (freed).
   * @param sort The sort to release.
   */
  void release(cvc5_sort_t* sort);
  /**
   * Increment the external ref count of a sort.
   * @param sort The sort to copy.
   * @return The copied sort.
   */
  cvc5_sort_t* copy(cvc5_sort_t* sort);
  /**
   * Decrement the external ref count of a datatype. If the ref count reaches
   * zero, the datatype is release (freed).
   * @param dt The datatype to release.
   */
  void release(cvc5_dt_t* dt);
  /**
   * Increment the external ref count of a datatype.
   * @param dt The datatype to copy.
   * @return The copied datatype.
   */
  cvc5_dt_t* copy(cvc5_dt_t* dt);
  /**
   * Decrement the external ref count of a datatype constructor. If the ref
   * count reaches zero, the datatype constructor is release (freed).
   * @param cons The datatype constructor to release.
   */
  void release(cvc5_dt_cons_t* cons);
  /**
   * Increment the external ref count of a datatype constructor.
   * @param cons The datatype constructor to copy.
   * @return The copied datatype constructor.
   */
  cvc5_dt_cons_t* copy(cvc5_dt_cons_t* cons);
  /**
   * Decrement the external ref count of a datatype selector. If the ref
   * count reaches zero, the datatype selector is release (freed).
   * @param cons The datatype selector to release.
   */
  void release(cvc5_dt_sel_t* sel);
  /**
   * Increment the external ref count of a datatype selector.
   * @param cons The datatype selector to copy.
   * @return The copied datatype selector.
   */
  cvc5_dt_sel_t* copy(cvc5_dt_sel_t* sel);
  /**
   * Decrement the external ref count of a datatype declaration. If the ref
   * count reaches zero, the datatype declaration is release (freed).
   * @param decl The datatype declaration to release.
   */
  void release(cvc5_dt_decl_t* decl);
  /**
   * Increment the external ref count of a datatype declaration.
   * @param decl The datatype declaration to copy.
   * @return The copied datatype declaration.
   */
  cvc5_dt_decl_t* copy(cvc5_dt_decl_t* decl);
  /**
   * Decrement the external ref count of a datatype constructor declaration. If
   * the ref count reaches zero, the datatype constructor declaration is
   * release (freed).
   * @param decl The datatype constructor declaration to release.
   */
  void release(cvc5_dt_cons_decl_t* decl);
  /**
   * Increment the external ref count of a datatype constructor declaration.
   * @param decl The datatype constructor declaration to copy.
   * @return The copied datatype constructor declaration.
   */
  cvc5_dt_cons_decl_t* copy(cvc5_dt_cons_decl_t* decl);

  /** Release all managed objects. */
  void release();

  /* ---------------------------------------------------- */

  /** The associated term manager instance. */
  cvc5::TermManager d_tm;

 private:
  std::unordered_map<cvc5::Sort, cvc5_sort_t> d_alloc_sorts;
  std::unordered_map<cvc5::Term, cvc5_term_t> d_alloc_terms;
  std::unordered_map<cvc5::Datatype, cvc5_dt_t> d_alloc_dts;
  std::unordered_map<cvc5::DatatypeConstructor, cvc5_dt_cons_t>
      d_alloc_dt_conss;
  std::unordered_map<cvc5::DatatypeSelector, cvc5_dt_sel_t> d_alloc_dt_sels;
  std::unordered_map<cvc5::DatatypeDecl, cvc5_dt_decl_t> d_alloc_dt_decls;
  std::unordered_map<cvc5::DatatypeConstructorDecl, cvc5_dt_cons_decl_t>
      d_alloc_dt_cons_decls;
};

Cvc5Sort Cvc5TermManager::export_sort(const cvc5::Sort& sort)
{
  Assert(!sort.isNull());
  auto [it, inserted] = d_alloc_sorts.try_emplace(sort, this, sort);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

Cvc5Term Cvc5TermManager::export_term(const cvc5::Term& term)
{
  Assert(!term.isNull());
  auto [it, inserted] = d_alloc_terms.try_emplace(term, this, term);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

Cvc5Datatype Cvc5TermManager::export_dt(const cvc5::Datatype& dt)
{
  Assert(!dt.isNull());
  auto [it, inserted] = d_alloc_dts.try_emplace(dt, this, dt);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

Cvc5DatatypeConstructor Cvc5TermManager::export_dt_cons(
    const cvc5::DatatypeConstructor& cons)
{
  Assert(!cons.isNull());
  auto [it, inserted] = d_alloc_dt_conss.try_emplace(cons, this, cons);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

Cvc5DatatypeSelector Cvc5TermManager::export_dt_sel(
    const cvc5::DatatypeSelector& sel)
{
  Assert(!sel.isNull());
  auto [it, inserted] = d_alloc_dt_sels.try_emplace(sel, this, sel);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

Cvc5DatatypeDecl Cvc5TermManager::export_dt_decl(const cvc5::DatatypeDecl& decl)
{
  Assert(!decl.isNull());
  auto [it, inserted] = d_alloc_dt_decls.try_emplace(decl, this, decl);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

Cvc5DatatypeConstructorDecl Cvc5TermManager::export_dt_cons_decl(
    const cvc5::DatatypeConstructorDecl& decl)
{
  Assert(!decl.isNull());
  auto [it, inserted] = d_alloc_dt_cons_decls.try_emplace(decl, this, decl);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

void Cvc5TermManager::release(cvc5_term_t* term)
{
  term->d_refs -= 1;
  if (term->d_refs == 0)
  {
    Assert(d_alloc_terms.find(term->d_term) != d_alloc_terms.end());
    d_alloc_terms.erase(term->d_term);
  }
}

cvc5_term_t* Cvc5TermManager::copy(cvc5_term_t* term)
{
  term->d_refs += 1;
  return term;
}

void Cvc5TermManager::release(cvc5_sort_t* sort)
{
  sort->d_refs -= 1;
  if (sort->d_refs == 0)
  {
    Assert(d_alloc_sorts.find(sort->d_sort) != d_alloc_sorts.end());
    d_alloc_sorts.erase(sort->d_sort);
  }
}

cvc5_sort_t* Cvc5TermManager::copy(cvc5_sort_t* sort)
{
  sort->d_refs += 1;
  return sort;
}

void Cvc5TermManager::release(cvc5_dt_t* dt)
{
  dt->d_refs -= 1;
  if (dt->d_refs == 0)
  {
    Assert(d_alloc_dts.find(dt->d_dt) != d_alloc_dts.end());
    d_alloc_dts.erase(dt->d_dt);
  }
}

cvc5_dt_t* Cvc5TermManager::copy(cvc5_dt_t* dt)
{
  dt->d_refs += 1;
  return dt;
}

void Cvc5TermManager::release(cvc5_dt_cons_t* cons)
{
  cons->d_refs -= 1;
  if (cons->d_refs == 0)
  {
    Assert(d_alloc_dt_conss.find(cons->d_dt_cons) != d_alloc_dt_conss.end());
    d_alloc_dt_conss.erase(cons->d_dt_cons);
  }
}

cvc5_dt_cons_t* Cvc5TermManager::copy(cvc5_dt_cons_t* cons)
{
  cons->d_refs += 1;
  return cons;
}

void Cvc5TermManager::release(cvc5_dt_sel_t* sel)
{
  sel->d_refs -= 1;
  if (sel->d_refs == 0)
  {
    Assert(d_alloc_dt_sels.find(sel->d_dt_sel) != d_alloc_dt_sels.end());
    d_alloc_dt_sels.erase(sel->d_dt_sel);
  }
}

cvc5_dt_sel_t* Cvc5TermManager::copy(cvc5_dt_sel_t* sel)
{
  sel->d_refs += 1;
  return sel;
}

void Cvc5TermManager::release(cvc5_dt_decl_t* decl)
{
  decl->d_refs -= 1;
  if (decl->d_refs == 0)
  {
    Assert(d_alloc_dt_decls.find(decl->d_decl) != d_alloc_dt_decls.end());
    d_alloc_dt_decls.erase(decl->d_decl);
  }
}

cvc5_dt_decl_t* Cvc5TermManager::copy(cvc5_dt_decl_t* decl)
{
  decl->d_refs += 1;
  return decl;
}

void Cvc5TermManager::release(cvc5_dt_cons_decl_t* decl)
{
  decl->d_refs -= 1;
  if (decl->d_refs == 0)
  {
    Assert(d_alloc_dt_cons_decls.find(decl->d_decl)
           != d_alloc_dt_cons_decls.end());
    d_alloc_dt_cons_decls.erase(decl->d_decl);
  }
}

cvc5_dt_cons_decl_t* Cvc5TermManager::copy(cvc5_dt_cons_decl_t* decl)
{
  decl->d_refs += 1;
  return decl;
}

void Cvc5TermManager::release()
{
  d_alloc_sorts.clear();
  d_alloc_terms.clear();
  d_alloc_dts.clear();
  d_alloc_dt_conss.clear();
  d_alloc_dt_sels.clear();
  d_alloc_dt_decls.clear();
  d_alloc_dt_cons_decls.clear();
}

/* -------------------------------------------------------------------------- */
/* Cvc5Sort                                                                   */
/* -------------------------------------------------------------------------- */

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
    res = a != b;
  }
  else
  {
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

/* Cvc5DatatypeDecl ---------------------------------------------------- */

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
  res = decl->d_decl.getNumConstructors();
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

/* Cvc5DatatypeSelector ------------------------------------------------ */

const char* cvc5_dt_del_get_name(Cvc5DatatypeSelector sel)
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

/* Cvc5DatatypeConstructor --------------------------------------------- */

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

/* Cvc5Datatype -------------------------------------------------------- */

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

/* -------------------------------------------------------------------------- */
/* Cvc5Term                                                                   */
/* -------------------------------------------------------------------------- */

Cvc5Sort cvc5_term_get_sort(Cvc5Term term)
{
  Cvc5Sort res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_TERM(term);
  res = term->d_tm->export_sort(term->d_term.getSort());
  CVC5_CAPI_TRY_CATCH_END;
  return res;
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
  delete tm;
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_term_manager_release(Cvc5TermManager* tm)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  tm->release();
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
  CVC5_CAPI_CHECK_NOT_NULL(params);
  std::vector<cvc5::Sort> cparams;
  for (size_t i = 0; i < size; ++i)
  {
    CVC5_CAPI_CHECK_SORT_AT_IDX(params, i);
    cparams.push_back(params[i]->d_sort);
  }
  res = tm->export_dt_decl(tm->d_tm.mkDatatypeDecl(name, cparams, is_codt));
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

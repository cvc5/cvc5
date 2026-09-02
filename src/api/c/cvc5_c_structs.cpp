/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 types definitions for the C API.
 */

#include "api/c/cvc5_c_structs.h"

#include "api/c/cvc5_checks.h"

/* -------------------------------------------------------------------------- */
/* Thread-local error state                                                   */
/* -------------------------------------------------------------------------- */

namespace cvc5 {

namespace {
/** Whether an error occurred during the most recent guarded C API call. */
thread_local bool s_error_flag = false;
/** The message associated with the most recent error (if any). */
thread_local std::string s_error_msg;
}  // namespace

void cvc5_capi_set_error(const std::string& msg)
{
  s_error_flag = true;
  s_error_msg = msg;
}

void cvc5_capi_reset_error()
{
  s_error_flag = false;
  s_error_msg.clear();
}

bool cvc5_capi_has_error() { return s_error_flag; }

const char* cvc5_capi_get_error_message() { return s_error_msg.c_str(); }

}  // namespace cvc5

/* -------------------------------------------------------------------------- */
/* Cvc5TermManager struct                                                     */
/* -------------------------------------------------------------------------- */

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

Cvc5Op Cvc5TermManager::export_op(const cvc5::Op& op)
{
  Assert(!op.isNull());
  auto [it, inserted] = d_alloc_ops.try_emplace(op, this, op);
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

Cvc5Stat Cvc5TermManager::export_stat(const cvc5::Stat& stat)
{
  auto s = std::make_unique<cvc5_stat_t>(this, stat);
  cvc5_stat_t* res = s.get();
  d_alloc_stats.emplace(res, std::move(s));
  return res;
}

Cvc5Statistics Cvc5TermManager::export_stats(const cvc5::Statistics& stat)
{
  auto s = std::make_unique<cvc5_stats_t>(this, stat);
  cvc5_stats_t* res = s.get();
  d_alloc_statistics.emplace(res, std::move(s));
  return res;
}

void Cvc5TermManager::release(cvc5_term_t* term)
{
  if (term)
  {
    term->d_refs -= 1;
    if (term->d_refs == 0)
    {
      Assert(d_alloc_terms.find(term->d_term) != d_alloc_terms.end());
      d_alloc_terms.erase(term->d_term);
      free_if_unused();
    }
  }
}

cvc5_term_t* Cvc5TermManager::copy(cvc5_term_t* term)
{
  if (term)
  {
    term->d_refs += 1;
  }
  return term;
}

void Cvc5TermManager::release(cvc5_op_t* op)
{
  if (op)
  {
    op->d_refs -= 1;
    if (op->d_refs == 0)
    {
      Assert(d_alloc_ops.find(op->d_op) != d_alloc_ops.end());
      d_alloc_ops.erase(op->d_op);
      free_if_unused();
    }
  }
}

cvc5_op_t* Cvc5TermManager::copy(cvc5_op_t* op)
{
  if (op)
  {
    op->d_refs += 1;
  }
  return op;
}

void Cvc5TermManager::release(cvc5_sort_t* sort)
{
  if (sort)
  {
    sort->d_refs -= 1;
    if (sort->d_refs == 0)
    {
      Assert(d_alloc_sorts.find(sort->d_sort) != d_alloc_sorts.end());
      d_alloc_sorts.erase(sort->d_sort);
      free_if_unused();
    }
  }
}

cvc5_sort_t* Cvc5TermManager::copy(cvc5_sort_t* sort)
{
  if (sort)
  {
    sort->d_refs += 1;
  }
  return sort;
}

void Cvc5TermManager::release(cvc5_dt_t* dt)
{
  if (dt)
  {
    dt->d_refs -= 1;
    if (dt->d_refs == 0)
    {
      Assert(d_alloc_dts.find(dt->d_dt) != d_alloc_dts.end());
      d_alloc_dts.erase(dt->d_dt);
      free_if_unused();
    }
  }
}

cvc5_dt_t* Cvc5TermManager::copy(cvc5_dt_t* dt)
{
  if (dt)
  {
    dt->d_refs += 1;
  }
  return dt;
}

void Cvc5TermManager::release(cvc5_dt_cons_t* cons)
{
  if (cons)
  {
    cons->d_refs -= 1;
    if (cons->d_refs == 0)
    {
      Assert(d_alloc_dt_conss.find(cons->d_dt_cons) != d_alloc_dt_conss.end());
      d_alloc_dt_conss.erase(cons->d_dt_cons);
      free_if_unused();
    }
  }
}

cvc5_dt_cons_t* Cvc5TermManager::copy(cvc5_dt_cons_t* cons)
{
  if (cons)
  {
    cons->d_refs += 1;
  }
  return cons;
}

void Cvc5TermManager::release(cvc5_dt_sel_t* sel)
{
  if (sel)
  {
    sel->d_refs -= 1;
    if (sel->d_refs == 0)
    {
      Assert(d_alloc_dt_sels.find(sel->d_dt_sel) != d_alloc_dt_sels.end());
      d_alloc_dt_sels.erase(sel->d_dt_sel);
      free_if_unused();
    }
  }
}

cvc5_dt_sel_t* Cvc5TermManager::copy(cvc5_dt_sel_t* sel)
{
  if (sel)
  {
    sel->d_refs += 1;
  }
  return sel;
}

void Cvc5TermManager::release(cvc5_dt_decl_t* decl)
{
  if (decl)
  {
    decl->d_refs -= 1;
    if (decl->d_refs == 0)
    {
      Assert(d_alloc_dt_decls.find(decl->d_decl) != d_alloc_dt_decls.end());
      d_alloc_dt_decls.erase(decl->d_decl);
      free_if_unused();
    }
  }
}

cvc5_dt_decl_t* Cvc5TermManager::copy(cvc5_dt_decl_t* decl)
{
  if (decl)
  {
    decl->d_refs += 1;
  }
  return decl;
}

void Cvc5TermManager::release(cvc5_dt_cons_decl_t* decl)
{
  if (decl)
  {
    decl->d_refs -= 1;
    if (decl->d_refs == 0)
    {
      Assert(d_alloc_dt_cons_decls.find(decl->d_decl)
             != d_alloc_dt_cons_decls.end());
      d_alloc_dt_cons_decls.erase(decl->d_decl);
      free_if_unused();
    }
  }
}

cvc5_dt_cons_decl_t* Cvc5TermManager::copy(cvc5_dt_cons_decl_t* decl)
{
  if (decl)
  {
    decl->d_refs += 1;
  }
  return decl;
}

void Cvc5TermManager::release(cvc5_stat_t* stat)
{
  if (stat)
  {
    stat->d_refs -= 1;
    if (stat->d_refs == 0)
    {
      Assert(d_alloc_stats.find(stat) != d_alloc_stats.end());
      d_alloc_stats.erase(stat);
      free_if_unused();
    }
  }
}

cvc5_stat_t* Cvc5TermManager::copy(cvc5_stat_t* stat)
{
  if (stat)
  {
    stat->d_refs += 1;
  }
  return stat;
}

void Cvc5TermManager::release(cvc5_stats_t* stat)
{
  if (stat)
  {
    stat->d_refs -= 1;
    if (stat->d_refs == 0)
    {
      Assert(d_alloc_statistics.find(stat) != d_alloc_statistics.end());
      d_alloc_statistics.erase(stat);
      free_if_unused();
    }
  }
}

cvc5_stats_t* Cvc5TermManager::copy(cvc5_stats_t* stat)
{
  if (stat)
  {
    stat->d_refs += 1;
  }
  return stat;
}

void Cvc5TermManager::release()
{
  d_alloc_sorts.clear();
  d_alloc_terms.clear();
  d_alloc_ops.clear();
  d_alloc_dts.clear();
  d_alloc_dt_conss.clear();
  d_alloc_dt_sels.clear();
  d_alloc_dt_decls.clear();
  d_alloc_dt_cons_decls.clear();
  d_alloc_stats.clear();
  d_alloc_statistics.clear();
  free_if_unused();
}

void Cvc5TermManager::inc_ref() { d_refs += 1; }

void Cvc5TermManager::dec_ref()
{
  Assert(d_refs > 0);
  d_refs -= 1;
  free_if_unused();
}

bool Cvc5TermManager::has_objects() const
{
  return !d_alloc_sorts.empty() || !d_alloc_terms.empty()
         || !d_alloc_ops.empty() || !d_alloc_dts.empty()
         || !d_alloc_dt_conss.empty() || !d_alloc_dt_sels.empty()
         || !d_alloc_dt_decls.empty() || !d_alloc_dt_cons_decls.empty()
         || !d_alloc_stats.empty() || !d_alloc_statistics.empty();
}

void Cvc5TermManager::free_if_unused()
{
  if (d_refs == 0 && !has_objects())
  {
    delete this;
  }
}

/* -------------------------------------------------------------------------- */
/* Cvc5 struct                                                                */
/* -------------------------------------------------------------------------- */

Cvc5::Cvc5(Cvc5TermManager* tm) : d_solver(tm->d_tm), d_tm(tm)
{
  // The solver keeps the term manager alive (e.g., to export objects created
  // via the solver).
  d_tm->inc_ref();
}

Cvc5Result Cvc5::export_result(const cvc5::Result& result)
{
  Assert(!result.isNull());
  cvc5_result_t* res = new cvc5_result_t(this, result);
  d_alloc_results.insert(res);
  return res;
}

void Cvc5::deregister(cvc5_result_t* result)
{
  Assert(d_alloc_results.find(result) != d_alloc_results.end());
  d_alloc_results.erase(result);
}

cvc5_result_t* cvc5_result_t::copy()
{
  d_refs += 1;
  return this;
}

void cvc5_result_t::release()
{
  d_refs -= 1;
  if (d_refs == 0)
  {
    // The solver may already be gone, in which case there is no cache entry
    // left to drop.
    if (d_cvc5)
    {
      d_cvc5->deregister(this);
    }
    delete this;
  }
}

Cvc5SynthResult Cvc5::export_synth_result(const cvc5::SynthResult& result)
{
  Assert(!result.isNull());
  cvc5_synth_result_t* res = new cvc5_synth_result_t(this, result);
  d_alloc_synth_results.insert(res);
  return res;
}

void Cvc5::deregister(cvc5_synth_result_t* result)
{
  Assert(d_alloc_synth_results.find(result) != d_alloc_synth_results.end());
  d_alloc_synth_results.erase(result);
}

cvc5_synth_result_t* cvc5_synth_result_t::copy()
{
  d_refs += 1;
  return this;
}

void cvc5_synth_result_t::release()
{
  d_refs -= 1;
  if (d_refs == 0)
  {
    if (d_cvc5)
    {
      d_cvc5->deregister(this);
    }
    delete this;
  }
}

cvc5_proof_t::cvc5_proof_t(Cvc5* cvc5,
                           Cvc5TermManager* tm,
                           const cvc5::Proof& proof)
    : d_proof(proof), d_cvc5(cvc5), d_tm(tm)
{
  // a proof needs its term manager to export terms and child proofs
  d_tm->inc_ref();
}

cvc5_proof_t::~cvc5_proof_t() { d_tm->dec_ref(); }

cvc5_proof_t* cvc5_proof_t::copy()
{
  d_refs += 1;
  return this;
}

void cvc5_proof_t::release()
{
  d_refs -= 1;
  if (d_refs == 0)
  {
    if (d_cvc5)
    {
      d_cvc5->deregister(this);
    }
    delete this;
  }
}

Cvc5Proof cvc5_proof_t::export_proof(const cvc5::Proof& proof)
{
  if (d_cvc5)
  {
    return d_cvc5->export_proof(proof);
  }
  // The solver is already gone: the exported proof is not associated with
  // any solver and is only freed by its own release.
  return new cvc5_proof_t(nullptr, d_tm, proof);
}

Cvc5Proof Cvc5::export_proof(const cvc5::Proof& proof)
{
  cvc5_proof_t* res = new cvc5_proof_t(this, d_tm, proof);
  d_alloc_proofs.insert(res);
  return res;
}

void Cvc5::deregister(cvc5_proof_t* proof)
{
  Assert(d_alloc_proofs.find(proof) != d_alloc_proofs.end());
  d_alloc_proofs.erase(proof);
}

cvc5_grammar_t* cvc5_grammar_t::copy()
{
  d_refs += 1;
  return this;
}

void cvc5_grammar_t::release()
{
  d_refs -= 1;
  if (d_refs == 0)
  {
    if (d_cvc5)
    {
      d_cvc5->deregister(this);
    }
    delete this;
  }
}

Cvc5Grammar Cvc5::export_grammar(const cvc5::Grammar& grammar)
{
  cvc5_grammar_t* res = new cvc5_grammar_t(this, grammar);
  d_alloc_grammars.insert(res);
  return res;
}

void Cvc5::deregister(cvc5_grammar_t* grammar)
{
  Assert(d_alloc_grammars.find(grammar) != d_alloc_grammars.end());
  d_alloc_grammars.erase(grammar);
}

Cvc5::~Cvc5()
{
  // Drop one reference on each result created by this solver: results the
  // user holds an additional reference to (via `cvc5_result_copy()`) survive
  // detached from the solver, the others are freed here.
  for (cvc5_result_t* res : d_alloc_results)
  {
    res->d_cvc5 = nullptr;
    res->release();
  }
  d_alloc_results.clear();
  for (cvc5_synth_result_t* res : d_alloc_synth_results)
  {
    res->d_cvc5 = nullptr;
    res->release();
  }
  d_alloc_synth_results.clear();
  for (cvc5_proof_t* res : d_alloc_proofs)
  {
    res->d_cvc5 = nullptr;
    res->release();
  }
  d_alloc_proofs.clear();
  for (cvc5_grammar_t* res : d_alloc_grammars)
  {
    res->d_cvc5 = nullptr;
    res->release();
  }
  d_alloc_grammars.clear();
  if (d_output_tag_file_stream.is_open())
  {
    d_output_tag_file_stream.close();
  }
  // reset redirected output stream returned by Solver::getOutput()
  if (d_output_tag_stream)
  {
    Assert(d_output_tag_streambuf);
    d_output_tag_stream->rdbuf(d_output_tag_streambuf);
  }
  // Drop our handle to the term manager. Note that this may free the term
  // manager wrapper (if it was already deleted by the user and no managed
  // objects are left). This is safe, the C++ solver instance holds its own
  // copy of the C++ term manager.
  d_tm->dec_ref();
}

std::vector<cvc5::Term> Cvc5::PluginCpp::check()
{
  Assert(d_plugin);
  std::vector<cvc5::Term> res;
  if (d_plugin->check)
  {
    size_t size;
    const Cvc5Term* terms = d_plugin->check(&size, d_plugin->d_check_state);
    for (size_t i = 0; i < size; ++i)
    {
      res.push_back(terms[i]->d_term);
    }
  }
  return res;
}

void Cvc5::PluginCpp::notifySatClause(const cvc5::Term& clause)
{
  Assert(d_plugin);
  if (d_plugin->notify_sat_clause)
  {
    d_plugin->notify_sat_clause(d_cvc5->d_tm->export_term(clause),
                                d_plugin->d_notify_sat_clause_state);
  }
}

void Cvc5::PluginCpp::notifyTheoryLemma(const cvc5::Term& lemma)
{
  Assert(d_plugin);
  if (d_plugin->notify_theory_lemma)
  {
    d_plugin->notify_theory_lemma(d_cvc5->d_tm->export_term(lemma),
                                  d_plugin->d_notify_theory_lemma_state);
  }
}

std::string Cvc5::PluginCpp::getName()
{
  Assert(d_plugin);
  Assert(d_plugin->get_name);
  return d_plugin->get_name();
}

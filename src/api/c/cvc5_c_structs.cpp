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
 * The cvc5 types definitions for the C API.
 */

#include "api/c/cvc5_c_structs.h"

#include "api/c/cvc5_checks.h"

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
  d_alloc_stats.emplace_back(this, stat);
  return &d_alloc_stats.back();
}

Cvc5Statistics Cvc5TermManager::export_stats(const cvc5::Statistics& stat)
{
  d_alloc_statistics.emplace_back(this, stat);
  return &d_alloc_statistics.back();
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
/* Cvc5 struct                                                                */
/* -------------------------------------------------------------------------- */

Cvc5::~Cvc5()
{
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
}

Cvc5Result Cvc5::export_result(const cvc5::Result& result)
{
  Assert(!result.isNull());
  auto [it, inserted] = d_alloc_results.try_emplace(result, this, result);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

void Cvc5::release(cvc5_result_t* result)
{
  result->d_refs -= 1;
  if (result->d_refs == 0)
  {
    Assert(d_alloc_results.find(result->d_result) != d_alloc_results.end());
    d_alloc_results.erase(result->d_result);
  }
}

cvc5_result_t* Cvc5::copy(cvc5_result_t* result)
{
  result->d_refs += 1;
  return result;
}

Cvc5SynthResult Cvc5::export_synth_result(const cvc5::SynthResult& result)
{
  Assert(!result.isNull());
  auto [it, inserted] = d_alloc_synth_results.try_emplace(result, this, result);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

void Cvc5::release(cvc5_synth_result_t* result)
{
  result->d_refs -= 1;
  if (result->d_refs == 0)
  {
    Assert(d_alloc_synth_results.find(result->d_result)
           != d_alloc_synth_results.end());
    d_alloc_synth_results.erase(result->d_result);
  }
}

cvc5_synth_result_t* Cvc5::copy(cvc5_synth_result_t* result)
{
  result->d_refs += 1;
  return result;
}

Cvc5Proof Cvc5::export_proof(const cvc5::Proof& proof)
{
  auto [it, inserted] = d_alloc_proofs.try_emplace(proof, this, proof);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

void Cvc5::release(cvc5_proof_t* proof)
{
  proof->d_refs -= 1;
  if (proof->d_refs == 0)
  {
    Assert(d_alloc_proofs.find(proof->d_proof) != d_alloc_proofs.end());
    d_alloc_proofs.erase(proof->d_proof);
  }
}

cvc5_proof_t* Cvc5::copy(cvc5_proof_t* proof)
{
  proof->d_refs += 1;
  return proof;
}

Cvc5Grammar Cvc5::export_grammar(const cvc5::Grammar& grammar)
{
  auto [it, inserted] = d_alloc_grammars.try_emplace(grammar, this, grammar);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

void Cvc5::release(cvc5_grammar_t* grammar)
{
  grammar->d_refs -= 1;
  if (grammar->d_refs == 0)
  {
    Assert(d_alloc_grammars.find(grammar->d_grammar) != d_alloc_grammars.end());
    d_alloc_grammars.erase(grammar->d_grammar);
  }
}

cvc5_grammar_t* Cvc5::copy(cvc5_grammar_t* grammar)
{
  grammar->d_refs += 1;
  return grammar;
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

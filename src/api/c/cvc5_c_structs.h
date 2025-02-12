/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 types definitions for the C API.
 */

#ifndef CVC5__C_API__CVC5_C_TYPES_H
#define CVC5__C_API__CVC5_C_TYPES_H

extern "C" {
#include <cvc5/c/cvc5.h>
}
#include <cvc5/cvc5.h>

#include <fstream>

/* -------------------------------------------------------------------------- */
/* Wrapper structs (associated with Cvc5TermManager)                          */
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

/** Wrapper for cvc5 C++ operators. */
struct cvc5_op_t
{
  /**
   * Constructor.
   * @param op The wrapped C++ operator.
   * @param tm The associated term manager.
   */
  cvc5_op_t(Cvc5TermManager* tm, const cvc5::Op& op) : d_op(op), d_tm(tm) {}
  /** The wrapped C++ op. */
  cvc5::Op d_op;
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

/**
 * Wrapper for cvc5 C++ term manager.
 * @note Visibility of this struct is set to export for linkage of parser
 *       library (it needs to be able to use member functions of the struct).
 */
struct CVC5_EXPORT Cvc5TermManager
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
   * Export C++ operator to C API.
   * @param op The operator to export.
   */
  Cvc5Op export_op(const cvc5::Op& op);
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

  /**
   * Export C++ statistic to C API.
   * @param statistic The statistic to export.
   */
  Cvc5Stat export_stat(const cvc5::Stat& stat);

  /**
   * Export C++ statistics to C API.
   * @param statistics The statistics to export.
   */
  Cvc5Statistics export_stats(const cvc5::Statistics& stat);

  /* Manual memory management for sorts and terms. ------ */

  /**
   * Decrement the external ref count of a term. If the ref count reaches zero,
   * the term is released (freed).
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
   * Decrement the external ref count of an operator. If the ref count reaches
   * zero, the operator is released (freed).
   * @param op The operator to release.
   */
  void release(cvc5_op_t* op);
  /**
   * Increment the external ref count of an operator.
   * @param op The operator to copy.
   * @return The copied operator.
   */
  cvc5_op_t* copy(cvc5_op_t* term);
  /**
   * Decrement the external ref count of a sort. If the ref count reaches zero,
   * the sort is released (freed).
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
   * zero, the datatype is released (freed).
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
   * count reaches zero, the datatype constructor is released (freed).
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
   * count reaches zero, the datatype selector is released (freed).
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
   * count reaches zero, the datatype declaration is released (freed).
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
  /** Cache of allocated sorts. */
  std::unordered_map<cvc5::Sort, cvc5_sort_t> d_alloc_sorts;
  /** Cache of allocated terms. */
  std::unordered_map<cvc5::Term, cvc5_term_t> d_alloc_terms;
  /** Cache of allocated operators. */
  std::unordered_map<cvc5::Op, cvc5_op_t> d_alloc_ops;
  /** Cache of allocated datatypes. */
  std::unordered_map<cvc5::Datatype, cvc5_dt_t> d_alloc_dts;
  /** Cache of allocated datatype constructors. */
  std::unordered_map<cvc5::DatatypeConstructor, cvc5_dt_cons_t>
      d_alloc_dt_conss;
  /** Cache of allocated datatype selectors. */
  std::unordered_map<cvc5::DatatypeSelector, cvc5_dt_sel_t> d_alloc_dt_sels;
  /** Cache of allocated datatype declarations. */
  std::unordered_map<cvc5::DatatypeDecl, cvc5_dt_decl_t> d_alloc_dt_decls;
  /** Cache of allocated datatype constructor declarations. */
  std::unordered_map<cvc5::DatatypeConstructorDecl, cvc5_dt_cons_decl_t>
      d_alloc_dt_cons_decls;
  /** Cache of allocated statistic objects. */
  std::vector<cvc5_stat_t> d_alloc_stats;
  /** Cache of allocated statistics objects. */
  std::vector<cvc5_stats_t> d_alloc_statistics;
};

/* -------------------------------------------------------------------------- */
/* Wrapper structs (associated with Cvc5)                                     */
/* -------------------------------------------------------------------------- */

/** Wrapper for cvc5 C++ results. */
struct cvc5_result_t
{
  /**
   * Constructor.
   * @param cvc5   The associated solver instance.
   * @param result The wrapped C++ result.
   */
  cvc5_result_t(Cvc5* cvc5, const cvc5::Result& result)
      : d_result(result), d_cvc5(cvc5)
  {
  }
  /** The wrapped C++ result. */
  cvc5::Result d_result;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated solver instance. */
  Cvc5* d_cvc5 = nullptr;
};

/** Wrapper for cvc5 C++ synthesis results. */
struct cvc5_synth_result_t
{
  /**
   * Constructor.
   * @param cvc5   The associated solver instance.
   * @param result The wrapped C++ synthesis result.
   */
  cvc5_synth_result_t(Cvc5* cvc5, const cvc5::SynthResult& result)
      : d_result(result), d_cvc5(cvc5)
  {
  }
  /** The wrapped C++ result. */
  cvc5::SynthResult d_result;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated solver instance. */
  Cvc5* d_cvc5 = nullptr;
};

/** Wrapper for cvc5 C++ proofs. */
struct cvc5_proof_t
{
  /**
   * Constructor.
   * @param cvc5   The associated solver instance.
   * @param proof The wrapped C++ proof.
   */
  cvc5_proof_t(Cvc5* cvc5, const cvc5::Proof& proof)
      : d_proof(proof), d_cvc5(cvc5)
  {
  }
  /** The wrapped C++ proof. */
  cvc5::Proof d_proof;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated solver instance. */
  Cvc5* d_cvc5 = nullptr;
};

/** Wrapper for cvc5 C++ grammars. */
struct cvc5_grammar_t
{
  /**
   * Constructor.
   * @param cvc5   The associated solver instance.
   * @param grammar The wrapped C++ grammar.
   */
  cvc5_grammar_t(Cvc5* cvc5, const cvc5::Grammar& grammar)
      : d_grammar(grammar), d_cvc5(cvc5)
  {
  }
  /** The wrapped C++ grammar. */
  cvc5::Grammar d_grammar;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated solver instance. */
  Cvc5* d_cvc5 = nullptr;
};

/** Wrapper for cvc5 C++ solver instance. */
struct Cvc5
{
  /**
   * Constructor.
   * @param tm The associated term manager instance.
   */
  Cvc5(Cvc5TermManager* tm) : d_solver(tm->d_tm), d_tm(tm) {}

  /** Destructor. */
  ~Cvc5();

  /**
   * Export C++ result to C API.
   * @param result The result to export.
   */
  Cvc5Result export_result(const cvc5::Result& result);
  /**
   * Decrement the external ref count of a result. If the ref count reaches
   * zero, the result is released (freed).
   * @param result The result to release.
   */
  void release(cvc5_result_t* result);
  /**
   * Increment the external ref count of a result.
   * @param result The result to copy.
   * @return The copied result.
   */
  cvc5_result_t* copy(cvc5_result_t* result);

  /**
   * Export C++ synthesis result to C API.
   * @param result Thesynthesis  result to export.
   */
  Cvc5SynthResult export_synth_result(const cvc5::SynthResult& result);
  /**
   * Decrement the external ref count of a synthesis result. If the ref count
   * reaches zero, the result is released (freed).
   * @param result The result to release.
   */
  void release(cvc5_synth_result_t* result);
  /**
   * Increment the external ref count of a synthesis result.
   * @param result The synthesis result to copy.
   * @return The copied synthesis result.
   */
  cvc5_synth_result_t* copy(cvc5_synth_result_t* result);

  /**
   * Export C++ proof to C API.
   * @param proof The proof to export.
   */
  Cvc5Proof export_proof(const cvc5::Proof& proof);
  /**
   * Decrement the external ref count of a proof. If the ref count reaches
   * zero, the proof is released (freed).
   * @param proof The proof to release.
   */
  void release(cvc5_proof_t* proof);
  /**
   * Increment the external ref count of a proof.
   * @param proof The proof to copy.
   * @return The copied proof.
   */
  cvc5_proof_t* copy(cvc5_proof_t* proof);

  /**
   * Export C++ grammar to C API.
   * @param grammar The grammar to export.
   */
  Cvc5Grammar export_grammar(const cvc5::Grammar& grammar);
  /**
   * Decrement the external ref count of a grammar. If the ref count reaches
   * zero, the grammar is released (freed).
   * @param grammar The grammar to release.
   */
  void release(cvc5_grammar_t* grammar);
  /**
   * Increment the external ref count of a grammar.
   * @param grammar The grammar to copy.
   * @return The copied grammar.
   */
  cvc5_grammar_t* copy(cvc5_grammar_t* grammar);

  /** The associated cvc5 instance. */
  cvc5::Solver d_solver;
  /** The associated term manager. */
  Cvc5TermManager* d_tm = nullptr;

  /** Cache of allocated results. */
  std::unordered_map<cvc5::Result, cvc5_result_t> d_alloc_results;
  /** Cache of allocated syntheis results. */
  std::unordered_map<cvc5::SynthResult, cvc5_synth_result_t>
      d_alloc_synth_results;
  /** Cache of allocated proofs. */
  std::unordered_map<cvc5::Proof, cvc5_proof_t> d_alloc_proofs;
  /** Cache of allocated grammars. */
  std::unordered_map<cvc5::Grammar, cvc5_grammar_t> d_alloc_grammars;
  /** Out file stream for output tag (configured via `cvc5_get_output()`. */
  std::ofstream d_output_tag_file_stream;
  /**
   * Out file stream for output tag returned by `Solver::getOutput()`. Cached
   * to reset on `cvc5_output_close()` or on destruction of `Cvc5` to
   * `d_output_tag_streambuf`.
   */
  std::ostream* d_output_tag_stream = nullptr;
  /**
   * Cache output stream buffer of the stream returned by `Solver::getOutput()`
   * before it was redirected to the file configured via `cvc5_get_output()`.
   * Cached to reset on `cvc5_output_close()` or on destruction of `Cvc5`.
   */
  std::streambuf* d_output_tag_streambuf = nullptr;

  /** The configured plugin. */
  class PluginCpp : public cvc5::Plugin
  {
   public:
    PluginCpp(cvc5::TermManager& tm, Cvc5* cvc5, Cvc5Plugin* plugin)
        : Plugin(tm), d_cvc5(cvc5), d_plugin(plugin)
    {
    }
    std::vector<cvc5::Term> check() override;
    void notifySatClause(const cvc5::Term& clause) override;
    void notifyTheoryLemma(const cvc5::Term& lemma) override;
    std::string getName() override;

   private:
    Cvc5* d_cvc5;
    Cvc5Plugin* d_plugin;
  };
  std::unique_ptr<PluginCpp> d_plugin = nullptr;
};

/** Wrapper for cvc5 C++ statistic. */
struct cvc5_stat_t
{
  /**
   * Constructor.
   * @param tm     The associated term manager instance.
   * @param result The wrapped C++ statistic.
   */
  cvc5_stat_t(Cvc5TermManager* tm, const cvc5::Stat& stat)
      : d_stat(stat), d_tm(tm)
  {
  }
  /**
   * Constructor.
   * @param cvc5   The associated solver instance.
   * @param result The wrapped C++ statistic.
   */
  cvc5_stat_t(Cvc5* cvc5, const cvc5::Stat& stat)
      : d_stat(stat), d_tm(cvc5->d_tm)
  {
  }
  /** The wrapped C++ statistic. */
  cvc5::Stat d_stat;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated term manager instance. */
  Cvc5TermManager* d_tm = nullptr;
};

/** Wrapper for cvc5 C++ statistics. */
struct cvc5_stats_t
{
  /**
   * Constructor.
   * @param tm     The associated term manager instance.
   * @param result The wrapped C++ statistics.
   */
  cvc5_stats_t(Cvc5TermManager* tm, const cvc5::Statistics& stat)
      : d_stat(stat), d_tm(tm)
  {
  }
  /**
   * Constructor.
   * @param cvc5   The associated solver instance.
   * @param result The wrapped C++ statistics.
   */
  cvc5_stats_t(Cvc5* cvc5, const cvc5::Statistics& stat)
      : d_stat(stat), d_tm(cvc5->d_tm)
  {
  }
  /** The wrapped C++ statistics. */
  cvc5::Statistics d_stat;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated term manager instance. */
  Cvc5TermManager* d_tm = nullptr;
  /** The associated iterator. */
  std::unique_ptr<cvc5::Statistics::iterator> d_iter = nullptr;
};

/* -------------------------------------------------------------------------- */
#endif

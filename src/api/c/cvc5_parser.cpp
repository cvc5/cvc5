/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 C Parser API.
 */

extern "C" {
#include <cvc5/c/cvc5_parser.h>
}

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include <fstream>
#include <memory>

#include "api/c/cvc5_c_structs.h"
#include "api/c/cvc5_checks.h"

/* -------------------------------------------------------------------------- */

/** Wrapper for cvc5 C++ command. */
struct cvc5_cmd_t
{
  /**
   * Constructor.
   * @param parser The associated parser instance.
   * @param cmd    The wrapped C++ command.
   */
  cvc5_cmd_t(Cvc5InputParser* parser, const cvc5::parser::Command& cmd)
      : d_cmd(cmd), d_parser(parser)
  {
  }
  /** The associated command instance. */
  cvc5::parser::Command d_cmd;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated parser instance. */
  Cvc5InputParser* d_parser = nullptr;
};

/** Wrapper for cvc5 C++ symbol manager. */
struct Cvc5SymbolManager
{
  /**
   * Constructor.
   * @param tm The associated term manager.
   */
  Cvc5SymbolManager(Cvc5TermManager* tm)
      : d_sm_wrapped(new cvc5::parser::SymbolManager(tm->d_tm)),
        d_sm(*d_sm_wrapped),
        d_tm(tm)
  {
    // The symbol manager keeps the term manager alive (e.g., to export
    // declared terms and sorts).
    d_tm->inc_ref();
  }
  /**
   * Constructor.
   * @param sm The wrapped symbol manager instance.
   * @param tm The associated term manager.
   */
  Cvc5SymbolManager(cvc5::parser::SymbolManager& sm, Cvc5TermManager* tm)
      : d_sm(sm), d_tm(tm)
  {
    d_tm->inc_ref();
  }
  /** Destructor. */
  ~Cvc5SymbolManager() { d_tm->dec_ref(); }
  /**
   * The created symbol manager instance.
   *
   * This will be a newly created symbol manager when created via
   * cvc5_symbol_manager_new(). However, if we create a parsere via
   * cvc5_parser_new() while passing NULL as a symbol manager, this will be
   * NULL and `d_sm` will point to the symbol manager created by the parser.
   */
  std::unique_ptr<cvc5::parser::SymbolManager> d_sm_wrapped;
  /** The associated symbol manager instance. */
  cvc5::parser::SymbolManager& d_sm;
  /** The associated term manager. */
  Cvc5TermManager* d_tm = nullptr;
};

/** Wrapper for cvc5 C++ parser. */
struct Cvc5InputParser
{
  /**
   * Constructor.
   * @param cvc5 The associated solver instance.
   */
  Cvc5InputParser(Cvc5* cvc5) : d_parser(&cvc5->d_solver), d_cvc5(cvc5)
  {
    d_sm_wrapped.reset(new Cvc5SymbolManager(*d_parser.getSymbolManager(),
                                             cvc5_get_tm(d_cvc5)));
    d_sm = d_sm_wrapped.get();
  }
  /**
   * Constructor.
   * @param cvc5 The associated solver instance.
   * @param sm   The associated symbol manager.
   */
  Cvc5InputParser(Cvc5* cvc5, Cvc5SymbolManager* sm)
      : d_parser(&cvc5->d_solver, &sm->d_sm), d_cvc5(cvc5), d_sm(sm)
  {
  }

  /**
   * Export C++ command to C API.
   * @param cmd The command to export.
   */
  Cvc5Command export_cmd(const cvc5::parser::Command& cmd);

  /**
   * Decrement the external ref count of a command. If the ref count reaches
   * zero, the command is released (freed).
   * @param cmd The command to release.
   */
  void release(cvc5_cmd_t* cmd);
  /**
   * Increment the external ref count of a command.
   * @param cmd The command to copy.
   * @return The copied command.
   */
  cvc5_cmd_t* copy(cvc5_cmd_t* cmd);
  /** Release all managed command objects. */
  void release();

  /**
   * Increment the number of external handles to this parser.
   *
   * A handle is held by the user (returned by `cvc5_parser_new()` and dropped
   * via `cvc5_parser_delete()`) and by each command allocated by this parser.
   */
  void inc_ref();
  /**
   * Decrement the number of external handles to this parser.
   *
   * The parser is freed once it has no external handles and no managed
   * command objects left. Commands thus keep their parser alive until they
   * are released, and remain valid after `cvc5_parser_delete()`.
   */
  void dec_ref();

  /** The associated input parser instance. */
  cvc5::parser::InputParser d_parser;
  /** The associated solver instance. */
  Cvc5* d_cvc5 = nullptr;
  /** The associated symbol manager instance. */
  Cvc5SymbolManager* d_sm = nullptr;
  /**
   * Maintain Cvc5SymbolManager wrapper instance if symbol manager was not
   * given via constructor but created by the parser.
   */
  std::unique_ptr<Cvc5SymbolManager> d_sm_wrapped;

 private:
  /** Free this parser if it has no external handles and no commands. */
  void free_if_unused();

  /** The number of external handles to this parser. */
  uint32_t d_refs = 1;
  /**
   * The allocated command objects.
   * @note Commands are never exported more than once, we thus key this cache
   *       on the allocated wrapper object.
   */
  std::unordered_map<cvc5_cmd_t*, std::unique_ptr<cvc5_cmd_t>> d_alloc_cmds;
};

/* -------------------------------------------------------------------------- */

Cvc5Command Cvc5InputParser::export_cmd(const cvc5::parser::Command& cmd)
{
  Assert(!cmd.isNull());
  auto c = std::make_unique<cvc5_cmd_t>(this, cmd);
  cvc5_cmd_t* res = c.get();
  d_alloc_cmds.emplace(res, std::move(c));
  // the command keeps this parser alive
  inc_ref();
  return res;
}

void Cvc5InputParser::release(cvc5_cmd_t* cmd)
{
  if (cmd)
  {
    cmd->d_refs -= 1;
    if (cmd->d_refs == 0)
    {
      Assert(d_alloc_cmds.find(cmd) != d_alloc_cmds.end());
      d_alloc_cmds.erase(cmd);
      dec_ref();
    }
  }
}

cvc5_cmd_t* Cvc5InputParser::copy(cvc5_cmd_t* cmd)
{
  if (cmd)
  {
    cmd->d_refs += 1;
  }
  return cmd;
}

void Cvc5InputParser::release()
{
  size_t ncmds = d_alloc_cmds.size();
  d_alloc_cmds.clear();
  // drop the handles held by the released commands
  Assert(d_refs >= ncmds);
  d_refs -= ncmds;
  free_if_unused();
}

void Cvc5InputParser::inc_ref() { d_refs += 1; }

void Cvc5InputParser::dec_ref()
{
  Assert(d_refs > 0);
  d_refs -= 1;
  free_if_unused();
}

void Cvc5InputParser::free_if_unused()
{
  if (d_refs == 0)
  {
    Assert(d_alloc_cmds.empty());
    delete this;
  }
}

/* -------------------------------------------------------------------------- */

Cvc5SymbolManager* cvc5_symbol_manager_new(Cvc5TermManager* tm)
{
  Cvc5SymbolManager* res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(tm);
  res = new Cvc5SymbolManager(tm);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_symbol_manager_delete(Cvc5SymbolManager* sm)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(sm);
  delete sm;
  CVC5_CAPI_TRY_CATCH_END;
}

bool cvc5_sm_is_logic_set(Cvc5SymbolManager* sm)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(sm);
  res = sm->d_sm.isLogicSet();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

const char* cvc5_sm_get_logic(Cvc5SymbolManager* sm)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(sm);
  str = sm->d_sm.getLogic();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

const Cvc5Sort* cvc5_sm_get_declared_sorts(Cvc5SymbolManager* sm, size_t* size)
{
  static thread_local std::vector<Cvc5Sort> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(sm);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto sorts = sm->d_sm.getDeclaredSorts();
  auto tm = sm->d_tm;
  for (auto& s : sorts)
  {
    res.push_back(tm->export_sort(s));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  // On error, `size` may be invalid (e.g. NULL) and `res` may hold stale data,
  // so we must not dereference `size` here; gate on the error state instead.
  return cvc5::cvc5_capi_has_error() || res.empty() ? nullptr : res.data();
}

const Cvc5Term* cvc5_sm_get_declared_terms(Cvc5SymbolManager* sm, size_t* size)
{
  static thread_local std::vector<Cvc5Term> res;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(sm);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  res.clear();
  auto terms = sm->d_sm.getDeclaredTerms();
  auto tm = sm->d_tm;
  for (auto& t : terms)
  {
    res.push_back(tm->export_term(t));
  }
  *size = res.size();
  CVC5_CAPI_TRY_CATCH_END;
  // On error, `size` may be invalid (e.g. NULL) and `res` may hold stale data,
  // so we must not dereference `size` here; gate on the error state instead.
  return cvc5::cvc5_capi_has_error() || res.empty() ? nullptr : res.data();
}

void cvc5_sm_get_named_terms(Cvc5SymbolManager* sm,
                             size_t* size,
                             Cvc5Term* terms[],
                             const char** names[])
{
  static thread_local std::vector<Cvc5Term> rterms;
  static thread_local std::vector<const char*> rnames;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(sm);
  CVC5_CAPI_CHECK_NOT_NULL(size);
  CVC5_CAPI_CHECK_NOT_NULL(terms);
  CVC5_CAPI_CHECK_NOT_NULL(names);
  rterms.clear();
  rnames.clear();
  auto res = sm->d_sm.getNamedTerms();
  auto tm = sm->d_tm;
  for (auto& t : res)
  {
    rterms.push_back(tm->export_term(t.first));
    rnames.push_back(t.second.c_str());
  }
  *size = rterms.size();
  *terms = rterms.data();
  *names = rnames.data();
  CVC5_CAPI_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */

const char* cvc5_cmd_invoke(Cvc5Command cmd, Cvc5* cvc5, Cvc5SymbolManager* sm)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_CMD(cmd);
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  CVC5_CAPI_CHECK_NOT_NULL(sm);
  std::stringstream ss;
  cmd->d_cmd.invoke(&cvc5->d_solver, &sm->d_sm, ss);
  str = ss.str();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

Cvc5Command cvc5_cmd_copy(Cvc5Command cmd)
{
  Cvc5Command res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_CMD(cmd);
  res = cmd->d_parser->copy(cmd);
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_cmd_release(Cvc5Command cmd)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_CMD(cmd);
  cmd->d_parser->release(cmd);
  CVC5_CAPI_TRY_CATCH_END;
}

const char* cvc5_cmd_to_string(const Cvc5Command cmd)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_CMD(cmd);
  str = cmd->d_cmd.toString();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

const char* cvc5_cmd_get_name(const Cvc5Command cmd)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_CMD(cmd);
  str = cmd->d_cmd.getCommandName();
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */

Cvc5InputParser* cvc5_parser_new(Cvc5* cvc5, Cvc5SymbolManager* sm)
{
  Cvc5InputParser* res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(cvc5);
  if (sm)
  {
    res = new Cvc5InputParser(cvc5, sm);
  }
  else
  {
    res = new Cvc5InputParser(cvc5);
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_parser_delete(Cvc5InputParser* parser)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(parser);
  // Commands allocated by this parser keep it alive, it is only freed once
  // all of them have been released.
  parser->dec_ref();
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_parser_release(Cvc5InputParser* parser)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(parser);
  parser->release();
  CVC5_CAPI_TRY_CATCH_END;
}

Cvc5* cvc5_parser_get_solver(Cvc5InputParser* parser)
{
  Cvc5* res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  res = parser->d_cvc5;
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5SymbolManager* cvc5_parser_get_sm(Cvc5InputParser* parser)
{
  Cvc5SymbolManager* res = nullptr;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  res = parser->d_sm;
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

void cvc5_parser_set_file_input(Cvc5InputParser* parser,
                                Cvc5InputLanguage lang,
                                const char* filename)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(parser);
  CVC5_CAPI_CHECK_INPUT_LANGUAGE(lang);
  CVC5_CAPI_CHECK_NOT_NULL(filename);
  parser->d_parser.setFileInput(static_cast<cvc5::modes::InputLanguage>(lang),
                                filename);
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_parser_set_str_input(Cvc5InputParser* parser,
                               Cvc5InputLanguage lang,
                               const char* input,
                               const char* name)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(parser);
  CVC5_CAPI_CHECK_INPUT_LANGUAGE(lang);
  CVC5_CAPI_CHECK_NOT_NULL(input);
  CVC5_CAPI_CHECK_NOT_NULL(name);
  parser->d_parser.setStringInput(
      static_cast<cvc5::modes::InputLanguage>(lang), input, name);
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_parser_set_inc_str_input(Cvc5InputParser* parser,
                                   Cvc5InputLanguage lang,
                                   const char* name)
{
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(parser);
  CVC5_CAPI_CHECK_INPUT_LANGUAGE(lang);
  CVC5_CAPI_CHECK_NOT_NULL(name);
  parser->d_parser.setIncrementalStringInput(
      static_cast<cvc5::modes::InputLanguage>(lang), name);
  CVC5_CAPI_TRY_CATCH_END;
}

void cvc5_parser_append_inc_str_input(Cvc5InputParser* parser,
                                      const char* input)
{
  static thread_local std::string error;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(parser);
  CVC5_CAPI_CHECK_NOT_NULL(input);
  parser->d_parser.appendIncrementalStringInput(input);
  CVC5_CAPI_TRY_CATCH_END;
}

Cvc5Command cvc5_parser_next_command(Cvc5InputParser* parser,
                                     const char** error_msg)
{
  Cvc5Command res = nullptr;
  static thread_local std::string error;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(parser);
  CVC5_CAPI_CHECK_NOT_NULL(error_msg);
  try
  {
    cvc5::parser::Command cres = parser->d_parser.nextCommand();
    res = cres.isNull() ? nullptr : parser->export_cmd(cres);
    error = "";
    *error_msg = nullptr;
  }
  catch (cvc5::parser::ParserException& e)
  {
    error = e.getMessage();
    *error_msg = error.c_str();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

Cvc5Term cvc5_parser_next_term(Cvc5InputParser* parser, const char** error_msg)
{
  Cvc5Term res = nullptr;
  static thread_local std::string error;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(parser);
  CVC5_CAPI_CHECK_NOT_NULL(error_msg);
  try
  {
    cvc5::Term cres = parser->d_parser.nextTerm();
    res = cres.isNull() ? nullptr : parser->d_cvc5->d_tm->export_term(cres);
    error = "";
    *error_msg = nullptr;
  }
  catch (cvc5::parser::ParserException& e)
  {
    error = e.getMessage();
    *error_msg = error.c_str();
  }
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

bool cvc5_parser_done(Cvc5InputParser* parser)
{
  bool res = false;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_NOT_NULL(parser);
  res = parser->d_parser.done();
  CVC5_CAPI_TRY_CATCH_END;
  return res;
}

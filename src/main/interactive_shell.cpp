/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Christopher L. Conway, Andrew V. Jones
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Interactive shell for cvc5.
 *
 * This file is the implementation for the cvc5 interactive shell.
 * The shell supports the editline library.
 */
#include "main/interactive_shell.h"

#include <cstring>
#include <unistd.h>

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <set>
#include <string>
#include <utility>
#include <vector>

// This must go before HAVE_LIBEDITLINE.
#include "base/cvc5config.h"

#if HAVE_LIBEDITLINE
#include <editline/readline.h>
#  if HAVE_EXT_STDIO_FILEBUF_H
#    include <ext/stdio_filebuf.h>
#  endif /* HAVE_EXT_STDIO_FILEBUF_H */
#endif   /* HAVE_LIBEDITLINE */

#include "api/cpp/cvc5.h"
#include "base/check.h"
#include "base/output.h"
#include "expr/symbol_manager.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "smt/command.h"
#include "theory/logic_info.h"

using namespace std;

namespace cvc5 {

using namespace parser;
using namespace language;

const string InteractiveShell::INPUT_FILENAME = "<shell>";

#if HAVE_LIBEDITLINE

#if HAVE_EXT_STDIO_FILEBUF_H
using __gnu_cxx::stdio_filebuf;
#endif /* HAVE_EXT_STDIO_FILEBUF_H */

char** commandCompletion(const char* text, int start, int end);
char* commandGenerator(const char* text, int state);

static const std::string smt2_commands[] = {
#include "main/smt2_tokens.h"
};/* smt2_commands */

static const std::string tptp_commands[] = {
#include "main/tptp_tokens.h"
};/* tptp_commands */

static const std::string* commandsBegin;
static const std::string* commandsEnd;

static set<string> s_declarations;

#endif /* HAVE_LIBEDITLINE */

InteractiveShell::InteractiveShell(api::Solver* solver,
                                   SymbolManager* sm,
                                   std::istream& in,
                                   std::ostream& out)
    : d_solver(solver), d_in(in), d_out(out), d_quit(false)
{
  ParserBuilder parserBuilder(solver, sm, true);
  /* Create parser with bogus input. */
  d_parser.reset(parserBuilder.build());
  if (d_solver->getOptionInfo("force-logic").setByUser)
  {
    LogicInfo tmp(d_solver->getOption("force-logic"));
    d_parser->forceLogic(tmp.getLogicString());
  }

#if HAVE_LIBEDITLINE
  if (&d_in == &std::cin && isatty(fileno(stdin)))
  {
    ::rl_readline_name = const_cast<char*>("cvc5");
#if EDITLINE_COMPENTRY_FUNC_RETURNS_CHARP
    ::rl_completion_entry_function = commandGenerator;
#else /* EDITLINE_COMPENTRY_FUNC_RETURNS_CHARP */
    ::rl_completion_entry_function = (int (*)(const char*, int)) commandGenerator;
#endif /* EDITLINE_COMPENTRY_FUNC_RETURNS_CHARP */
    ::using_history();

    std::string lang = solver->getOption("input-language");
    if (lang == "LANG_TPTP")
    {
      d_historyFilename = string(getenv("HOME")) + "/.cvc5_history_tptp";
      commandsBegin = tptp_commands;
      commandsEnd =
          tptp_commands + sizeof(tptp_commands) / sizeof(*tptp_commands);
    }
    else if (lang == "LANG_SMTLIB_V2_6")
    {
      d_historyFilename = string(getenv("HOME")) + "/.cvc5_history_smtlib2";
      commandsBegin = smt2_commands;
      commandsEnd =
          smt2_commands + sizeof(smt2_commands) / sizeof(*smt2_commands);
    }
    else
    {
      throw Exception("internal error: unhandled language " + lang);
    }
    d_usingEditline = true;
    int err = ::read_history(d_historyFilename.c_str());
    ::stifle_history(s_historyLimit);
    if (d_solver->getOptionInfo("verbosity").intValue() >= 1)
    {
      if(err == 0) {
        d_solver->getDriverOptions().err()
            << "Read " << ::history_length << " lines of history from "
            << d_historyFilename << std::endl;
      } else {
        d_solver->getDriverOptions().err()
            << "Could not read history from " << d_historyFilename << ": "
            << strerror(err) << std::endl;
      }
    }
  }
  else
  {
    d_usingEditline = false;
  }
#else  /* HAVE_LIBEDITLINE */
  d_usingEditline = false;
#endif /* HAVE_LIBEDITLINE */
}/* InteractiveShell::InteractiveShell() */

InteractiveShell::~InteractiveShell() {
#if HAVE_LIBEDITLINE
  int err = ::write_history(d_historyFilename.c_str());
  if (d_solver->getOptionInfo("verbosity").intValue() >= 1)
  {
    if (err == 0)
    {
      d_solver->getDriverOptions().err()
          << "Wrote " << ::history_length << " lines of history to "
          << d_historyFilename << std::endl;
    } else {
      d_solver->getDriverOptions().err()
          << "Could not write history to " << d_historyFilename << ": "
          << strerror(err) << std::endl;
  }
  }
#endif /* HAVE_LIBEDITLINE */
}

Command* InteractiveShell::readCommand()
{
  char* lineBuf = NULL;
  string line = "";

restart:

  /* Don't do anything if the input is closed or if we've seen a
   * QuitCommand. */
  if(d_in.eof() || d_quit) {
    d_out << endl;
    return NULL;
  }

  /* If something's wrong with the input, there's nothing we can do. */
  if( !d_in.good() ) {
    throw ParserException("Interactive input broken.");
  }

  /* Prompt the user for input. */
  if (d_usingEditline)
  {
#if HAVE_LIBEDITLINE
    lineBuf = ::readline(line == "" ? "cvc5> " : "... > ");
    if(lineBuf != NULL && lineBuf[0] != '\0') {
      ::add_history(lineBuf);
    }
    line += lineBuf == NULL ? "" : lineBuf;
    free(lineBuf);
#endif /* HAVE_LIBEDITLINE */
  }
  else
  {
    if (line == "")
    {
      d_out << "cvc5> " << flush;
    }
    else
    {
      d_out << "... > " << flush;
    }

    /* Read a line */
    stringbuf sb;
    d_in.get(sb);
    line += sb.str();
  }

  string input = "";
  while(true) {
    Debug("interactive") << "Input now '" << input << line << "'" << endl
                         << flush;

    Assert(!(d_in.fail() && !d_in.eof()) || line.empty());

    /* Check for failure. */
    if(d_in.fail() && !d_in.eof()) {
      /* This should only happen if the input line was empty. */
      Assert(line.empty());
      d_in.clear();
    }

    /* Strip trailing whitespace. */
    int n = line.length() - 1;
    while( !line.empty() && isspace(line[n]) ) {
      line.erase(n,1);
      n--;
    }

    /* If we hit EOF, we're done. */
    if ((!d_usingEditline && d_in.eof())
        || (d_usingEditline && lineBuf == NULL))
    {
      input += line;

      if(input.empty()) {
        /* Nothing left to parse. */
        d_out << endl;
        return NULL;
      }

      /* Some input left to parse, but nothing left to read.
         Jump out of input loop. */
      d_out << endl;
      input = line = "";
      d_in.clear();
      goto restart;
    }

    if (!d_usingEditline)
    {
      /* Extract the newline delimiter from the stream too */
      int c CVC5_UNUSED = d_in.get();
      Assert(c == '\n');
      Debug("interactive") << "Next char is '" << (char)c << "'" << endl
                           << flush;
    }

    input += line;

    /* If the last char was a backslash, continue on the next line. */
    n = input.length() - 1;
    if( !line.empty() && input[n] == '\\' ) {
      input[n] = '\n';
      if (d_usingEditline)
      {
#if HAVE_LIBEDITLINE
        lineBuf = ::readline("... > ");
        if(lineBuf != NULL && lineBuf[0] != '\0') {
          ::add_history(lineBuf);
        }
        line = lineBuf == NULL ? "" : lineBuf;
        free(lineBuf);
#endif /* HAVE_LIBEDITLINE */
      }
      else
      {
        d_out << "... > " << flush;

        /* Read a line */
        stringbuf sb;
        d_in.get(sb);
        line = sb.str();
      }
    } else {
      /* No continuation, we're done. */
      Debug("interactive") << "Leaving input loop." << endl << flush;
      break;
    }
  }

  d_parser->setInput(Input::newStringInput(
      d_solver->getOption("input-language"), input, INPUT_FILENAME));

  /* There may be more than one command in the input. Build up a
     sequence. */
  CommandSequence *cmd_seq = new CommandSequence();
  Command *cmd;

  try
  {
    while ((cmd = d_parser->nextCommand()))
    {
      cmd_seq->addCommand(cmd);
      if (dynamic_cast<QuitCommand*>(cmd) != NULL)
      {
        d_quit = true;
        break;
      }
      else
      {
#if HAVE_LIBEDITLINE
        if (dynamic_cast<DeclareFunctionCommand*>(cmd) != NULL)
        {
          s_declarations.insert(
              dynamic_cast<DeclareFunctionCommand*>(cmd)->getSymbol());
        }
        else if (dynamic_cast<DefineFunctionCommand*>(cmd) != NULL)
        {
          s_declarations.insert(
              dynamic_cast<DefineFunctionCommand*>(cmd)->getSymbol());
        }
        else if (dynamic_cast<DeclareSortCommand*>(cmd) != NULL)
        {
          s_declarations.insert(
              dynamic_cast<DeclareSortCommand*>(cmd)->getSymbol());
        }
        else if (dynamic_cast<DefineSortCommand*>(cmd) != NULL)
        {
          s_declarations.insert(
              dynamic_cast<DefineSortCommand*>(cmd)->getSymbol());
        }
#endif /* HAVE_LIBEDITLINE */
      }
    }
  }
  catch (ParserEndOfFileException& pe)
  {
    line += "\n";
    goto restart;
  }
  catch (ParserException& pe)
  {
    if (d_solver->getOption("output-language") == "LANG_SMTLIB_V2_6")
    {
      d_out << "(error \"" << pe << "\")" << endl;
    }
    else
    {
      d_out << pe << endl;
    }
    // We can't really clear out the sequence and abort the current line,
    // because the parse error might be for the second command on the
    // line.  The first ones haven't yet been executed by the SolverEngine,
    // but the parser state has already made the variables and the mappings
    // in the symbol table.  So unfortunately, either we exit cvc5 entirely,
    // or we commit to the current line up to the command with the parse
    // error.
    //
    // FIXME: does that mean e.g. that a pushed LET scope might not yet have
    // been popped?!
    //
    // delete cmd_seq;
    // cmd_seq = new CommandSequence();
  }

  return cmd_seq;
}/* InteractiveShell::readCommand() */

#if HAVE_LIBEDITLINE

char** commandCompletion(const char* text, int start, int end) {
  Debug("rl") << "text: " << text << endl;
  Debug("rl") << "start: " << start << " end: " << end << endl;
  return rl_completion_matches(text, commandGenerator);
}

// Our peculiar versions of "less than" for strings
struct StringPrefix1Less {
  bool operator()(const std::string& s1, const std::string& s2) {
    size_t l1 = s1.length(), l2 = s2.length();
    size_t l = l1 <= l2 ? l1 : l2;
    return s1.compare(0, l1, s2, 0, l) < 0;
  }
};/* struct StringPrefix1Less */
struct StringPrefix2Less {
  bool operator()(const std::string& s1, const std::string& s2) {
    size_t l1 = s1.length(), l2 = s2.length();
    size_t l = l1 <= l2 ? l1 : l2;
    return s1.compare(0, l, s2, 0, l2) < 0;
  }
};/* struct StringPrefix2Less */

char* commandGenerator(const char* text, int state) {
  static thread_local const std::string* rlCommand;
  static thread_local set<string>::const_iterator* rlDeclaration;

  const std::string* i = lower_bound(commandsBegin, commandsEnd, text, StringPrefix2Less());
  const std::string* j = upper_bound(commandsBegin, commandsEnd, text, StringPrefix1Less());

  set<string>::const_iterator ii = lower_bound(s_declarations.begin(), s_declarations.end(), text, StringPrefix2Less());
  set<string>::const_iterator jj = upper_bound(s_declarations.begin(), s_declarations.end(), text, StringPrefix1Less());

  if(rlDeclaration == NULL) {
    rlDeclaration = new set<string>::const_iterator();
  }

  if(state == 0) {
    rlCommand = i;
    *rlDeclaration = ii;
  }

  if(rlCommand != j) {
    return strdup((*rlCommand++).c_str());
  }

  return *rlDeclaration == jj ? NULL : strdup((*(*rlDeclaration)++).c_str());
}

#endif /* HAVE_LIBEDITLINE */

}  // namespace cvc5

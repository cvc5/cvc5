/*********************                                                        */
/*! \file interactive_shell.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Interactive shell for CVC4
 **
 ** This file is the implementation for the CVC4 interactive shell.
 ** The shell supports the readline library.
 **/

#include <iostream>
#include <cstdlib>
#include <vector>
#include <string>
#include <set>
#include <algorithm>
#include <utility>

#include "cvc4autoconfig.h"

#include "main/interactive_shell.h"

#include "expr/command.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "util/options.h"
#include "util/language.h"

#include <string.h>

#if HAVE_LIBREADLINE
#  include <readline/readline.h>
#  include <readline/history.h>
#  include <ext/stdio_filebuf.h>
#endif /* HAVE_LIBREADLINE */

using namespace std;

namespace CVC4 {

using namespace parser;
using namespace language;

const string InteractiveShell::INPUT_FILENAME = "<shell>";

#if HAVE_LIBREADLINE

using __gnu_cxx::stdio_filebuf;

//char** commandCompletion(const char* text, int start, int end);
char* commandGenerator(const char* text, int state);

static const char* const cvc_commands[] = {
#include "main/cvc_tokens.h"
};/* cvc_commands */

static const char* const smt_commands[] = {
#include "main/smt_tokens.h"
};/* smt_commands */

static const char* const smt2_commands[] = {
#include "main/smt2_tokens.h"
};/* smt2_commands */

static const char* const* commandsBegin;
static const char* const* commandsEnd;

static set<string> s_declarations;

#endif /* HAVE_LIBREADLINE */

InteractiveShell::InteractiveShell(ExprManager& exprManager,
                                   const Options& options) :
  d_in(*options.in),
  d_out(*options.out),
  d_options(options),
  d_quit(false) {
  ParserBuilder parserBuilder(&exprManager, INPUT_FILENAME, options);
  /* Create parser with bogus input. */
  d_parser = parserBuilder.withStringInput("").build();

#if HAVE_LIBREADLINE
  if(d_in == cin) {
    ::rl_readline_name = "CVC4";
    ::rl_completion_entry_function = commandGenerator;
    ::using_history();

    switch(OutputLanguage lang = toOutputLanguage(d_options.inputLanguage)) {
    case output::LANG_CVC4:
      d_historyFilename = string(getenv("HOME")) + "/.cvc4_history";
      commandsBegin = cvc_commands;
      commandsEnd = cvc_commands + sizeof(cvc_commands) / sizeof(*cvc_commands);
      break;
    case output::LANG_SMTLIB:
      d_historyFilename = string(getenv("HOME")) + "/.cvc4_history_smtlib";
      commandsBegin = smt_commands;
      commandsEnd = smt_commands + sizeof(smt_commands) / sizeof(*smt_commands);
      break;
    case output::LANG_SMTLIB_V2:
      d_historyFilename = string(getenv("HOME")) + "/.cvc4_history_smtlib2";
      commandsBegin = smt2_commands;
      commandsEnd = smt2_commands + sizeof(smt2_commands) / sizeof(*smt2_commands);
      break;
    default: Unhandled(lang);
    }
    d_usingReadline = true;
    int err = ::read_history(d_historyFilename.c_str());
    ::stifle_history(s_historyLimit);
    if(Notice.isOn()) {
      if(err == 0) {
        Notice() << "Read " << ::history_length << " lines of history from "
                 << d_historyFilename << std::endl;
      } else {
        Notice() << "Could not read history from " << d_historyFilename
                 << ": " << strerror(err) << std::endl;
      }
    }
  } else {
    d_usingReadline = false;
  }
#else /* HAVE_LIBREADLINE */
  d_usingReadline = false;
#endif /* HAVE_LIBREADLINE */
}/* InteractiveShell::InteractiveShell() */

InteractiveShell::~InteractiveShell() {
#if HAVE_LIBREADLINE
  int err = ::write_history(d_historyFilename.c_str());
  if(err == 0) {
    Notice() << "Wrote " << ::history_length << " lines of history to "
             << d_historyFilename << std::endl;
  } else {
    Notice() << "Could not write history to " << d_historyFilename
             << ": " << strerror(err) << std::endl;
  }
#endif /* HAVE_LIBREADLINE */
}

Command* InteractiveShell::readCommand() {
  /* Don't do anything if the input is closed or if we've seen a
   * QuitCommand. */
  if( d_in.eof() || d_quit ) {
    return NULL;
  }

  /* If something's wrong with the input, there's nothing we can do. */
  if( !d_in.good() ) {
    throw ParserException("Interactive input broken.");
  }

  char* lineBuf = NULL;
  string input;
  stringbuf sb;
  string line;

  /* Prompt the user for input. */
  if(d_usingReadline) {
#if HAVE_LIBREADLINE
    lineBuf = ::readline(d_options.verbosity >= 0 ? "CVC4> " : "");
    if(lineBuf != NULL && lineBuf[0] != '\0') {
      ::add_history(lineBuf);
    }
    line = lineBuf == NULL ? "" : lineBuf;
    free(lineBuf);
#endif /* HAVE_LIBREADLINE */
  } else {
    if(d_options.verbosity >= 0) {
      d_out << "CVC4> " << flush;
    }

    /* Read a line */
    d_in.get(sb,'\n');
    line = sb.str();
  }
  while(true) {
    Debug("interactive") << "Input now '" << input << line << "'" << endl << flush;

    Assert( !(d_in.fail() && !d_in.eof()) || line.empty() );

    /* Check for failure. */
    if(d_in.fail() && !d_in.eof()) {
      /* This should only happen if the input line was empty. */
      Assert( line.empty() );
      d_in.clear();
    }

    /* Strip trailing whitespace. */
    int n = line.length() - 1;
    while( !line.empty() && isspace(line[n]) ) {
      line.erase(n,1);
      n--;
    }

    /* If we hit EOF, we're done. */
    if( (!d_usingReadline && d_in.eof()) ||
        (d_usingReadline && lineBuf == NULL) ) {
      input += line;

      if( input.empty() ) {
        /* Nothing left to parse. */
        return NULL;
      }

      /* Some input left to parse, but nothing left to read.
         Jump out of input loop. */
      break;
    }

    if(!d_usingReadline) {
      /* Extract the newline delimiter from the stream too */
      int c CVC4_UNUSED = d_in.get();
      Assert( c == '\n' );
      Debug("interactive") << "Next char is '" << (char)c << "'" << endl << flush;
    }

    input += line;

    /* If the last char was a backslash, continue on the next line. */
    n = input.length() - 1;
    if( !line.empty() && input[n] == '\\' ) {
      input[n] = '\n';
      if(d_usingReadline) {
#if HAVE_LIBREADLINE
        lineBuf = ::readline(d_options.verbosity >= 0 ? "... > " : "");
        if(lineBuf != NULL && lineBuf[0] != '\0') {
          ::add_history(lineBuf);
        }
        line = lineBuf == NULL ? "" : lineBuf;
        free(lineBuf);
#endif /* HAVE_LIBREADLINE */
      } else {
        if(d_options.verbosity >= 0) {
          d_out << "... > " << flush;
        }

        /* Read a line */
        d_in.get(sb,'\n');
        line = sb.str();
      }
    } else {
      /* No continuation, we're done. */
      Debug("interactive") << "Leaving input loop." << endl << flush;
      break;
    }
  }

  d_parser->setInput(Input::newStringInput(d_options.inputLanguage, input, INPUT_FILENAME));

  /* There may be more than one command in the input. Build up a
     sequence. */
  CommandSequence *cmd_seq = new CommandSequence();
  Command *cmd;

  try {
    while( (cmd = d_parser->nextCommand()) ) {
      cmd_seq->addCommand(cmd);
      if(dynamic_cast<QuitCommand*>(cmd) != NULL) {
        d_quit = true;
        break;
      } else {
#if HAVE_LIBREADLINE
        if(dynamic_cast<DeclareFunctionCommand*>(cmd) != NULL) {
          s_declarations.insert(dynamic_cast<DeclareFunctionCommand*>(cmd)->getSymbol());
        } else if(dynamic_cast<DefineFunctionCommand*>(cmd) != NULL) {
          s_declarations.insert(dynamic_cast<DefineFunctionCommand*>(cmd)->getSymbol());
        } else if(dynamic_cast<DeclareTypeCommand*>(cmd) != NULL) {
          s_declarations.insert(dynamic_cast<DeclareTypeCommand*>(cmd)->getSymbol());
        } else if(dynamic_cast<DefineTypeCommand*>(cmd) != NULL) {
          s_declarations.insert(dynamic_cast<DefineTypeCommand*>(cmd)->getSymbol());
        }
#endif /* HAVE_LIBREADLINE */
      }
    }
  } catch(ParserException& pe) {
    d_out << pe << endl;
    // We can't really clear out the sequence and abort the current line,
    // because the parse error might be for the second command on the
    // line.  The first ones haven't yet been executed by the SmtEngine,
    // but the parser state has already made the variables and the mappings
    // in the symbol table.  So unfortunately, either we exit CVC4 entirely,
    // or we commit to the current line up to the command with the parse
    // error.
    //
    // FIXME: does that mean e.g. that a pushed LET scope might not yet have
    // been popped?!
    //
    //delete cmd_seq;
    //cmd_seq = new CommandSequence();
  }

  return cmd_seq;
}/* InteractiveShell::readCommand() */

#if HAVE_LIBREADLINE

/*char** commandCompletion(const char* text, int start, int end) {
  Debug("rl") << "text: " << text << endl;
  Debug("rl") << "start: " << start << " end: " << end << endl;
  return rl_completion_matches(text, commandGenerator);
}*/

// For some reason less<string> crashes on us; oh well,
// we don't need to copy into string anyway.
// Can't use less<const char*> because it compares pointers(?).
struct stringLess {
  bool operator()(const char* s1, const char* s2) {
    size_t l1 = strlen(s1), l2 = strlen(s2);
    return strncmp(s1, s2, l1 <= l2 ? l1 : l2) == -1;
  }
};/* struct string_less */

char* commandGenerator(const char* text, int state) {
  static CVC4_THREADLOCAL(const char* const*) rlPointer;
  static CVC4_THREADLOCAL(set<string>::const_iterator*) rlDeclaration;

  const char* const* i = lower_bound(commandsBegin, commandsEnd, text, stringLess());
  const char* const* j = upper_bound(commandsBegin, commandsEnd, text, stringLess());

  set<string>::const_iterator ii = lower_bound(s_declarations.begin(), s_declarations.end(), text, less<string>());
  set<string>::const_iterator jj = upper_bound(s_declarations.end(), s_declarations.end(), text, less<string>());

  if(rlDeclaration == NULL) {
    rlDeclaration = new set<string>::const_iterator();
  }

  if(state == 0) {
    rlPointer = i;
    *rlDeclaration = ii;
  }

  if(rlPointer != j) {
    return strdup(*rlPointer++);
  }

  return *rlDeclaration == jj ? NULL : strdup((*(*rlDeclaration)++).c_str());
}

#endif /* HAVE_LIBREADLINE */

}/* CVC4 namespace */


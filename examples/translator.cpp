/*********************                                                        */
/*! \file translator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief CVC4 translator
 **
 ** The CVC4 translator executable.  This program translates from one of
 ** CVC4's input languages to one of its output languages.
 **/

#include <cerrno>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <getopt.h>
#include <iostream>

#include <cvc4/api/cvc4cpp.h>
#include <cvc4/cvc4.h>
#include <cvc4/expr/expr_iomanip.h>
#include <cvc4/options/set_language.h>

using namespace std;
using namespace CVC4;
using namespace CVC4::language;
using namespace CVC4::parser;

enum {
  INPUT_LANG = 'L',
  OUTPUT_LANG = 'O',
  OUTPUT_FILE = 'o',
  HELP = 'h',
  DEFAULT_DAG_THRESH,
  EXPAND_DEFINITIONS,
  COMBINE_ASSERTIONS,
};/* enum */

const struct option longopts[] = {
  { "output-lang", required_argument, NULL, OUTPUT_LANG },
  { "output-language", required_argument, NULL, OUTPUT_LANG },
  { "expand-definitions", no_argument, NULL, EXPAND_DEFINITIONS },
  { "combine-assertions", no_argument, NULL, COMBINE_ASSERTIONS },
  { "dag-thresh", required_argument, NULL, DEFAULT_DAG_THRESH },
  { "lang", required_argument, NULL, INPUT_LANG },
  { "language", required_argument, NULL, INPUT_LANG },
  { "out", required_argument, NULL, OUTPUT_FILE },
  { "help", no_argument, NULL, HELP },
  { NULL, no_argument, NULL, 0 },
};/* longopts */

static void showHelp() {
  cerr << "cvc4-translator translation tool" << endl
       << "  --output-language | -O  set output language (default smt2)" << endl
       << "  --input-language | -L   set input language (default auto)" << endl
       << "  --out | -o              set output file (- for stdout)" << endl
       << "  --dag-thresh=N  set DAG threshold" << endl
       << "  --expand-definitions    expand define-funs" << endl
       << "  --combine-assertions    combine all assertions into one" << endl
       << "  --help | -h             this help" << endl
       << "Options and input filenames can be intermixed, and order is important." << endl
       << "For instance, \"-O smt2 x -O cvc4 y\" reads file x in smt2 format and"
       << "file y in cvc4 format and writes all output to stdout." << endl
       << "Some canonicalization may occur." << endl
       << "Comments and formatting are not preserved." << endl;
}

static void readFile(const char* filename, InputLanguage fromLang, OutputLanguage toLang, bool expand_definitions, bool combine_assertions, ostream* out) {
  if(fromLang == input::LANG_AUTO) {
    unsigned len = strlen(filename);
    if(len >= 5 && !strcmp(".smt2", filename + len - 5)) {
      fromLang = language::input::LANG_SMTLIB_V2;
    } else if((len >= 2 && !strcmp(".p", filename + len - 2)) ||
              (len >= 5 && !strcmp(".tptp", filename + len - 5))) {
      fromLang = language::input::LANG_TPTP;
    } else if(( len >= 4 && !strcmp(".cvc", filename + len - 4) ) ||
              ( len >= 5 && !strcmp(".cvc4", filename + len - 5) )) {
      fromLang = language::input::LANG_CVC4;
    } else {
      throw Exception("cannot determine input language to use for `" + string(filename) + "'");
    }
  }

  if(toLang == output::LANG_AUTO) {
    toLang = toOutputLanguage(fromLang);
  }

  *out << language::SetLanguage(toLang);

  Options opts;
  opts.setInputLanguage(fromLang);
  ExprManager exprMgr(opts);
  std::unique_ptr<api::Solver> solver =
      std::unique_ptr<api::Solver>(new api::Solver(&opts));
  ParserBuilder parserBuilder(solver.get(), filename, opts);
  if(!strcmp(filename, "-")) {
    parserBuilder.withFilename("<stdin>");
    parserBuilder.withLineBufferedStreamInput(cin);
  }
  Parser *parser = parserBuilder.build();
  // we only use the SmtEngine to do definition expansion for us
  SmtEngine *smt = expand_definitions ? new SmtEngine(&exprMgr) : NULL;
  // store up the assertions into one big conjunction
  std::vector<Expr> assertions;
  while(Command* cmd = parser->nextCommand()) {
    if(expand_definitions && dynamic_cast<DefineFunctionCommand*>(cmd) != NULL) {
      // tell the SmtEngine about the definition, but don't print it
      cmd->invoke(smt);
    } else {
      // have to switch on the command and expand definitions inside it
      if(expand_definitions && dynamic_cast<AssertCommand*>(cmd) != NULL) {
        Expr e = static_cast<AssertCommand*>(cmd)->getExpr();
        delete cmd;
        cmd = new AssertCommand(smt->expandDefinitions(e));
      } else if(expand_definitions && dynamic_cast<QueryCommand*>(cmd) != NULL) {
        Expr e = static_cast<QueryCommand*>(cmd)->getExpr();
        delete cmd;
        cmd = new QueryCommand(smt->expandDefinitions(e));
      } else if(expand_definitions && dynamic_cast<CheckSatCommand*>(cmd) != NULL) {
        Expr e = static_cast<CheckSatCommand*>(cmd)->getExpr();
        delete cmd;
        cmd = new CheckSatCommand(smt->expandDefinitions(e));
      } else if(expand_definitions && dynamic_cast<SimplifyCommand*>(cmd) != NULL) {
        Expr e = static_cast<SimplifyCommand*>(cmd)->getTerm();
        delete cmd;
        cmd = new SimplifyCommand(smt->expandDefinitions(e));
      } else if(expand_definitions && dynamic_cast<ExpandDefinitionsCommand*>(cmd) != NULL) {
        Expr e = static_cast<ExpandDefinitionsCommand*>(cmd)->getTerm();
        delete cmd;
        cmd = new ExpandDefinitionsCommand(smt->expandDefinitions(e));
      } else if(expand_definitions && dynamic_cast<GetValueCommand*>(cmd) != NULL) {
        vector<Expr> terms = static_cast<GetValueCommand*>(cmd)->getTerms();
        delete cmd;
        for(size_t i = 0; i < terms.size(); ++i) {
          terms[i] = smt->expandDefinitions(terms[i]);
        }
        cmd = new GetValueCommand(terms);
      }

      if(combine_assertions && dynamic_cast<AssertCommand*>(cmd) != NULL) {
        // store up the assertion, don't print it yet
        assertions.push_back(static_cast<AssertCommand*>(cmd)->getExpr());
      } else {
        if(combine_assertions &&
           ( dynamic_cast<CheckSatCommand*>(cmd) != NULL ||
             dynamic_cast<QueryCommand*>(cmd) != NULL ||
             dynamic_cast<PushCommand*>(cmd) != NULL ||
             dynamic_cast<PopCommand*>(cmd) != NULL ||
             dynamic_cast<SimplifyCommand*>(cmd) != NULL ||
             dynamic_cast<QuitCommand*>(cmd) != NULL )) {
          // combine all the stored assertions and print them at this point
          if(!assertions.empty()) {
            if(assertions.size() > 1) {
              *out << AssertCommand(exprMgr.mkExpr(kind::AND, assertions)) << endl;
            } else {
              *out << AssertCommand(assertions[0]) << endl;
            }
            assertions.clear();
          }
        }

        // now print the cmd we just parsed
        *out << cmd << endl;
      }
    }
    if(dynamic_cast<QuitCommand*>(cmd) != NULL) {
      delete cmd;
      break;
    }
    delete cmd;
  }
  if(!assertions.empty()) {
    if(assertions.size() > 1) {
      *out << AssertCommand(exprMgr.mkExpr(kind::AND, assertions)) << endl;
    } else {
      *out << AssertCommand(assertions[0]) << endl;
    }
    assertions.clear();
  }
  *out << flush;
  delete smt;
  delete parser;
}

/**
 * Translate from an input language to an output language.
 */
int main(int argc, char* argv[]) {
  ostream* out = &cout;
  InputLanguage fromLang = input::LANG_AUTO;
  OutputLanguage toLang = output::LANG_SMTLIB_V2;
  size_t files = 0;
  int dag_thresh = 1;
  bool expand_definitions = false;
  bool combine_assertions = false;

  try {
    int c;
    while((c = getopt_long(argc, argv, "-L:O:o:h", longopts, NULL)) != -1) {
      switch(c) {
      case 1:
        ++files;
        *out << expr::ExprDag(dag_thresh);
        readFile(optarg, (!strcmp(optarg, "-") && fromLang == input::LANG_AUTO) ? input::LANG_CVC4 : fromLang, toLang, expand_definitions, combine_assertions, out);
        break;
      case INPUT_LANG:
        if(!strcmp(optarg, "help")) {
          Options::printLanguageHelp(cerr);
          exit(1);
        }
        fromLang = toInputLanguage(optarg);
        break;
      case OUTPUT_LANG:
        if(!strcmp(optarg, "help")) {
          Options::printLanguageHelp(cerr);
          exit(1);
        }
        toLang = toOutputLanguage(optarg);
        break;
      case OUTPUT_FILE:
        out->flush();
        if(out != &cout) {
          ((ofstream*)out)->close();
          delete out;
        }
        if(strcmp(optarg, "-")) {
          out = new ofstream(optarg);
        } else {
          out = &cout;
        }
        break;
      case DEFAULT_DAG_THRESH: {
          if(!isdigit(*optarg)) {
            cerr << "error: --dag-thresh requires non-negative argument: `"
                 << optarg << "' invalid." << endl;
            exit(1);
          }
          char* end;
          unsigned long ul = strtoul(optarg, &end, 10);
          if(errno != 0 || *end != '\0') {
            cerr << "error: --dag-thresh argument malformed: `"
                 << optarg << "'." << endl;
            exit(1);
          }
          dag_thresh = ul > INT_MAX ? INT_MAX : int(ul);
        }
        break;
      case EXPAND_DEFINITIONS:
        expand_definitions = true;
        break;
      case COMBINE_ASSERTIONS:
        combine_assertions = true;
        break;
      case 'h':
        showHelp();
        exit(0);
      case '?':
        showHelp();
        exit(1);
      default:
        cerr << "internal error.  translator failed ("
             << char(c) << "," << c << ")." << endl;
        exit(1);
      }
    }

    if(files == 0) {
      *out << expr::ExprDag(dag_thresh);
      readFile("-", fromLang == input::LANG_AUTO ? input::LANG_CVC4 : fromLang, toLang, expand_definitions, combine_assertions, out);
      exit(0);
    }
  } catch(Exception& e) {
    cerr << e << endl;
    exit(1);
  }

  return 0;
}

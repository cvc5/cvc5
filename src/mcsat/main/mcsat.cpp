#define __BUILDING_CVC4LIB_UNIT_TEST

#include <string>

#include "parser/parser_builder.h"
#include "parser/parser.h"
#include "options/options.h"
#include "util/language.h"
#include "expr/expr_manager.h"
#include "expr/command.h"

#include "options/options.h"
#include "main/options.h"

using namespace CVC4;
using namespace CVC4::parser;

#include "mcsat/mcsat.h"

using namespace std;

void printUsage(Options& opts, bool full) {
  stringstream ss;
  ss << "usage: " << opts[options::binary_name] << " [options] [input-file]" << endl
      << endl
      << "Without an input file, or with `-', CVC4 reads from standard input." << endl
      << endl 
      << "CVC4 options:" << endl;
  if(full) {
    Options::printUsage( ss.str(), *opts[options::out] );
  } else {
    Options::printShortUsage( ss.str(), *opts[options::out] );
  }
}

void execute(Command* command, mcsat::MCSatEngine& engine);

int main(int argc, char* argv[]) {
  
  // Parse the options
  Options options;
  vector<string> filenames = options.parseOptions(argc, argv); 

  // Help?
  if(options[options::help]) {
    printUsage(options, true);  
    exit(1);
  }
  
  // Create the expression manager
  ExprManager exprManager(options);

  // Output as SMT2
  Debug.getStream() << expr::ExprSetDepth(-1) << expr::ExprSetLanguage(language::output::LANG_CVC4);
  
  // Solve the problems 
  for (unsigned i = 0; i < filenames.size(); ++ i) {
    try {

      // Setup the langage based on the options or extension
      if(options[options::inputLanguage] == language::input::LANG_AUTO) {
        size_t pos = filenames[i].find_last_of('.');
        if (pos != string::npos) {
          string extension = filenames[i].substr(pos + 1);
          if (extension == "smt2") {
            options.set(options::inputLanguage, language::input::LANG_SMTLIB_V2);
          } else if (extension == "smt") {
            options.set(options::inputLanguage, language::input::LANG_SMTLIB_V1);
          } else if (extension == "smt1") {
            options.set(options::inputLanguage, language::input::LANG_SMTLIB_V1);
          } else if (extension == "cvc") {
            options.set(options::inputLanguage, language::input::LANG_CVC4);
          } else if (extension == "cvc4") {
            options.set(options::inputLanguage, language::input::LANG_TPTP);
          }
        }
      }

      // Create the parser
      ParserBuilder parserBuilder(&exprManager, filenames[i], options);
      Parser* parser = parserBuilder.build();
  
      // Create the MCSAT engine
      mcsat::MCSatEngine mcSolver(&exprManager);

      // Parse and assert
      Command* cmd;
      while ((cmd = parser->nextCommand())) {
        if (!options[options::parseOnly]) {
          execute(cmd, mcSolver);
        }
        delete cmd;
      }
  
      // Check the problem
      if (!options[options::parseOnly]) {
        bool result = mcSolver.check();
        cout << (result ? "sat" : "unsat") << endl;
      }
      
      // Dump the statistics if asked for 
      if(options[options::statistics]) {
	exprManager.getStatistics().flushInformation(std::cerr);
	mcSolver.getStatistics().flushInformation(std::cerr);
      }

      // Get rid of the parser
      delete parser;

    } catch (const Exception& e) {
      std::cerr << e << std::endl;
    }
  }
}

void execute(Command* command, mcsat::MCSatEngine& engine) {

  // Individual assertion
  AssertCommand* assert = dynamic_cast<AssertCommand*>(command);
  if (assert) {
    // Assert to mcsat
    engine.addAssertion(assert->getExpr(), true);
    return;
  }

  CheckSatCommand* checkSat = dynamic_cast<CheckSatCommand*>(command);
  if (checkSat) {
    // Assert to mcsat
    engine.addAssertion(checkSat->getExpr(), true);
    return;
  }

  // Sequence of assertions
  CommandSequence *cmdSequence = dynamic_cast<CommandSequence*>(command);
  if(cmdSequence != NULL) {
    CommandSequence::iterator it = cmdSequence->begin();
    CommandSequence::iterator it_end = cmdSequence->end();
    for (; it != it_end; ++ it) {
      execute(*it, engine);
    }
    return;
  }
}

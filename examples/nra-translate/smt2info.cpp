/*********************                                                        */
/*! \file smt2info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Aina Niemetz, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <cassert>
#include <iostream>
#include <string>
#include <typeinfo>
#include <vector>

#include <cvc4/api/cvc4cpp.h>
#include <cvc4/cvc4.h>

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::options;

unsigned compute_degree(ExprManager& exprManager, const Expr& term) {
  unsigned n = term.getNumChildren();    
  unsigned degree = 0;

  // boolean stuff
  if (term.getType() == exprManager.booleanType()) {
    for (unsigned i = 0; i < n; ++ i) {
      degree = std::max(degree, compute_degree(exprManager, term[i]));
    }
    return degree;
  }

  // terms
  if (n == 0) {
    if (term.getKind() == kind::CONST_RATIONAL) {
      return 0;
    } else {
      return 1;
    }
  } else {
    unsigned degree = 0;  
    if (term.getKind() == kind::MULT) {
      for (unsigned i = 0; i < n; ++ i) {
        degree += std::max(degree, compute_degree(exprManager, term[i]));
      }
    } else {
      for (unsigned i = 0; i < n; ++ i) {
        degree = std::max(degree, compute_degree(exprManager, term[i]));
      }
    }    
    return degree;    
  }
}


int main(int argc, char* argv[]) 
{

  try {

    // Get the filename 
    string input(argv[1]);

    // Create the expression manager
    Options options;
    options.setInputLanguage(language::input::LANG_SMTLIB_V2);
    std::unique_ptr<api::Solver> solver =
        std::unique_ptr<api::Solver>(new api::Solver(&options));

    // Create the parser
    ParserBuilder parserBuilder(solver.get(), input, options);
    Parser* parser = parserBuilder.build();

    // Variables and assertions
    vector<string> variables;
    vector<string> info_tags;
    vector<string> info_data;
    vector<Expr> assertions;
  
    Command* cmd;
    while ((cmd = parser->nextCommand())) {
    
      SetInfoCommand* setinfo = dynamic_cast<SetInfoCommand*>(cmd);
      if (setinfo) {
        info_tags.push_back(setinfo->getFlag());
        info_data.push_back(setinfo->getSExpr().getValue());
        delete cmd;
        continue;
      }
  
      DeclareFunctionCommand* declare = dynamic_cast<DeclareFunctionCommand*>(cmd);
      if (declare) {
        variables.push_back(declare->getSymbol());
        delete cmd;
        continue;
      }
      
      AssertCommand* assert = dynamic_cast<AssertCommand*>(cmd);
      if (assert) {
        assertions.push_back(assert->getExpr());
        delete cmd;
        continue;
      }
  
      delete cmd;  
    }
    
    cout << "variables: " << variables.size() << endl;
  
    unsigned total_degree = 0;
    for (unsigned i = 0; i < assertions.size(); ++ i) {
      total_degree =
          std::max(total_degree,
                   compute_degree(*solver->getExprManager(), assertions[i]));
    }
  
    cout << "degree: " << total_degree << endl;
  
    // Get rid of the parser
    delete parser;
  } catch (Exception& e) {
    cerr << e << endl;
  }
}

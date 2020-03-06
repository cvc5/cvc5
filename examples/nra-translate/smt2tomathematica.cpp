/*********************                                                        */
/*! \file smt2tomathematica.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Andrew Reynolds, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
#include <map>
#include <string>
#include <typeinfo>
#include <vector>

#include <cvc4/api/cvc4cpp.h>
#include <cvc4/cvc4.h>

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;

void translate_to_mathematica(
        string input,
        const vector<string>& info_tags,
        const vector<string>& info_data,
	const map<Expr, unsigned>& variables,
	const vector<Expr>& assertions);

int main(int argc, char* argv[])
{

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
  std::map<Expr, unsigned> variables;
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
      string name = declare->getSymbol();
      Expr var = parser->getVariable(name).getExpr();
      unsigned n = variables.size();
      variables[var] = n;
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

  // Do the translation
  translate_to_mathematica(input, info_tags, info_data, variables, assertions);
	
  // Get rid of the parser
  delete parser;
}

void translate_to_mathematica_term(const map<Expr, unsigned>& variables, const Expr& term) {
  bool first;

  unsigned n = term.getNumChildren();
  
  if (n == 0) {
    if (term.getKind() == kind::CONST_RATIONAL) {
      cout << term.getConst<Rational>();
    } else {
      assert(variables.find(term) != variables.end());
      cout << "x" << variables.find(term)->second;
    }
  } else {
        
    switch (term.getKind()) {
      case kind::PLUS:
        cout << "(";
        first = true;
        for (unsigned i = 0; i < n; ++ i) {
          if (!first) {
            cout << " + ";
          }
          first = false;
          translate_to_mathematica_term(variables, term[i]);
        }
        cout << ")";
        break;
      case kind::MULT:
        cout << "(";
        first = true;
        for (unsigned i = 0; i < n; ++ i) {
          if (!first) {
            cout << " * ";
          }
          first = false;
          translate_to_mathematica_term(variables, term[i]);
        }
        cout << ")";
        break;      
      case kind::MINUS:
        cout << "(";
        translate_to_mathematica_term(variables, term[0]);
        cout << " - ";
        translate_to_mathematica_term(variables, term[1]);        
        cout << ")";
        break;
      case kind::DIVISION:
        // we only allow division by constant
        assert(term[1].getKind() == kind::CONST_RATIONAL);
        cout << "(";
        translate_to_mathematica_term(variables, term[0]);
        cout << " / ";
        translate_to_mathematica_term(variables, term[1]);        
        cout << ")";
        break;
      case kind::UMINUS:
        cout << "(-(";
        translate_to_mathematica_term(variables, term[0]);
        cout << "))";
        break;
      default:
        assert(false);
        break;
    }
  }  
}

void translate_to_mathematica(const map<Expr, unsigned>& variables, const Expr& assertion) {
  bool first;
  
  unsigned n = assertion.getNumChildren();
  
  if (n == 0) {
    assert(false);
  } else {
    
    std::string op;
    bool binary = false;
    bool theory = false;
    
    
    switch (assertion.getKind()) {
      case kind::NOT: 
        cout << "!";  
        translate_to_mathematica(variables, assertion[0]);
        break;
      case kind::OR:
        first = true;
        cout << "(";
        for (unsigned i = 0; i < n; ++ i) {
          if (!first) {
            cout << " || ";
          }
          first = false;
          translate_to_mathematica(variables, assertion[i]);
        }
        cout << ")";
        break;
      case kind::AND:
        first = true;
        cout << "(";
        for (unsigned i = 0; i < n; ++ i) {
          if (!first) {
            cout << " && ";
          }
          first = false;
          translate_to_mathematica(variables, assertion[i]);
        }
        cout << ")";
        break;      
      case kind::IMPLIES:
        cout << "Implies[";
        translate_to_mathematica(variables, assertion[0]);
        cout << ",";
        translate_to_mathematica(variables, assertion[1]);
        cout << "]";
        break;         
      case kind::EQUAL:
      if( assertion[0].getType().isBoolean() ){
        cout << "Equivalent[";
        translate_to_mathematica(variables, assertion[0]);
        cout << ",";
        translate_to_mathematica(variables, assertion[1]);
        cout << "]";
      }else{
        op = "==";
        theory = true;
      }
	      break;
      case kind::LT:
        op = "<";
        theory = true;
        break;
      case kind::LEQ:
        op = "<=";
        theory = true;
        break;
      case kind::GT:
        op = ">";
        theory = true;
        break;
      case kind::GEQ:
        op = ">=";
        theory = true;
        break;
      default:
        assert(false);
        break;
    }

    if (binary) {
      cout << "(";
      translate_to_mathematica(variables, assertion[0]);
      cout << " " << op << " ";
      translate_to_mathematica(variables, assertion[1]);
      cout << ")";
    }      

    if (theory) {
      cout << "(";
      translate_to_mathematica_term(variables, assertion[0]);
      cout << " " << op << " ";
      translate_to_mathematica_term(variables, assertion[1]);
      cout << ")";
    }      
  }  
}

void translate_to_mathematica(
        string input,
        const vector<string>& info_tags,
        const vector<string>& info_data,
        const std::map<Expr, unsigned>& variables,
	const vector<Expr>& assertions)
{
  bool first;

  // Dump out the information
  cout << "(* translated from " << input << " ";

  bool dump_tags = false;
  if (dump_tags) {  
    first = true;  
    for (unsigned i = 0; i < info_tags.size(); ++ i) {
      if (!first) {
        cout << ", "; 
      }
      first = false;
      cout << info_tags[i] << " = " << info_data[i];
    }
  }
  
  cout << "*)" << endl;   

  cout << "Resolve[";

  // Formula 
  cout << "Exists[{";
  first = true;
  for (unsigned i = 0; i < variables.size(); ++ i) {
    if (!first) {
      cout << ",";
    }
    first = false;
    cout << "x" << i;
  }
  cout << "}, ";
  
  if (assertions.size() > 1) {
    first = true;
    for (unsigned i = 0; i < assertions.size(); ++ i) {
      if (!first) {
        cout << " && ";
      } 
      first = false;
      translate_to_mathematica(variables, assertions[i]);
    }
  } else {
    translate_to_mathematica(variables, assertions[0]);
  }
  cout << "]";


  // End resolve
  cout << ", Reals]" << endl;
}

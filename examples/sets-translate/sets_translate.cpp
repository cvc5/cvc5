/*********************                                                        */
/*! \file sets_translate.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Andres Noetzli, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <boost/algorithm/string.hpp> // include Boost, a C++ library
#include <cassert>
#include <iostream>
#include <string>
#include <typeinfo>
#include <unordered_map>
#include <vector>

#include <cvc4/api/cvc4cpp.h>
#include <cvc4/cvc4.h>
#include <cvc4/options/set_language.h>

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::options;

bool nonsense(char c) { return !isalnum(c); }

#ifdef ENABLE_AXIOMS
const bool enableAxioms = true;
#else
const bool enableAxioms = false;
#endif

string setaxioms[] = {
  "(declare-fun memberHOLDA (HOLDB (Set HOLDB)) Bool)",
  "",
  "(declare-fun unionHOLDA ((Set HOLDB) (Set HOLDB)) (Set HOLDB))",
  "(assert (forall ((?X (Set HOLDB)) (?Y (Set HOLDB)) (?x HOLDB))",
  "                (= (memberHOLDA ?x (unionHOLDA ?X ?Y))",
  "                     (or (memberHOLDA ?x ?X) (memberHOLDA ?x ?Y))",
  "                ) ) )",
  "",
  "",
  "(declare-fun intersectionHOLDA ((Set HOLDB) (Set HOLDB)) (Set HOLDB))",
  "(assert (forall ((?X (Set HOLDB)) (?Y (Set HOLDB)) (?x HOLDB))",
  "                (= (memberHOLDA ?x (intersectionHOLDA ?X ?Y))",
  "                     (and (memberHOLDA ?x ?X) (memberHOLDA ?x ?Y))",
  "                ) ) )",
  "",
  "(declare-fun setminusHOLDA ((Set HOLDB) (Set HOLDB)) (Set HOLDB))",
  "(assert (forall ((?X (Set HOLDB)) (?Y (Set HOLDB)) (?x HOLDB))",
  "                (= (memberHOLDA ?x (setminusHOLDA ?X ?Y))",
  "                     (and (memberHOLDA ?x ?X) (not (memberHOLDA ?x ?Y)))",
  "                ) ) )",
  "",
  "(declare-fun singletonHOLDA (HOLDB) (Set HOLDB))",
  "(assert (forall ((?x HOLDB) (?y HOLDB))",
  "                (= (memberHOLDA ?x (singletonHOLDA ?y))",
  "                     (= ?x ?y)",
  "                ) ) )",
  "",
  "(declare-fun emptysetHOLDA () (Set HOLDB))",
  "(assert (forall ((?x HOLDB)) (not (memberHOLDA ?x emptysetHOLDA)) ) )",
  "",
  "(define-fun subsetHOLDA ((X (Set HOLDB)) (Y (Set HOLDB))) Bool (= (unionHOLDA X Y) Y))",
  ""
};

class Mapper {
  set< Type > setTypes;
  map< Type, Type > mapTypes;
  map< pair<Type, Kind>, Expr > setoperators;
  unordered_map< Expr, Expr, ExprHashFunction > substitutions;
  ostringstream sout;
  ExprManager* em;
  int depth;

  Expr add(SetType t, Expr e) {

    if(setTypes.find(t) == setTypes.end() ) {
      // mark as processed
      setTypes.insert(t);

      Type elementType = t.getElementType();
      ostringstream oss_type;
      oss_type << language::SetLanguage(language::output::LANG_SMTLIB_V2)
               << elementType;
      string elementTypeAsString = oss_type.str();
      elementTypeAsString.erase(
        remove_if(elementTypeAsString.begin(), elementTypeAsString.end(), nonsense),
        elementTypeAsString.end());

      // define-sort
      ostringstream oss_name;
      oss_name << language::SetLanguage(language::output::LANG_SMTLIB_V2)
               << "(Set " << elementType << ")";
      string name = oss_name.str();
      Type newt = em->mkArrayType(t.getElementType(), em->booleanType());
      mapTypes[t] = newt;

      // diffent types
      vector<Type> t_t;
      t_t.push_back(t);
      t_t.push_back(t);
      vector<Type> elet_t;
      elet_t.push_back(elementType);
      elet_t.push_back(t);

      if(!enableAxioms)
        sout << "(define-fun emptyset" << elementTypeAsString << "    "
             << " ()"
             << " " << name
             << " ( (as const " << name << ") false ) )" << endl;
      setoperators[ make_pair(t, kind::EMPTYSET) ] =
        em->mkVar( std::string("emptyset") + elementTypeAsString,
                   t);

      if(!enableAxioms)
        sout << "(define-fun singleton" << elementTypeAsString << "     "
             << " ( (x " << elementType << ") )"
             << " " << name << ""
             << " (store emptyset" << elementTypeAsString << " x true) )" << endl;
      setoperators[ make_pair(t, kind::SINGLETON) ] =
        em->mkVar( std::string("singleton") + elementTypeAsString,
                   em->mkFunctionType( elementType, t ) );

      if(!enableAxioms)
        sout << "(define-fun union" << elementTypeAsString << "       "
             << " ( (s1 " << name << ") (s2 " << name << ") )"
             << " " << name << ""
             << " ((_ map or) s1 s2))" << endl;
      setoperators[ make_pair(t, kind::UNION) ] =
        em->mkVar( std::string("union") + elementTypeAsString,
                   em->mkFunctionType( t_t, t ) );

      if(!enableAxioms)
        sout << "(define-fun intersection" << elementTypeAsString << ""
             << " ( (s1 " << name << ") (s2 " << name << ") )"
             << " " << name << ""
             << " ((_ map and) s1 s2))" << endl;
      setoperators[ make_pair(t, kind::INTERSECTION) ] =
        em->mkVar( std::string("intersection") + elementTypeAsString,
                   em->mkFunctionType( t_t, t ) );

      if(!enableAxioms)
        sout << "(define-fun setminus" << elementTypeAsString << "    "
             << " ( (s1 " << name << ") (s2 " << name << ") )"
             << " " << name << ""
             << " (intersection" << elementTypeAsString << " s1 ((_ map not) s2)))" << endl;
      setoperators[ make_pair(t, kind::SETMINUS) ] =
        em->mkVar( std::string("setminus") + elementTypeAsString,
                   em->mkFunctionType( t_t, t ) );

      if(!enableAxioms)
        sout << "(define-fun member" << elementTypeAsString << "          "
             << " ( (x " << elementType << ")" << " (s " << name << "))"
             << " Bool"
             << " (select s x) )" << endl;
      setoperators[ make_pair(t, kind::MEMBER) ] =
        em->mkVar( std::string("member") + elementTypeAsString,
                   em->mkPredicateType( elet_t ) );

      if(!enableAxioms)
        sout << "(define-fun subset" << elementTypeAsString << "    "
             << " ( (s1 " << name << ") (s2 " << name << ") )"
             << " Bool"
             <<" (= emptyset" << elementTypeAsString << " (setminus" << elementTypeAsString << " s1 s2)) )" << endl;
      setoperators[ make_pair(t, kind::SUBSET) ] =
        em->mkVar( std::string("subset") + elementTypeAsString,
                   em->mkPredicateType( t_t ) );

      if(enableAxioms) {
        int N = sizeof(setaxioms) / sizeof(setaxioms[0]);
        for(int i = 0; i < N; ++i) {
          string s = setaxioms[i];
          ostringstream oss;
          oss << language::SetLanguage(language::output::LANG_SMTLIB_V2) << elementType;
          boost::replace_all(s, "HOLDA", elementTypeAsString);
          boost::replace_all(s, "HOLDB", oss.str());
          if( s == "" ) continue;
          sout << s << endl;
        }
      }

    }
    Expr ret;
    if(e.getKind() == kind::EMPTYSET) {
      ret = setoperators[ make_pair(t, e.getKind()) ];
    } else {
      vector<Expr> children = e.getChildren();
      children.insert(children.begin(), setoperators[ make_pair(t, e.getKind()) ]);
      ret = em->mkExpr(kind::APPLY_UF, children);
    }
    // cout << "returning " << ret  << endl;
    return ret;
  }

public:
  Mapper(ExprManager* e) : em(e),depth(0) {
    sout << language::SetLanguage(language::output::LANG_SMTLIB_V2);
  }

  void defineSetSort() {
    if(setTypes.empty()) {
      cout << "(define-sort Set (X) (Array X Bool) )" << endl;
    }
  }


  Expr collectSortsExpr(Expr e)
  {
    if(substitutions.find(e) != substitutions.end()) {
      return substitutions[e];
    }
    ++depth;
    Expr old_e = e;
    for(unsigned i = 0; i < e.getNumChildren(); ++i) {
      collectSortsExpr(e[i]);
    }
    e = e.substitute(substitutions);
    // cout << "[debug] " << e << " " << e.getKind() << " " << theory::kindToTheoryId(e.getKind()) << endl;
    if(theory::kindToTheoryId(e.getKind()) == theory::THEORY_SETS) {
      SetType t = SetType(e.getType().isBoolean() ? e[1].getType() : e.getType());
      substitutions[e] = add(t, e);
      e = e.substitute(substitutions);
    }
    substitutions[old_e] = e;
    // cout << ";"; for(int i = 0; i < depth; ++i) cout << " "; cout << old_e << " => " << e << endl;
    --depth;
    return e;
  }

  void dump() {
    cout << sout.str();
  }
};


int main(int argc, char* argv[])
{

  try {

    // Get the filename
    string input;
    if(argc > 1){
      input = string(argv[1]);
    } else {
      input = "<stdin>";
    }

    // Create the expression manager
    Options options;
    options.setInputLanguage(language::input::LANG_SMTLIB_V2);
    cout << language::SetLanguage(language::output::LANG_SMTLIB_V2);
    // cout << Expr::dag(0);
    std::unique_ptr<api::Solver> solver =
        std::unique_ptr<api::Solver>(new api::Solver(&options));

    Mapper m(solver->getExprManager());

    // Create the parser
    ParserBuilder parserBuilder(solver.get(), input, options);
    if(input == "<stdin>") parserBuilder.withStreamInput(cin);
    std::unique_ptr<Parser> parser;
    parser.reset(parserBuilder.build());

    // Variables and assertions
    vector<string> variables;
    vector<string> info_tags;
    vector<string> info_data;
    vector<Expr> assertions;

    Command* cmd = NULL;
    CommandSequence commandsSequence;
    bool logicisset = false;

    while ((cmd = parser->nextCommand())) {

      // till logic is set, don't do any modifications
      if(!parser->logicIsSet()) {
        cout << (*cmd) << endl;
        delete cmd;
        continue;
      }

      // transform set-logic command, if there is one
      SetBenchmarkLogicCommand* setlogic = dynamic_cast<SetBenchmarkLogicCommand*>(cmd);
      if(setlogic) {
	LogicInfo logicinfo(setlogic->getLogic());
	if(!logicinfo.isTheoryEnabled(theory::THEORY_SETS)) {
	  cerr << "Sets theory not enabled. Stopping translation." << endl;
	  return 0;
	}
        logicinfo = logicinfo.getUnlockedCopy();
        if(enableAxioms) {
          logicinfo.enableQuantifiers();
          logicinfo.lock();
          if(!logicinfo.hasEverything()) {
            (logicinfo = logicinfo.getUnlockedCopy()).disableTheory(theory::THEORY_SETS);
            logicinfo.lock();
            cout << SetBenchmarkLogicCommand(logicinfo.getLogicString()) << endl;
          }
        } else {
          logicinfo.enableTheory(theory::THEORY_ARRAYS);
          // we print logic string only for Quantifiers, for Z3 stuff
          // we don't set the logic
        }

        delete cmd;
        continue;
      }

      // if we reach here, logic is set by now, so can define our sort
      if( !logicisset ) {
        logicisset = true;
        m.defineSetSort();
      }

      // declare/define-sort commands are printed immediately
      DeclareTypeCommand* declaresort = dynamic_cast<DeclareTypeCommand*>(cmd);
      DefineTypeCommand* definesort = dynamic_cast<DefineTypeCommand*>(cmd);
      if(declaresort || definesort) {
        cout << *cmd << endl;
        delete cmd;
        continue;
      }

      // other commands are queued up, while replacing with new function symbols
      AssertCommand* assert = dynamic_cast<AssertCommand*>(cmd);
      DeclareFunctionCommand* declarefun = dynamic_cast<DeclareFunctionCommand*>(cmd);
      DefineFunctionCommand* definefun = dynamic_cast<DefineFunctionCommand*>(cmd);

      Command* new_cmd = NULL;
      if (assert)
      {
        Expr newexpr = m.collectSortsExpr(assert->getExpr());
        new_cmd = new AssertCommand(newexpr);
      }
      else if (declarefun)
      {
        Expr newfunc = m.collectSortsExpr(declarefun->getFunction());
        new_cmd = new DeclareFunctionCommand(
            declarefun->getSymbol(), newfunc, declarefun->getType());
      }
      else if (definefun)
      {
        Expr newfunc = m.collectSortsExpr(definefun->getFunction());
        Expr newformula = m.collectSortsExpr(definefun->getFormula());
        new_cmd = new DefineFunctionCommand(definefun->getSymbol(),
                                            newfunc,
                                            definefun->getFormals(),
                                            newformula,
                                            false);
      }

      if(new_cmd == NULL) {
        commandsSequence.addCommand(cmd);
      } else {
        commandsSequence.addCommand(new_cmd);
        delete cmd;
      }

    }

    m.dump();
    cout << commandsSequence;
    
  
    // Get rid of the parser
    //delete parser;
  } catch (Exception& e) {
    cerr << e << endl;
  }
}

/*********************                                                        */
/*! \file smt2.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definitions of SMT2 constants.
 **
 ** Definitions of SMT2 constants.
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__SMT2_H
#define __CVC4__PARSER__SMT2_H

#include <sstream>
#include <stack>
#include <string>
#include <utility>

#include "parser/parser.h"
#include "parser/smt1/smt1.h"
#include "theory/logic_info.h"
#include "util/abstract_value.h"

namespace CVC4 {

class SExpr;

namespace parser {

class Smt2 : public Parser {
  friend class ParserBuilder;

public:
  enum Theory {
    THEORY_ARRAYS,
    THEORY_BITVECTORS,
    THEORY_CORE,
    THEORY_DATATYPES,
    THEORY_INTS,
    THEORY_REALS,
    THEORY_REALS_INTS,
    THEORY_QUANTIFIERS,
    THEORY_SETS,
    THEORY_STRINGS,
    THEORY_UF,
    THEORY_FP,
    THEORY_SEP
  };

private:
  bool d_logicSet;
  LogicInfo d_logic;
  std::hash_map<std::string, Kind, StringHashFunction> operatorKindMap;
  std::pair<Expr, std::string> d_lastNamedTerm;
  // this is a user-context stack
  std::stack< std::map<Expr, std::string> > d_unsatCoreNames;
  std::vector<Expr> d_sygusVars, d_sygusConstraints, d_sygusFunSymbols;
  std::vector< std::pair<std::string, Expr> > d_sygusFuns;
  std::map< Expr, bool > d_sygusVarPrimed;
  size_t d_nextSygusFun;

protected:
  Smt2(ExprManager* exprManager, Input* input, bool strictMode = false, bool parseOnly = false);

public:
  /**
   * Add theory symbols to the parser state.
   *
   * @param theory the theory to open (e.g., Core, Ints)
   */
  void addTheory(Theory theory);

  void addOperator(Kind k, const std::string& name);

  Kind getOperatorKind(const std::string& name) const;

  bool isOperatorEnabled(const std::string& name) const;

  bool isTheoryEnabled(Theory theory) const;

  bool logicIsSet();

  void reset();

  void resetAssertions();

  /**
   * Sets the logic for the current benchmark. Declares any logic and
   * theory symbols.
   *
   * @param name the name of the logic (e.g., QF_UF, AUFLIA)
   */
  void setLogic(std::string name);

  /**
   * Get the logic.
   */
  const LogicInfo& getLogic() const { return d_logic; }

  bool v2_0() const {
    return getInput()->getLanguage() == language::input::LANG_SMTLIB_V2_0;
  }
  // 2.6 is a superset of 2.5, use exact=false to query whether smt lib 2.5 or above
  bool v2_5( bool exact = true ) const {
    return exact ? getInput()->getLanguage() == language::input::LANG_SMTLIB_V2_5 : 
                   ( getInput()->getLanguage() >= language::input::LANG_SMTLIB_V2_5 && 
                     getInput()->getLanguage() <= language::input::LANG_SMTLIB_V2 );
  }
  bool v2_6() const {
    return getInput()->getLanguage() == language::input::LANG_SMTLIB_V2_6;
  }
  bool sygus() const {
    return getInput()->getLanguage() == language::input::LANG_SYGUS;
  }

  void setLanguage(InputLanguage lang);

  void setInfo(const std::string& flag, const SExpr& sexpr);

  void setOption(const std::string& flag, const SExpr& sexpr);

  void checkThatLogicIsSet();

  void checkUserSymbol(const std::string& name) {
    if(name.length() > 0 && (name[0] == '.' || name[0] == '@')) {
      std::stringstream ss;
      ss << "cannot declare or define symbol `" << name << "'; symbols starting with . and @ are reserved in SMT-LIB";
      parseError(ss.str());
    }
  }

  void includeFile(const std::string& filename);

  void setLastNamedTerm(Expr e, std::string name) {
    d_lastNamedTerm = std::make_pair(e, name);
  }

  void clearLastNamedTerm() {
    d_lastNamedTerm = std::make_pair(Expr(), "");
  }

  std::pair<Expr, std::string> lastNamedTerm() {
    return d_lastNamedTerm;
  }

  void pushUnsatCoreNameScope() {
    d_unsatCoreNames.push(d_unsatCoreNames.top());
  }

  void popUnsatCoreNameScope() {
    d_unsatCoreNames.pop();
  }

  void registerUnsatCoreName(std::pair<Expr, std::string> name) {
    d_unsatCoreNames.top().insert(name);
  }

  std::map<Expr, std::string> getUnsatCoreNames() {
    return d_unsatCoreNames.top();
  }

  bool isAbstractValue(const std::string& name) {
    return name.length() >= 2 && name[0] == '@' && name[1] != '0' &&
      name.find_first_not_of("0123456789", 1) == std::string::npos;
  }

  Expr mkAbstractValue(const std::string& name) {
    assert(isAbstractValue(name));
    return getExprManager()->mkConst(AbstractValue(Integer(name.substr(1))));
  }

  Expr mkSygusVar(const std::string& name, const Type& type, bool isPrimed = false);

  void mkSygusDefaultGrammar( const Type& range, Expr& bvl, const std::string& fun, std::vector<CVC4::Datatype>& datatypes,
                              std::vector<Type>& sorts, std::vector< std::vector<Expr> >& ops, std::vector<Expr> sygus_vars, int& startIndex );

  void mkSygusConstantsForType( const Type& type, std::vector<CVC4::Expr>& ops );

  void processSygusGTerm( CVC4::SygusGTerm& sgt, int index,
                          std::vector< CVC4::Datatype >& datatypes,
                          std::vector< CVC4::Type>& sorts,
                          std::vector< std::vector<CVC4::Expr> >& ops,
                          std::vector< std::vector<std::string> >& cnames,
                          std::vector< std::vector< std::vector< CVC4::Type > > >& cargs,
                          std::vector< bool >& allow_const,
                          std::vector< std::vector< std::string > >& unresolved_gterm_sym,
                          std::vector<CVC4::Expr>& sygus_vars,
                          std::map< CVC4::Type, CVC4::Type >& sygus_to_builtin, std::map< CVC4::Type, CVC4::Expr >& sygus_to_builtin_expr,
                          CVC4::Type& ret, bool isNested = false );

  static bool pushSygusDatatypeDef( Type t, std::string& dname,
                                    std::vector< CVC4::Datatype >& datatypes,
                                    std::vector< CVC4::Type>& sorts,
                                    std::vector< std::vector<CVC4::Expr> >& ops,
                                    std::vector< std::vector<std::string> >& cnames,
                                    std::vector< std::vector< std::vector< CVC4::Type > > >& cargs,
                                    std::vector< bool >& allow_const,
                                    std::vector< std::vector< std::string > >& unresolved_gterm_sym );

  static bool popSygusDatatypeDef( std::vector< CVC4::Datatype >& datatypes,
                                   std::vector< CVC4::Type>& sorts,
                                   std::vector< std::vector<CVC4::Expr> >& ops,
                                   std::vector< std::vector<std::string> >& cnames,
                                   std::vector< std::vector< std::vector< CVC4::Type > > >& cargs,
                                   std::vector< bool >& allow_const,
                                   std::vector< std::vector< std::string > >& unresolved_gterm_sym );

  void setSygusStartIndex( std::string& fun, int startIndex,
                           std::vector< CVC4::Datatype >& datatypes,
                           std::vector< CVC4::Type>& sorts,
                           std::vector< std::vector<CVC4::Expr> >& ops );

  void addSygusFun(const std::string& fun, Expr eval) {
    d_sygusFuns.push_back(std::make_pair(fun, eval));
  }

  void defineSygusFuns();

  void mkSygusDatatype( CVC4::Datatype& dt, std::vector<CVC4::Expr>& ops,
                        std::vector<std::string>& cnames, std::vector< std::vector< CVC4::Type > >& cargs,
                        std::vector<std::string>& unresolved_gterm_sym,
                        std::map< CVC4::Type, CVC4::Type >& sygus_to_builtin );

  // i is index in datatypes/ops
  // j is index is datatype
  Expr getSygusAssertion( std::vector<DatatypeType>& datatypeTypes, std::vector< std::vector<Expr> >& ops,
                          std::map<DatatypeType, Expr>& evals, std::vector<Expr>& terms,
                          Expr eval, const Datatype& dt, size_t i, size_t j );



  void addSygusConstraint(Expr constraint) {
    d_sygusConstraints.push_back(constraint);
  }

  Expr getSygusConstraints() {
    switch(d_sygusConstraints.size()) {
    case 0: return getExprManager()->mkConst(bool(true));
    case 1: return d_sygusConstraints[0];
    default: return getExprManager()->mkExpr(kind::AND, d_sygusConstraints);
    }
  }

  const std::vector<Expr>& getSygusVars() {
    return d_sygusVars;
  }
  const void getSygusPrimedVars( std::vector<Expr>& vars, bool isPrimed );

  const std::vector<Expr>& getSygusFunSymbols() {
    return d_sygusFunSymbols;
  }

  /**
   * Smt2 parser provides its own checkDeclaration, which does the
   * same as the base, but with some more helpful errors.
   */
  void checkDeclaration(const std::string& name, DeclarationCheck check,
                        SymbolType type = SYM_VARIABLE,
                        std::string notes = "") throw(ParserException) {
    // if the symbol is something like "-1", we'll give the user a helpful
    // syntax hint.  (-1 is a valid identifier in SMT-LIB, NOT unary minus.)
    if( check != CHECK_DECLARED ||
        name[0] != '-' ||
        name.find_first_not_of("0123456789", 1) != std::string::npos ) {
      this->Parser::checkDeclaration(name, check, type, notes);
      return;
    }else{
      //it is allowable in sygus
      if( sygus() && name[0]=='-' ){
        //do not check anything
        return;
      }
    }

    std::stringstream ss;
    ss << notes
       << "You may have intended to apply unary minus: `(- "
       << name.substr(1)
       << ")'\n";
    this->Parser::checkDeclaration(name, check, type, ss.str());
  }

  void checkOperator(Kind kind, unsigned numArgs) throw(ParserException) {
    Parser::checkOperator(kind, numArgs);
    // strict SMT-LIB mode enables extra checks for some bitvector operators
    // that CVC4 permits as N-ary but the standard requires is binary
    if(strictModeEnabled()) {
      switch(kind) {
      case kind::BITVECTOR_CONCAT:
      case kind::BITVECTOR_AND:
      case kind::BITVECTOR_OR:
      case kind::BITVECTOR_XOR:
      case kind::BITVECTOR_MULT:
      case kind::BITVECTOR_PLUS:
        if(numArgs != 2) {
          parseError("Operator requires exact 2 arguments in strict SMT-LIB "
                     "compliance mode: " + kindToString(kind));
        }
        break;
      default:
        break; /* no problem */
      }
    }
  }

  // Throw a ParserException with msg appended with the current logic.
  inline void parseErrorLogic(const std::string& msg) throw(ParserException) {
    const std::string withLogic = msg + getLogic().getLogicString();
    parseError(withLogic);
  }

private:
  std::map< CVC4::Expr, CVC4::Type > d_sygus_bound_var_type;
  std::map< CVC4::Expr, std::vector< CVC4::Expr > > d_sygus_let_func_to_vars;
  std::map< CVC4::Expr, CVC4::Expr > d_sygus_let_func_to_body;
  std::map< CVC4::Expr, unsigned > d_sygus_let_func_to_num_input_vars;
  //auxiliary define-fun functions introduced for production rules
  std::vector< CVC4::Expr > d_sygus_defined_funs;

  void collectSygusLetArgs( CVC4::Expr e, std::vector< CVC4::Type >& sygusArgs, std::vector< CVC4::Expr >& builtinArgs );

  void addSygusDatatypeConstructor( CVC4::Datatype& dt, CVC4::Expr op, std::string& cname, std::vector< CVC4::Type >& cargs,
                                    CVC4::Expr& let_body, std::vector< CVC4::Expr >& let_args, unsigned let_num_input_args );

  Type processSygusNestedGTerm( int sub_dt_index, std::string& sub_dname, std::vector< CVC4::Datatype >& datatypes,
                                std::vector< CVC4::Type>& sorts,
                                std::vector< std::vector<CVC4::Expr> >& ops,
                                std::vector< std::vector<std::string> >& cnames,
                                std::vector< std::vector< std::vector< CVC4::Type > > >& cargs,
                                std::vector< bool >& allow_const,
                                std::vector< std::vector< std::string > >& unresolved_gterm_sym,
                                std::map< CVC4::Type, CVC4::Type >& sygus_to_builtin,
                                std::map< CVC4::Type, CVC4::Expr >& sygus_to_builtin_expr, Type sub_ret );

  void processSygusLetConstructor( std::vector< CVC4::Expr >& let_vars, int index,
                                   std::vector< CVC4::Datatype >& datatypes,
                                   std::vector< CVC4::Type>& sorts,
                                   std::vector< std::vector<CVC4::Expr> >& ops,
                                   std::vector< std::vector<std::string> >& cnames,
                                   std::vector< std::vector< std::vector< CVC4::Type > > >& cargs,
                                   std::vector<CVC4::Expr>& sygus_vars,
                                   std::map< CVC4::Type, CVC4::Type >& sygus_to_builtin,
                                   std::map< CVC4::Type, CVC4::Expr >& sygus_to_builtin_expr );

  void addArithmeticOperators();

  void addBitvectorOperators();

  void addStringOperators();

  void addFloatingPointOperators();

  void addSepOperators();
};/* class Smt2 */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__SMT2_H */

/*********************                                                        */
/*! \file tptp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Francois Bobot, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definitions of TPTP constants.
 **
 ** Definitions of TPTP constants.
 **/

#include "parser/antlr_input.h" // Needs to go first.

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__TPTP_H
#define __CVC4__PARSER__TPTP_H

#include <cassert>
#include <ext/hash_set>

#include "parser/parser.h"
#include "smt/command.h"
#include "util/hash.h"

namespace CVC4 {

class SExpr;

namespace parser {

class Tptp : public Parser {
  friend class ParserBuilder;

  // In CNF variable are implicitly binded
  // d_freevar collect them
  std::vector< Expr > d_freeVar;
  Expr d_rtu_op;
  Expr d_stu_op;
  Expr d_utr_op;
  Expr d_uts_op;
  // The set of expression that already have a bridge
  std::hash_set<Expr, ExprHashFunction> d_r_converted;
  std::hash_map<std::string, Expr, StringHashFunction> d_distinct_objects;
  
  std::vector< pANTLR3_INPUT_STREAM > d_in_created;

  // TPTP directory where to find includes;
  // empty if none could be determined
  std::string d_tptpDir;

  // hack to make output SZS ontology-compliant
  bool d_hasConjecture;

  static void myPopCharStream(pANTLR3_LEXER lexer);
  void (*d_oldPopCharStream)(pANTLR3_LEXER);

public:

  bool cnf; // in a cnf formula
  bool fof; // in an fof formula

  void addFreeVar(Expr var) {
    assert(cnf);
    d_freeVar.push_back(var);
  }
  std::vector< Expr > getFreeVar() {
    assert(cnf);
    std::vector< Expr > r;
    r.swap(d_freeVar);
    return r;
  }

  inline Expr convertRatToUnsorted(Expr expr) {
    ExprManager * em = getExprManager();

    // Create the conversion function If they doesn't exists
    if(d_rtu_op.isNull()) {
      Type t;
      // Conversion from rational to unsorted
      t = em->mkFunctionType(em->realType(), d_unsorted);
      d_rtu_op = em->mkVar("$$rtu",t);
      preemptCommand(new DeclareFunctionCommand("$$rtu", d_rtu_op, t));
      // Conversion from unsorted to rational
      t = em->mkFunctionType(d_unsorted, em->realType());
      d_utr_op = em->mkVar("$$utr",t);
      preemptCommand(new DeclareFunctionCommand("$$utr", d_utr_op, t));
    }
    // Add the inverse in order to show that over the elements that
    // appear in the problem there is a bijection between unsorted and
    // rational
    Expr ret = em->mkExpr(kind::APPLY_UF,d_rtu_op,expr);
    if(d_r_converted.find(expr) == d_r_converted.end()) {
      d_r_converted.insert(expr);
      Expr eq = em->mkExpr(kind::EQUAL, expr,
                           em->mkExpr(kind::APPLY_UF, d_utr_op, ret));
      preemptCommand(new AssertCommand(eq));
    }
    return ret;
  }

  inline Expr convertStrToUnsorted(std::string str) {
    Expr& e = d_distinct_objects[str];
    if(e.isNull()) {
      e = getExprManager()->mkConst(UninterpretedConstant(d_unsorted, d_distinct_objects.size() - 1));
    }
    return e;
  }

public:

  // CNF and FOF are unsorted so we define this common type.
  // This is also the Type of $i in TFF.
  Type d_unsorted;

  enum Theory {
    THEORY_CORE,
  };/* enum Theory */

  enum FormulaRole {
    FR_AXIOM,
    FR_HYPOTHESIS,
    FR_DEFINITION,
    FR_ASSUMPTION,
    FR_LEMMA,
    FR_THEOREM,
    FR_CONJECTURE,
    FR_NEGATED_CONJECTURE,
    FR_UNKNOWN,
    FR_PLAIN,
    FR_FI_DOMAIN,
    FR_FI_FUNCTORS,
    FR_FI_PREDICATES,
    FR_TYPE,
  };/* enum FormulaRole */

  bool hasConjecture() const { return d_hasConjecture; }

protected:
  Tptp(ExprManager* exprManager, Input* input, bool strictMode = false, bool parseOnly = false);

public:
  ~Tptp();
  /**
   * Add theory symbols to the parser state.
   *
   * @param theory the theory to open (e.g., Core, Ints)
   */
  void addTheory(Theory theory);

  inline void makeApplication(Expr& expr, std::string& name,
                              std::vector<Expr>& args, bool term);

  inline Command* makeCommand(FormulaRole fr, Expr& expr, bool cnf);

  /** Ugly hack because I don't know how to return an expression from a
      token */
  Expr d_tmp_expr;

  /** Push a new stream in the lexer. When EOF is reached the previous stream
      is reused */
  void includeFile(std::string fileName);

  /** Check a TPTP let binding for well-formedness. */
  void checkLetBinding(std::vector<Expr>& bvlist, Expr lhs, Expr rhs, bool formula);

private:

  void addArithmeticOperators();
};/* class Tptp */

inline void Tptp::makeApplication(Expr& expr, std::string& name,
                                  std::vector<Expr>& args, bool term) {
  if(args.empty()) { // Its a constant
    if(isDeclared(name)) { // already appeared
      expr = getVariable(name);
    } else {
      Type t = term ? d_unsorted : getExprManager()->booleanType();
      expr = mkVar(name, t, ExprManager::VAR_FLAG_GLOBAL); // levelZero
      preemptCommand(new DeclareFunctionCommand(name, expr, t));
    }
  } else { // Its an application
    if(isDeclared(name)) { // already appeared
      expr = getVariable(name);
    } else {
      std::vector<Type> sorts(args.size(), d_unsorted);
      Type t = term ? d_unsorted : getExprManager()->booleanType();
      t = getExprManager()->mkFunctionType(sorts, t);
      expr = mkVar(name, t, ExprManager::VAR_FLAG_GLOBAL); // levelZero
      preemptCommand(new DeclareFunctionCommand(name, expr, t));
    }
    // args might be rationals, in which case we need to create
    // distinct constants of the "unsorted" sort to represent them
    for(size_t i = 0; i < args.size(); ++i) {
      if(args[i].getType().isReal() && FunctionType(expr.getType()).getArgTypes()[i] == d_unsorted) {
        args[i] = convertRatToUnsorted(args[i]);
      }
    }
    expr = getExprManager()->mkExpr(kind::APPLY_UF, expr, args);
  }
}

inline Command* Tptp::makeCommand(FormulaRole fr, Expr& expr, bool cnf) {
  // For SZS ontology compliance.
  // if we're in cnf() though, conjectures don't result in "Theorem" or
  // "CounterSatisfiable".
  if(!cnf && (fr == FR_NEGATED_CONJECTURE || fr == FR_CONJECTURE)) {
    d_hasConjecture = true;
  }
  switch(fr) {
  case FR_AXIOM:
  case FR_HYPOTHESIS:
  case FR_DEFINITION:
  case FR_ASSUMPTION:
  case FR_LEMMA:
  case FR_THEOREM:
  case FR_NEGATED_CONJECTURE:
  case FR_PLAIN:
    // it's a usual assert
    return new AssertCommand(expr);
  case FR_CONJECTURE:
    // something to prove
    return new AssertCommand(getExprManager()->mkExpr(kind::NOT,expr));
  case FR_UNKNOWN:
  case FR_FI_DOMAIN:
  case FR_FI_FUNCTORS:
  case FR_FI_PREDICATES:
  case FR_TYPE:
    return new EmptyCommand("Untreated role");
  }
  assert(false);// unreachable
  return NULL;
}

namespace tptp {
/**
 * Just exists to provide the uintptr_t constructor that ANTLR
 * requires.
 */
struct myExpr : public CVC4::Expr {
  myExpr() : CVC4::Expr() {}
  myExpr(void*) : CVC4::Expr() {}
  myExpr(const Expr& e) : CVC4::Expr(e) {}
  myExpr(const myExpr& e) : CVC4::Expr(e) {}
};/* struct myExpr */

enum NonAssoc {
  NA_IFF,
  NA_IMPLIES,
  NA_REVIMPLIES,
  NA_REVIFF,
  NA_REVOR,
  NA_REVAND,
};

}/* CVC4::parser::tptp namespace */


}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__TPTP_INPUT_H */

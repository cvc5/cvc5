/*********************                                                        */
/*! \file tptp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Francois Bobot, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
#include <unordered_map>
#include <unordered_set>

#include "parser/parser.h"
#include "smt/command.h"
#include "util/hash.h"

namespace CVC4 {
namespace parser {

class Tptp : public Parser {
 private:
  friend class ParserBuilder;
 public:
  bool cnf() const { return d_cnf; }
  void setCnf(bool cnf) { d_cnf = cnf; }

  bool fof() const { return d_fof; }
  void setFof(bool fof) { d_fof = fof; }

  void addFreeVar(Expr var);
  std::vector< Expr > getFreeVar();

  Expr convertRatToUnsorted(Expr expr);
  Expr convertStrToUnsorted(std::string str);

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
  Tptp(ExprManager* exprManager, Input* input, bool strictMode = false,
       bool parseOnly = false);

 public:
  ~Tptp();
  /**
   * Add theory symbols to the parser state.
   *
   * @param theory the theory to open (e.g., Core, Ints)
   */
  void addTheory(Theory theory);

  void makeApplication(Expr& expr, std::string& name, std::vector<Expr>& args,
                       bool term);

  Command* makeCommand(FormulaRole fr, Expr& expr, bool cnf);

  /** Ugly hack because I don't know how to return an expression from a
      token */
  Expr d_tmp_expr;

  /** Push a new stream in the lexer. When EOF is reached the previous stream
      is reused */
  void includeFile(std::string fileName);

  /** Check a TPTP let binding for well-formedness. */
  void checkLetBinding(std::vector<Expr>& bvlist, Expr lhs, Expr rhs,
                       bool formula);

 private:
  void addArithmeticOperators();

  // In CNF variable are implicitly binded
  // d_freevar collect them
  std::vector< Expr > d_freeVar;
  Expr d_rtu_op;
  Expr d_stu_op;
  Expr d_utr_op;
  Expr d_uts_op;
  // The set of expression that already have a bridge
  std::unordered_set<Expr, ExprHashFunction> d_r_converted;
  std::unordered_map<std::string, Expr> d_distinct_objects;

  std::vector< pANTLR3_INPUT_STREAM > d_in_created;

  // TPTP directory where to find includes;
  // empty if none could be determined
  std::string d_tptpDir;

  // hack to make output SZS ontology-compliant
  bool d_hasConjecture;

  bool d_cnf; // in a cnf formula
  bool d_fof; // in an fof formula

  static void myPopCharStream(pANTLR3_LEXER lexer);
  void (*d_oldPopCharStream)(pANTLR3_LEXER);
};/* class Tptp */


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

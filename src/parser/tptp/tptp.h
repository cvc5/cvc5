/******************************************************************************
 * Top contributors (to current version):
 *   Francois Bobot, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definition of TPTP parser.
 */

#include "cvc5parser_private.h"
#include "parser/antlr_input.h"  // Needs to go first.

#ifndef CVC5__PARSER__TPTP_H
#define CVC5__PARSER__TPTP_H

#include <unordered_map>
#include <unordered_set>

#include "api/cpp/cvc5.h"
#include "parser/parse_op.h"
#include "parser/parser.h"
#include "util/hash.h"

namespace cvc5 {

class Solver;

namespace parser {

class Command;

/*
 * This class is deprecated and used only for the ANTLR parser.
 */
class Tptp : public Parser {
 private:
  friend class ParserBuilder;
 public:
  bool cnf() const { return d_cnf; }
  void setCnf(bool cnf) { d_cnf = cnf; }

  bool fof() const { return d_fof; }
  void setFof(bool fof) { d_fof = fof; }

  bool hol() const;
  void setHol();

  void addFreeVar(cvc5::Term var);
  std::vector<cvc5::Term> getFreeVar();

  cvc5::Term convertRatToUnsorted(cvc5::Term expr);
  /**
   * Returns a free constant corresponding to the string str. We ensure that
   * these constants are one-to-one with str. We assert that all these free
   * constants are pairwise distinct before issuing satisfiability queries.
   */
  cvc5::Term convertStrToUnsorted(std::string str);

  // CNF and FOF are unsorted so we define this common type.
  // This is also the cvc5::Sort of $i in TFF.
  cvc5::Sort d_unsorted;

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
  Tptp(cvc5::Solver* solver,
       SymbolManager* sm,
       bool strictMode = false,
       bool parseOnly = false);

 public:
  ~Tptp();
  /**
   * Add theory symbols to the parser state.
   *
   * @param theory the theory to open (e.g., Core, Ints)
   */
  void addTheory(Theory theory);

  /** creates a lambda abstraction around application of given kind
   *
   * Given a kind k and type argType = t1...tn -> t, creates a lambda
   * expression
   *  (lambda x1:t1,...,xn:tn . (k x1 ... xn)) : t
   */
  cvc5::Term mkLambdaWrapper(cvc5::Kind k, cvc5::Sort argType);

  /** get assertion expression, based on the formula role.
  * expr should have Boolean type.
  * This returns the expression that should be asserted, given the formula role fr.
  * For example, if the role is "conjecture", then the return value is the negation of expr.
  */
  cvc5::Term getAssertionExpr(FormulaRole fr, cvc5::Term expr);

  /** get assertion for distinct constants
   *
   * This returns a node of the form distinct( k1, ..., kn ) where k1, ..., kn
   * are the distinct constants introduced by this parser (see
   * convertStrToUnsorted) if n>1, or null otherwise.
   */
  cvc5::Term getAssertionDistinctConstants();

  /** returns the appropriate AssertCommand, given a role, expression expr to
   * assert, and information about the assertion. The assertion expr is
   * literally what should be asserted (it is already been processed with
   * getAssertionExpr above). This may set a flag in the parser to mark
   * that we have asserted a conjecture.
   */
  Command* makeAssertCommand(FormulaRole fr, cvc5::Term expr, bool cnf);

  /** Ugly hack because I don't know how to return an expression from a
      token */
  cvc5::Term d_tmp_expr;

  /** Push a new stream in the lexer. When EOF is reached the previous stream
      is reused */
  void includeFile(std::string fileName);

  /** Check a TPTP let binding for well-formedness. */
  void checkLetBinding(const std::vector<cvc5::Term>& bvlist,
                       cvc5::Term lhs,
                       cvc5::Term rhs,
                       bool formula);
  /**
   * This converts a ParseOp to expression, assuming it is a standalone term.
   *
   * There are three cases in TPTP: either p already has an expression, in which
   * case this function just returns it, or p has just a name or a builtin kind.
   */
  cvc5::Term parseOpToExpr(ParseOp& p);
  /**
   * Apply parse operator to list of arguments, and return the resulting
   * expression.
   *
   * args must not be empty (otherwise the above method should have been
   * called).
   *
   * There are three cases in TPTP: either p already has an expression, in which
   * case this function just applies it to the arguments, or p has
   * just a name or a builtin kind, in which case the respective operator is
   * built.
   *
   * Note that the case of uninterpreted functions in TPTP this need not have
   * been previously declared, which leads to a more convoluted processing than
   * what is necessary in parsing SMT-LIB.
   */
  cvc5::Term applyParseOp(ParseOp& p, std::vector<cvc5::Term>& args);
  /**
   * Make decimal, returns a real corresponding to string ( snum "." sden ),
   * negated if pos is false, having exponent exp, negated exponent if posE is
   * false.
   */
  cvc5::Term mkDecimal(
      std::string& snum, std::string& sden, bool pos, size_t exp, bool posE);

 private:
  void addArithmeticOperators();
  /** is the name declared, if so, return the term for that name */
  cvc5::Term isTptpDeclared(const std::string& name);
  /**
   * Make APPLY_UF from arguments, which ensures that subyping is not used.
   */
  Term makeApplyUf(std::vector<Term>& args);

  // In CNF variable are implicitly binded
  // d_freevar collect them
  std::vector<cvc5::Term> d_freeVar;
  cvc5::Term d_rtu_op;
  cvc5::Term d_stu_op;
  cvc5::Term d_utr_op;
  cvc5::Term d_uts_op;
  // The set of expression that already have a bridge
  std::unordered_set<cvc5::Term> d_r_converted;
  std::unordered_map<std::string, cvc5::Term> d_distinct_objects;
  /**
   * TPTP automatically declares symbols as they are parsed inline. This
   * requires using an auxiliary symbol table for such symbols. This must be
   * independent of the main symbol table which is aware of quantifier
   * scopes.
   */
  std::unordered_map<std::string, cvc5::Term> d_auxSymbolTable;

  std::vector< pANTLR3_INPUT_STREAM > d_in_created;

  // TPTP directory where to find includes;
  // empty if none could be determined
  std::string d_tptpDir;

  // the null expression
  cvc5::Term d_nullExpr;

  // hack to make output SZS ontology-compliant
  bool d_hasConjecture;

  bool d_cnf; // in a cnf formula
  bool d_fof; // in an fof formula
  bool d_hol;  // in a thf formula
};/* class Tptp */


namespace tptp {
/**
 * Just exists to provide the uintptr_t constructor that ANTLR
 * requires.
 */
struct myExpr : public cvc5::Term
{
  myExpr() : cvc5::Term() {}
  myExpr(void*) : cvc5::Term() {}
  myExpr(const cvc5::Term& e) : cvc5::Term(e) {}
  myExpr(const myExpr& e) : cvc5::Term(e) {}
}; /* struct myExpr*/

enum NonAssoc {
  NA_IFF,
  NA_IMPLIES,
  NA_REVIMPLIES,
  NA_REVIFF,
  NA_REVOR,
  NA_REVAND,
};

}  // namespace tptp

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__TPTP_INPUT_H */

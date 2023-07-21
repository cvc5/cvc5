/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definitions of SMT2 constants.
 */

#include "cvc5parser_private.h"

#ifndef CVC5__PARSER__SMT2__SMT2_STATE_H
#define CVC5__PARSER__SMT2__SMT2_STATE_H

#include <cvc5/cvc5.h>

#include <optional>
#include <sstream>
#include <stack>
#include <string>
#include <unordered_map>
#include <utility>

#include "parser/parse_op.h"
#include "parser/parser.h"
#include "theory/logic_info.h"

namespace cvc5 {
namespace parser {

/*
 * The state information when parsing smt2 inputs.
 */
class Smt2State : public ParserState
{
 public:
  Smt2State(ParserStateCallback* psc,
            Solver* solver,
            SymbolManager* sm,
            bool strictMode = false,
            bool isSygus = false);

  ~Smt2State();

  /**
   * Add core theory symbols to the parser state.
   */
  void addCoreSymbols();

  void addOperator(Kind k, const std::string& name);

  /**
   * Registers an indexed function symbol.
   *
   * @param tKind The kind of the term that uses the operator kind (e.g.
   *              BITVECTOR_EXTRACT). If an indexed function symbol is
   *              overloaded (e.g., `to_fp`), this argument should
   *              be`UNDEFINED_KIND`.
   * @param name The name of the symbol (e.g. "extract")
   */
  void addIndexedOperator(Kind tKind, const std::string& name);
  /**
   * Registers a closure kind
   *
   * @param tKind The kind of the term that uses the operator kind (e.g.
   *              LAMBDA).
   * @param name The name of the symbol (e.g. "lambda")
   */
  void addClosureKind(Kind tKind, const std::string& name);
  /**
   * Checks whether an indexed operator is enabled. All indexed operators in
   * the current logic are considered to be enabled. This includes operators
   * such as `to_fp`, which do not correspond to a single kind.
   *
   * @param name The name of the indexed operator.
   * @return true if the indexed operator is enabled.
   */
  bool isIndexedOperatorEnabled(const std::string& name) const;

  Kind getOperatorKind(const std::string& name) const;

  bool isOperatorEnabled(const std::string& name) const;

  /** Parse block models mode */
  modes::BlockModelsMode getBlockModelsMode(const std::string& mode);
  /** Parse learned literal type */
  modes::LearnedLitType getLearnedLitType(const std::string& mode);
  /** Parse proof component */
  modes::ProofComponent getProofComponent(const std::string& pc);

  bool isTheoryEnabled(internal::theory::TheoryId theory) const;

  /**
   * Checks if higher-order support is enabled.
   *
   * @return true if higher-order support is enabled, false otherwise
   */
  bool isHoEnabled() const;
  /**
   * @return true if cardinality constraints are enabled, false otherwise
   */
  bool hasCardinalityConstraints() const;

  bool logicIsSet() override;

  /**
   * Creates an indexed constant, e.g. (_ +oo 8 24) (positive infinity
   * as a 32-bit floating-point constant).
   *
   * @param name The name of the constant (e.g. "+oo")
   * @param numerals The parameters for the constant (e.g. [8, 24])
   * @return The term corresponding to the constant or a parse error if name is
   *         not valid.
   */
  Term mkIndexedConstant(const std::string& name,
                         const std::vector<uint32_t>& numerals);
  /** Same as above, for constants indexed by symbols. */
  Term mkIndexedConstant(const std::string& name,
                         const std::vector<std::string>& symbols);
  /**
   * Make the operator for kind k that is indexed by the given symbols.
   * The arguments are passed for the purposes of resolving overloading.
   * For example, this method is used to construct the proper tester. This
   * requires knowing the type of the (first) argument in args.
   */
  Term mkIndexedOp(Kind k,
                   const std::vector<std::string>& symbols,
                   const std::vector<Term>& args);

  /**
   * Creates an indexed operator kind, e.g. BITVECTOR_EXTRACT for "extract".
   *
   * @param name The name of the operator (e.g. "extract")
   * @return The kind corresponding to the indexed operator or a parse
   *         error if the name is not valid.
   */
  Kind getIndexedOpKind(const std::string& name);
  /**
   * Creates the closure kind, e.g. FORALL for "forall".
   *
   * @param name The name of the operator (e.g. "forall")
   * @return The kind corresponding to the closure or a parse
   *         error if the name is not valid.
   */
  Kind getClosureKind(const std::string& name);

  /**
   * If we are in a version < 2.6, this updates name to the tester name of cons,
   * e.g. "is-cons".
   */
  bool getTesterName(Term cons, std::string& name) override;

  /** Make function defined by a define-fun(s)-rec command.
   *
   * fname : the name of the function.
   * sortedVarNames : the list of variable arguments for the function.
   * t : the range type of the function we are defining.
   *
   * This function will create a bind a new function term to name fname.
   * The type of this function is
   * ParserState::mkFlatFunctionType(sorts,t,flattenVars),
   * where sorts are the types in the second components of sortedVarNames.
   * As descibed in ParserState::mkFlatFunctionType, new bound variables may be
   * added to flattenVars in this function if the function is given a function
   * range type.
   */
  Term bindDefineFunRec(
      const std::string& fname,
      const std::vector<std::pair<std::string, Sort>>& sortedVarNames,
      Sort t,
      std::vector<Term>& flattenVars);

  /** Push scope for define-fun-rec
   *
   * This calls ParserState::pushScope() and sets up
   * initial information for reading a body of a function definition
   * in the define-fun-rec and define-funs-rec command.
   * The input parameters func/flattenVars are the result
   * of a call to mkDefineRec above.
   *
   * func : the function whose body we are defining.
   * sortedVarNames : the list of variable arguments for the function.
   * flattenVars : the implicit variables introduced when defining func.
   *
   * This function:
   * (1) Calls ParserState::pushScope().
   * (2) Computes the bound variable list for the quantified formula
   *     that defined this definition and stores it in bvs.
   */
  void pushDefineFunRecScope(
      const std::vector<std::pair<std::string, Sort>>& sortedVarNames,
      Term func,
      const std::vector<Term>& flattenVars,
      std::vector<Term>& bvs);

  void reset() override;

  /**
   * Creates a command that adds an invariant constraint.
   *
   * @param names Name of four symbols corresponding to the
   *              function-to-synthesize, precondition, postcondition,
   *              transition relation.
   * @return The command that adds an invariant constraint
   */
  std::unique_ptr<Command> invConstraint(const std::vector<std::string>& names);

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
  const internal::LogicInfo& getLogic() const { return d_logic; }

  /**
   * Create a Sygus grammar.
   * @param boundVars the parameters to corresponding synth-fun/synth-inv
   * @param ntSymbols the pre-declaration of the non-terminal symbols
   * @return a pointer to the grammar
   */
  Grammar* mkGrammar(const std::vector<Term>& boundVars,
                     const std::vector<Term>& ntSymbols);

  /** Are we using a sygus language?  */
  bool sygus() const;

  /**
   * Are we using SyGuS grammars? This is true if the input is the SyGuS
   * language or if produce-abducts or produce-interpolants is true. Enables
   * grammar-specific token `Constant`.
   */
  bool hasGrammars() const;

  void checkThatLogicIsSet();

  /**
   * Checks whether the current logic allows free sorts. If the logic does not
   * support free sorts, the function triggers a parse error.
   */
  void checkLogicAllowsFreeSorts();

  /**
   * Checks whether the current logic allows functions of non-zero arity. If
   * the logic does not support such functions, the function triggers a parse
   * error.
   */
  void checkLogicAllowsFunctions();

  void checkUserSymbol(const std::string& name)
  {
    if (name.length() > 0 && (name[0] == '.' || name[0] == '@'))
    {
      std::stringstream ss;
      ss << "cannot declare or define symbol `" << name
         << "'; symbols starting with . and @ are reserved in SMT-LIB";
      parseError(ss.str());
    }
    else if (isOperatorEnabled(name))
    {
      std::stringstream ss;
      ss << "Symbol `" << name << "' is shadowing a theory function symbol";
      parseError(ss.str());
    }
  }
  void setLastNamedTerm(Term e, std::string name)
  {
    d_lastNamedTerm = std::make_pair(e, name);
  }

  void clearLastNamedTerm() { d_lastNamedTerm = std::make_pair(Term(), ""); }

  std::pair<Term, std::string> lastNamedTerm() { return d_lastNamedTerm; }

  /** Does name denote an abstract value? (of the form '@n' for numeral n). */
  bool isAbstractValue(const std::string& name);

  /**
   * Make real or int from numeral string.
   *
   * In particular, if arithmetic is enabled, but integers are disabled, then
   * we construct a real. Otherwise, we construct an integer.
   */
  Term mkRealOrIntFromNumeral(const std::string& str);

  /**
   * Smt2 parser provides its own checkDeclaration, which does the
   * same as the base, but with some more helpful errors.
   */
  void checkDeclaration(const std::string& name,
                        DeclarationCheck check,
                        SymbolType type = SYM_VARIABLE,
                        std::string notes = "")
  {
    // if the symbol is something like "-1", we'll give the user a helpful
    // syntax hint.  (-1 is a valid identifier in SMT-LIB, NOT unary minus.)
    if (name.length() > 1 && name[0] == '-'
        && name.find_first_not_of("0123456789", 1) == std::string::npos)
    {
      std::stringstream ss;
      ss << notes << "You may have intended to apply unary minus: `(- "
         << name.substr(1) << ")'\n";
      this->ParserState::checkDeclaration(name, check, type, ss.str());
      return;
    }
    this->ParserState::checkDeclaration(name, check, type, notes);
  }
  /**
   * Notify that expression expr was given name std::string via a :named
   * attribute.
   */
  void notifyNamedExpression(Term& expr, std::string name);

  // Throw a ParserException with msg appended with the current logic.
  inline void parseErrorLogic(const std::string& msg)
  {
    const std::string withLogic = msg + getLogic().getLogicString();
    parseError(withLogic);
  }

  //------------------------- processing parse operators
  /**
   * Given a parse operator p, apply a type ascription to it. This method is run
   * when we encounter "(as t type)" and information regarding t has been stored
   * in p.
   *
   * This updates p to take into account the ascription. This may include:
   * - Converting an (pre-ascribed) array constant specification "const" to
   * an ascribed array constant specification (as const type) where type is
   * (Array T1 T2) for some T1, T2.
   * - Converting a (nullary or non-nullary) parametric datatype constructor to
   * the specialized constructor for the given type.
   * - Converting an empty set, universe set, or separation nil reference to
   * the respective term of the given type.
   * - If p's expression field is set, then we leave p unchanged, check if
   * that expression has the given type and throw a parse error otherwise.
   */
  void parseOpApplyTypeAscription(ParseOp& p, Sort type);
  /**
   * This converts a ParseOp to expression, assuming it is a standalone term.
   *
   * In particular:
   * - If p's expression field is set, then that expression is returned.
   * - If p's name field is set, then we look up that name in the symbol table
   * of this class.
   * In other cases, a parse error is thrown.
   */
  Term parseOpToExpr(ParseOp& p);
  /**
   * Apply parse operator to list of arguments, and return the resulting
   * expression.
   *
   * This method involves two phases.
   * (1) Processing the operator represented by p,
   * (2) Applying that operator to the set of arguments.
   *
   * For (1), this involves determining the kind of the overall expression. We
   * may be in one the following cases:
   * - If p's expression field is set, we may choose to prepend it to args, or
   * otherwise determine the appropriate kind of the overall expression based on
   * this expression.
   * - If p's name field is set, then we get the appropriate symbol for that
   * name, which may involve disambiguating that name if it is overloaded based
   * on the types of args. We then determine the overall kind of the return
   * expression based on that symbol.
   * - p's kind field may be already set.
   *
   * For (2), we construct the overall expression, which may involve the
   * following:
   * - If p is an array constant specification (as const (Array T1 T2)), then
   * we return the appropriate array constant based on args[0].
   * - If p represents a tuple selector, then we infer the appropriate tuple
   * selector expression based on the type of args[0].
   * - If the overall kind of the expression is chainable, we may convert it
   * to a left- or right-associative chain.
   * - If the overall kind is SUB and args has size 1, then we return an
   * application of NEG.
   * - If the overall expression is a partial application, then we process this
   * as a chain of HO_APPLY terms.
   */
  Term applyParseOp(const ParseOp& p, std::vector<Term>& args);
  /**
   * Returns a (parameterized) sort, given a name and args.
   */
  Sort getParametricSort(const std::string& name,
                         const std::vector<Sort>& args) override;
  /**
   * Returns a (indexed) sort, given a name and numeric indices.
   */
  Sort getIndexedSort(const std::string& name,
                      const std::vector<std::string>& numerals);
  /** is closure? */
  bool isClosure(const std::string& name);
  //------------------------- end processing parse operators

  /**
   * Handles a push command.
   *
   * @return An instance of `PushCommand`
   */
  std::unique_ptr<Command> handlePush(std::optional<uint32_t> nscopes);
  /**
   * Handles a pop command.
   *
   * @return An instance of `PopCommand`
   */
  std::unique_ptr<Command> handlePop(std::optional<uint32_t> nscopes);

 private:
  void addArithmeticOperators();

  void addTranscendentalOperators();

  void addQuantifiersOperators();

  void addBitvectorOperators();

  void addFiniteFieldOperators();

  void addDatatypesOperators();

  void addStringOperators();

  void addFloatingPointOperators();

  void addSepOperators();

  /**
   * Utility function to create a conjunction of expressions.
   *
   * @param es Expressions in the conjunction
   * @return True if `es` is empty, `e` if `es` consists of a single element
   *         `e`, the conjunction of expressions otherwise.
   */
  Term mkAnd(const std::vector<Term>& es) const;
  /**
   * @return True if term t an integer value.
   */
  static bool isConstInt(const Term& t);
  /**
   * @return True if term t is a bit-vector value.
   */
  static bool isConstBv(const Term& t);

  /** Are we parsing a sygus file? */
  bool d_isSygus;
  /** Has the logic been set (either by forcing it or a set-logic command)? */
  bool d_logicSet;
  /** Have we seen a set-logic command yet? */
  bool d_seenSetLogic;
  /** The current logic */
  internal::LogicInfo d_logic;
  /** Maps strings to the operator it is bound to */
  std::unordered_map<std::string, Kind> d_operatorKindMap;
  /**
   * Maps indexed symbols to the kind of the operator (e.g. "extract" to
   * BITVECTOR_EXTRACT).
   */
  std::unordered_map<std::string, Kind> d_indexedOpKindMap;
  /** Closure map */
  std::unordered_map<std::string, Kind> d_closureKindMap;
  /** The last named term and its name */
  std::pair<Term, std::string> d_lastNamedTerm;
  /**
   * A list of sygus grammar objects. We keep track of them here to ensure that
   * they don't get deleted before the commands using them get invoked.
   */
  std::vector<std::unique_ptr<Grammar>> d_allocGrammars;
};

}  // namespace parser
}  // namespace cvc5

#endif

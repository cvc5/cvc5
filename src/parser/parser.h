/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A collection of state for use by parser implementations.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__PARSER_H
#define CVC5__PARSER__PARSER_H

#include <list>
#include <memory>
#include <set>
#include <string>

#include "api/cpp/cvc5.h"
#include "cvc5_export.h"
#include "expr/kind.h"
#include "expr/symbol_manager.h"
#include "expr/symbol_table.h"
#include "parser/input.h"
#include "parser/parse_op.h"
#include "parser/parser_exception.h"
#include "util/unsafe_interrupt_exception.h"

namespace cvc5 {

// Forward declarations
class Command;
class ResourceManager;

namespace parser {

class Input;

/** Types of checks for the symbols */
enum DeclarationCheck {
  /** Enforce that the symbol has been declared */
  CHECK_DECLARED,
  /** Enforce that the symbol has not been declared */
  CHECK_UNDECLARED,
  /** Don't check anything */
  CHECK_NONE
};/* enum DeclarationCheck */

/**
 * Returns a string representation of the given object (for
 * debugging).
 */
inline std::ostream& operator<<(std::ostream& out, DeclarationCheck check);
inline std::ostream& operator<<(std::ostream& out, DeclarationCheck check) {
  switch(check) {
  case CHECK_NONE:
    return out << "CHECK_NONE";
  case CHECK_DECLARED:
    return out << "CHECK_DECLARED";
  case CHECK_UNDECLARED:
    return out << "CHECK_UNDECLARED";
  default:
    return out << "DeclarationCheck!UNKNOWN";
  }
}

/**
 * Types of symbols. Used to define namespaces.
 */
enum SymbolType {
  /** Variables */
  SYM_VARIABLE,
  /** Sorts */
  SYM_SORT
};/* enum SymbolType */

/**
 * Returns a string representation of the given object (for
 * debugging).
 */
inline std::ostream& operator<<(std::ostream& out, SymbolType type);
inline std::ostream& operator<<(std::ostream& out, SymbolType type) {
  switch(type) {
  case SYM_VARIABLE:
    return out << "SYM_VARIABLE";
  case SYM_SORT:
    return out << "SYM_SORT";
  default:
    return out << "SymbolType!UNKNOWN";
  }
}

/**
 * This class encapsulates all of the state of a parser, including the
 * name of the file, line number and column information, and in-scope
 * declarations.
 */
class CVC5_EXPORT Parser
{
  friend class ParserBuilder;
private:

 /** The input that we're parsing. */
 std::unique_ptr<Input> d_input;

 /**
  * Reference to the symbol manager, which manages the symbol table used by
  * this parser.
  */
 SymbolManager* d_symman;

 /**
  * This current symbol table used by this parser, from symbol manager.
  */
 SymbolTable* d_symtab;

 /**
  * The level of the assertions in the declaration scope.  Things declared
  * after this level are bindings from e.g. a let, a quantifier, or a
  * lambda.
  */
 size_t d_assertionLevel;

 /** How many anonymous functions we've created. */
 size_t d_anonymousFunctionCount;

 /** Are we done */
 bool d_done;

 /** Are semantic checks enabled during parsing? */
 bool d_checksEnabled;

 /** Are we parsing in strict mode? */
 bool d_strictMode;

 /** Are we only parsing? */
 bool d_parseOnly;

 /**
  * Can we include files?  (Set to false for security purposes in
  * e.g. the online version.)
  */
 bool d_canIncludeFile;

 /**
  * Whether the logic has been forced with --force-logic.
  */
 bool d_logicIsForced;

 /**
  * The logic, if d_logicIsForced == true.
  */
 std::string d_forcedLogic;

 /** The set of operators available in the current logic. */
 std::set<api::Kind> d_logicOperators;

 /** The set of attributes already warned about. */
 std::set<std::string> d_attributesWarnedAbout;

 /**
  * The current set of unresolved types.  We can get by with this NOT
  * being on the scope, because we can only have one DATATYPE
  * definition going on at one time.  This is a bit hackish; we
  * depend on mkMutualDatatypeTypes() to check everything and clear
  * this out.
  */
 std::set<api::Sort> d_unresolved;

 /**
  * "Preemption commands": extra commands implied by subterms that
  * should be issued before the currently-being-parsed command is
  * issued.  Used to support SMT-LIBv2 ":named" attribute on terms.
  *
  * Owns the memory of the Commands in the queue.
  */
 std::list<Command*> d_commandQueue;

 /** Lookup a symbol in the given namespace (as specified by the type).
  * Only returns a symbol if it is not overloaded, returns null otherwise.
  */
 api::Term getSymbol(const std::string& var_name, SymbolType type);

protected:
 /** The API Solver object. */
 api::Solver* d_solver;

 /**
  * Create a parser state.
  *
  * @attention The parser takes "ownership" of the given
  * input and will delete it on destruction.
  *
  * @param solver solver API object
  * @param symm reference to the symbol manager
  * @param input the parser input
  * @param strictMode whether to incorporate strict(er) compliance checks
  * @param parseOnly whether we are parsing only (and therefore certain checks
  * need not be performed, like those about unimplemented features, @see
  * unimplementedFeature())
  */
 Parser(api::Solver* solver,
        SymbolManager* sm,
        bool strictMode = false,
        bool parseOnly = false);

public:

  virtual ~Parser();

  /** Get the associated solver. */
  api::Solver* getSolver() const;

  /** Get the associated input. */
  Input* getInput() const { return d_input.get(); }

  /** Get unresolved sorts */
  inline std::set<api::Sort>& getUnresolvedSorts() { return d_unresolved; }

  /** Deletes and replaces the current parser input. */
  void setInput(Input* input)  {
    d_input.reset(input);
    d_input->setParser(*this);
    d_done = false;
  }

  /**
   * Check if we are done -- either the end of input has been reached, or some
   * error has been encountered.
   * @return true if parser is done
   */
  inline bool done() const {
    return d_done;
  }

  /** Sets the done flag */
  inline void setDone(bool done = true) {
    d_done = done;
  }

  /** Enable semantic checks during parsing. */
  void enableChecks() { d_checksEnabled = true; }

  /** Disable semantic checks during parsing. Disabling checks may lead to crashes on bad inputs. */
  void disableChecks() { d_checksEnabled = false; }

  /** Enable strict parsing, according to the language standards. */
  void enableStrictMode() { d_strictMode = true; }

  /** Disable strict parsing. Allows certain syntactic infelicities to
      pass without comment. */
  void disableStrictMode() { d_strictMode = false; }

  bool strictModeEnabled() { return d_strictMode; }

  void allowIncludeFile() { d_canIncludeFile = true; }
  void disallowIncludeFile() { d_canIncludeFile = false; }
  bool canIncludeFile() const { return d_canIncludeFile; }

  /** Expose the functionality from SMT/SMT2 parsers, while making
      implementation optional by returning false by default. */
  virtual bool logicIsSet() { return false; }

  virtual void forceLogic(const std::string& logic);

  const std::string& getForcedLogic() const { return d_forcedLogic; }
  bool logicIsForced() const { return d_logicIsForced; }

  /**
   * Gets the variable currently bound to name.
   *
   * @param name the name of the variable
   * @return the variable expression
   * Only returns a variable if its name is not overloaded, returns null otherwise.
   */
  api::Term getVariable(const std::string& name);

  /**
   * Gets the function currently bound to name.
   *
   * @param name the name of the variable
   * @return the variable expression
   * Only returns a function if its name is not overloaded, returns null otherwise.
   */
  api::Term getFunction(const std::string& name);

  /**
   * Returns the expression that name should be interpreted as, based on the current binding.
   *
   * The symbol name should be declared.
   * This creates the expression that the string "name" should be interpreted as.
   * Typically this corresponds to a variable, but it may also correspond to
   * a nullary constructor or a defined function.
   * Only returns an expression if its name is not overloaded, returns null otherwise.
   */
  virtual api::Term getExpressionForName(const std::string& name);

  /**
   * Returns the expression that name should be interpreted as, based on the
   * current binding.
   *
   * This is the same as above but where the name has been type cast to t.
   */
  virtual api::Term getExpressionForNameAndType(const std::string& name,
                                                api::Sort t);

  /**
   * If this method returns true, then name is updated with the tester name
   * for constructor cons.
   *
   * In detail, notice that (user-defined) datatypes associate a unary predicate
   * for each constructor, called its "tester". This symbol is automatically
   * defined when a datatype is defined. The tester name for a constructor
   * (e.g. "cons") depends on the language:
   * - In smt versions < 2.6, the (non-standard) syntax is "is-cons",
   * - In smt versions >= 2.6, the indexed symbol "(_ is cons)" is used. Thus,
   * no tester symbol is necessary, since "is" is a builtin symbol. We still use
   * the above syntax if strict mode is disabled.
   * - In cvc, the syntax for testers is "is_cons".
   */
  virtual bool getTesterName(api::Term cons, std::string& name);

  /**
   * Returns the kind that should be used for applications of expression fun.
   * This is a generalization of ExprManager::operatorToKind that also
   * handles variables whose types are "function-like", i.e. where
   * checkFunctionLike(fun) returns true.
   *
   * For examples of the latter, this function returns
   *   APPLY_UF if fun has function type,
   *   APPLY_CONSTRUCTOR if fun has constructor type.
   */
  api::Kind getKindForFunction(api::Term fun);

  /**
   * Returns a sort, given a name.
   * @param sort_name the name to look up
   */
  api::Sort getSort(const std::string& sort_name);

  /**
   * Returns a (parameterized) sort, given a name and args.
   */
  api::Sort getSort(const std::string& sort_name,
                    const std::vector<api::Sort>& params);

  /**
   * Returns arity of a (parameterized) sort, given a name and args.
   */
  size_t getArity(const std::string& sort_name);

  /**
   * Checks if a symbol has been declared.
   * @param name the symbol name
   * @param type the symbol type
   * @return true iff the symbol has been declared with the given type
   */
  bool isDeclared(const std::string& name, SymbolType type = SYM_VARIABLE);

  /**
   * Checks if the declaration policy we want to enforce holds
   * for the given symbol.
   * @param name the symbol to check
   * @param check the kind of check to perform
   * @param type the type of the symbol
   * @param notes notes to add to a parse error (if one is generated)
   * @throws ParserException if checks are enabled and the check fails
   */
  void checkDeclaration(const std::string& name,
                        DeclarationCheck check,
                        SymbolType type = SYM_VARIABLE,
                        std::string notes = "");

  /**
   * Checks whether the given expression is function-like, i.e.
   * it expects arguments. This is checked by looking at the type
   * of fun. Examples of function types are function, constructor,
   * selector, tester.
   * @param fun the expression to check
   * @throws ParserException if checks are enabled and fun is not
   * a function
   */
  void checkFunctionLike(api::Term fun);

  /** Create a new cvc5 variable expression of the given type.
   *
   * It is inserted at context level zero in the symbol table if levelZero is
   * true, or if we are using global declarations.
   *
   * If a symbol with name already exists,
   *  then if doOverload is true, we create overloaded operators.
   *  else if doOverload is false, the existing expression is shadowed by the
   * new expression.
   */
  api::Term bindVar(const std::string& name,
                    const api::Sort& type,
                    bool levelZero = false,
                    bool doOverload = false);

  /**
   * Create a set of new cvc5 variable expressions of the given type.
   *
   * It is inserted at context level zero in the symbol table if levelZero is
   * true, or if we are using global declarations.
   *
   * For each name, if a symbol with name already exists,
   *  then if doOverload is true, we create overloaded operators.
   *  else if doOverload is false, the existing expression is shadowed by the
   * new expression.
   */
  std::vector<api::Term> bindVars(const std::vector<std::string> names,
                                  const api::Sort& type,
                                  bool levelZero = false,
                                  bool doOverload = false);

  /**
   * Create a new cvc5 bound variable expression of the given type. This binds
   * the symbol name to that variable in the current scope.
   */
  api::Term bindBoundVar(const std::string& name, const api::Sort& type);
  /**
   * Create a new cvc5 bound variable expressions of the given names and types.
   * Like the method above, this binds these names to those variables in the
   * current scope.
   */
  std::vector<api::Term> bindBoundVars(
      std::vector<std::pair<std::string, api::Sort> >& sortedVarNames);

  /**
   * Create a set of new cvc5 bound variable expressions of the given type.
   *
   * For each name, if a symbol with name already exists,
   *  then if doOverload is true, we create overloaded operators.
   *  else if doOverload is false, the existing expression is shadowed by the
   * new expression.
   */
  std::vector<api::Term> bindBoundVars(const std::vector<std::string> names,
                                       const api::Sort& type);

  /** Create a new variable definition (e.g., from a let binding).
   * levelZero is set if the binding must be done at level 0.
   * If a symbol with name already exists,
   *  then if doOverload is true, we create overloaded operators.
   *  else if doOverload is false, the existing expression is shadowed by the
   * new expression.
   */
  void defineVar(const std::string& name,
                 const api::Term& val,
                 bool levelZero = false,
                 bool doOverload = false);

  /**
   * Create a new type definition.
   *
   * @param name The name of the type
   * @param type The type that should be associated with the name
   * @param levelZero If true, the type definition is considered global and
   *                  cannot be removed by popping the user context
   * @param skipExisting If true, the type definition is ignored if the same
   *                     symbol has already been defined. It is assumed that
   *                     the definition is the exact same as the existing one.
   */
  void defineType(const std::string& name,
                  const api::Sort& type,
                  bool levelZero = false,
                  bool skipExisting = false);

  /**
   * Create a new (parameterized) type definition.
   *
   * @param name The name of the type
   * @param params The type parameters
   * @param type The type that should be associated with the name
   * @param levelZero If true, the type definition is considered global and
   *                  cannot be removed by poppoing the user context
   */
  void defineType(const std::string& name,
                  const std::vector<api::Sort>& params,
                  const api::Sort& type,
                  bool levelZero = false);

  /** Create a new type definition (e.g., from an SMT-LIBv2 define-sort). */
  void defineParameterizedType(const std::string& name,
                               const std::vector<api::Sort>& params,
                               const api::Sort& type);

  /**
   * Creates a new sort with the given name.
   */
  api::Sort mkSort(const std::string& name);

  /**
   * Creates a new sort constructor with the given name and arity.
   */
  api::Sort mkSortConstructor(const std::string& name, size_t arity);

  /**
   * Creates a new "unresolved type," used only during parsing.
   */
  api::Sort mkUnresolvedType(const std::string& name);

  /**
   * Creates a new unresolved (parameterized) type constructor of the given
   * arity.
   */
  api::Sort mkUnresolvedTypeConstructor(const std::string& name, size_t arity);
  /**
   * Creates a new unresolved (parameterized) type constructor given the type
   * parameters.
   */
  api::Sort mkUnresolvedTypeConstructor(const std::string& name,
                                        const std::vector<api::Sort>& params);

  /**
   * Creates a new unresolved (parameterized) type constructor of the given
   * arity. Calls either mkUnresolvedType or mkUnresolvedTypeConstructor
   * depending on the arity.
   */
  api::Sort mkUnresolvedType(const std::string& name, size_t arity);

  /**
   * Returns true IFF name is an unresolved type.
   */
  bool isUnresolvedType(const std::string& name);

  /**
   * Creates and binds sorts of a list of mutually-recursive datatype
   * declarations.
   *
   * For each symbol defined by the datatype, if a symbol with name already
   * exists, then if doOverload is true, we create overloaded operators. Else, if
   * doOverload is false, the existing expression is shadowed by the new
   * expression.
   */
  std::vector<api::Sort> bindMutualDatatypeTypes(
      std::vector<api::DatatypeDecl>& datatypes, bool doOverload = false);

  /** make flat function type
   *
   * Returns the "flat" function type corresponding to the function taking
   * argument types "sorts" and range type "range".  A flat function type is
   * one whose range is not a function. Notice that if sorts is empty and range
   * is not a function, then this function returns range itself.
   *
   * If range is a function type, we add its function argument sorts to sorts
   * and consider its function range as the new range. For each sort S added
   * to sorts in this process, we add a new bound variable of sort S to
   * flattenVars.
   *
   * For example:
   * mkFlattenFunctionType( { Int, (-> Real Real) }, (-> Int Bool), {} ):
   * - returns the the function type (-> Int (-> Real Real) Int Bool)
   * - updates sorts to { Int, (-> Real Real), Int },
   * - updates flattenVars to { x }, where x is bound variable of type Int.
   *
   * Notice that this method performs only one level of flattening, for example,
   * mkFlattenFunctionType({ Int, (-> Real Real) }, (-> Int (-> Int Bool)), {}):
   * - returns the the function type (-> Int (-> Real Real) Int (-> Int Bool))
   * - updates sorts to { Int, (-> Real Real), Int },
   * - updates flattenVars to { x }, where x is bound variable of type Int.
   *
   * This method is required so that we do not return functions
   * that have function return type (these give an unhandled exception
   * in the ExprManager). For examples of the equivalence between function
   * definitions in the proposed higher-order extension of the smt2 language,
   * see page 3 of http://matryoshka.gforge.inria.fr/pubs/PxTP2017.pdf.
   *
   * The argument flattenVars is needed in the case of defined functions
   * with function return type. These have implicit arguments, for instance:
   *    (define-fun Q ((x Int)) (-> Int Int) (lambda y (P x)))
   * is equivalent to the command:
   *    (define-fun Q ((x Int) (z Int)) Int (@ (lambda y (P x)) z))
   * where @ is (higher-order) application. In this example, z is added to
   * flattenVars.
   */
  api::Sort mkFlatFunctionType(std::vector<api::Sort>& sorts,
                               api::Sort range,
                               std::vector<api::Term>& flattenVars);

  /** make flat function type
   *
   * Same as above, but does not take argument flattenVars.
   * This is used when the arguments of the function are not important (for
   * instance, if we are only using this type in a declare-fun).
   */
  api::Sort mkFlatFunctionType(std::vector<api::Sort>& sorts, api::Sort range);

  /** make higher-order apply
   *
   * This returns the left-associative curried application of (function) expr to
   * the arguments in args.
   *
   * For example, mkHoApply( f, { a, b }, 0 ) returns
   *  (HO_APPLY (HO_APPLY f a) b)
   *
   * If args is non-empty, the expected type of expr is (-> T0 ... Tn T), where
   *    args[i].getType() = Ti
   * for each i where 0 <= i < args.size(). If expr is not of this
   * type, the expression returned by this method will not be well typed.
   */
  api::Term mkHoApply(api::Term expr, const std::vector<api::Term>& args);

  /** Apply type ascription
   *
   * Return term t with a type ascription applied to it. This is used for
   * syntax like (as t T) in smt2 and t::T in the CVC language. This includes:
   * - (as emptyset (Set T))
   * - (as emptybag (Bag T))
   * - (as univset (Set T))
   * - (as sep.nil T)
   * - (cons T)
   * - ((as cons T) t1 ... tn) where cons is a parametric datatype constructor.
   *
   * The term to ascribe t is a term whose kind and children (but not type)
   * are equivalent to that of the term returned by this method.
   *
   * Notice that method is not necessarily a cast. In actuality, the above terms
   * should be understood as symbols indexed by types. However, SMT-LIB does not
   * permit types as indices, so we must use, e.g. (as emptyset (Set T))
   * instead of (_ emptyset (Set T)).
   *
   * @param t The term to ascribe a type
   * @param s The sort to ascribe
   * @return Term t with sort s ascribed.
   */
  api::Term applyTypeAscription(api::Term t, api::Sort s);

  /**
   * Add an operator to the current legal set.
   *
   * @param kind the built-in operator to add
   */
  void addOperator(api::Kind kind);

  /**
   * Preempt the next returned command with other ones; used to
   * support the :named attribute in SMT-LIBv2, which implicitly
   * inserts a new command before the current one. Also used in TPTP
   * because function and predicate symbols are implicitly declared.
   */
  void preemptCommand(Command* cmd);

  /** Is the symbol bound to a boolean variable? */
  bool isBoolean(const std::string& name);

  /** Is fun a function (or function-like thing)?
   * Currently this means its type is either a function, constructor, tester, or
   * selector.
   */
  bool isFunctionLike(api::Term fun);

  /** Is the symbol bound to a predicate? */
  bool isPredicate(const std::string& name);

  /** Parse and return the next command. */
  Command* nextCommand();

  /** Parse and return the next expression. */
  api::Term nextExpression();

  /** Issue a warning to the user. */
  void warning(const std::string& msg) { d_input->warning(msg); }
  /** Issue a warning to the user, but only once per attribute. */
  void attributeNotSupported(const std::string& attr);

  /** Raise a parse error with the given message. */
  inline void parseError(const std::string& msg) { d_input->parseError(msg); }
  /** Unexpectedly encountered an EOF */
  inline void unexpectedEOF(const std::string& msg)
  {
    d_input->parseError(msg, true);
  }

  /**
   * If we are parsing only, don't raise an exception; if we are not,
   * raise a parse error with the given message.  There is no actual
   * parse error, everything is as expected, but we cannot create the
   * Expr, Type, or other requested thing yet due to internal
   * limitations.  Even though it's not a parse error, we throw a
   * parse error so that the input line and column information is
   * available.
   *
   * Think quantifiers.  We don't have a TheoryQuantifiers yet, so we
   * have no kind::FORALL or kind::EXISTS.  But we might want to
   * support parsing quantifiers (just not doing anything with them).
   * So this mechanism gives you a way to do it with --parse-only.
   */
  inline void unimplementedFeature(const std::string& msg)
  {
    if(!d_parseOnly) {
      parseError("Unimplemented feature: " + msg);
    }
  }

  /**
   * Gets the current declaration level.
   */
  size_t scopeLevel() const;

  /**
   * Pushes a scope. All subsequent symbol declarations made are only valid in
   * this scope, i.e. they are deleted on the next call to popScope.
   *
   * The argument isUserContext is true, when we are pushing a user context
   * e.g. via the smt2 command (push n). This may also include one initial
   * pushScope when the parser is initialized. User-context pushes and pops
   * have an impact on both expression names and the symbol table, whereas
   * other pushes and pops only have an impact on the symbol table.
   */
  void pushScope(bool isUserContext = false);

  void popScope();

  virtual void reset();

  /** Return the symbol manager used by this parser. */
  SymbolManager* getSymbolManager();

  //------------------------ operator overloading
  /** is this function overloaded? */
  bool isOverloadedFunction(api::Term fun)
  {
    return d_symtab->isOverloadedFunction(fun);
  }

  /** Get overloaded constant for type.
   * If possible, it returns a defined symbol with name
   * that has type t. Otherwise returns null expression.
  */
  api::Term getOverloadedConstantForType(const std::string& name, api::Sort t)
  {
    return d_symtab->getOverloadedConstantForType(name, t);
  }

  /**
   * If possible, returns a defined function for a name
   * and a vector of expected argument types. Otherwise returns
   * null expression.
   */
  api::Term getOverloadedFunctionForTypes(const std::string& name,
                                          std::vector<api::Sort>& argTypes)
  {
    return d_symtab->getOverloadedFunctionForTypes(name, argTypes);
  }
  //------------------------ end operator overloading
  /**
   * Make string constant
   *
   * This makes the string constant based on the string s. This may involve
   * processing ad-hoc escape sequences (if the language is not
   * SMT-LIB 2.6 or higher), or otherwise calling the solver to construct
   * the string.
   */
  api::Term mkStringConstant(const std::string& s);

  /**
   * Make string constant from a single character in hex representation
   *
   * This makes the string constant based on the character from the strings,
   * represented as a hexadecimal code point.
   */
  api::Term mkCharConstant(const std::string& s);

  /** ad-hoc string escaping
   *
   * Returns the (internal) vector of code points corresponding to processing
   * the escape sequences in string s. This is to support string inputs that
   * do no comply with the SMT-LIB standard.
   *
   * This method handles escape sequences, including \n, \t, \v, \b, \r, \f, \a,
   * \\, \x[N] and octal escape sequences of the form \[c1]([c2]([c3])?)? where
   * c1, c2, c3 are digits from 0 to 7.
   */
  std::wstring processAdHocStringEsc(const std::string& s);
}; /* class Parser */

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__PARSER_STATE_H */

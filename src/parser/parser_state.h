/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A collection of state for use by parser implementations.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__PARSER_STATE_H
#define CVC5__PARSER__PARSER_STATE_H

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_export.h>

#include <list>
#include <memory>
#include <string>

#include "parser/api/cpp/symbol_manager.h"
#include "parser/parse_op.h"
#include "parser/parser_exception.h"
#include "parser/parser_utils.h"
#include "parser/symbol_table.h"

namespace cvc5 {
namespace parser {

class Command;

/**
 * Callback from the parser state to the parser, for command preemption
 * and error handling.
 */
class ParserStateCallback
{
 public:
  ParserStateCallback() {}
  virtual ~ParserStateCallback() {}
  /** Issue a warning to the user. */
  virtual void warning(const std::string& msg) = 0;
  /** Raise a parse error with the given message. */
  virtual void parseError(const std::string& msg) = 0;
  /** Unexpectedly encountered an EOF */
  virtual void unexpectedEOF(const std::string& msg) = 0;
};

/**
 * This class encapsulates all of the state of a parser, including the
 * name of the file, line number and column information, and in-scope
 * declarations.
 */
class CVC5_EXPORT ParserState
{
 public:
  /**
   * Create a parser state.
   *
   * @attention The parser takes "ownership" of the given
   * input and will delete it on destruction.
   *
   * @param psc The callback for implementing parser-specific methods
   * @param solver solver API object
   * @param symm reference to the symbol manager
   * @param input the parser input
   * @param strictMode whether to incorporate strict(er) compliance checks
   */
  ParserState(ParserStateCallback* psc,
              Solver* solver,
              SymbolManager* sm,
              bool strictMode = false);

  virtual ~ParserState();

  /** Get the associated solver. */
  Solver* getSolver() const;

  /** Enable semantic checks during parsing. */
  void enableChecks() { d_checksEnabled = true; }

  /** Disable semantic checks during parsing. Disabling checks may lead to
   * crashes on bad inputs. */
  void disableChecks() { d_checksEnabled = false; }

  /** Enable strict parsing, according to the language standards. */
  void enableStrictMode() { d_strictMode = true; }

  /** Disable strict parsing. Allows certain syntactic infelicities to
      pass without comment. */
  void disableStrictMode() { d_strictMode = false; }

  bool strictModeEnabled() { return d_strictMode; }

  const std::string& getForcedLogic() const;
  bool logicIsForced() const;

  /** Expose the functionality from SMT/SMT2 parsers, while making
      implementation optional by returning false by default. */
  virtual bool logicIsSet() { return false; }

  /**
   * Gets the variable currently bound to name.
   *
   * @param name the name of the variable
   * @return the variable expression
   * Only returns a variable if its name is not overloaded, returns null
   * otherwise.
   */
  Term getVariable(const std::string& name);

  /**
   * Returns the expression that name should be interpreted as, based on the
   * current binding.
   *
   * This is the same as above but where the name has been type cast to t.
   */
  virtual Term getExpressionForNameAndType(const std::string& name, Sort t);

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
  virtual bool getTesterName(Term cons, std::string& name);

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
  Kind getKindForFunction(Term fun);

  /**
   * Returns a sort, given a name.
   * @param sort_name the name to look up
   */
  Sort getSort(const std::string& sort_name);

  /**
   * Returns a (parameterized) sort, given a name and args.
   */
  virtual Sort getParametricSort(const std::string& sort_name,
                                 const std::vector<Sort>& params);

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
  void checkFunctionLike(Term fun);

  /** Create a new cvc5 variable expression of the given type.
   *
   * If a symbol with name already exists,
   *  then if doOverload is true, we create overloaded operators.
   *  else if doOverload is false, the existing expression is shadowed by the
   * new expression.
   */
  Term bindVar(const std::string& name,
               const Sort& type,
               bool doOverload = false);

  /**
   * Create a new cvc5 bound variable expression of the given type. This binds
   * the symbol name to that variable in the current scope.
   */
  Term bindBoundVar(const std::string& name, const Sort& type);
  /**
   * Create a new cvc5 bound variable expressions of the given names and types.
   * Like the method above, this binds these names to those variables in the
   * current scope.
   */
  std::vector<Term> bindBoundVars(
      std::vector<std::pair<std::string, Sort> >& sortedVarNames);

  /**
   * Create a set of new cvc5 bound variable expressions of the given type.
   *
   * For each name, if a symbol with name already exists,
   *  then if doOverload is true, we create overloaded operators.
   *  else if doOverload is false, the existing expression is shadowed by the
   * new expression.
   */
  std::vector<Term> bindBoundVars(const std::vector<std::string> names,
                                  const Sort& type);

  /** Create a new variable definition (e.g., from a let binding).
   * If a symbol with name already exists,
   *  then if doOverload is true, we create overloaded operators.
   *  else if doOverload is false, the existing expression is shadowed by the
   * new expression.
   */
  void defineVar(const std::string& name,
                 const Term& val,
                 bool doOverload = false);

  /**
   * Create a new type definition.
   *
   * @param name The name of the type
   * @param type The type that should be associated with the name
   * @param skipExisting If true, the type definition is ignored if the same
   *                     symbol has already been defined. It is assumed that
   *                     the definition is the exact same as the existing one.
   */
  void defineType(const std::string& name,
                  const Sort& type,
                  bool skipExisting = false);

  /**
   * Create a new (parameterized) type definition.
   *
   * @param name The name of the type
   * @param params The type parameters
   * @param type The type that should be associated with the name
   */
  void defineType(const std::string& name,
                  const std::vector<Sort>& params,
                  const Sort& type);

  /** Create a new type definition (e.g., from an SMT-LIBv2 define-sort). */
  void defineParameterizedType(const std::string& name,
                               const std::vector<Sort>& params,
                               const Sort& type);

  /**
   * Creates a new sort with the given name.
   */
  Sort mkSort(const std::string& name);

  /**
   * Creates a new sort constructor with the given name and arity.
   */
  Sort mkSortConstructor(const std::string& name, size_t arity);

  /**
   * Creates a new "unresolved type," used only during parsing.
   */
  Sort mkUnresolvedType(const std::string& name);

  /**
   * Creates a new unresolved (parameterized) type constructor of the given
   * arity.
   */
  Sort mkUnresolvedTypeConstructor(const std::string& name, size_t arity);
  /**
   * Creates a new unresolved (parameterized) type constructor given the type
   * parameters.
   */
  Sort mkUnresolvedTypeConstructor(const std::string& name,
                                   const std::vector<Sort>& params);

  /**
   * Creates a new unresolved (parameterized) type constructor of the given
   * arity. Calls either mkUnresolvedType or mkUnresolvedTypeConstructor
   * depending on the arity.
   */
  Sort mkUnresolvedType(const std::string& name, size_t arity);

  /**
   * Creates sorts of a list of mutually-recursive datatype declarations.
   *
   * For each symbol defined by the datatype, it checks whether the binding
   * will succeed. However, it does not actually implement the binding yet,
   * as this is only done when the command is executed.
   */
  std::vector<Sort> mkMutualDatatypeTypes(std::vector<DatatypeDecl>& datatypes);

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
  Sort mkFlatFunctionType(std::vector<Sort>& sorts,
                          Sort range,
                          std::vector<Term>& flattenVars);

  /** make flat function type
   *
   * Same as above, but does not take argument flattenVars.
   * This is used when the arguments of the function are not important (for
   * instance, if we are only using this type in a declare-fun).
   */
  Sort mkFlatFunctionType(std::vector<Sort>& sorts, Sort range);

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
  Term mkHoApply(Term expr, const std::vector<Term>& args);

  /** Apply type ascription
   *
   * Return term t with a type ascription applied to it. This is used for
   * syntax like (as t T) in smt2 and t::T in the CVC language. This includes:
   * - (as set.empty (Set T))
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
   * permit types as indices, so we must use, e.g. (as set.empty (Set T))
   * instead of (_ set.empty (Set T)).
   *
   * @param t The term to ascribe a type
   * @param s The sort to ascribe
   * @return Term t with sort s ascribed.
   */
  Term applyTypeAscription(Term t, Sort s);

  /**
   * Add an operator to the current legal set.
   *
   * @param kind the built-in operator to add
   */
  void addOperator(Kind kind);

  /** Is fun a function (or function-like thing)?
   * Currently this means its type is either a function, constructor, tester, or
   * selector.
   */
  bool isFunctionLike(Term fun);

  //-------------------- callbacks to parser
  /** Issue a warning to the user. */
  void warning(const std::string& msg);
  /** Raise a parse error with the given message. */
  void parseError(const std::string& msg);
  /** Unexpectedly encountered an EOF */
  void unexpectedEOF(const std::string& msg);
  //-------------------- end callbacks to parser
  /** Issue a warning to the user, but only once per attribute. */
  void attributeNotSupported(const std::string& attr);

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
  void unimplementedFeature(const std::string& msg)
  {
    parseError("Unimplemented feature: " + msg);
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

  /** Push scope for get-value
   *
   * This pushes a scope by a call to pushScope that binds all relevant bindings
   * required for parsing the SMT-LIB command `get-value`. This includes
   * all uninterpreted constant values in user-defined uninterpreted sorts.
   */
  void pushGetValueScope();

  void popScope();

  virtual void reset();

  /** Return the symbol manager used by this parser. */
  SymbolManager* getSymbolManager();

  //------------------------ operator overloading
  /** is this function overloaded? */
  bool isOverloadedFunction(Term fun)
  {
    return d_symtab->isOverloadedFunction(fun);
  }

  /** Get overloaded constant for type.
   * If possible, it returns a defined symbol with name
   * that has type t. Otherwise returns null expression.
   */
  Term getOverloadedConstantForType(const std::string& name, Sort t)
  {
    return d_symtab->getOverloadedConstantForType(name, t);
  }

  /**
   * If possible, returns a defined function for a name
   * and a vector of expected argument types. Otherwise returns
   * null expression.
   */
  Term getOverloadedFunctionForTypes(const std::string& name,
                                     std::vector<Sort>& argTypes)
  {
    return d_symtab->getOverloadedFunctionForTypes(name, argTypes);
  }
  //------------------------ end operator overloading

  /**
   * Make string constant from a single character in hex representation
   *
   * This makes the string constant based on the character from the strings,
   * represented as a hexadecimal code point.
   */
  Term mkCharConstant(const std::string& s);

  /**
   * Strip quotes off a string, or return a parse error otherwise.
   */
  std::string stripQuotes(const std::string& s);

 protected:
  /** The API Solver object. */
  Solver* d_solver;

 private:
  /** The callback */
  ParserStateCallback* d_psc;
  /**
   * Reference to the symbol manager, which manages the symbol table used by
   * this parser.
   */
  SymbolManager* d_symman;

  /**
   * This current symbol table used by this parser, from symbol manager.
   */
  internal::parser::SymbolTable* d_symtab;

  /** Are semantic checks enabled during parsing? */
  bool d_checksEnabled;

  /** Are we parsing in strict mode? */
  bool d_strictMode;

  /** Are we in parse-only mode? */
  bool d_parseOnly;

  /** The set of operators available in the current logic. */
  std::set<Kind> d_logicOperators;

  /** The set of attributes already warned about. */
  std::set<std::string> d_attributesWarnedAbout;

  /**
   * "Preemption commands": extra commands implied by subterms that
   * should be issued before the currently-being-parsed command is
   * issued.  Used to support SMT-LIBv2 ":named" attribute on terms.
   *
   * Owns the memory of the Commands in the queue.
   */
  std::list<Command*> d_commandQueue;
}; /* class Parser */

/** Compute the unsigned integer for a token. */
uint32_t stringToUnsigned(const std::string& str);

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__PARSER_STATE_H */

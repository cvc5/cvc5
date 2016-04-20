/*********************                                                        */
/*! \file cvc3_compat.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief CVC3 compatibility layer for CVC4
 **
 ** CVC3 compatibility layer for CVC4.  This version was derived from
 ** the following CVS revisions of the following files in CVC3.  If
 ** those files have a later revision, then this file might be out of
 ** date.  Note that this compatibility layer is not safe for use in
 ** multithreaded contexts where multiple threads are accessing this
 ** compatibility layer functionality.
 **
 ** src/include/vc.h 1.36
 ** src/include/expr.h 1.39
 ** src/include/command_line_flags.h 1.3
 ** src/include/queryresult.h 1.2
 ** src/include/formula_value.h 1.1
 **/

#include "cvc4_public.h"

#ifndef __CVC4__CVC3_COMPAT_H
#define __CVC4__CVC3_COMPAT_H

// keep the CVC3 include guard also
#if defined(_cvc3__include__vc_h_) ||                                   \
    defined(_cvc3__expr_h_) ||                                          \
    defined(_cvc3__command_line_flags_h_) ||                            \
    defined(_cvc3__include__queryresult_h_) ||                          \
    defined(_cvc3__include__formula_value_h_)

#error "A CVC3 header file was included before CVC4's cvc3_compat.h header.  Please include cvc3_compat.h rather than any CVC3 headers."

#else

// define these so the files are skipped if the user #includes them too
#define _cvc3__expr_h_
#define _cvc3__include__vc_h_
#define _cvc3__command_line_flags_h_
#define _cvc3__include__queryresult_h_
#define _cvc3__include__formula_value_h_

#include <stdlib.h>
#include <map>
#include <utility>

#include "base/exception.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/type.h"
#include "parser/parser.h"
#include "smt/smt_engine.h"
#include "util/hash.h"
#include "util/integer.h"
#include "util/rational.h"

//class CInterface;

namespace CVC3 {

const CVC4::Kind EQ = CVC4::kind::EQUAL;
const CVC4::Kind LE = CVC4::kind::LEQ;
const CVC4::Kind GE = CVC4::kind::GEQ;
const CVC4::Kind DIVIDE = CVC4::kind::DIVISION;
const CVC4::Kind BVLT = CVC4::kind::BITVECTOR_ULT;
const CVC4::Kind BVLE = CVC4::kind::BITVECTOR_ULE;
const CVC4::Kind BVGT = CVC4::kind::BITVECTOR_UGT;
const CVC4::Kind BVGE = CVC4::kind::BITVECTOR_UGE;
const CVC4::Kind BVPLUS = CVC4::kind::BITVECTOR_PLUS;
const CVC4::Kind BVSUB = CVC4::kind::BITVECTOR_SUB;
const CVC4::Kind BVCONST = CVC4::kind::CONST_BITVECTOR;
const CVC4::Kind EXTRACT = CVC4::kind::BITVECTOR_EXTRACT;
const CVC4::Kind CONCAT = CVC4::kind::BITVECTOR_CONCAT;

std::string int2string(int n) CVC4_PUBLIC;

//! Different types of command line flags
typedef enum CVC4_PUBLIC {
  CLFLAG_NULL,
  CLFLAG_BOOL,
  CLFLAG_INT,
  CLFLAG_STRING,
  CLFLAG_STRVEC //!< Vector of pair<string, bool>
} CLFlagType;

std::ostream& operator<<(std::ostream& out, CLFlagType clft) CVC4_PUBLIC;

/*!
  Class CLFlag (for Command Line Flag)

  Author: Sergey Berezin

  Date: Fri May 30 14:10:48 2003

  This class implements a data structure to hold a value of a single
  command line flag.
*/
class CVC4_PUBLIC CLFlag {
  //! Type of the argument
  CLFlagType d_tp;
  //! The argument
  union {
    bool b;
    int i;
    std::string* s;
    std::vector<std::pair<std::string,bool> >* sv;
  } d_data;

public:

  //! Constructor for a boolean flag
  CLFlag(bool b, const std::string& help, bool display = true);
  //! Constructor for an integer flag
  CLFlag(int i, const std::string& help, bool display = true);
  //! Constructor for a string flag
  CLFlag(const std::string& s, const std::string& help, bool display = true);
  //! Constructor for a string flag from char*
  CLFlag(const char* s, const std::string& help, bool display = true);
  //! Constructor for a vector flag
  CLFlag(const std::vector<std::pair<std::string,bool> >& sv,
	 const std::string& help, bool display = true);
  //! Default constructor
  CLFlag();
  //! Copy constructor
  CLFlag(const CLFlag& f);
  //! Destructor
  ~CLFlag();

  //! Assignment from another flag
  CLFlag& operator=(const CLFlag& f);
  //! Assignment of a boolean value
  /*! The flag must already have the right type */
  CLFlag& operator=(bool b);
  //! Assignment of an integer value
  /*! The flag must already have the right type */
  CLFlag& operator=(int i);
  //! Assignment of a string value
  /*! The flag must already have a string type. */
  CLFlag& operator=(const std::string& s);
  //! Assignment of an string value from char*
  /*! The flag must already have a string type. */
  CLFlag& operator=(const char* s);
  //! Assignment of a string value with a boolean tag to a vector flag
  /*! The flag must already have a vector type.  The pair of
    <string,bool> will be appended to the vector. */
  CLFlag& operator=(const std::pair<std::string,bool>& p);
  //! Assignment of a vector value
  /*! The flag must already have a vector type. */
  CLFlag& operator=(const std::vector<std::pair<std::string,bool> >& sv);

  // Accessor methods
  //! Return the type of the flag
  CLFlagType getType() const;
  /*! @brief Return true if the flag was modified from the default
    value (e.g. set on the command line) */
  bool modified() const;
  //! Return true if flag should be displayed in regular help
  bool display() const;

  // The value accessors return a reference.  For the system-wide
  // flags, this reference will remain valid throughout the run of the
  // program, even if the flag's value changes.  So, the reference can
  // be cached, and the value can be checked directly (which is more
  // efficient).
  const bool& getBool() const;

  const int& getInt() const;

  const std::string& getString() const;

  const std::vector<std::pair<std::string,bool> >& getStrVec() const;

  const std::string& getHelp() const;

};/* class CLFlag */

///////////////////////////////////////////////////////////////////////
// Class CLFlag (for Command Line Flag)
//
// Author: Sergey Berezin
// Date: Fri May 30 14:10:48 2003
//
// Database of command line flags.
///////////////////////////////////////////////////////////////////////

class CVC4_PUBLIC CLFlags {
  typedef std::map<std::string, CLFlag> FlagMap;
  FlagMap d_map;

public:
  // Public methods
  // Add a new flag.  The name must be a complete flag name.
  void addFlag(const std::string& name, const CLFlag& f);
  // Count how many flags match the name prefix
  size_t countFlags(const std::string& name) const;
  // Match the name prefix and add all the matching names to the vector
  size_t countFlags(const std::string& name,
		    std::vector<std::string>& names) const;
  // Retrieve an existing flag.  The 'name' must be a full name of an
  // existing flag.
  const CLFlag& getFlag(const std::string& name) const;

  const CLFlag& operator[](const std::string& name) const;

  // Setting the flag to a new value, but preserving the help string.
  // The 'name' prefix must uniquely resolve to an existing flag.
  void setFlag(const std::string& name, const CLFlag& f);

  // Variants of setFlag for all the types
  void setFlag(const std::string& name, bool b);
  void setFlag(const std::string& name, int i);
  void setFlag(const std::string& name, const std::string& s);
  void setFlag(const std::string& name, const char* s);
  void setFlag(const std::string& name, const std::pair<std::string, bool>& p);
  void setFlag(const std::string& name,
	       const std::vector<std::pair<std::string, bool> >& sv);

};/* class CLFlags */

class CVC4_PUBLIC ExprManager;
class CVC4_PUBLIC Context;
class CVC4_PUBLIC Proof {};
class CVC4_PUBLIC Theorem {};

using CVC4::InputLanguage;
using CVC4::Integer;
using CVC4::Rational;
using CVC4::Exception;
using CVC4::Cardinality;
using namespace CVC4::kind;

typedef size_t ExprIndex;
typedef CVC4::TypeCheckingException TypecheckException;
typedef size_t Unsigned;

static const int READ = ::CVC4::kind::SELECT;
static const int WRITE = ::CVC4::kind::STORE;

// CVC4 has a more sophisticated Cardinality type;
// but we can support comparison against CVC3's more
// coarse-grained Cardinality.
enum CVC4_PUBLIC CVC3CardinalityKind {
  CARD_FINITE,
  CARD_INFINITE,
  CARD_UNKNOWN
};/* enum CVC3CardinalityKind */

std::ostream& operator<<(std::ostream& out, CVC3CardinalityKind c) CVC4_PUBLIC;

bool operator==(const Cardinality& c, CVC3CardinalityKind d) CVC4_PUBLIC;
bool operator==(CVC3CardinalityKind d, const Cardinality& c) CVC4_PUBLIC;
bool operator!=(const Cardinality& c, CVC3CardinalityKind d) CVC4_PUBLIC;
bool operator!=(CVC3CardinalityKind d, const Cardinality& c) CVC4_PUBLIC;

class CVC4_PUBLIC Expr;

template <class T>
class CVC4_PUBLIC ExprMap : public std::map<Expr, T> {
};/* class ExprMap<T> */

template <class T>
class CVC4_PUBLIC ExprHashMap : public std::hash_map<Expr, T, CVC4::ExprHashFunction> {
public:
  void insert(Expr a, Expr b);
};/* class ExprHashMap<T> */

class CVC4_PUBLIC Type : public CVC4::Type {
public:
  Type();
  Type(const CVC4::Type& type);
  Type(const Type& type);
  Expr getExpr() const;

  // Reasoning about children
  int arity() const;
  Type operator[](int i) const;

  // Core testers
  bool isBool() const;
  bool isSubtype() const;
  //! Return cardinality of type
  Cardinality card() const;
  //! Return nth (starting with 0) element in a finite type
  /*! Returns NULL Expr if unable to compute nth element
   */
  Expr enumerateFinite(Unsigned n) const;
  //! Return size of a finite type; returns 0 if size cannot be determined
  Unsigned sizeFinite() const;

  // Core constructors
  static Type typeBool(ExprManager* em);
  static Type funType(const std::vector<Type>& typeDom, const Type& typeRan);
  Type funType(const Type& typeRan) const;

};/* class CVC3::Type */

class CVC4_PUBLIC Expr;
typedef Expr Op;

/**
 * Expr class for CVC3 compatibility layer.
 *
 * This class is identical to (and convertible to/from) a CVC4 Expr,
 * except that a few additional functions are supported to provide
 * naming compatibility with CVC3.
 */
class CVC4_PUBLIC Expr : public CVC4::Expr {
public:
  typedef CVC4::Expr::const_iterator iterator;

  Expr();
  Expr(const Expr& e);
  Expr(const CVC4::Expr& e);
  Expr(CVC4::Kind k);

  // Compound expression constructors
  Expr eqExpr(const Expr& right) const;
  Expr notExpr() const;
  Expr negate() const; // avoid double-negatives
  Expr andExpr(const Expr& right) const;
  Expr orExpr(const Expr& right) const;
  Expr iteExpr(const Expr& thenpart, const Expr& elsepart) const;
  Expr iffExpr(const Expr& right) const;
  Expr impExpr(const Expr& right) const;
  Expr xorExpr(const Expr& right) const;

  Expr substExpr(const std::vector<Expr>& oldTerms,
                 const std::vector<Expr>& newTerms) const;
  Expr substExpr(const ExprHashMap<Expr>& oldToNew) const;

  Expr operator!() const;
  Expr operator&&(const Expr& right) const;
  Expr operator||(const Expr& right) const;

  static size_t hash(const Expr& e);

  size_t hash() const;

  // Core expression testers

  bool isFalse() const;
  bool isTrue() const;
  bool isBoolConst() const;
  bool isVar() const;
  bool isBoundVar() const;
  bool isString() const;
  bool isSymbol() const;
  bool isTerm() const;
  bool isType() const;
  bool isClosure() const;
  bool isQuantifier() const;
  bool isForall() const;
  bool isExists() const;
  bool isLambda() const;
  bool isApply() const;
  bool isTheorem() const;
  bool isConstant() const;
  bool isRawList() const;

  bool isAtomic() const;
  bool isAtomicFormula() const;
  bool isAbsAtomicFormula() const;
  bool isLiteral() const;
  bool isAbsLiteral() const;
  bool isBoolConnective() const;
  bool isPropLiteral() const;
  bool isPropAtom() const;

  std::string getName() const;
  std::string getUid() const;

  std::string getString() const;
  std::vector<Expr> getVars() const;
  Expr getExistential() const;
  int getBoundIndex() const;
  Expr getBody() const;
  Theorem getTheorem() const;

  bool isEq() const;
  bool isNot() const;
  bool isAnd() const;
  bool isOr() const;
  bool isITE() const;
  bool isIff() const;
  bool isImpl() const;
  bool isXor() const;

  bool isRational() const;
  bool isSkolem() const;

  const Rational& getRational() const;

  Op mkOp() const;
  Op getOp() const;
  Expr getOpExpr() const;
  int getOpKind() const;
  Expr getExpr() const;// since people are used to doing getOp().getExpr() in CVC3

  //! Get the manual triggers of the closure Expr
  std::vector< std::vector<Expr> > getTriggers() const;

  // Get the expression manager.  The expression must be non-null.
  ExprManager* getEM() const;

  // Return a ref to the vector of children.
  std::vector<Expr> getKids() const;

  // Get the index field
  ExprIndex getIndex() const;

  // Return the number of children.  Note, that an application of a
  // user-defined function has the arity of that function (the number
  // of arguments), and the function name itself is part of the
  // operator.
  int arity() const;

  // Return the ith child.  As with arity, it's also the ith argument
  // in function application.
  Expr operator[](int i) const;

  //! Remove leading NOT if any
  Expr unnegate() const;

  // Check if Expr is not Null
  bool isInitialized() const;

  //! Get the type.  Recursively compute if necessary
  Type getType() const;
  //! Look up the current type. Do not recursively compute (i.e. may be NULL)
  Type lookupType() const;

  //! Pretty-print the expression
  void pprint() const;
  //! Pretty-print without dagifying
  void pprintnodag() const;

};/* class CVC3::Expr */

bool isArrayLiteral(const Expr&) CVC4_PUBLIC;

class CVC4_PUBLIC ExprManager : public CVC4::ExprManager {
public:
  std::string getKindName(int kind);
  //! Get the input language for printing
  InputLanguage getInputLang() const;
  //! Get the output language for printing
  InputLanguage getOutputLang() const;
};/* class CVC3::ExprManager */

typedef CVC4::Statistics Statistics;

#define PRESENTATION_LANG ::CVC4::language::input::LANG_CVC4
#define SMTLIB_LANG ::CVC4::language::input::LANG_SMTLIB_V1
#define SMTLIB_V2_LANG ::CVC4::language::input::LANG_SMTLIB_V2
#define TPTP_LANG ::CVC4::language::input::LANG_TPTP
#define AST_LANG ::CVC4::language::input::LANG_AST

/*****************************************************************************/
/*
 * Type for result of queries.  VALID and UNSATISFIABLE are treated as
 * equivalent, as are SATISFIABLE and INVALID.
 */
/*****************************************************************************/
typedef enum CVC4_PUBLIC QueryResult {
  SATISFIABLE = 0,
  INVALID = 0,
  VALID = 1,
  UNSATISFIABLE = 1,
  ABORT,
  UNKNOWN
} QueryResult;

std::ostream& operator<<(std::ostream& out, QueryResult qr);
std::string QueryResultToString(QueryResult query_result);

/*****************************************************************************/
/*
 * Type for truth value of formulas.
 */
/*****************************************************************************/
typedef enum CVC4_PUBLIC FormulaValue {
  TRUE_VAL,
  FALSE_VAL,
  UNKNOWN_VAL
} FormulaValue;

std::ostream& operator<<(std::ostream& out, FormulaValue fv) CVC4_PUBLIC;

/*****************************************************************************/
/*!
 *\class ValidityChecker
 *\brief CVC3 API (compatibility layer for CVC4)
 *
 * All terms and formulas are represented as expressions using the Expr class.
 * The notion of a context is also important.  A context is a "background" set
 * of formulas which are assumed to be true or false.  Formulas can be added to
 * the context explicitly, using assertFormula, or they may be added as part of
 * processing a query command.  At any time, the current set of formulas making
 * up the context can be retrieved using getAssumptions.
 */
/*****************************************************************************/
class CVC4_PUBLIC ValidityChecker {

  CLFlags* d_clflags;
  CVC4::Options d_options;
  CVC3::ExprManager* d_em;
  std::map<CVC4::ExprManager*, CVC4::ExprManagerMapCollection> d_emmc;
  std::set<ValidityChecker*> d_reverseEmmc;
  CVC4::SmtEngine* d_smt;
  CVC4::parser::Parser* d_parserContext;
  std::vector<Expr> d_exprTypeMapRemove;
  unsigned d_stackLevel;

  friend class Type; // to reach in to d_exprTypeMapRemove

  typedef std::hash_map<std::string, const CVC4::Datatype*, CVC4::StringHashFunction> ConstructorMap;
  typedef std::hash_map<std::string, std::pair<const CVC4::Datatype*, std::string>, CVC4::StringHashFunction> SelectorMap;

  ConstructorMap d_constructors;
  SelectorMap d_selectors;

  ValidityChecker(const CLFlags& clflags);

  void setUpOptions(CVC4::Options& options, const CLFlags& clflags);

  // helper function for bitvectors
  Expr bvpad(int len, const Expr& e);

public:
  //! Constructor
  ValidityChecker();
  //! Destructor
  virtual ~ValidityChecker();

  //! Return the set of command-line flags
  /*!  The flags are returned by reference, and if modified, will have an
    immediate effect on the subsequent commands.  Note that not all flags will
    have such an effect; some flags are used only at initialization time (like
    "sat"), and therefore, will not take effect if modified after
    ValidityChecker is created.
  */
  virtual CLFlags& getFlags() const;
  //! Force reprocessing of all flags
  virtual void reprocessFlags();

  /***************************************************************************/
  /*
   * Static methods
   */
  /***************************************************************************/

  //! Create the set of command line flags with default values;
  /*!
    \return the set of flags by value
  */
  static CLFlags createFlags();
  //! Create an instance of ValidityChecker
  /*!
    \param flags is the set of command line flags.
  */
  static ValidityChecker* create(const CLFlags& flags);
  //! Create an instance of ValidityChecker using default flag values.
  static ValidityChecker* create();

  /***************************************************************************/
  /*!
   *\name Type-related methods
   * Methods for creating and looking up types
   *\sa class Type
   *@{
   */
  /***************************************************************************/

  // Basic types
  virtual Type boolType(); //!< Create type BOOLEAN

  virtual Type realType(); //!< Create type REAL

  virtual Type intType(); //!< Create type INT

  //! Create a subrange type [l..r]
  /*! l and r can be Null; l=Null represents minus infinity, r=Null is
   * plus infinity.
   */
  virtual Type subrangeType(const Expr& l, const Expr& r);

  //! Creates a subtype defined by the given predicate
  /*!
   * \param pred is a predicate taking one argument of type T and returning
   * Boolean.  The resulting type is a subtype of T whose elements x are those
   * satisfying the predicate pred(x).
   *
   * \param witness is an expression of type T for which pred holds (if a Null
   *  expression is passed as a witness, cvc will try to prove \f$\exists x. pred(x))\f$.
   *  if the witness check fails, a TypecheckException is thrown.
   */
  virtual Type subtypeType(const Expr& pred, const Expr& witness);

  // Tuple types
  //! 2-element tuple
  virtual Type tupleType(const Type& type0, const Type& type1);

  //! 3-element tuple
  virtual Type tupleType(const Type& type0, const Type& type1,
			 const Type& type2);
  //! n-element tuple (from a vector of types)
  virtual Type tupleType(const std::vector<Type>& types);

  // Record types
  //! 1-element record
  virtual Type recordType(const std::string& field, const Type& type);

  //! 2-element record
  /*! Fields will be sorted automatically */
  virtual Type recordType(const std::string& field0, const Type& type0,
			  const std::string& field1, const Type& type1);
  //! 3-element record
  /*! Fields will be sorted automatically */
  virtual Type recordType(const std::string& field0, const Type& type0,
			  const std::string& field1, const Type& type1,
			  const std::string& field2, const Type& type2);
  //! n-element record (fields and types must be of the same length)
  /*! Fields will be sorted automatically */
  virtual Type recordType(const std::vector<std::string>& fields,
			  const std::vector<Type>& types);

  // Datatypes

  //! Single datatype, single constructor
  /*! The types are either type exressions (obtained from a type with
   *  getExpr()) or string expressions containing the name of (one of) the
   *  dataType(s) being defined. */
  virtual Type dataType(const std::string& name,
                        const std::string& constructor,
                        const std::vector<std::string>& selectors,
                        const std::vector<Expr>& types);

  //! Single datatype, multiple constructors
  /*! The types are either type exressions (obtained from a type with
   *  getExpr()) or string expressions containing the name of (one of) the
   *  dataType(s) being defined. */
  virtual Type dataType(const std::string& name,
                        const std::vector<std::string>& constructors,
                        const std::vector<std::vector<std::string> >& selectors,
                        const std::vector<std::vector<Expr> >& types);

  //! Multiple datatypes
  /*! The types are either type exressions (obtained from a type with
   *  getExpr()) or string expressions containing the name of (one of) the
   *  dataType(s) being defined. */
  virtual void dataType(const std::vector<std::string>& names,
                        const std::vector<std::vector<std::string> >& constructors,
                        const std::vector<std::vector<std::vector<std::string> > >& selectors,
                        const std::vector<std::vector<std::vector<Expr> > >& types,
                        std::vector<Type>& returnTypes);

  //! Create an array type (ARRAY typeIndex OF typeData)
  virtual Type arrayType(const Type& typeIndex, const Type& typeData);

  //! Create a bitvector type of length n
  virtual Type bitvecType(int n);

  //! Create a function type typeDom -> typeRan
  virtual Type funType(const Type& typeDom, const Type& typeRan);

  //! Create a function type (t1,t2,...,tn) -> typeRan
  virtual Type funType(const std::vector<Type>& typeDom, const Type& typeRan);

  //! Create named user-defined uninterpreted type
  virtual Type createType(const std::string& typeName);

  //! Create named user-defined interpreted type (type abbreviation)
  virtual Type createType(const std::string& typeName, const Type& def);

  //! Lookup a user-defined (uninterpreted) type by name.  Returns Null if none.
  virtual Type lookupType(const std::string& typeName);

  /*@}*/ // End of Type-related methods

  /***************************************************************************/
  /*!
   *\name General Expr methods
   *\sa class Expr
   *\sa class ExprManager
   *@{
   */
  /***************************************************************************/

  //! Return the ExprManager
  virtual ExprManager* getEM();

  //! Create a variable with a given name and type
  /*!
    \param name is the name of the variable
    \param type is its type.  The type cannot be a function type.
    \return an Expr representation of a new variable
   */
  virtual Expr varExpr(const std::string& name, const Type& type);

  //! Create a variable with a given name, type, and value
  virtual Expr varExpr(const std::string& name, const Type& type,
		       const Expr& def);

  //! Get the variable associated with a name, and its type
  /*!
    \param name is the variable name
    \param type is where the type value is returned

    \return a variable by the name. If there is no such Expr, a NULL \
    Expr is returned.
  */
  virtual Expr lookupVar(const std::string& name, Type* type);

  //! Get the type of the Expr.
  virtual Type getType(const Expr& e);

  //! Get the largest supertype of the Expr.
  virtual Type getBaseType(const Expr& e);

  //! Get the largest supertype of the Type.
  virtual Type getBaseType(const Type& t);

  //! Get the subtype predicate
  virtual Expr getTypePred(const Type&t, const Expr& e);

  //! Create a string Expr
  virtual Expr stringExpr(const std::string& str);

  //! Create an ID Expr
  virtual Expr idExpr(const std::string& name);

  //! Create a list Expr
  /*! Intermediate representation for DP-specific expressions.
   *  Normally, the first element of the list is a string Expr
   *  representing an operator, and the rest of the list are the
   *  arguments.  For example,
   *
   *  kids.push_back(vc->stringExpr("PLUS"));
   *  kids.push_back(x); // x and y are previously created Exprs
   *  kids.push_back(y);
   *  Expr lst = vc->listExpr(kids);
   *
   * Or, alternatively (using its overloaded version):
   *
   * Expr lst = vc->listExpr("PLUS", x, y);
   *
   * or
   *
   * vector<Expr> summands;
   * summands.push_back(x); summands.push_back(y); ...
   * Expr lst = vc->listExpr("PLUS", summands);
   */
  virtual Expr listExpr(const std::vector<Expr>& kids);

  //! Overloaded version of listExpr with one argument
  virtual Expr listExpr(const Expr& e1);

  //! Overloaded version of listExpr with two arguments
  virtual Expr listExpr(const Expr& e1, const Expr& e2);

  //! Overloaded version of listExpr with three arguments
  virtual Expr listExpr(const Expr& e1, const Expr& e2, const Expr& e3);

  //! Overloaded version of listExpr with string operator and many arguments
  virtual Expr listExpr(const std::string& op,
			const std::vector<Expr>& kids);

  //! Overloaded version of listExpr with string operator and one argument
  virtual Expr listExpr(const std::string& op, const Expr& e1);

  //! Overloaded version of listExpr with string operator and two arguments
  virtual Expr listExpr(const std::string& op, const Expr& e1,
			const Expr& e2);

  //! Overloaded version of listExpr with string operator and three arguments
  virtual Expr listExpr(const std::string& op, const Expr& e1,
			const Expr& e2, const Expr& e3);

  //! Prints e to the standard output
  virtual void printExpr(const Expr& e);

  //! Prints e to the given ostream
  virtual void printExpr(const Expr& e, std::ostream& os);

  //! Parse an expression using a Theory-specific parser
  virtual Expr parseExpr(const Expr& e);

  //! Parse a type expression using a Theory-specific parser
  virtual Type parseType(const Expr& e);

  //! Import the Expr from another instance of ValidityChecker
  /*! When expressions need to be passed among several instances of
   *  ValidityChecker, they need to be explicitly imported into the
   *  corresponding instance using this method.  The return result is
   *  an identical expression that belongs to the current instance of
   *  ValidityChecker, and can be safely used as part of more complex
   *  expressions from the same instance.
   */
  virtual Expr importExpr(const Expr& e);

  //! Import the Type from another instance of ValidityChecker
  /*! \sa getType() */
  virtual Type importType(const Type& t);

  //! Parse a sequence of commands from a presentation language string
  virtual void cmdsFromString(const std::string& s,
                              InputLanguage lang = PRESENTATION_LANG);

  //! Parse an expression from a presentation language string
  /*! Only PRESENTATION_LANG and SMTLIB_V2_LANG are supported. Any other
   *  value for lang will raise an exception.
   */
  virtual Expr exprFromString(const std::string& e,
                              InputLanguage lang = PRESENTATION_LANG);

  /*@}*/ // End of General Expr Methods

  /***************************************************************************/
  /*!
   *\name Core expression methods
   * Methods for manipulating core expressions
   *
   * Except for equality and ite, the children provided as arguments must be of
   * type Boolean.
   *@{
   */
  /***************************************************************************/

  //! Return TRUE Expr
  virtual Expr trueExpr();

  //! Return FALSE Expr
  virtual Expr falseExpr();

  //! Create negation
  virtual Expr notExpr(const Expr& child);

  //! Create 2-element conjunction
  virtual Expr andExpr(const Expr& left, const Expr& right);

  //! Create n-element conjunction
  virtual Expr andExpr(const std::vector<Expr>& children);

  //! Create 2-element disjunction
  virtual Expr orExpr(const Expr& left, const Expr& right);

  //! Create n-element disjunction
  virtual Expr orExpr(const std::vector<Expr>& children);

  //! Create Boolean implication
  virtual Expr impliesExpr(const Expr& hyp, const Expr& conc);

  //! Create left IFF right (boolean equivalence)
  virtual Expr iffExpr(const Expr& left, const Expr& right);

  //! Create an equality expression.
  /*!
    The two children must have the same type, and cannot be of type
    Boolean.
  */
  virtual Expr eqExpr(const Expr& child0, const Expr& child1);

  //! Create IF ifpart THEN thenpart ELSE elsepart ENDIF
  /*!
    \param ifpart must be of type Boolean.
    \param thenpart and \param elsepart must have the same type, which will
    also be the type of the ite expression.
  */
  virtual Expr iteExpr(const Expr& ifpart, const Expr& thenpart,
		       const Expr& elsepart);

  /**
   * Create an expression asserting that all the children are different.
   * @param children the children to be asserted different
   */
  virtual Expr distinctExpr(const std::vector<Expr>& children);

  /*@}*/ // End of Core expression methods

  /***************************************************************************/
  /*!
   *\name User-defined (uninterpreted) function methods
   * Methods for manipulating uninterpreted function expressions
   *@{
   */
  /***************************************************************************/

  //! Create a named uninterpreted function with a given type
  /*!
    \param name is the new function's name (as ID Expr)
    \param type is a function type ( [range -> domain] )
  */
  virtual Op createOp(const std::string& name, const Type& type);

  //! Create a named user-defined function with a given type
  virtual Op createOp(const std::string& name, const Type& type,
		      const Expr& def);

  //! Get the Op associated with a name, and its type
  /*!
    \param name is the operator name
    \param type is where the type value is returned

    \return an Op by the name. If there is no such Op, a NULL \
    Op is returned.
  */
  virtual Op lookupOp(const std::string& name, Type* type);

  //! Unary function application (op must be of function type)
  virtual Expr funExpr(const Op& op, const Expr& child);

  //! Binary function application (op must be of function type)
  virtual Expr funExpr(const Op& op, const Expr& left, const Expr& right);

  //! Ternary function application (op must be of function type)
  virtual Expr funExpr(const Op& op, const Expr& child0,
		       const Expr& child1, const Expr& child2);

  //! n-ary function application (op must be of function type)
  virtual Expr funExpr(const Op& op, const std::vector<Expr>& children);

  /*@}*/ // End of User-defined (uninterpreted) function methods

  /***************************************************************************/
  /*!
   *\name Arithmetic expression methods
   * Methods for manipulating arithmetic expressions
   *
   * These functions create arithmetic expressions.  The children provided
   * as arguments must be of type Real.
   *@{
   */
  /***************************************************************************/

  /*!
   * Add the pair of variables to the variable ordering for aritmetic solving.
   * Terms that are not arithmetic will be ignored.
   * \param smaller the smaller variable
   * \param bigger the bigger variable
   */
  virtual bool addPairToArithOrder(const Expr& smaller, const Expr& bigger);

  //! Create a rational number with numerator n and denominator d.
  /*!
    \param n the numerator
    \param d the denominator, cannot be 0.
  */
  virtual Expr ratExpr(int n, int d = 1);

  //! Create a rational number with numerator n and denominator d.
  /*!
    Here n and d are given as strings.  They are converted to
    arbitrary-precision integers according to the given base.
  */
  virtual Expr ratExpr(const std::string& n, const std::string& d, int base);

  //! Create a rational from a single string.
  /*!
    \param n can be a string containing an integer, a pair of integers
    "nnn/ddd", or a number in the fixed or floating point format.
    \param base is the base in which to interpret the string.
  */
  virtual Expr ratExpr(const std::string& n, int base = 10);

  //! Unary minus.
  virtual Expr uminusExpr(const Expr& child);

  //! Create 2-element sum (left + right)
  virtual Expr plusExpr(const Expr& left, const Expr& right);

  //! Create n-element sum
  virtual Expr plusExpr(const std::vector<Expr>& children);

  //! Make a difference (left - right)
  virtual Expr minusExpr(const Expr& left, const Expr& right);

  //! Create a product (left * right)
  virtual Expr multExpr(const Expr& left, const Expr& right);

  //! Create a power expression (x ^ n); n must be integer
  virtual Expr powExpr(const Expr& x, const Expr& n);

  //! Create expression x / y
  virtual Expr divideExpr(const Expr& numerator, const Expr& denominator);

  //! Create (left < right)
  virtual Expr ltExpr(const Expr& left, const Expr& right);

  //! Create (left <= right)
  virtual Expr leExpr(const Expr& left, const Expr& right);

  //! Create (left > right)
  virtual Expr gtExpr(const Expr& left, const Expr& right);

  //! Create (left >= right)
  virtual Expr geExpr(const Expr& left, const Expr& right);

  /*@}*/ // End of Arithmetic expression methods

  /***************************************************************************/
  /*!
   *\name Record expression methods
   * Methods for manipulating record expressions
   *@{
   */
  /***************************************************************************/

  //! Create a 1-element record value (# field := expr #)
  /*! Fields will be sorted automatically */
  virtual Expr recordExpr(const std::string& field, const Expr& expr);

  //! Create a 2-element record value (# field0 := expr0, field1 := expr1 #)
  /*! Fields will be sorted automatically */
  virtual Expr recordExpr(const std::string& field0, const Expr& expr0,
			  const std::string& field1, const Expr& expr1);

  //! Create a 3-element record value (# field_i := expr_i #)
  /*! Fields will be sorted automatically */
  virtual Expr recordExpr(const std::string& field0, const Expr& expr0,
			  const std::string& field1, const Expr& expr1,
			  const std::string& field2, const Expr& expr2);

  //! Create an n-element record value (# field_i := expr_i #)
  /*!
   * \param fields
   * \param exprs must be the same length as fields
   *
   * Fields will be sorted automatically
   */
  virtual Expr recordExpr(const std::vector<std::string>& fields,
			  const std::vector<Expr>& exprs);

  //! Create record.field (field selection)
  /*! Create an expression representing the selection of a field from
    a record. */
  virtual Expr recSelectExpr(const Expr& record, const std::string& field);

  //! Record update; equivalent to "record WITH .field := newValue"
  /*! Notice the `.' before field in the presentation language (and
    the comment above); this is to distinguish it from datatype
    update.
  */
  virtual Expr recUpdateExpr(const Expr& record, const std::string& field,
			     const Expr& newValue);

  /*@}*/ // End of Record expression methods

  /***************************************************************************/
  /*!
   *\name Array expression methods
   * Methods for manipulating array expressions
   *@{
   */
  /***************************************************************************/

  //! Create an expression array[index] (array access)
  /*! Create an expression for the value of array at the given index */
  virtual Expr readExpr(const Expr& array, const Expr& index);

  //! Array update; equivalent to "array WITH index := newValue"
  virtual Expr writeExpr(const Expr& array, const Expr& index,
			 const Expr& newValue);

  /*@}*/ // End of Array expression methods

  /***************************************************************************/
  /*!
   *\name Bitvector expression methods
   * Methods for manipulating bitvector expressions
   *@{
   */
  /***************************************************************************/

  // Bitvector constants
  // From a string of digits in a given base
  virtual Expr newBVConstExpr(const std::string& s, int base = 2);
  // From a vector of bools
  virtual Expr newBVConstExpr(const std::vector<bool>& bits);
  // From a rational: bitvector is of length 'len', or the min. needed length when len=0.
  virtual Expr newBVConstExpr(const Rational& r, int len = 0);

  // Concat and extract
  virtual Expr newConcatExpr(const Expr& t1, const Expr& t2);
  virtual Expr newConcatExpr(const std::vector<Expr>& kids);
  virtual Expr newBVExtractExpr(const Expr& e, int hi, int low);

  // Bitwise Boolean operators: Negation, And, Nand, Or, Nor, Xor, Xnor
  virtual Expr newBVNegExpr(const Expr& t1);

  virtual Expr newBVAndExpr(const Expr& t1, const Expr& t2);
  virtual Expr newBVAndExpr(const std::vector<Expr>& kids);

  virtual Expr newBVOrExpr(const Expr& t1, const Expr& t2);
  virtual Expr newBVOrExpr(const std::vector<Expr>& kids);

  virtual Expr newBVXorExpr(const Expr& t1, const Expr& t2);
  virtual Expr newBVXorExpr(const std::vector<Expr>& kids);

  virtual Expr newBVXnorExpr(const Expr& t1, const Expr& t2);
  virtual Expr newBVXnorExpr(const std::vector<Expr>& kids);

  virtual Expr newBVNandExpr(const Expr& t1, const Expr& t2);
  virtual Expr newBVNorExpr(const Expr& t1, const Expr& t2);
  virtual Expr newBVCompExpr(const Expr& t1, const Expr& t2);

  // Unsigned bitvector inequalities
  virtual Expr newBVLTExpr(const Expr& t1, const Expr& t2);
  virtual Expr newBVLEExpr(const Expr& t1, const Expr& t2);

  // Signed bitvector inequalities
  virtual Expr newBVSLTExpr(const Expr& t1, const Expr& t2);
  virtual Expr newBVSLEExpr(const Expr& t1, const Expr& t2);

  // Sign-extend t1 to a total of len bits
  virtual Expr newSXExpr(const Expr& t1, int len);

  // Bitvector arithmetic: unary minus, plus, subtract, multiply
  virtual Expr newBVUminusExpr(const Expr& t1);
  virtual Expr newBVSubExpr(const Expr& t1, const Expr& t2);
  //! 'numbits' is the number of bits in the result
  virtual Expr newBVPlusExpr(int numbits, const std::vector<Expr>& k);
  virtual Expr newBVPlusExpr(int numbits, const Expr& t1, const Expr& t2);
  virtual Expr newBVMultExpr(int numbits,
                             const Expr& t1, const Expr& t2);

  virtual Expr newBVUDivExpr(const Expr& t1, const Expr& t2);
  virtual Expr newBVURemExpr(const Expr& t1, const Expr& t2);
  virtual Expr newBVSDivExpr(const Expr& t1, const Expr& t2);
  virtual Expr newBVSRemExpr(const Expr& t1, const Expr& t2);
  virtual Expr newBVSModExpr(const Expr& t1, const Expr& t2);

  // Left shift by r bits: result is old size + r bits
  virtual Expr newFixedLeftShiftExpr(const Expr& t1, int r);
  // Left shift by r bits: result is same size as t1
  virtual Expr newFixedConstWidthLeftShiftExpr(const Expr& t1, int r);
  // Logical right shift by r bits: result is same size as t1
  virtual Expr newFixedRightShiftExpr(const Expr& t1, int r);
  // Left shift with shift parameter an arbitrary bit-vector expr
  virtual Expr newBVSHL(const Expr& t1, const Expr& t2);
  // Logical right shift with shift parameter an arbitrary bit-vector expr
  virtual Expr newBVLSHR(const Expr& t1, const Expr& t2);
  // Arithmetic right shift with shift parameter an arbitrary bit-vector expr
  virtual Expr newBVASHR(const Expr& t1, const Expr& t2);
  // Get value of BV Constant
  virtual Rational computeBVConst(const Expr& e);

  /*@}*/ // End of Bitvector expression methods

  /***************************************************************************/
  /*!
   *\name Other expression methods
   * Methods for manipulating other kinds of expressions
   *@{
   */
  /***************************************************************************/

  //! Tuple expression
  virtual Expr tupleExpr(const std::vector<Expr>& exprs);

  //! Tuple select; equivalent to "tuple.n", where n is an numeral (e.g. tup.5)
  virtual Expr tupleSelectExpr(const Expr& tuple, int index);

  //! Tuple update; equivalent to "tuple WITH index := newValue"
  virtual Expr tupleUpdateExpr(const Expr& tuple, int index,
			       const Expr& newValue);

  //! Datatype constructor expression
  virtual Expr datatypeConsExpr(const std::string& constructor, const std::vector<Expr>& args);

  //! Datatype selector expression
  virtual Expr datatypeSelExpr(const std::string& selector, const Expr& arg);

  //! Datatype tester expression
  virtual Expr datatypeTestExpr(const std::string& constructor, const Expr& arg);

  //! Create a bound variable with a given name, unique ID (uid) and type
  /*!
    \param name is the name of the variable
    \param uid is the unique ID (a string), which must be unique for
    each variable
    \param type is its type.  The type cannot be a function type.
    \return an Expr representation of a new variable
   */
  virtual Expr boundVarExpr(const std::string& name,
			    const std::string& uid,
			    const Type& type);

  //! Universal quantifier
  virtual Expr forallExpr(const std::vector<Expr>& vars, const Expr& body);
  //! Universal quantifier with a trigger
  virtual Expr forallExpr(const std::vector<Expr>& vars, const Expr& body, 
                          const Expr& trigger);
  //! Universal quantifier with a set of triggers.
  virtual Expr forallExpr(const std::vector<Expr>& vars, const Expr& body,
                          const std::vector<Expr>& triggers);
  //! Universal quantifier with a set of multi-triggers.
  virtual Expr forallExpr(const std::vector<Expr>& vars, const Expr& body,
			  const std::vector<std::vector<Expr> >& triggers);

  //! Set triggers for quantifier instantiation
  /*!
   * \param e the expression for which triggers are being set.
   * \param triggers Each item in triggers is a vector of Expr containing one
   * or more patterns.  A pattern is a term or Atomic predicate sub-expression
   * of e.  A vector containing more than one pattern is treated as a
   * multi-trigger.  Patterns will be matched in the order they occur in
   * the vector.
  */
  virtual void setTriggers(const Expr& e, const std::vector<std::vector<Expr> > & triggers);
  //! Set triggers for quantifier instantiation (no multi-triggers)
  virtual void setTriggers(const Expr& e, const std::vector<Expr>& triggers);
  //! Set a single trigger for quantifier instantiation
  virtual void setTrigger(const Expr& e, const Expr& trigger);
  //! Set a single multi-trigger for quantifier instantiation
  virtual void setMultiTrigger(const Expr& e, const std::vector<Expr>& multiTrigger);

  //! Existential quantifier
  virtual Expr existsExpr(const std::vector<Expr>& vars, const Expr& body);

  //! Lambda-expression
  virtual Op lambdaExpr(const std::vector<Expr>& vars, const Expr& body);

  //! Transitive closure of a binary predicate
  virtual Op transClosure(const Op& op);

  //! Symbolic simulation expression
  /*!
   * \param f is the next state function (LAMBDA-expression)
   * \param s0 is the initial state
   * \param inputs is the vector of LAMBDA-expressions representing
   * the sequences of inputs to f
   * \param n is a constant, the number of cycles to run the simulation.
   */
  virtual Expr simulateExpr(const Expr& f, const Expr& s0,
			    const std::vector<Expr>& inputs,
			    const Expr& n);

  /*@}*/ // End of Other expression methods

  /***************************************************************************/
  /*!
   *\name Validity checking methods
   * Methods related to validity checking
   *
   * This group includes methods for asserting formulas, checking
   * validity in the given logical context, manipulating the scope
   * level of the context, etc.
   *@{
   */
  /***************************************************************************/

  //! Set the resource limit (0==unlimited, 1==exhausted).
  /*! Currently, the limit is the total number of processed facts. */
  virtual void setResourceLimit(unsigned limit);

  //! Set a time limit in tenth of a second,
  /*! counting the cpu time used by the current process from now on.
   *  Currently, when the limit is reached, cvc3 tries to quickly
   *  terminate, probably with the status unknown.
   */
  virtual void setTimeLimit(unsigned limit);

  //! Assert a new formula in the current context.
  /*! This creates the assumption e |- e.  The formula must have Boolean type.
  */
  virtual void assertFormula(const Expr& e);

  //! Register an atomic formula of interest.
  /*! Registered atoms are tracked by the decision procedures.  If one of them
      is deduced to be true or false, it is added to a list of implied literals.
      Implied literals can be retrieved with the getImpliedLiteral function */
  virtual void registerAtom(const Expr& e);

  //! Return next literal implied by last assertion.  Null Expr if none.
  /*! Returned literals are either registered atomic formulas or their negation
   */
  virtual Expr getImpliedLiteral();

  //! Simplify e with respect to the current context
  virtual Expr simplify(const Expr& e);

  //! Check validity of e in the current context.
  /*! If it returns VALID, the scope and context are the same
   *  as when called.  If it returns INVALID, the context will be one which
   *  falsifies the query.  If it returns UNKNOWN, the context will falsify the
   *  query, but the context may be inconsistent.  Finally, if it returns
   *  ABORT, the context will be one which satisfies as much as possible.
   *
   *  \param e is the queried formula
   */
  virtual QueryResult query(const Expr& e);

  //! Check satisfiability of the expr in the current context.
  /*! Equivalent to query(!e) */
  virtual QueryResult checkUnsat(const Expr& e);

  //! Get the next model
  /*! This method should only be called after a query which returns
    INVALID.  Its return values are as for query(). */
  virtual QueryResult checkContinue();

  //! Restart the most recent query with e as an additional assertion.
  /*! This method should only be called after a query which returns
    INVALID.  Its return values are as for query(). */
  virtual QueryResult restart(const Expr& e);

  //! Returns to context immediately before last invalid query.
  /*! This method should only be called after a query which returns false.
   */
  virtual void returnFromCheck();

  //! Get assumptions made by the user in this and all previous contexts.
  /*! User assumptions are created either by calls to assertFormula or by a
   * call to query.  In the latter case, the negated query is added as an
   * assumption.
   * \param assumptions should be empty on entry.
  */
  virtual void getUserAssumptions(std::vector<Expr>& assumptions);

  //! Get assumptions made internally in this and all previous contexts.
  /*! Internal assumptions are literals assumed by the sat solver.
   * \param assumptions should be empty on entry.
  */
  virtual void getInternalAssumptions(std::vector<Expr>& assumptions);

  //! Get all assumptions made in this and all previous contexts.
  /*! \param assumptions should be empty on entry.
  */
  virtual void getAssumptions(std::vector<Expr>& assumptions);

  //! Returns the set of assumptions used in the proof of queried formula.
  /*! It returns a subset of getAssumptions().  If the last query was false
   *  or there has not yet been a query, it does nothing.
   *  NOTE: this functionality is not supported yet
   *  \param assumptions should be empty on entry.
  */
  virtual void getAssumptionsUsed(std::vector<Expr>& assumptions);

  virtual Expr getProofQuery();


  //! Return the internal assumptions that make the queried formula false.
  /*! This method should only be called after a query which returns
    false.  It will try to return the simplest possible subset of
    the internal assumptions sufficient to make the queried expression
    false.
    \param assumptions should be empty on entry.
    \param inOrder if true, returns the assumptions in the order they
    were made.  This is slightly more expensive than inOrder = false.
  */
  virtual void getCounterExample(std::vector<Expr>& assumptions,
                                 bool inOrder=true);

  //! Will assign concrete values to all user created variables
  /*! This function should only be called after a query which return false.
  */
  virtual void getConcreteModel(ExprMap<Expr> & m);

  //! If the result of the last query was UNKNOWN try to actually build the model
  //! to verify the result.
  /*! This function should only be called after a query which return unknown.
  */
  virtual QueryResult tryModelGeneration();

  //:ALEX: returns the current truth value of a formula
  // returns UNKNOWN_VAL if e is not associated
  // with a boolean variable in the SAT module,
  // i.e. if its value can not determined without search.
  virtual FormulaValue value(const Expr& e);

  //! Returns true if the current context is inconsistent.
  /*! Also returns a minimal set of assertions used to determine the
   inconsistency.
   \param assumptions should be empty on entry.
  */
  virtual bool inconsistent(std::vector<Expr>& assumptions);

  //! Returns true if the current context is inconsistent.
  virtual bool inconsistent();

  //! Returns true if the invalid result from last query() is imprecise
  /*!
   * Some decision procedures in CVC are incomplete (quantifier
   * elimination, non-linear arithmetic, etc.).  If any incomplete
   * features were used during the last query(), and the result is
   * "invalid" (query() returns false), then this result is
   * inconclusive.  It means that the system gave up the search for
   * contradiction at some point.
   */
  virtual bool incomplete();

  //! Returns true if the invalid result from last query() is imprecise
  /*!
   * \sa incomplete()
   *
   * The argument is filled with the reasons for incompleteness (they
   * are intended to be shown to the end user).
   */
  virtual bool incomplete(std::vector<std::string>& reasons);

  //! Returns the proof term for the last proven query
  /*! If there has not been a successful query, it should return a NULL proof
  */
  virtual Proof getProof();

  //! Evaluate an expression and return a concrete value in the model
  /*! If the last query was not invalid, should return NULL expr */
  virtual Expr getValue(const Expr& e);

  //! Returns the TCC of the last assumption or query
  /*! Returns Null if no assumptions or queries were performed. */
  virtual Expr getTCC();

  //! Return the set of assumptions used in the proof of the last TCC
  virtual void getAssumptionsTCC(std::vector<Expr>& assumptions);

  //! Returns the proof of TCC of the last assumption or query
  /*! Returns Null if no assumptions or queries were performed. */
  virtual Proof getProofTCC();

  //! After successful query, return its closure |- Gamma => phi
  /*! Turn a valid query Gamma |- phi into an implication
   * |- Gamma => phi.
   *
   * Returns Null if last query was invalid.
   */
  virtual Expr getClosure();

  //! Construct a proof of the query closure |- Gamma => phi
  /*! Returns Null if last query was Invalid. */
  virtual Proof getProofClosure();

  /*@}*/ // End of Validity checking methods

  /***************************************************************************/
  /*!
   *\name Context methods
   * Methods for manipulating contexts
   *
   * Contexts support stack-based push and pop.  There are two
   * separate notions of the current context stack.  stackLevel(), push(),
   * pop(), and popto() work with the user-level notion of the stack.
   *
   * scopeLevel(), pushScope(), popScope(), and poptoScope() work with
   * the internal stack which is more fine-grained than the user
   * stack.
   *
   * Do not use the scope methods unless you know what you are doing.
   * *@{
   */
  /***************************************************************************/

  //! Returns the current stack level.  Initial level is 0.
  virtual int stackLevel();

  //! Checkpoint the current context and increase the scope level
  virtual void push();

  //! Restore the current context to its state at the last checkpoint
  virtual void pop();

  //! Restore the current context to the given stackLevel.
  /*!
    \param stackLevel should be greater than or equal to 0 and less
    than or equal to the current scope level.
  */
  virtual void popto(int stackLevel);

  //! Returns the current scope level.  Initially, the scope level is 1.
  virtual int scopeLevel();

  /*! @brief Checkpoint the current context and increase the
   * <strong>internal</strong> scope level.  Do not use unless you
   * know what you're doing!
   */
  virtual void pushScope();

  /*! @brief Restore the current context to its state at the last
   * <strong>internal</strong> checkpoint.  Do not use unless you know
   * what you're doing!
   */
  virtual void popScope();

  //! Restore the current context to the given scopeLevel.
  /*!
    \param scopeLevel should be less than or equal to the current scope level.

    If scopeLevel is less than 1, then the current context is reset
    and the scope level is set to 1.
  */
  virtual void poptoScope(int scopeLevel);

  //! Get the current context
  virtual Context* getCurrentContext();

  //! Destroy and recreate validity checker: resets everything except for flags
  virtual void reset();

  //! Add an annotation to the current script - prints annot when translating
  virtual void logAnnotation(const Expr& annot);

  /*@}*/ // End of Context methods

  /***************************************************************************/
  /*!
   *\name Reading files
   * Methods for reading external files
   *@{
   */
  /***************************************************************************/

  //! Read and execute the commands from a file given by name ("" means stdin)
  virtual void loadFile(const std::string& fileName,
			InputLanguage lang = PRESENTATION_LANG,
			bool interactive = false,
                        bool calledFromParser = false);

  //! Read and execute the commands from a stream
  virtual void loadFile(std::istream& is,
			InputLanguage lang = PRESENTATION_LANG,
			bool interactive = false);

  /*@}*/ // End of methods for reading files

  /***************************************************************************/
  /*!
   *\name Reporting Statistics
   * Methods for collecting and reporting run-time statistics
   *@{
   */
  /***************************************************************************/

  //! Get statistics object
  virtual Statistics getStatistics();

  //! Print collected statistics to stdout
  virtual void printStatistics();

  /*@}*/ // End of Statistics Methods

};/* class ValidityChecker */

template <class T>
void ExprHashMap<T>::insert(Expr a, Expr b) {
  (*this)[a] = b;
}

// Comparison (the way that CVC3 does it)
int compare(const Expr& e1, const Expr& e2);

}/* CVC3 namespace */

#endif /* _cvc3__include__vc_h_ */
#endif /* __CVC4__CVC3_COMPAT_H */

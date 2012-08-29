/*****************************************************************************/
/*!
 * \file c_interface.h
 *
 * Authors: Clark Barrett
 *          Cristian Cadar
 *
 * Created: Thu Jun  5 10:34:02 2003
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * COPYING file provided with this distribution.
 *
 * <hr>
 *
 */
/*****************************************************************************/

#include "cvc4_public.h"

#ifndef _cvc3__include__c_interface_h_
#define _cvc3__include__c_interface_h_

#include "bindings/compat/c/c_interface_defs.h"

//! Flags can be NULL
VC vc_createValidityChecker(Flags flags);
//! Create validity checker's flags
Flags vc_createFlags();
//! Destroy the validity checker.
/*! Must be called after all other objects are deleted, except the flags */
void vc_destroyValidityChecker(VC vc);
//! Delete the flags
void vc_deleteFlags(Flags flags);
//! Delete type
void vc_deleteType(Type t);
//! Delete expression
void vc_deleteExpr(Expr e);
//! Delete operator
void vc_deleteOp(Op op);
//! Delete vector of expressions
void vc_deleteVector(Expr* e);
//! Delete vector of types
void vc_deleteTypeVector(Type* e);

// Setting the flags
//! Set a boolean flag to true or false
void vc_setBoolFlag(Flags flags, char* name, int val);
//! Set an integer flag to the given value
void vc_setIntFlag(Flags flags, char* name, int val);
//! Set a string flag to the given value
void vc_setStringFlag(Flags flags, char* name, char* val);
//! Add a (string, bool) pair to the multy-string flag
void vc_setStrSeqFlag(Flags flags, char* name, char* str, int val);

// Basic types
Type vc_boolType(VC vc);
Type vc_realType(VC vc);
Type vc_intType(VC vc);

//! Create a subrange type
Type vc_subRangeType(VC vc, int lowerEnd, int upperEnd);

//! Creates a subtype defined by the given predicate
/*!
 * \param vc the validity checker
 *
 * \param pred is a predicate taking one argument of type T and returning
 * Boolean.  The resulting type is a subtype of T whose elements x are those
 * satisfying the predicate pred(x).
 *
 * \param witness is an expression of type T for which pred holds (if a Null
 *  expression is passed as a witness, cvc will try to prove \f$\exists x. pred(x))\f$.
 *  if the witness check fails, a TypecheckException is thrown.
 */
Type vc_subtypeType(VC vc, Expr pred, Expr witness);

// Tuple types
Type vc_tupleType2(VC vc, Type type0, Type type1);
Type vc_tupleType3(VC vc, Type type0, Type type1, Type type2);
//! Create a tuple type.  'types' is an array of types of length numTypes.
Type vc_tupleTypeN(VC vc, Type* types, int numTypes);

// Record types
Type vc_recordType1(VC vc, char* field, Type type);
Type vc_recordType2(VC vc, char* field0, Type type0,
                           char* field1, Type type1);
Type vc_recordType3(VC vc, char* field0, Type type0,
	                   char* field1, Type type1,
	                   char* field2, Type type2);
//! Create a record type.
/*! 'fields' and 'types' are arrays of length numFields. */
Type vc_recordTypeN(VC vc, char** fields, Type* types, int numFields);

// Datatypes

//! Single datatype, single constructor
/*! The types are either type exressions (obtained from a type with
 *  getExpr()) or string expressions containing the name of (one of) the
 *  dataType(s) being defined. */
Type vc_dataType1(VC vc, char* name, char* constructor, int arity,
                  char** selectors, Expr* types);

//! Single datatype, multiple constructors
/*! The types are either type exressions (obtained from a type with
 *  getExpr()) or string expressions containing the name of (one of) the
 *  dataType(s) being defined. */
Type vc_dataTypeN(VC vc, char* name, int numCons, char** constructors,
                  int* arities, char*** selectors, Expr** types);

//! Multiple datatypes
/*! The types are either type exressions (obtained from a type with
 *  getExpr()) or string expressions containing the name of (one of) the
 *  dataType(s) being defined.
 *  Returns an array of size numTypes which must be freed by calling
 *  vc_deleteTypeVector.
 */
Type* vc_dataTypeMN(VC vc, int numTypes, char** names,
                    int* numCons, char*** constructors,
                    int** arities, char**** selectors,
                    Expr*** types);

//! Create an array type
Type vc_arrayType(VC vc, Type typeIndex, Type typeData);

//! Create a bitvector type of length n
Type vc_bvType(VC vc, int n);

//! Create a function type with 1 argument
Type vc_funType1(VC vc, Type a1, Type typeRan);
//! Create a function type with 2 arguments
Type vc_funType2(VC vc, Type a1, Type a2, Type typeRan);
//! Create a function type with 3 arguments
Type vc_funType3(VC vc, Type a1, Type a2, Type a3, Type typeRan);
//! Create a function type with N arguments
Type vc_funTypeN(VC vc, Type* args, Type typeRan, int numArgs);

// User-defined types

//! Create an uninterpreted named type
Type vc_createType(VC vc, char* typeName);
//! Lookup a user-defined (uninterpreted) type by name
Type vc_lookupType(VC vc, char* typeName);

/////////////////////////////////////////////////////////////////////////////
// Expr manipulation methods                                               //
/////////////////////////////////////////////////////////////////////////////

//! Return the ExprManager
ExprManager* vc_getEM(VC vc);

//! Create a variable with a given name and type
/*! The type cannot be a function type. */
Expr vc_varExpr(VC vc, char* name, Type type);

//! Create a variable with a given name, type, and value
Expr vc_varExprDef(VC vc, char* name, Type type,
                   Expr def);

//! Get the expression and type associated with a name.
/*!  If there is no such Expr, a NULL Expr is returned. */
Expr vc_lookupVar(VC vc, char* name, Type* type);

//! Get the type of the Expr.
Type vc_getType(VC vc, Expr e);

//! Get the largest supertype of the Expr.
Type vc_getBaseType(VC vc, Expr e);

//! Get the largest supertype of the Type.
Type vc_getBaseTypeOfType(VC vc, Type t);

//! Get the subtype predicate
Expr vc_getTypePred(VC vc, Type t, Expr e);

//! Create a string Expr
Expr vc_stringExpr(VC vc, char* str);

//! Create an ID Expr
Expr vc_idExpr(VC vc, char* name);

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
Expr vc_listExpr(VC vc, int numKids, Expr* kids);

// Expr I/O
//! Expr vc_parseExpr(VC vc, char* s);
void vc_printExpr(VC vc, Expr e);
//! Print e into a char*
/*! Note that the ownership of the char* is given to the caller
  which should free the memory when it is done with it.  This
  can be done by calling vc_deleteString. */
char* vc_printExprString(VC vc, Expr e);
//! Delete char* returned by previous function
void vc_deleteString(char* str);
//! Print 'e' into an open file descriptor
void vc_printExprFile(VC vc, Expr e, int fd);

//! Import the Expr from another instance of VC
/*! When expressions need to be passed among several instances of
 *  VC, they need to be explicitly imported into the
 *  corresponding instance using this method.  The return result is
 *  an identical expression that belongs to the current instance of
 *  VC, and can be safely used as part of more complex
 *  expressions from the same instance.
 \param vc is the instance to be imported into
 \param e is the expression created using a different (not vc) instance
 */
Expr vc_importExpr(VC vc, Expr e);

//! Import the Type from another instance of VC
/*! \sa vc_importExpr() */
Type vc_importType(Type t);

//! Create an equality expression.  The two children must have the same type.
Expr vc_eqExpr(VC vc, Expr child0, Expr child1);

//! Create an all distinct expression. All children must ahve the same type.
Expr vc_distinctExpr(VC vc, Expr* children, int numChildren);

// Boolean expressions

// The following functions create Boolean expressions.  The children provided
// as arguments must be of type Boolean.
Expr vc_trueExpr(VC vc);
Expr vc_falseExpr(VC vc);
Expr vc_notExpr(VC vc, Expr child);
Expr vc_andExpr(VC vc, Expr left, Expr right);
Expr vc_andExprN(VC vc, Expr* children, int numChildren);
Expr vc_orExpr(VC vc, Expr left, Expr right);
Expr vc_orExprN(VC vc, Expr* children, int numChildren);
Expr vc_impliesExpr(VC vc, Expr hyp, Expr conc);
Expr vc_iffExpr(VC vc, Expr left, Expr right);
Expr vc_iteExpr(VC vc, Expr ifpart, Expr thenpart, Expr elsepart);

// Substitution

// Substitutes oldTerms for newTerms in e.
// This function doesn't actually exist in ValidityChecker interface,
// but it does in Expr, and its functionality is needed in the C interface.
// For consistency, it is represented here as if it were in ValidityChecker.
Expr vc_substExpr(VC vc, Expr e,
                  Expr* oldTerms, int numOldTerms,
                  Expr* newTerms, int numNewTerms);

// User-defined (uninterpreted) functions.

//! Create an operator from a function with a given name and type.
/*! Name is given as an ID Expr, and the type must be a function type. */
Op vc_createOp(VC vc, char* name, Type type);

//! Create a named user-defined function with a given type
Op vc_createOpDef(VC vc, char* name, Type type, Expr def);

//! Lookup an operator by name.
/*! Returns the operator and the type if the operator exists.
 * Returns NULL otherwise
 */
Op vc_lookupOp(VC vc, char* name, Type* type);

//! Create expressions with a user-defined operator.
/*!  op must have a function type. */
Expr vc_funExpr1(VC vc, Op op, Expr child);
Expr vc_funExpr2(VC vc, Op op, Expr left, Expr right);
Expr vc_funExpr3(VC vc, Op op, Expr child0, Expr child1, Expr child2);
Expr vc_funExprN(VC vc, Op op, Expr* children, int numChildren);

// Arithmetic

//! Create a rational number with numerator n and denominator d.
/*! d cannot be 0. */
Expr vc_ratExpr(VC vc, int n, int d);

//! Create a rational number n/d; n and d are given as strings
/*! n and d are converted to arbitrary-precision integers according to
 *  the given base.  d cannot be 0.  */
Expr vc_ratExprFromStr(VC vc, char* n, char* d, int base);

//! Create a rational from a single string.
/*!
  \param vc the validity checker
  \param n can be a string containing an integer, a pair of integers
  "nnn/ddd", or a number in the fixed or floating point format.
  \param base is the base in which to interpret the string.
*/
Expr vc_ratExprFromStr1(VC vc, char* n, int base);

//! Unary minus.  Child must have a numeric type.
Expr vc_uminusExpr(VC vc, Expr child);

// plus, minus, mult.  Children must have numeric types.
Expr vc_plusExpr(VC vc, Expr left, Expr right);
Expr vc_plusExprN(VC vc, Expr* children, int numChildren);
Expr vc_minusExpr(VC vc, Expr left, Expr right);
Expr vc_multExpr(VC vc, Expr left, Expr right);
Expr vc_powExpr(VC vc, Expr pow, Expr base);
Expr vc_divideExpr(VC vc, Expr numerator, Expr denominator);

// The following functions create less-than, less-than or equal,
// greater-than, and greater-than or equal expressions of type Boolean.
// Their arguments must be of numeric types.
Expr vc_ltExpr(VC vc, Expr left, Expr right);
Expr vc_leExpr(VC vc, Expr left, Expr right);
Expr vc_gtExpr(VC vc, Expr left, Expr right);
Expr vc_geExpr(VC vc, Expr left, Expr right);

// Records

// Create record literals;
Expr vc_recordExpr1(VC vc, char* field, Expr expr);
Expr vc_recordExpr2(VC vc, char* field0, Expr expr0,
		                   char* field1, Expr expr1);
Expr vc_recordExpr3(VC vc, char* field0, Expr expr0,
                                   char* field1, Expr expr1,
		                   char* field2, Expr expr2);
Expr vc_recordExprN(VC vc, char** fields, Expr* exprs, int numFields);

//! Create an expression representing the selection of a field from a record.
Expr vc_recSelectExpr(VC vc, Expr record, char* field);

//! Record update; equivalent to "record WITH .field := newValue"
Expr vc_recUpdateExpr(VC vc, Expr record, char* field, Expr newValue);

// Arrays

//! Create an expression for the value of array at the given index
Expr vc_readExpr(VC vc, Expr array, Expr index);

//! Array update; equivalent to "array WITH [index] := newValue"
Expr vc_writeExpr(VC vc, Expr array, Expr index, Expr newValue);

// Bitvectors
// Additional type constructor
Type vc_bv32Type(VC vc);

// Bitvector constants
Expr vc_bvConstExprFromStr(VC vc, char* binary_repr);
Expr vc_bvConstExprFromInt(VC vc, int n_bits, unsigned int value);
Expr vc_bv32ConstExprFromInt(VC vc, unsigned int value);
Expr vc_bvConstExprFromLL(VC vc, int n_bits, unsigned long value);

// Concat and extract
Expr vc_bvConcatExpr(VC vc, Expr left, Expr right);
Expr vc_bvConcatExprN(VC vc, Expr* children, int numChildren);
Expr vc_bvExtract(VC vc, Expr child, int high_bit_no, int low_bit_no);
Expr vc_bvBoolExtract(VC vc, Expr child, int bit_no);

// Bitwise Boolean operators: Negation, And, Or, Xor
Expr vc_bvNotExpr(VC vc, Expr child);
Expr vc_bvAndExpr(VC vc, Expr left, Expr right);
Expr vc_bvOrExpr(VC vc, Expr left, Expr right);
Expr vc_bvXorExpr(VC vc, Expr left, Expr right);

// Unsigned bitvector inequalities
Expr vc_bvLtExpr(VC vc, Expr left, Expr right);
Expr vc_bvLeExpr(VC vc, Expr left, Expr right);
Expr vc_bvGtExpr(VC vc, Expr left, Expr right);
Expr vc_bvGeExpr(VC vc, Expr left, Expr right);

// Signed bitvector inequalities
Expr vc_bvSLtExpr(VC vc, Expr left, Expr right);
Expr vc_bvSLeExpr(VC vc, Expr left, Expr right);
Expr vc_bvSGtExpr(VC vc, Expr left, Expr right);
Expr vc_bvSGeExpr(VC vc, Expr left, Expr right);

// Sign-extend child to a total of nbits bits
Expr vc_bvSignExtend(VC vc, Expr child, int nbits);

// Bitvector arithmetic: unary minus, plus, subtract, multiply
Expr vc_bvUMinusExpr(VC vc, Expr child);
Expr vc_bvPlusExpr(VC vc, int n_bits, Expr left, Expr right);
Expr vc_bv32PlusExpr(VC vc, Expr left, Expr right);
Expr vc_bvMinusExpr(VC vc, int n_bits, Expr left, Expr right);
Expr vc_bv32MinusExpr(VC vc, Expr left, Expr right);
Expr vc_bvMultExpr(VC vc, int n_bits, Expr left, Expr right);
Expr vc_bv32MultExpr(VC vc, Expr left, Expr right);
Expr vc_bvUDivExpr(VC vc, Expr left, Expr right);
Expr vc_bvURemExpr(VC vc, Expr left, Expr right);
Expr vc_bvSDivExpr(VC vc, Expr left, Expr right);
Expr vc_bvSRemExpr(VC vc, Expr left, Expr right);
Expr vc_bvSModExpr(VC vc, Expr left, Expr right);

// Shift operators
Expr vc_bvLeftShiftExpr(VC vc, int sh_amt, Expr child);
Expr vc_bvRightShiftExpr(VC vc, int sh_amt, Expr child);
Expr vc_bv32LeftShiftExpr(VC vc, int sh_amt, Expr child);
Expr vc_bv32RightShiftExpr(VC vc, int sh_amt, Expr child);
Expr vc_bvVar32LeftShiftExpr(VC vc, Expr sh_amt, Expr child);
Expr vc_bvVar32RightShiftExpr(VC vc, Expr sh_amt, Expr child);
Expr vc_bvVar32DivByPowOfTwoExpr(VC vc, Expr child, Expr rhs);

/*C pointer support:  C interface to support C memory arrays in CVC3 */
Expr vc_bvCreateMemoryArray(VC vc, char * arrayName);
Expr vc_bvReadMemoryArray(VC vc,
			  Expr array, Expr byteIndex, int numOfBytes);
Expr vc_bvWriteToMemoryArray(VC vc,
			     Expr array, Expr  byteIndex,
			     Expr element, int numOfBytes);

// Tuples

//! Create a tuple expression
/*! 'children' is an array of elements of length numChildren */
Expr vc_tupleExprN(VC vc, Expr* children, int numChildren);

//! Tuple select; equivalent to "tuple.n", where n is an numeral (e.g. tup.5)
Expr vc_tupleSelectExpr(VC vc, Expr tuple, int index);

//! Tuple update; equivalent to "tuple WITH index := newValue"
Expr vc_tupleUpdateExpr(VC vc, Expr tuple, int index, Expr newValue);

// Datatypes

//! Datatype constructor expression
Expr vc_datatypeConsExpr(VC vc, char* constructor, int numArgs, Expr* args);

//! Datatype selector expression
Expr vc_datatypeSelExpr(VC vc, char* selector, Expr arg);

//! Datatype tester expression
Expr vc_datatypeTestExpr(VC vc, char* constructor, Expr arg);

// Quantifiers

//! Create a bound variable.
/*! \param vc the validity checker
 * \param name
 * \param uid is a fresh unique string to distinguish this variable
 * from other bound variables with the same name
 * \param type
 */
Expr vc_boundVarExpr(VC vc, char* name, char *uid, Type type);

//! Create a FORALL quantifier.
/*! Bvars is an array of bound variables of length numBvars. */
Type vc_forallExpr(VC vc, Expr* Bvars, int numBvars, Expr f);

//! Set triggers for a forallExpr
void vc_setTriggers(VC vc, Expr e, int numTrigs, Expr* triggers);

//! Create an EXISTS quantifier.
/*! Bvars is an array of bound variables of length numBvars. */
Expr vc_existsExpr(VC vc, Expr* Bvars, int numBvars, Expr f);

//! Lambda-expression
Op vc_lambdaExpr(VC vc, int numVars, Expr* vars, Expr body);

/////////////////////////////////////////////////////////////////////////////
// Context-related methods                                                 //
/////////////////////////////////////////////////////////////////////////////

//! Set the resource limit (0==unlimited, 1==exhausted).
/*! Currently, the limit is the total number of processed facts. */
void vc_setResourceLimit(VC vc, unsigned limit);

//! Assert a new formula in the current context.
/*! The formula must have Boolean type. */
void vc_assertFormula(VC vc, Expr e);

//! Register an atomic formula of interest.
/*! Registered atoms are tracked by the decision procedures.  If one of them
    is deduced to be true or false, it is added to a list of implied literals.
    Implied literals can be retrieved with the getImpliedLiteral function */
void vc_registerAtom(VC vc, Expr e);

//! Return next literal implied by last assertion.  Null if none.
/*! Returned literals are either registered atomic formulas or their negation
 */
Expr vc_getImpliedLiteral(VC vc);

//! Simplify e with respect to the current context
Expr vc_simplify(VC vc, Expr e);

//! Check validity of e in the current context.
/*! Possible results are: 0 = invalid, 1 = valid, 2 = abort, 3 = unknown,
 * -100 = exception (type error, internal error, etc).
 * If the result is 1, then the resulting context is the same as
 * the starting context.  If the result is 0 or 3, then the resulting
 * context is a context in which e is false (though the context may be
 * inconsistent in the case of an unknown result).  e must have Boolean
 * type.  In the case of a result of -100, refer to vc_get_error_string()
 * to see what went wrong. */
int vc_query(VC vc, Expr e);

//! Get the next model
/*! This method should only be called after a query which returns
  0.  Its return values are as for vc_query(). */
int vc_checkContinue(VC vc);

//! Restart the most recent query with e as an additional assertion.
/*! This method should only be called after a query which returns
  0.  Its return values are as for vc_query(). */
int vc_restart(VC vc, Expr e);

//! Returns to context immediately before last invalid query.
/*! This method should only be called after a query which returns 0.
 */
void vc_returnFromCheck(VC vc);

//! Get assumptions made by the user in this and all previous contexts.
/*! User assumptions are created either by calls to assertFormula or by a
 * call to query.  In the latter case, the negated query is added as an
 * assumption.  The caller is responsible for freeing the array when
 * finished with it.
 */
Expr* vc_getUserAssumptions(VC vc, int* size);

//! Get assumptions made internally in this and all previous contexts.
/*! Internal assumptions are literals assumed by the sat solver.
 * The caller is responsible for freeing the array when finished with it by
 * calling vc_deleteVector.
 */
Expr* vc_getInternalAssumptions(VC vc, int* size);

//! Get all assumptions made in this and all previous contexts.
/*!
 * The caller is responsible for freeing the array when finished with it by
 * calling vc_deleteVector.
 */
Expr* vc_getAssumptions(VC vc, int* size);

//yeting, for proof translation, get the assumptions used.
//the assumptions used are different from the user assumptions.
//the assumptions used are preprocessed if 'preprocess' is ena
Expr vc_getProofAssumptions(VC vc);

//yeting, for proof translation,
Expr vc_getProofQuery(VC vc);

//! Returns the set of assumptions used in the proof of queried formula.
/*! It returns a subset of getAssumptions().  If the last query was false
 *  or there has not yet been a query, it does nothing.
 * The caller is responsible for freeing the array when finished with it by
 * calling vc_deleteVector.
 */
Expr* vc_getAssumptionsUsed(VC vc, int* size);

//! Return the counterexample after a failed query.
/*! This method should only be called after a query which returns
 * false.  It will try to return the simplest possible set of
 * assertions which are sufficient to make the queried expression
 * false.  The caller is responsible for freeing the array when finished with
 * it by calling vc_deleteVector.
 */
Expr* vc_getCounterExample(VC vc, int* size);

//! Will assign concrete values to all user created variables
/*! This function should only be called after a query which return false.
 * Returns an array of Exprs with size *size.
 * The caller is responsible for freeing the array when finished with it by
 * calling vc_deleteVector.
 */
Expr* vc_getConcreteModel(VC vc, int* size);

// Returns true if the current context is inconsistent.
/*! Also returns a minimal set of assertions used to determine the
 * inconsistency. The caller is responsible for freeing the array when finished
 * with it by calling vc_deleteVector.
 */
int vc_inconsistent(VC vc, Expr** assumptions, int* size);

//! Returns non-NULL if the invalid result from last query() is imprecise
/*!
 * The return value is filled with the reasons for incompleteness (it
 * is intended to be shown to the end user).  The caller is responsible for
 * freeing the string returned by calling vc_deleteString.
 */
char* vc_incomplete(VC vc);

//! Returns the proof for the last proven query
Expr vc_getProof(VC vc);

//! Returns the proof of a .cvc file, if it is valid.
Expr vc_getProofOfFile(VC vc, char * filename);

//! Returns the TCC of the last assumption or query
/*! Returns Null Expr if no assumptions or queries were performed. */
Expr vc_getTCC(VC vc);

//! Return the set of assumptions used in the proof of the last TCC
/*! The caller is responsible for freeing the array when finished with it by
 * calling vc_deleteVector.
 */
Expr* vc_getAssumptionsTCC(VC vc, int* size);

//! Returns the proof of TCC of the last assumption or query
/*! Returns Null Expr if no assumptions or queries were performed. */
Expr vc_getProofTCC(VC vc);

//! After successful query, return its closure |- Gamma => phi
/*! Turn a valid query Gamma |- phi into an implication
 * |- Gamma => phi.
 *
 * Returns Null Expr if last query was invalid.
 */
Expr vc_getClosure(VC vc);

//! Construct a proof of the query closure |- Gamma => phi
/*! Returns Null if last query was Invalid. */
Expr vc_getProofClosure(VC vc);

//! Returns the current stack level.  Initial level is 0.
int vc_stackLevel(VC vc);

//! Checkpoint the current context and increase the scope level
void vc_push(VC vc);

//! Restore the current context to its state at the last checkpoint
void vc_pop(VC vc);

//! Restore the current context to the given stackLevel.
/*! stackLevel must be less than or equal to the current stack level.
 */
void vc_popto(VC vc, int stackLevel);

//! Get the current context
Context* vc_getCurrentContext(VC vc);

/* ---------------------------------------------------------------------- */
/*  Util                                                                  */
/* ---------------------------------------------------------------------- */

// Order

//! Compares two expressions
/*! If e1 < e2, e1==e2, and e1 > e2, it returns -1, 0, 1
 * respectively.  A return value of -100 signals an error (refer to
 * vc_get_error_string() for details).
 *
 * Can't be 'compare' because already defined in ocaml */
int vc_compare_exprs(Expr e1,Expr e2);

// Printing

//! Convert Expr to string
char* vc_exprString(Expr e);
//! Convert Type to string
char* vc_typeString(Type t);

// What kind of Expr?
int vc_isClosure(Expr e);
int vc_isQuantifier(Expr e);
int vc_isLambda(Expr e);
Expr vc_isVar(Expr e);

int vc_arity(Expr e);
int vc_getKind(Expr e);
Expr vc_getChild(Expr e, int i);
int vc_getNumVars(Expr e);
Expr vc_getVar(Expr e, int i);
Expr vc_getBody(Expr e);
Expr vc_getExistential(Expr e);
Expr vc_getFun(VC vc, Expr e);
Expr vc_toExpr(Type t);

//! Translate a kind int to a string
const char* vc_getKindString(VC vc,int kind);

//! Translate a kind string to an int
int vc_getKindInt(VC vc,char* kind_name);

//! Return an int from a rational expression
int vc_getInt(Expr e);

//! Return an int from a constant bitvector expression
int vc_getBVInt(VC vc, Expr e);
//! Return an unsigned int from a constant bitvector expression
unsigned int vc_getBVUnsigned(VC vc, Expr e);

// Debug
int vc_get_error_status();
void vc_reset_error_status();
char* vc_get_error_string();

//! Print statistics
void vc_print_statistics(VC vc);

#endif



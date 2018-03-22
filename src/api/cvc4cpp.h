#ifndef __CVC4__CPP_H
#define __CVC4__CPP_H

#include "cvc4_public.h"

#include <unordered_map>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace CVC4 {

class Expr;
class Datatype;
class DatatypeConstructor;
class DatatypeConstructorArg;
class ExprManager;
class SmtEngine;
class Type;
class Options;
class Random;
class Result;

namespace api {


/* -------------------------------------------------------------------------- */
/* Result                                                                     */
/* -------------------------------------------------------------------------- */

/**
 * Encapsulation of a three-valued solver result, with explanations.
 */
class CVC4_PUBLIC Result
{
  public:
    /**
     * Constructor.
     * @param r the internal result that is to be wrapped by this result
     * @return the Result
     */
    Result (const CVC4::Result& r);

    /**
     * Return true if query was a satisfiable checkSat() or checkSatAssuming()
     * query.
     */
    bool isSat () const;

    /**
     * Return true if query was an unsatisfiable checkSat() or
     * checkSatAssuming() query.
     */
    bool isUnsat () const;

    /**
     * Return true if query was a checkSat() or checkSatAssuming() query and
     * CVC4 was not able to determine (un)satisfiability.
     */
    bool isSatUnknown () const;

    /**
     * Return true if corresponding query was a valid checkValid() or
     * checkValidAssuming() query.
     */
    bool isValid () const;

    /**
     * Return true if corresponding query was an invalid checkValid() or
     * checkValidAssuming() query.
     */
    bool isInvalid () const;

    /**
     * Return true if query was a checkValid() or checkValidAssuming() query
     * and CVC4 was not able to determine (in)validity..
     */
    bool isValidUnknown () const;

    /**
     * Operator overloading for equality of two results.
     * @param r the result to compare to for equality
     * @return true if the results are equal
     */
    bool operator== (const Result& r) const;

    /**
     * Operator overloading for disequality of two results.
     * @param r the result to compare to for disequality
     * @return true if the results are disequal
     */
    bool operator!= (const Result& r) const;

    /**
     * @return an explanation for an unknown query result.
     */
    std::string getUnknownExplanation () const;

    /**
     * @return a string representation of this result.
     */
    std::string toString () const;

  private:
    /* The interal result wrapped by this result. */
    const CVC4::Result* d_result;
};

/**
 * Serialize a result to given stream.
 * @param out the output stream
 * @param r the result to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<< (std::ostream& out, const Result& r) CVC4_PUBLIC;


/* -------------------------------------------------------------------------- */
/* Kind                                                                       */
/* -------------------------------------------------------------------------- */

/**
 * The kind of a CVC4 term.
 */
enum CVC4_PUBLIC Kind
{
  /**
   * Internal kind.
   * Should never be exposed or created via the API.
   */
  INTERNAL_KIND = -2,
  /**
   * Undefined kind.
   * Should never be exposed or created via the API.
   */
  UNDEFINED_KIND = -1,
  /**
   * Null kind (kind of null term Term()).
   * Do not explicitly create via API functions other than Term().
   */
  NULL_EXPR,

  /* Builtin --------------------------------------------------------------- */

  /**
   * Uninterpreted constant.
   * Parameters: 2
   *   -[1]: Sort of the constant
   *   -[2]: ???int32_t index???
   * Create with:
   *   mkConst(Kind, Sort, int32_t)
   */
  UNINTERPRETED_CONSTANT,
  /**
   * Abstract value (other than uninterpreted sort constants).
   * Parameters: 1
   *   -[1]: ???index???.
   * Create with:
   *   mkConst(Kind kind, const char* s, uint32_t base = 10)
   *   mkConst(Kind kind, const std::string& s, uint32_t base = 10)
   *   mkConst(Kind kind, uint32_t arg)
   *   mkConst(Kind kind, int32_t arg)
   *   mkConst(Kind kind, int64_t arg)
   *   mkConst(Kind kind, uint64_t arg)
   */
  ABSTRACT_VALUE,
#if 0
  /* Built-in operator */
  BUILTIN,
#endif
  /**
   * Defined function.
   * Parameters: 3 (4)
   *   See defineFun().
   * Create with:
   *   defineFun(const std::string& symbol,
   *             const std::vector<Term>& bound_vars,
   *             Sort sort,
   *             Term term)
   *   defineFun(Term fun,
   *             const std::vector<Term>& bound_vars,
   *             Term term)
   */
  FUNCTION,
  /**
   * Application of a defined function.
   * Parameters: n > 1
   *   -[1]..[n]: the function argument instantiation Terms
   * Create with:
   *   mkTerm(Kind kind, Term child)
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  APPLY,
  /**
   * Equality.
   * Parameters: 2
   *   -[1]..[2]: Terms with same Sort.
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  EQUAL,
  /**
   * Disequality.
   * Parameters: n > 1
   *   -[1]..[n]: Terms with same Sort.
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  DISTINCT,
  /**
   * Variable.
   * Not permitted in bindings (forall, exists, ...).
   * Parameters:
   *   See mkVar().
   * Create with:
   *   mkVar(const std::string& symbol, Sort sort)
   *   mkVar(Sort sort)
   */
  VARIABLE,
  /**
   * Bound variable.
   * Permitted in bindings and in the lambda and quantifier bodies only.
   * Parameters:
   *   See mkBoundVar().
   * Create with:
   *   mkBoundVar(const std::string& symbol, Sort sort)
   *   mkBoundVar(Sort sort)
   */
  BOUND_VARIABLE,
#if 0
  /* Skolem variable (internal only) */
  SKOLEM,
  /* Symbolic expression (any arity) */
  SEXPR,
#endif
  /**
   * Lambda expression.
   * Parameters: 2
   *   -[1]: a BOUND_VAR_LIST
   *   -[2]: the lambda body
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  LAMBDA,
  /**
   * Hilbert choice (epsilon) expression.
   * Parameters: 2
   *   -[1]: a BOUND_VAR_LIST
   *   -[2]: the Hilbert choice body
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  CHOICE,
  /**
   * Chained operation.
   * Parameters: n > 1
   *   -[1]: a term of kind CHAIN_OP (represents a binary op)
   *   -[2]..[n]: arguments to that operator
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   * Turned into a conjunction of binary applications of the operator on
   * adjoining parameters.
   */
  CHAIN,
  /**
   * Chained operator.
   * Parameters: 1
   *   -[1]: the kind of the binary operation.
   * Create with:
   *   mkOpTerm(Kind opkind, Kind kind)
   */
  CHAIN_OP,

  /* Boolean --------------------------------------------------------------- */

  /**
   * Boolean constant.
   * Parameters: 1
   *   -[1]: the Boolean value of the constant
   * Create with:
   *   mkTrue()
   *   mkFalse()
   *   mkBoolean(bool val)
   *   mkConst(Kind kind, bool arg)
   */
  CONST_BOOLEAN,
  /* Logical not.
   * Parameters: 1
   *   -[1]: the Boolean Term to negate
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  NOT,
  /* Logical and.
   * Parameters: n > 1
   *   -[1]..[n]: the Boolean Term of the conjunction
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  AND,
  /**
   * Logical implication.
   * Parameters: 2
   *   -[1]..[2]: Boolean Terms, [1] implies [2]
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  IMPLIES,
  /* Logical or.
   * Parameters: n > 1
   *   -[1]..[n]: the Boolean Term of the disjunction
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  OR,
  /* Logical exclusive or.
   * Parameters: 2
   *   -[1]..[2]: Boolean Terms, [1] xor [2]
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  XOR,
  /* If-then-else.
   * Parameters: 3
   *   -[1] is a Boolean condition Term
   *   -[2] the 'then' Term
   *   -[3] the 'else' Term
   * 'then' and 'else' term must have same base sort.
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  ITE,

  /* UF -------------------------------------------------------------------- */

  /* Application of an uninterpreted function.
   * Parameters: n > 1
   *   -[1]: the function Term
   *   -[2]..[n]: function argument instantiation Terms
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  APPLY_UF,
  /**
   * Boolean term variable
   * ???
   */
  BOOLEAN_TERM_VARIABLE,
  /**
   * Cardinality constraint on sort S.
   * Parameters: 2
   *   -[1]: a Term of Sort S
   *   -[2]: a positive integer constant that bounds the cardinality of sort S
   * Create with:
   *   ???
   */
  CARDINALITY_CONSTRAINT,
  /**
   * Combined cardinality constraint.
   * Parameters: 1
   *   -[1]: a positive integer constant that bounds the sum of the
   *         cardinalities of all sorts in the signature
   * Create with:
   *   ???
   */
  COMBINED_CARDINALITY_CONSTRAINT,
  /**
   * Partial uninterpreted function application.
   * Parameters: n  ??? > 1 ???
   *   -[1]..[n]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  PARTIAL_APPLY_UF,
#if 0
  /* cardinality value of sort S:
   * first parameter is (any) term of sort S */
   CARDINALITY_VALUE,
#endif
  /**
   * Higher-order (partial) function application
   * Parameters: n  ???  n > 1 ???
   *   -[1]..[n]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  HO_APPLY,

  /* Arithmetic ------------------------------------------------------------ */

  /**
   * Arithmetic addition.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of Sort Integer, Real (sorts must match).
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  PLUS,
  /**
   * Arithmetic multiplication.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of Sort Integer, Real (sorts must match).
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  MULT,
  /* Synonym for MULT.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of Sort Integer, Real (sorts must match).
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  NONLINEAR_MULT,
  /**
   * Arithmetic subtraction.
   * Parameters: 2
   *   -[1]..[2]: Terms of Sort Integer, Real (sorts must match).
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  MINUS,
  /**
   * Arithmetic negation.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  UMINUS,
  /**
   * Real division, division by 0 undefined
   * Parameters: 2
   *   -[1]..[2]: Terms of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  DIVISION,
  /**
   * Real division with interpreted division by 0
   * Parameters: 2
   *   -[1]..[2]: Terms of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  DIVISION_TOTAL,
  /**
   * Integer division, division by 0 undefined.
   * Parameters: 2
   *   -[1]..[2]: Terms of Sort Integer
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INTS_DIVISION,
  /**
   * Integer division with interpreted division by 0.
   * Parameters: 2
   *   -[1]..[2]: Terms of Sort Integer
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INTS_DIVISION_TOTAL,
  /**
   * Integer modulus, division by 0 undefined.
   * Parameters: 2
   *   -[1]..[2]: Terms of Sort Integer
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INTS_MODULUS,
  /**
   * Integer modulus with interpreted division by 0.
   * Parameters: 2
   *   -[1]..[2]: Terms of Sort Integer
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INTS_MODULUS_TOTAL,
  /**
   * Absolute value.
   * Parameters: 1
   *   -[1]: Term of Sort Integer
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ABS,
  /**
   * Divisibility-by-k predicate.
   * Parameters: 2
   *   -[1]: a DIVISIBLE_OP Term
   *   -[2]: an Integer Term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  DIVISIBLE,
  /**
   * Arithmetic power.
   * Parameters: 2
   *   -[1]..[2]: Terms of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  POW,
  /**
   * Exponential.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  EXPONENTIAL,
  /**
   * Sine.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  SINE,
  /**
   * Consine.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  COSINE,
  /**
   * Tangent.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  TANGENT,
  /**
   * Cosecant.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  COSECANT,
  /**
   * Secant.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  SECANT,
  /**
   * Cotangent.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  COTANGENT,
  /**
   * Arc sine.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ARCSINE,
  /**
   * Arc consine.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ARCCOSINE,
  /**
   * Arc tangent.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ARCTANGENT,
  /**
   * Arc cosecant.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ARCCOSECANT,
  /**
   * Arc secant.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ARCSECANT,
  /**
   * Arc cotangent.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ARCCOTANGENT,
  /**
   * Square root.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  SQRT,
  /**
   * Operator for the divisibility-by-k predicate.
   * Parameter: 1
   *   -[1]: the k to divide by (Sort Integer)
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param)
   */
  DIVISIBLE_OP,
  /**
   * Multiple-precision rational constant.
   * Parameters:
   *   See mkInteger(), mkReal(), mkRational()
   * Create with:
   *   mkInteger(const char* s, uint32_t base = 10)
   *   mkInteger(const std::string& s, uint32_t base = 10)
   *   mkInteger(int32_t val)
   *   mkInteger(uint32_t val)
   *   mkInteger(int64_t val)
   *   mkInteger(uint64_t val)
   *   mkReal(const char* s, uint32_t base = 10)
   *   mkReal(const std::string& s, uint32_t base = 10)
   *   mkReal(int32_t val)
   *   mkReal(int64_t val)
   *   mkReal(uint32_t val)
   *   mkReal(uint64_t val)
   *   mkRational(int32_t num, int32_t den)
   *   mkRational(int64_t num, int64_t den)
   *   mkRational(uint32_t num, uint32_t den)
   *   mkRational(uint64_t num, uint64_t den)
   *   mkConst(Kind kind, const char* s, uint32_t base = 10)
   *   mkConst(Kind kind, const std::string& s, uint32_t base = 10)
   *   mkConst(Kind kind, uint32_t arg)
   *   mkConst(Kind kind, int64_t arg)
   *   mkConst(Kind kind, uint64_t arg)
   *   mkConst(Kind kind, int32_t arg)
   *   mkConst(Kind kind, int32_t arg1, int32_t arg2)
   *   mkConst(Kind kind, int64_t arg1, int64_t arg2)
   *   mkConst(Kind kind, uint32_t arg1, uint32_t arg2)
   *   mkConst(Kind kind, uint64_t arg1, uint64_t arg2)
   */
  CONST_RATIONAL,
  /**
   * Less than.
   * Parameters: 2
   *   -[1]..[2]: Terms of Sort Integer, Real; [1] < [2]
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  LT,
  /**
   * Less than or equal.
   * Parameters: 2
   *   -[1]..[2]: Terms of Sort Integer, Real; [1] <= [2]
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  LEQ,
  /**
   * Greater than.
   * Parameters: 2
   *   -[1]..[2]: Terms of Sort Integer, Real, [1] > [2]
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  GT,
  /**
   * Greater than or equal.
   * Parameters: 2
   *   -[1]..[2]: Terms of Sort Integer, Real; [1] >= [2]
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  GEQ,
  /**
   * Is-integer predicate.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  IS_INTEGER,
  /**
   * Convert Term to Integer by the floor function.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  TO_INTEGER,
  /**
   * Convert Term to Real.
   * Parameters: 1
   *   -[1]: Term of Sort Integer, Real
   * this is a no-op in CVC4, as Integer is a subtype of Real.
   */
  TO_REAL,
  /**
   * Pi constant.
   * Create with:
   *   mkPi()
   */
  PI,

  /* BV -------------------------------------------------------------------- */

  /**
   * Fixed-size bit-vector constant.
   * Parameters:
   *   See mkBitVector().
   * Create with:
   *   mkBitVector(uint32_t size)
   *   mkBitVector(uint32_t size, uint32_t val)
   *   mkBitVector(uint32_t size, uint64_t val)
   *   mkBitVector(const char* s, uint32_t base = 2)
   *   mkBitVector(std::string& s, uint32_t base = 2)
   *   mkConst(Kind kind, const char* s, uint32_t base = 10)
   *   mkConst(Kind kind, const std::string& s, uint32_t base = 10)
   *   mkConst(Kind kind, uint32_t arg)
   *   mkConst(Kind kind, uint32_t arg1, uint64_t arg2)
   */
  CONST_BITVECTOR,
  /**
   * Concatenation of two or more bit-vectors.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_CONCAT,
  /**
   * Bit-wise and.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_AND,
  /**
   * Bit-wise or.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_OR,
  /**
   * Bit-wise xor.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_XOR,
  /**
   * Bit-wise negation.
   * Parameters: 1
   *   -[1]: Term of bit-vector Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  BITVECTOR_NOT,
  /**
   * Bit-wise nand.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_NAND,
  /**
   * Bit-wise nor.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_NOR,
  /**
   * Bit-wise xnor.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_XNOR,
  /**
   * Equality comparison (returns bit-vector of size 1).
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_COMP,
  /**
   * Multiplication of two or more bit-vectors.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_MULT,
  /**
   * Addition of two or more bit-vectors.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_PLUS,
  /**
   * Subtraction of two bit-vectors.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SUB,
  /**
   * Negation of a bit-vector (two's complement).
   * Parameters: 1
   *   -[1]: Term of bit-vector Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  BITVECTOR_NEG,
  /**
   * Unsigned division of two bit-vectors, truncating towards 0.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_UDIV,
  /**
   * Unsigned remainder from truncating division of two bit-vectors.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_UREM,
  /**
   * Two's complement signed division of two bit-vectors.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SDIV,
  /**
   * Two's complement signed remainder of two bit-vectors
   * (sign follows dividend).
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SREM,
  /**
   * Two's complement signed remainder
   * (sign follows divisor).
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SMOD,
  /**
   * Unsigned division of two bit-vectors, truncating towards 0
   * (defined to be the all-ones bit pattern, if divisor is 0).
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_UDIV_TOTAL,
  /**
   * Unsigned remainder from truncating division of two bit-vectors
   * (defined to be equal to the dividend, if divisor is 0).
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_UREM_TOTAL,
  /**
   * Bit-vector shift left.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SHL,
  /**
   * Bit-vector logical shift right.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_LSHR,
  /**
   * Bit-vector arithmetic shift right.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_ASHR,
  /**
   * Bit-vector unsigned less than.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_ULT,
  /**
   * Bit-vector unsigned less than or equal.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_ULE,
  /**
   * Bit-vector unsigned greater than.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_UGT,
  /**
   * Bit-vector unsigned greater than or equal.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_UGE,
  /* Bit-vector signed less than.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SLT,
  /**
   * Bit-vector signed less than or equal.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SLE,
  /**
   * Bit-vector signed greater than.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SGT,
  /**
   * Bit-vector signed greater than or equal.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SGE,
  /**
   * Bit-vector unsigned less than, returns bit-vector of size 1.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_ULTBV,
  /**
   * Bit-vector signed less than. returns bit-vector of size 1.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector Sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SLTBV,
  /**
   * Same semantics as regular ITE, but condition is bit-vector of size 1.
   * Parameters: 3
   *   -[1]: a bit-vector condition Term of size 1
   *   -[2]: the 'then' Term
   *   -[3]: the 'else' Term
   * 'then' and 'else' term must have same base sort.
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_ITE,
  /**
   * Bit-vector redor.
   * Parameters: 1
   *   -[1]: Term of bit-vector Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  BITVECTOR_REDOR,
  /**
   * Bit-vector redand.
   * Parameters: 1
   *   -[1]: Term of bit-vector Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  BITVECTOR_REDAND,
#if 0
  /* formula to be treated as a bv atom via eager bit-blasting
   * (internal-only symbol) */
  BITVECTOR_EAGER_ATOM,
  /* term to be treated as a variable. used for eager bit-blasting Ackermann
   * expansion of bvudiv (internal-only symbol) */
  BITVECTOR_ACKERMANIZE_UDIV,
  /* term to be treated as a variable. used for eager bit-blasting Ackermann
   * expansion of bvurem (internal-only symbol) */
  BITVECTOR_ACKERMANIZE_UREM,
  /* operator for the bit-vector boolean bit extract.
   * One parameter, parameter is the index of the bit to extract */
  BITVECTOR_BITOF_OP,
#endif
  /**
   * Operator for bit-vector extract (from index 'high' to 'low').
   * Parameters: 2
   *   -[1]: the 'high' index
   *   -[2]: the 'low' index
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param, uint32_t param)
   */
  BITVECTOR_EXTRACT_OP,
  /**
   * Operator for bit-vector repeat.
   * Parameter 1:
   *   -[1]: the number of times to repeat a given bit-vector
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param).
   */
  BITVECTOR_REPEAT_OP,
  /**
   * Operator for bit-vector zero-extend.
   * Parameter 1:
   *   -[1]: the number of bits by which a given bit-vector is to be extended
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param).
   */
  BITVECTOR_ZERO_EXTEND_OP,
  /**
   * Operator for bit-vector sign-extend.
   * Parameter 1:
   *   -[1]: the number of bits by which a given bit-vector is to be extended
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param).
   */
  BITVECTOR_SIGN_EXTEND_OP,
  /**
   * Operator for bit-vector rotate left.
   * Parameter 1:
   *   -[1]: the number of bits by which a given bit-vector is to be rotated
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param).
   */
  BITVECTOR_ROTATE_LEFT_OP,
  /**
   * Operator for bit-vector rotate right.
   * Parameter 1:
   *   -[1]: the number of bits by which a given bit-vector is to be rotated
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param).
   */
  BITVECTOR_ROTATE_RIGHT_OP,
#if 0
  /* bit-vector boolean bit extract.
   * first parameter is a BITVECTOR_BITOF_OP, second is a bit-vector term */
  BITVECTOR_BITOF,
#endif
  /* Bit-vector extract.
   * Parameters: 2
   *   -[1]: a BITVECTOR_EXTRACT_OP Term
   *   -[2]: a bit-vector term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  BITVECTOR_EXTRACT,
  /* Bit-vector repeat.
   * Parameters: 2
   *   -[1]: is a BITVECTOR_REPEAT_OP Term
   *   -[2]: a bit-vector term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  BITVECTOR_REPEAT,
  /* Bit-vector zero-extend.
   * Parameters: 2
   *   -[1]: a BITVECTOR_ZERO_EXTEND_OP Term
   *   -[2]: a bit-vector term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  BITVECTOR_ZERO_EXTEND,
  /* Bit-vector sign-extend.
   * Parameters: 2
   *   -[1]: a BITVECTOR_SIGN_EXTEND_OP Term
   *   -[2]: a bit-vector term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  BITVECTOR_SIGN_EXTEND,
  /* Bit-vector rotate left.
   * Parameters: 2
   *   -[1]: a BITVECTOR_ROTATE_LEFT_OP Term
   *   -[2]: a bit-vector term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  BITVECTOR_ROTATE_LEFT,
  /**
   * Bit-vector rotate right.
   * Parameters: 2
   *   -[1]: a BITVECTOR_ROTATE_RIGHT_OP Term
   *   -[2]: a bit-vector term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  BITVECTOR_ROTATE_RIGHT,
  /**
   * Operator for the conversion from Integer to bit-vector.
   * Parameter: 1
   *   -[1]: the size of the bit-vector to convert to
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param).
   */
  INT_TO_BITVECTOR_OP,
  /**
   * Integer conversion to bit-vector.
   * Parameters: 2
   *   -[1]: an INT_TO_BITVECTOR_OP Term
   *   -[2]: an Integer term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INT_TO_BITVECTOR,
  /**
   * Bit-vector conversion to (nonnegative) integer.
   * Parameter: 1
   *   -[1]: Term of bit-vector Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  BITVECTOR_TO_NAT,

  /* FP -------------------------------------------------------------------- */

  /**
   * Floating-point constant, constructed from a double or string.
   * !! Note: Currently unsupported !!
   * Parameters: 3
   *   -[1]: size of the exponent
   *   -[2]: size of the significand
   *   -[3]: the value of the floating-point constant
   * Create with:
   *   mkConst(Kind kind, uint32_t arg1, uint32_t arg2, double arg3)
   *   mkConst(Kind kind, uint32_t arg1, uint32_t arg2, const std::string& arg3)
   */
  CONST_FLOATINGPOINT,
  /**
   * Floating-point rounding mode term.
   * Create with:
   *   mkConst(RoundingMode rm)
   */
  CONST_ROUNDINGMODE,
  /**
   * A floating-point constant, constructed from a bit vector.
   * Parameters: 3
   *   -[1]: size of the exponent
   *   -[2]: size of the significand
   *   -[3]: the value of the floating-point as a bit-vector
   * Create with:
   *   mkConst(Kind kind, uint32_t arg1, uint32_t arg2, Term arg3)
   */
  FLOATINGPOINT_FP,
  /**
   * Floating-point equality.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_EQ,
  /**
   * Floating-point absolute value.
   * Parameters: 1
   *   -[1]: Term of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ABS,
  /**
   * Floating-point negation.
   * Parameters: 1
   *   -[1]: Term of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_NEG,
  /**
   * Floating-point addition.
   * Parameters: 3
   *   -[1]: is a CONST_ROUNDINGMODE
   *   -[2]: a floating point term
   *   -[3]: a floating point term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_PLUS,
  /**
   * Floating-point sutraction.
   * Parameters: 3
   *   -[1]: a CONST_ROUNDINGMODE
   *   -[2]: a floating point term
   *   -[3]: a floating point term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_SUB,
  /**
   * Floating-point multiply.
   * Parameters: 3
   *   -[1]: a CONST_ROUNDINGMODE
   *   -[2]: a floating point term
   *   -[3]: a floating point term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_MULT,
  /**
   * Floating-point division.
   * Parameters: 3
   *   -[1]: a CONST_ROUNDINGMODE
   *   -[2]: a floating point term
   *   -[3]: a floating point term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_DIV,
  /**
   * Floating-point fused multiply and add.
   * Parameters: 4
   *   -[1]: a CONST_ROUNDINGMODE
   *   -[2]: a floating point term
   *   -[3]: a floating point term
   *   -[4]: a floating point term
   * Create with:
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_FMA,
  /**
   * Floating-point square root.
   * Parameters: 2
   *   -[1]: a CONST_ROUNDINGMODE
   *   -[2]: a floating point term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_SQRT,
  /**
   * Floating-point remainder.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_REM,
  /**
   * Floating-point round to integral.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_RTI,
  /**
   * Floating-point minimum.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_MIN,
  /**
   * Floating-point maximum.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_MAX,
#if 0
  /* floating-point minimum (defined for all inputs) */
  FLOATINGPOINT_MIN_TOTAL,
  /* floating-point maximum (defined for all inputs) */
  FLOATINGPOINT_MAX_TOTAL,
#endif
  /**
   * Floating-point less than or equal.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_LEQ,
  /**
   * Floating-point less than.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_LT,
  /**
   * Floating-point greater than or equal.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_GEQ,
  /**
   * Floating-point greater than.
   * Parameters: 2
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_GT,
  /**
   * Floating-point is normal.
   * Parameters: 1
   *   -[1]: Term of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISN,
  /**
   * Floating-point is sub-normal.
   * Parameters: 1
   *   -[1]: Term of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISSN,
  /**
   * Floating-point is zero.
   * Parameters: 1
   *   -[1]: Term of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISZ,
  /**
   * Floating-point is infinite.
   * Parameters: 1
   *   -[1]: Term of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISINF,
  /**
   * Floating-point is NaN.
   * Parameters: 1
   *   -[1]: Term of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISNAN,
  /**
   * Floating-point is negative.
   * Parameters: 1
   *   -[1]: Term of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISNEG,
  /**
   * Floating-point is positive.
   * Parameters: 1
   *   -[1]: Term of floating point Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISPOS,
  /**
   * Operator for to_fp from bit vector.
   * Parameters: 2
   *   -[1]: the exponent size,
   *   -[2]: the significand size
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param1, uint32_t param2)
   */
  FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP,
  /**
   * Conversion from an IEEE-754 bit vector to floating-point.
   * Parameters: 2
   *   -[1]: a FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP Term
   *   -[2]: a floating point Term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_FP_IEEE_BITVECTOR,
  /**
   * Operator for to_fp from floating point.
   * Parameters: 2
   *   -[1]: is the exponent size,
   *   -[2]: is the significand size
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param1, uint32_t param2)
   */
  FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP,
  /**
   * Conversion between floating-point sorts.
   * Parameters: 2
   *   -[1]: a FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP Term
   *   -[2]: a floating point Term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_FP_FLOATINGPOINT,
  /**
   * Operator for to_fp from real.
   * Parameters: 2
   *   -[1]: the exponent size,
   *   -[2]: the significand size
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param1, uint32_t param2)
   */
  FLOATINGPOINT_TO_FP_REAL_OP,
  /**
   * Conversion from a real to floating-point.
   * Parameters: 2
   *   -[1]: a FLOATINGPOINT_TO_FP_REAL_OP Term
   *   -[2]: a floating point Term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_FP_REAL,
  /*
   * Operator for to_fp from signed bit vector.
   * Parameters: 2
   *   -[1]: the exponent size,
   *   -[2]: the significand size
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param1, uint32_t param2)
   */
  FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP,
  /**
   * Conversion from a signed bit vector to floating-point.
   * Parameters: 2
   *   -[1]: a FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP Term
   *   -[2]: a floating point Term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
  /**
   * Operator for to_fp from unsigned bit vector.
   * Parameters: 2
   *   -[1]: the exponent size,
   *   -[2]: the significand size
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param1, uint32_t param2)
   */
  FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP,
  /**
   * Operator for converting an unsigned bit vector to floating-point.
   * Parameters: 2
   *   -[1]: a FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP Term
   *   -[2]: a floating point Term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
  /**
   * Operator for a generic to_fp.
   * Parameters: 2
   *   -[1]: the exponent size,
   *   -[2]: the significand size
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param1, uint32_t param2)
   */
  FLOATINGPOINT_TO_FP_GENERIC_OP,
  /**
   * Generic conversion to floating-point, used in parsing only.
   * Parameters: 2
   *   -[1]: a FLOATINGPOINT_TO_FP_GENERIC_OP Term
   *   -[2]: a floating point Term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_FP_GENERIC,
  /**
   * Operator for to_ubv.
   * Parameters: 1
   *   -[1]: the size of the bit-vector to convert to
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param)
   */
  FLOATINGPOINT_TO_UBV_OP,
  /**
   * Conversion from a floating-point value to an unsigned bit vector.
   * Parameters: 2
   *   -[1]: a FLOATINGPOINT_TO_FP_TO_UBV_OP Term
   *   -[2]: a floating point Term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_UBV,
  /**
   * Operator for to_ubv_total.
   * Parameters: 1
   *   -[1]: the size of the bit-vector to convert to.
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param)
   */
  FLOATINGPOINT_TO_UBV_TOTAL_OP,
  /**
   * Conversion from  a floating-point value to an unsigned bit vector
   * (defined for all inputs).
   * Parameters: 2
   *   -[1]: a FLOATINGPOINT_TO_FP_TO_UBV_TOTAL_OP Term
   *   -[2]: a floating point Term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_UBV_TOTAL,
  /**
   * Operator for to_sbv.
   * Parameters: 1
   *   -[1]: the size of the bit-vector to convert to
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param)
   */
  FLOATINGPOINT_TO_SBV_OP,
  /**
   * Conversion from a floating-point value to a signed bit vector.
   * Parameters: 2
   *   -[1]: a FLOATINGPOINT_TO_FP_TO_SBV_OP Term
   *   -[2]: a floating point Term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_SBV,
  /**
   * Operator for to_sbv_total.
   * Parameters: 1
   *   -[1]: the size of the bit-vector to convert to
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param)
   */
  FLOATINGPOINT_TO_SBV_TOTAL_OP,
  /**
   * Conversion from a floating-point value to a signed bit vector
   * (defined for all inputs).
   * Parameters: 2
   *   -[1]: a FLOATINGPOINT_TO_FP_TO_SBV_TOTAL_OP Term
   *   -[2]: a floating point Term
   * Create with:
   *   mkTerm(Term opTerm, Term child)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_SBV_TOTAL,
  /**
   * Floating-point to real.
   * Parameters: 1
   *   -[1]: a floating point Term
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_TO_REAL,
  /**
   * Floating-point to real (defined for all inputs).
   * Parameters: 1
   *   -[1]: a floating point Term
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_TO_REAL_TOTAL,

  /* Arrays ---------------------------------------------------------------- */

  /**
   * Aarray select.
   * Parameters: 2
   *   -[1]: an array term
   *   -[2]: the selection index
   * Create with:
   *   mkTerm(Term opTerm, Term child1, Term child2)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  SELECT,
  /**
   * Array store.
   * Parameters: 3
   *   -[1]: an array term
   *   -[2]: the store index
   *   -[3]: the term to store at the index
   * Create with:
   *   mkTerm(Term opTerm, Term child1, Term child2, Term child3)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   */
  STORE,
  /**
   * Constant array.
   * Parameters: 2
   *   -[1]: an array sort
   *   -[2]: a term representing a constant
   * Create with:
   *   mkTerm(Term opTerm, Term child1, Term child2)
   *   mkTerm(Term opTerm, const std::vector<Term>& children)
   *
   * Note: We currently support the creation of constant arrays, but under some
   * conditions when there is a chain of equalities connecting two constant
   * arrays, the solver doesn't know what to do and aborts (Issue #1667).
   */
  STORE_ALL,
#if 0
  /* array table function (internal-only symbol) */
  ARR_TABLE_FUN,
  /* array lambda (internal-only symbol) */
  ARRAY_LAMBDA,
  /* partial array select, for internal use only */
  PARTIAL_SELECT_0,
  /* partial array select, for internal use only */
  PARTIAL_SELECT_1,
#endif

  /* Datatypes ------------------------------------------------------------- */

  /**
   * Constructor application.
   * Paramters: n > 0
   *   -[1]: the constructor
   *   -[2]..[n]: parameters to the constructor
   * Create with:
   *   mkTerm(Kind kind)
   *   mkTerm(Kind kind, Term child)
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  APPLY_SELECTOR,
  /**
   * Datatype selector application.
   * Parameters: 1
   *   -[1]: a datatype term (undefined if mis-applied)
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  APPLY_CONSTRUCTOR,
  /**
   * Datatype selector application.
   * Parameters: 1
   *   -[1]: a datatype term (defined rigidly if mis-applied)
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  APPLY_SELECTOR_TOTAL,
  /**
   * Datatype tester application.
   * Parameters: 2
   *   -[1]: a tester term
   *   -[2]: a datatype term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  APPLY_TESTER,
#if 0
  /* Parametric datatype term.  */
  PARAMETRIC_DATATYPE,
  /* type ascription, for datatype constructor applications;
   * first parameter is an ASCRIPTION_TYPE, second is the datatype constructor
   * application being ascribed */
  APPLY_TYPE_ASCRIPTION,
#endif
  /**
   * Operator for a tuple update.
   * Parameters: 1
   *   -[1]: the index of the tuple to be updated
   * Create with:
   *   mkOpTerm(Kind kind, uint32_t param)
   */
  TUPLE_UPDATE_OP,
  /**
   * Tuple update.
   * Parameters: 3
   *   -[1]: a TUPLE_UPDATE_OP (which references an index)
   *   -[2]: the tuple
   *   -[3]: the element to store in the tuple at the given index
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  TUPLE_UPDATE,
  /**
   * Operator for a record update.
   * Parameters: 1
   *   -[1]: the name of the field to be updated
   * Create with:
   *   mkOpTerm(Kind kind, const std::string& param)
   */
  RECORD_UPDATE_OP,
  /**
   * Record update.
   * Parameters: 3
   *   -[1]: a RECORD_UPDATE_OP Term (which references a field)
   *   -[2]: a record term to update
   *   -[3]: the element to store in the record in the given field
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  RECORD_UPDATE,
#if 0
  /* datatypes size */
  DT_SIZE,
  /* datatypes height bound */
  DT_HEIGHT_BOUND,
  /* datatypes height bound */
  DT_SIZE_BOUND,
  /* datatypes sygus bound */
  DT_SYGUS_BOUND,
  /* datatypes sygus term order */
  DT_SYGUS_TERM_ORDER,
  /* datatypes sygus is constant */
  DT_SYGUS_IS_CONST,
#endif

  /* Separation Logic ------------------------------------------------------ */

  /**
   * Separation logic nil constant.
   * Parameters: 0
   * Create with:
   *   mkConst(Kind kind)
   */
  SEP_NIL,
  /**
   * Separation logic empty heap.
   * Parameters: 2
   *   -[1]: ???
   *   -[2]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEP_EMP,
  /**
   * Separation logic points to relation.
   * Parameters: 2
   *   -[1]: ???
   *   -[2]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEP_PTO,
  /**
   * Separation logic star.
   * Parameters: 2
   *   -[1]: ???
   *   -[2]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEP_STAR,
  /**
   * Separation logic magic wand.
   * Parameters: 2
   *   -[1]: ???
   *   -[2]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEP_WAND,
#if 0
  /* separation label (internal use only) */
  SEP_LABEL,
#endif

  /* Sets ------------------------------------------------------------------ */

  /**
   * Empty set constant.
   * Parameters: 1
   *   -[1]: the sort of the set elements
   * Create with:
   *   mkEmptySet(Sort sort)
   *   mkConst(Sort sort)
   */
  EMPTYSET,
  /**
   * Set union.
   * Parameters: 2
   *   -[1]..[2]: Terms of set Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  UNION,
  /**
   * Set intersection.
   * Parameters: 2
   *   -[1]..[2]: Terms of set Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INTERSECTION,
  /**
   * Set subtraction.
   * Parameters: 2
   *   -[1]..[2]: Terms of set Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SETMINUS,
  /**
   * Subset predicate.
   * Parameters: 2
   *   -[1]..[2]: Terms of set Sort, [1] a subset of set [2]?
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SUBSET,
  /**
   * Set membership predicate.
   * Parameters: 2
   *   -[1]..[2]: Terms of set Sort, [1] a member of set [2]?
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  MEMBER,
  /**
   * The set of the single element given as a parameter.
   * Parameters: 1
   *   -[1]: the single element
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  SINGLETON,
  /**
   * The set obtained by inserting elements;
   * Parameters: n > 0
   *   -[1]..[n-1]: the elements inserted into set [n]
   *   -[n]: a set Term
   * Create with:
   *   mkTerm(Kind kind, Term child)
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INSERT,
  /**
   * Set cardinality.
   * Parameters: 1
   *   -[1]: the set to determine the cardinality of
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  CARD,
  /**
   * Set complement with respect to finite universe.
   * Parameters: 1
   *   -[1]: is the set to complement
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  COMPLEMENT,
  /**
   * Finite universe set.
   * All set variables must be interpreted as subsets of it.
   * Create with:
   *   mkUniverseSet(Sort sort)
   */
  UNIVERSE_SET,
  /**
   * Set join.
   * Parameters: 2
   *   -[1]..[2]: Terms of set Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  JOIN,
  /**
   * Set cartesian product.
   * Parameters: 2
   *   -[1]..[2]: Terms of set Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  PRODUCT,
  /**
   * Set transpose.
   * Parameters: 1
   *   -[1]: Term of set Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  TRANSPOSE,
  /**
   * Set transitive closure.
   * Parameters: 1
   *   -[1]: Term of set Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  TCLOSURE,
  /**
   * Set join image.
   * Parameters: 2
   *   -[1]..[2]: Terms of set Sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  JOIN_IMAGE,
  /**
   * Set identity.
   * Parameters: 1
   *   -[1]: Term of set Sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  IDEN,

  /* Strings --------------------------------------------------------------- */

  /**
   * String concat.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of String sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_CONCAT,
  /**
   * String membership.
   * Parameters: 2
   *   -[1]..[2]: Terms of String sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_IN_REGEXP,
  /**
   * String length.
   * Parameters: 1
   *   -[1]: Term of String sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_LENGTH,
  /**
   * String substr.
   * Parameters: 3
   *   -[1]: ???
   *   -[2]: ???
   *   -[3]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_SUBSTR,
  /**
   * String ???.
   * Parameters: 2
   *   -[1]: ???
   *   -[2]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_CHARAT,
  /**
   * String contains.
   * Parameters: 2
   *   -[1]: ???
   *   -[2]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_STRCTN,
  /**
   * String index-of.
   * Parameters: 3
   *   -[1]: ???
   *   -[2]: ???
   *   -[3]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_STRIDOF,
  /**
   * String replace.
   * Parameters: 3
   *   -[1]: ???
   *   -[2]: ???
   *   -[3]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_STRREPL,
  /**
   * String prefix-of.
   * Parameters: 2
   *   -[1]: ???
   *   -[2]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_PREFIX,
  /**
   * String suffix-of.
   * Parameters: 2
   *   -[1]: ???
   *   -[2]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_SUFFIX,
  /**
   * Integer to string.
   * Parameters: 1
   *   -[1]: Term of sort Integer
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_ITOS,
  /**
   * String to integer (total function).
   * Parameters: 1
   *   -[1]: Term of sort String
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_STOI,
  /**
   * String of characters constant.
   * Parameters:
   *   See mkString()
   * Create with:
   *   mkString(const char* s)
   *   mkString(const std::string& s)
   *   mkString(const unsigned char c)
   *   mkString(const std::vector<unsigned>& s)
   *   mkConst(Kind kind, const char* s)
   *   mkConst(Kind kind, const std::string& s)
   */
  CONST_STRING,
  /**
   * Regular expression constant.
   * Parameters:
   *   See mkRegExp()
   * Create with:
   *   mkRegExp()
   *   mkRegExp(int32_t type)
   *   mkConst(Kind kind)
   *   mkConst(Kind kind, int32_t arg)  ??? what is arg?
   */
  CONST_REGEXP,
  /**
   * Conversion from string to regexp.
   * Parameters: 1
   *   -[1]: Term of sort String
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_TO_REGEXP,
  /**
   * Regexp Concatenation .
   * Parameters: 2
   *   -[1]..[2]: Terms of Regexp sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  REGEXP_CONCAT,
  /**
   * Regexp union.
   * Parameters: 2
   *   -[1]..[2]: Terms of Regexp sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  REGEXP_UNION,
  /**
   * Regexp intersection.
   * Parameters: 2
   *   -[1]..[2]: Terms of Regexp sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  REGEXP_INTER,
  /**
   * Regexp *.
   * Parameters: 1
   *   -[1]: Term of sort Regexp
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  REGEXP_STAR,
  /**
   * Regexp +.
   * Parameters: 1
   *   -[1]: Term of sort Regexp
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  REGEXP_PLUS,
  /**
   * Regexp ?.
   * Parameters: 1
   *   -[1]: Term of sort Regexp
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  REGEXP_OPT,
  /**
   * Regexp range.
   * Parameters: 1
   *   -[1]: Term of sort Regexp
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  REGEXP_RANGE,
  /**
   * Regexp loop.
   * Parameters: 2 (3)
   *   -[1]: ???
   *   -[2]: ???
   *   -[3]: ???
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  REGEXP_LOOP,
  /**
   * Regexp empty.
   * Parameters: ???
   * Create with:
   *   ???
   */
  REGEXP_EMPTY,
  /**
   * Regexp all characters.
   * Parameters: ???
   * Create with:
   *   ???
   */
  REGEXP_SIGMA,
#if 0
  /* regexp rv (internal use only) */
  REGEXP_RV,
#endif

  /* Quantifiers ----------------------------------------------------------- */

  /**
   * Universally quantified formula.
   * Parameters: 2 (3)
   *   -[1]: a BOUND_VAR_LIST Term
   *   -[2]: the quantifier body
   *   -[3]: (optional) an INST_PATTERN_LIST Term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FORALL,
  /**
   * Existentially quantified formula.
   * Parameters: 2 (3)
   *   -[1]: a BOUND_VAR_LIST Term
   *   -[2]: the quantifier body
   *   -[3]: (optional) an INST_PATTERN_LIST Term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  EXISTS,
#if 0
  /* instantiation constant */
  INST_CONSTANT,
  /* instantiation pattern */
  INST_PATTERN,
  /* a list of bound variables (used to bind variables under a quantifier) */
  BOUND_VAR_LIST,
  /* instantiation no-pattern */
  INST_NO_PATTERN,
  /* instantiation attribute */
  INST_ATTRIBUTE,
  /* a list of instantiation patterns */
  INST_PATTERN_LIST,
  /* predicate for specifying term in instantiation closure. */
  INST_CLOSURE,
  /* general rewrite rule (for rewrite-rules theory) */
  REWRITE_RULE,
  /* actual rewrite rule (for rewrite-rules theory) */
  RR_REWRITE,
  /* actual reduction rule (for rewrite-rules theory) */
  RR_REDUCTION,
  /* actual deduction rule (for rewrite-rules theory) */
  RR_DEDUCTION,

  /* Sort Kinds ------------------------------------------------------------ */

  /* array type */
   ARRAY_TYPE,
  /* a type parameter for type ascription */
  ASCRIPTION_TYPE,
  /* constructor */
  CONSTRUCTOR_TYPE,
  /* a datatype type index */
  DATATYPE_TYPE,
  /* selector */
  SELECTOR_TYPE,
  /* set type, takes as parameter the type of the elements */
  SET_TYPE,
  /* sort tag */
  SORT_TAG,
  /* specifies types of user-declared 'uninterpreted' sorts */
  SORT_TYPE,
  /* tester */
  TESTER_TYPE,
  /* a representation for basic types */
  TYPE_CONSTANT,
  /* a function type */
  FUNCTION_TYPE,
  /* the type of a symbolic expression */
  SEXPR_TYPE,
  /* bit-vector type */
  BITVECTOR_TYPE,
  /* floating-point type */
  FLOATINGPOINT_TYPE,
#endif

  /* ----------------------------------------------------------------------- */
  /* marks the upper-bound of this enumeration */
  LAST_KIND
};

/**
 * Serialize a kind to given stream.
 * @param out the output stream
 * @param k the kind to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, Kind k) CVC4_PUBLIC;

/**
 * Hash function for Kinds.
 */
struct CVC4_PUBLIC KindHashFunction
{
  size_t operator()(Kind k) const;
};

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

struct SortHashFunction;
class Datatype;

/**
 * The sort of a CVC4 term.
 */
class CVC4_PUBLIC Sort
{
  friend class DatatypeConstructorDecl;
  friend class DatatypeDecl;
  friend class Solver;
  friend struct SortHashFunction;

  public:
    /**
     * Constructor.
     * @param t the internal type that is to be wrapped by this sort
     * @return the Sort
     */
    Sort(const CVC4::Type& t);

    /**
     * Copy constructor.
     */
    Sort(const Sort& s);

    /**
     * Destructor.
     */
    ~Sort();

    /**
     * Assignment operator.
     * @param s the sort to assign to this sort
     * @return this sort after assignment
     */
    Sort& operator=(const Sort& s);

    /**
     * Comparison for structural equality.
     * @param s the sort to compare to
     * @return true if the sorts are equal
     */
    bool operator==(const Sort& s) const;

    /**
     * Comparison for structural disequality.
     * @param s the sort to compare to
     * @return true if the sorts are not equal
     */
    bool operator!=(const Sort& s) const;

    /**
     * Is this a Boolean sort?
     * @return true if the sort is a Boolean sort
     */
    bool isBoolean() const;

    /**
     * Is this a integer sort?
     * @return true if the sort is a integer sort
     */
    bool isInteger() const;

    /**
     * Is this a real sort?
     * @return true if the sort is a real sort
     */
    bool isReal() const;

    /**
     * Is this a string sort?
     * @return true if the sort is the string sort
     */
    bool isString() const;

    /**
     * Is this a regexp sort?
     * @return true if the sort is the regexp sort
     */
    bool isRegExp() const;

    /**
     * Is this a rounding mode sort?
     * @return true if the sort is the rounding mode sort
     */
    bool isRoundingMode() const;

    /**
     * Is this a bit-vector sort?
     * @return true if the sort is a bit-vector sort
     */
    bool isBitVector() const;

    /**
     * Is this a floating-point sort?
     * @return true if the sort is a floating-point sort
     */
    bool isFloatingPoint() const;

    /**
     * Is this a datatype sort?
     * @return true if the sort is a datatype sort
     */
    bool isDatatype() const;

    /**
     * Is this a function sort?
     * @return true if the sort is a function sort
     */
    bool isFunction() const;

    /**
     * Is this a predicate sort?
     * That is, is this a function sort mapping to Boolean? All predicate
     * sorts are also function sorts.
     * @return true if the sort is a predicate sort
     */
    bool isPredicate() const;

    /**
     * Is this a tuple sort?
     * @return true if the sort is a tuple sort
     */
    bool isTuple() const;

    /**
     * Is this a record sort?
     * @return true if the sort is a record sort
     */
    bool isRecord() const;

    /**
     * Is this an array sort?
     * @return true if the sort is a array sort
     */
    bool isArray() const;

    /**
     * Is this a Set sort?
     * @return true if the sort is a Set sort
     */
    bool isSet() const;

    /**
     * Is this a sort kind?
     * @return true if this is a sort kind
     */
    bool isSort() const;

    /**
     * Is this a sort constructor kind?
     * @return true if this is a sort constructor kind
     */
    bool isSortConstructor() const;

    /**
     * @return the underlying datatype of a datatype sort
     */
    Datatype getDatatype() const;

    /**
     * Instantiate a parameterized datatype/sort sort.
     * Create sorts parameter with Solver::mkParamSort().
     * @param params the list of sort parameters to instantiate with
     */
    Sort instantiate(const std::vector<Sort>& params) const;

    /**
     * Output a string representation of this sort to a given stream.
     * @param out the output stream
     */
    void toStream(std::ostream& out) const;

    /**
     * @return a string representation of this sort
     */
    std::string toString() const;

  private:
    /* The interal type wrapped by this sort. */
    CVC4::Type* d_type;
};

/**
 * Serialize a sort to given stream.
 * @param out the output stream
 * @param s the sort to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<< (std::ostream& out, const Sort& s) CVC4_PUBLIC;

/**
 * Hash function for Sorts.
 */
struct CVC4_PUBLIC SortHashFunction
{
  size_t operator()(const Sort& s) const;
};


/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

struct TermHashFunction;

/**
 * A CVC4 Term.
 */
class CVC4_PUBLIC Term
{
  friend class Solver;
  friend struct TermHashFunction;

  public:
    /**
     * Constructor.
     */
    Term();

    /**
     * Constructor.
     * @param e the internal expression that is to be wrapped by this term
     * @return the Term
     */
    Term(const CVC4::Expr& e);

    /**
     * Copy constructor.
     */
    Term(const Term& t);

    /**
     * Destructor.
     */
    ~Term();

    /**
     * Assignment operator, makes a copy of the given term.
     * Both terms must belong to the same solver object.
     * @param t the term to assign
     * @return the reference to this term after assignment
     */
    Term& operator=(const Term& t);

    /**
     * Syntactic equality operator.
     * Return true if both terms are syntactically identical.
     * Both terms must belong to the same solver object.
     * @param t the term to compare to for equality
     * @return true if the terms are equal
     */
    bool operator==(const Term& t) const;

    /**
     * Syntactic disequality operator.
     * Return true if both terms differ syntactically.
     * Both terms must belong to the same solver object.
     * @param t the term to compare to for disequality
     * @return true if terms are disequal
     */
    bool operator!=(const Term& t) const;

    /**
     * @return the kind of this term
     */
    Kind getKind() const;

    /**
     * @return the sort of this term
     */
    Sort getSort() const;

    /**
     * @return true if this Term is a null term
     */
    bool isNull() const;

    /**
     * Boolean negation.
     * @return the Boolean negation of this term
     */
    Term notTerm() const;

    /**
     * Boolean or.
     * @param t a Boolean term
     * @return the conjunction of this term and the given term
     */
    Term andTerm(const Term& t) const;

    /**
     * Boolean or.
     * @param t a Boolean term
     * @return the disjunction of this term and the given term
     */
    Term orTerm(const Term& t) const;

    /**
     * Boolean exclusive or.
     * @param t a Boolean term
     * @return the exclusive disjunction of this term and the given term
     */
    Term xorTerm(const Term& t) const;

    /**
     * Boolean if-and-only-if.
     * @param t a Boolean term
     * @return the Boolean equivalence of this term and the given term
     */
    Term iffTerm(const Term& t) const;

    /**
     * Boolean implication.
     * @param t a Boolean term
     * @return the implication of this term and the given term
     */
    Term impTerm(const Term& t) const;

    /**
     * If-then-else with this term as the Boolean condition.
     * @param then_t the 'then' term
     * @param else_t the 'else' term
     * @return the if-then-else term with this term as the Boolean condition
     */
    Term iteTerm(const Term& then_t, const Term& else_t) const;

    /**
     * @return a string representation of this term
     */
    std::string toString() const;

    /**
     * Iterator for the children of a Term.
     */
    class const_iterator : public std::iterator<std::input_iterator_tag, Term>
    {
      friend class Term;

      public:
        /**
         * Constructor.
         */
        const_iterator();

        /**
         * Copy constructor.
         */
        const_iterator(const const_iterator& it);

        /**
         * Destructor.
         */
        ~const_iterator();

        /**
         * Assignment operator.
         * @param it the iterator to assign to
         * @return the reference to the iterator after assignment
         */
        const_iterator& operator=(const const_iterator& it);

        /**
         * Equality operator.
         * @param it the iterator to compare to for equality
         * @return true if the iterators are equal
         */
        bool operator==(const const_iterator& it) const;

        /**
         * Disequality operator.
         * @param it the iterator to compare to for disequality
         * @return true if the iterators are disequal
         */
        bool operator!=(const const_iterator& it) const;

        /**
         * Increment operator (prefix).
         * @return a reference to the iterator after incrementing by one
         */
        const_iterator& operator++();

        /**
         * Increment operator (postfix).
         * @return a reference to the iterator after incrementing by one
         */
        const_iterator operator++(int);

        /**
         * Dereference operator.
         * @return the term this iterator points to
         */
        Term operator*() const;

      private:
        /* The internal expression iterator wrapped by this iterator. */
        void* d_iterator;
        /* Constructor. */
        explicit const_iterator(void*);
    };

  /**
   * @return an iterator to the first child of this Term
   */
  const_iterator begin() const;

  /**
   * @return an iterator to one-off-the-last child of this Term
   */
  const_iterator end() const;

  private:
    /* The internal expression wrapped by this term. */
    CVC4::Expr* d_expr;
};

/**
 * Serialize a term to given stream.
 * @param out the output stream
 * @param t the term to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<< (std::ostream& out, const Term& t) CVC4_PUBLIC;

/**
 * Serialize a vector of terms to given stream.
 * @param out the output stream
 * @param vector the vector of terms to be serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const std::vector<Term>& vector) CVC4_PUBLIC;

/**
 * Serialize a set of terms to the given stream.
 * @param out the output stream
 * @param set the set of terms to be serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const std::set<Term>& set) CVC4_PUBLIC;

/**
 * Serialize an unordered_set of terms to the given stream.
 *
 * @param out the output stream
 * @param unordered_set the set of terms to be serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const std::unordered_set<Term, TermHashFunction>&
                             unordered_set) CVC4_PUBLIC;

/**
 * Serialize a map of terms to the given stream.
 *
 * @param out the output stream
 * @param map the map of terms to be serialized to the given stream
 * @return the output stream
 */
template <typename V>
std::ostream& operator<<(std::ostream& out,
                         const std::map<Term, V>& map) CVC4_PUBLIC;

/**
 * Serialize an unordered_map of terms to the given stream.
 *
 * @param out the output stream
 * @param unordered_map the map of terms to be serialized to the given stream
 * @return the output stream
 */
template <typename V>
std::ostream& operator<<(std::ostream& out,
                         const std::unordered_map<Term, V, TermHashFunction>&
                             unordered_map) CVC4_PUBLIC;

/**
 * Hash function for Terms.
 */
struct CVC4_PUBLIC TermHashFunction
{
  size_t operator()(const Term& t) const;
};


/* -------------------------------------------------------------------------- */
/* Datatypes                                                                  */
/* -------------------------------------------------------------------------- */

class DatatypeConstructorIterator;
class DatatypeIterator;

/**
 * A place-holder sort to allow a DatatypeDecl to refer to itself.
 * Self-sorted fields of DatatypeDecls will be properly sorted when a Sort is
 * created for the DatatypeDecl.
 */
class CVC4_PUBLIC DatatypeDeclSelfSort
{
};

/**
 * A CVC4 datatype selector declaration.
 */
class CVC4_PUBLIC DatatypeSelectorDecl
{
  friend class DatatypeConstructorDecl;
  public:
    /**
     * Constructor.
     * @param name the name of the datatype selector
     * @param sort the sort of the datatype selector
     * @return the DatatypeSelectorDecl
     */
    DatatypeSelectorDecl(const std::string& name, Sort sort);

    /**
     * Constructor.
     * @param name the name of the datatype selector
     * @param sort the sort of the datatype selector
     * @return the DAtatypeSelectorDecl
     */
    DatatypeSelectorDecl(const std::string& name, DatatypeDeclSelfSort sort);

    /**
     * @return a string representation of this datatype selector
     */
    std::string toString() const;

  private:
    /* The name of the datatype selector. */
    std::string d_name;
    /* The sort of the datatype selector. */
    Sort d_sort;
};

/**
 * A CVC4 datatype constructor declaration.
 */
class CVC4_PUBLIC DatatypeConstructorDecl
{
  friend class DatatypeDecl;
  public:
    /**
     * Constructor.
     * @param name the name of the datatype constructor
     * @return the DatatypeConstructorDecl
     */
    DatatypeConstructorDecl(const std::string& name);

    /**
     * Destructor.
     */
    ~DatatypeConstructorDecl();

    /**
     * Add datatype selector declaration.
     * @param stor the datatype selector declaration to add
     */
    void addSelector(const DatatypeSelectorDecl& stor);

    /**
     * @return a string representation of this datatype constructor declaration
     */
    std::string toString() const;

  private:
    /* The internal (intermediate) datatype constructor wrapped by this
     * datatype constructor declaration. */
    std::shared_ptr<CVC4::DatatypeConstructor> d_ctor;
};

/**
 * A CVC4 datatype declaration.
 */
class CVC4_PUBLIC DatatypeDecl
{
  friend class Solver;
  public:
    /**
     * Constructor.
     * @param name the name of the datatype
     * @param isCoDatatype true if a codatatype is to be constructed
     * @return the DatatypeDecl
     */
    DatatypeDecl(const std::string& name, bool isCoDatatype = false);

    /**
     * Constructor for parameterized datatype declaration.
     * Create sorts parameter with Solver::mkParamSort().
     * @param name the name of the datatype
     * @param param the sort parameter
     * @param isCoDatatype true if a codatatype is to be constructed
     */
    DatatypeDecl(const std::string& name,
                 Sort param,
                 bool isCoDatatype = false);

    /**
     * Constructor for parameterized datatype declaration.
     * Create sorts parameter with Solver::mkParamSort().
     * @param name the name of the datatype
     * @param params a list of sort parameters
     * @param isCoDatatype true if a codatatype is to be constructed
     */
    DatatypeDecl(const std::string& name,
                 const std::vector<Sort>& params,
                 bool isCoDatatype = false);

    /**
     * Destructor.
     */
    ~DatatypeDecl();

    /**
     * Add datatype constructor declaration.
     * @param ctor the datatype constructor declaration to add
     */
    void addConstructor(const DatatypeConstructorDecl& ctor);

    /**
     * @return a string representation of this datatype declaration
     */
    std::string toString() const;

  private:
    /* The internal (intermediate) datatype wrapped by this datatype
     * declaration */
    std::shared_ptr<CVC4::Datatype> d_dtype;
};

/**
 * A CVC4 datatype selector.
 */
class CVC4_PUBLIC DatatypeSelector
{
  public:
    /**
     * Constructor.
     */
    DatatypeSelector();

    /**
     * Constructor.
     * @param stor the internal datatype selector to be wrapped
     * @return the DatatypeSelector
     */
    DatatypeSelector(const CVC4::DatatypeConstructorArg& stor);

    /**
     * Destructor.
     */
    ~DatatypeSelector();

    /**
     * @return a string representation of this datatype selector
     */
    std::string toString() const;

  private:
    /* The internal datatype selector wrapped by this datatype selector. */
    std::shared_ptr<CVC4::DatatypeConstructorArg> d_stor;
};

/**
 * A CVC4 datatype constructor.
 */
class CVC4_PUBLIC DatatypeConstructor
{
  public:
    /**
     * Constructor.
     */
    DatatypeConstructor();

    /**
     * Constructor.
     * @param ctor the internal datatype constructor to be wrapped
     * @return thte DatatypeConstructor
     */
    DatatypeConstructor(const CVC4::DatatypeConstructor& ctor);

    /**
     * Destructor.
     */
    ~DatatypeConstructor();

    /**
     * Get the datatype selector with the given name.
     * This is a linear search through the selectors, so in case of
     * multiple, similarly-named selectors, the first is returned.
     * @param name the name of the datatype selector
     * @return the first datatype selector with the given name
     */
    DatatypeSelector operator[](const std::string& name) const;
    DatatypeSelector getSelector(const std::string& name) const;

    /**
     * Get the term representation of the datatype selector with the given name.
     * This is a linear search through the arguments, so in case of multiple,
     * similarly-named arguments, the selector for the first is returned.
     * @param name the name of the datatype selector
     * @return a term representing the datatype selector with the given name
     */
    Term getSelectorTerm(const std::string& name) const;

    /**
     * @return a string representation of this datatype constructor
     */
    std::string toString() const;

    /**
     * Iterator for the selectors of a datatype constructor.
     */
    class const_iterator
        : public std::iterator<std::input_iterator_tag, DatatypeConstructor>
    {
      friend class DatatypeConstructor; // to access constructor

      public:
        /**
         * Assignment operator.
         * @param it the iterator to assign to
         * @return the reference to the iterator after assignment
         */
        const_iterator& operator=(const const_iterator& it);

        /**
         * Equality operator.
         * @param it the iterator to compare to for equality
         * @return true if the iterators are equal
         */
        bool operator==(const const_iterator& it) const;

        /**
         * Disequality operator.
         * @param it the iterator to compare to for disequality
         * @return true if the iterators are disequal
         */
        bool operator!=(const const_iterator& it) const;

        /**
         * Increment operator (prefix).
         * @return a reference to the iterator after incrementing by one
         */
        const_iterator& operator++();

        /**
         * Increment operator (postfix).
         * @return a reference to the iterator after incrementing by one
         */
        const_iterator operator++(int);

        /**
         * Dereference operator.
         * @return a reference to the selector this iterator points to
         */
        const DatatypeSelector& operator*() const;

        /**
         * Dereference operator.
         * @return a pointer to the selector this iterator points to
         */
        const DatatypeSelector* operator->() const;

      private:
        /**
         * Constructor.
         * @param ctor the internal datatype constructor to iterate over
         * @param true if this is a begin() iterator
         */
        const_iterator(const CVC4::DatatypeConstructor& ctor, bool begin);
        /* A pointer to the list of selectors of the internal datatype
         * constructor to iterate over.
         * This pointer is maintained for operators == and != only. */
        const void* d_int_stors;
        /* The list of datatype selector (wrappers) to iterate over. */
        std::vector<DatatypeSelector> d_stors;
        /* The current index of the iterator. */
        size_t d_idx;
    };

    /**
     * @return an iterator to the first selector of this constructor
     */
    const_iterator begin() const;

    /**
     * @return an iterator to one-off-the-last selector of this constructor
     */
    const_iterator end() const;

  private:
    /* The internal datatype constructor wrapped by this datatype constructor.*/
    std::shared_ptr<CVC4::DatatypeConstructor> d_ctor;
};

/*
 * A CVC4 datatype.
 */
class CVC4_PUBLIC Datatype
{
  public:
    /**
     * Constructor.
     * @param dtype the internal datatype to be wrapped
     * @return the Datatype
     */
    Datatype(const CVC4::Datatype& dtype);

    /**
     * Destructor.
     */
    ~Datatype();

    /**
     * Get the datatype constructor with the given name.
     * This is a linear search through the constructors, so in case of multiple,
     * similarly-named constructors, the first is returned.
     * @param name the name of the datatype constructor
     * @return the datatype constructor with the given name
     */
    DatatypeConstructor operator[](const std::string& name) const;
    DatatypeConstructor getConstructor(const std::string& name) const;

    /**
     * Get a term representing the datatype constructor with the given name.
     * This is a linear search through the constructors, so in case of multiple,
     * similarly-named constructors, the
     * first is returned.
     */
    Term getConstructorTerm(const std::string& name) const;

    /**
     * @return a string representation of this datatype
     */
    std::string toString() const;

    /**
     * Iterator for the constructors of a datatype.
     */
    class const_iterator
        : public std::iterator<std::input_iterator_tag, Datatype>
    {
      friend class Datatype; // to access constructor

      public:
        /**
         * Assignment operator.
         * @param it the iterator to assign to
         * @return the reference to the iterator after assignment
         */
        const_iterator& operator=(const const_iterator& it);

        /**
         * Equality operator.
         * @param it the iterator to compare to for equality
         * @return true if the iterators are equal
         */
        bool operator==(const const_iterator& it) const;

        /**
         * Disequality operator.
         * @param it the iterator to compare to for disequality
         * @return true if the iterators are disequal
         */
        bool operator!=(const const_iterator& it) const;

        /**
         * Increment operator (prefix).
         * @return a reference to the iterator after incrementing by one
         */
        const_iterator& operator++();

        /**
         * Increment operator (postfix).
         * @return a reference to the iterator after incrementing by one
         */
        const_iterator operator++(int);

        /**
         * Dereference operator.
         * @return a reference to the constructor this iterator points to
         */
        const DatatypeConstructor& operator*() const;

        /**
         * Dereference operator.
         * @return a pointer to the constructor this iterator points to
         */
        const DatatypeConstructor* operator->() const;

      private:
        /**
         * Constructor.
         * @param dtype the internal datatype to iterate over
         * @param true if this is a begin() iterator
         */
        const_iterator(const CVC4::Datatype& dtype, bool begin);
        /* A pointer to the list of constructors of the internal datatype
         * to iterate over.
         * This pointer is maintained for operators == and != only. */
        const void* d_int_ctors;
        /* The list of datatype constructor (wrappers) to iterate over. */
        std::vector<DatatypeConstructor> d_ctors;
        /* The current index of the iterator. */
        size_t d_idx;
    };

    /**
     * @return an iterator to the first constructor of this datatype
     */
    const_iterator begin() const;

    /**
     * @return an iterator to one-off-the-last constructor of this datatype
     */
    const_iterator end() const;

  private:
    /* The internal datatype wrapped by this datatype. */
    std::shared_ptr<CVC4::Datatype> d_dtype;
};

/**
 * Serialize a datatype declaration to given stream.
 * @param out the output stream
 * @param dtdecl the datatype declaration to be serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeDecl& dtdecl) CVC4_PUBLIC;

/**
 * Serialize a datatype constructor declaration to given stream.
 * @param out the output stream
 * @param ctordecl the datatype constructor declaration to be serialized
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeConstructorDecl& ctordecl) CVC4_PUBLIC;

/**
 * Serialize a datatype selector declaration to given stream.
 * @param out the output stream
 * @param stordecl the datatype selector declaration to be serialized
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeSelectorDecl& stordecl) CVC4_PUBLIC;

/**
 * Serialize a datatype to given stream.
 * @param out the output stream
 * @param dtdecl the datatype to be serialized to given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const Datatype& dtype) CVC4_PUBLIC;

/**
 * Serialize a datatype constructor to given stream.
 * @param out the output stream
 * @param ctor the datatype constructor to be serialized to given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeConstructor& ctor) CVC4_PUBLIC;

/**
 * Serialize a datatype selector to given stream.
 * @param out the output stream
 * @param ctor the datatype selector to be serialized to given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeSelector& stor) CVC4_PUBLIC;


/* -------------------------------------------------------------------------- */
/* Rounding Mode for Floating Points                                          */
/* -------------------------------------------------------------------------- */

/**
 * A CVC4 floating point rounding mode.
 */
enum CVC4_PUBLIC RoundingMode
{
  ROUND_NEAREST_TIES_TO_EVEN,
  ROUND_TOWARD_POSITIVE,
  ROUND_TOWARD_NEGATIVE,
  ROUND_TOWARD_ZERO,
  ROUND_NEAREST_TIES_TO_AWAY,
};

/**
 * Hash function for RoundingModes.
 */
struct CVC4_PUBLIC RoundingModeHashFunction
{
  inline size_t operator() (const RoundingMode& rm) const;
};

/* -------------------------------------------------------------------------- */
/* Solver                                                                     */
/* -------------------------------------------------------------------------- */

/*
 * A CVC4 solver.
 */
class CVC4_PUBLIC Solver
{
  public:

    /* .................................................................... */
    /* Constructors/Destructors                                             */
    /* .................................................................... */

    /**
     * Constructor.
     * @param opts a pointer to a solver options object (for parser only)
     * @return the Solver
     */
    Solver (Options* opts = nullptr);

    /**
     * Destructor.
     */
    ~Solver();

    /**
     * Disallow copy/assignment.
     */
    Solver(const Solver&) CVC4_UNDEFINED;
    Solver& operator=(const Solver&) CVC4_UNDEFINED;


    /* .................................................................... */
    /* Sorts Handling                                                       */
    /* .................................................................... */

    /**
     * @return sort Boolean
     */
    Sort getBooleanSort () const;

    /**
     * @return sort Integer (in CVC4, Integer is a subtype of Real)
     */
    Sort getIntegerSort () const;

    /**
     * @return sort Real
     */
    Sort getRealSort    () const;

    /**
     * @return sort RegExp
     */
    Sort getRegExpSort  () const;

    /**
     * @return sort RoundingMode
     */
    Sort getRoundingmodeSort () const;

    /**
     * @return sort String
     */
    Sort getStringSort  () const;

    /**
     * Create an array sort.
     * @param indexSort the array index sort
     * @param elemSort the array element sort
     * @return the array sort
     */
    Sort mkArraySort(Sort indexSort, Sort elemSort) const;

    /**
     * Create a bit-vector sort.
     * @param size the bit-width of the bit-vector sort
     * @return the bit-vector sort
     */
    Sort mkBitVectorSort(uint32_t size) const;

    /**
     * Create a datatype sort.
     * @param dtypedecl the datatype declaration from which the sort is created
     * @return the datatype sort
     */
    Sort mkDatatypeSort(DatatypeDecl dtypedecl) const;

    /**
     * Create function sort.
     * @param domain the sort of the fuction argument
     * @param range the sort of the function return value
     * @return the function sort
     */
    Sort mkFunctionSort(Sort domain, Sort range) const;

    /**
     * Create function sort.
     * @param argSorts the sort of the function arguments
     * @param range the sort of the function return value
     * @return the function sort
     */
    Sort mkFunctionSort(const std::vector<Sort>& argSorts, Sort range) const;

    /**
     * Create a sort parameter.
     * @param symbol the name of the sort
     * @return the sort parameter
     */
    Sort mkParamSort(const std::string& symbol) const;

    /**
     * Create a predicate sort.
     * @param sorts the list of sorts of the predicate
     * @return the predicate sort
     */
    Sort mkPredicateSort(const std::vector<Sort>& sorts) const;

    /**
     * Create a record sort
     * @param fields the list of fields of the record
     * @return the record sort
     */
    Sort mkRecordSort(
        const std::vector<std::pair<std::string, Sort>>& fields) const;

    /**
     * Create a set sort.
     * @param elemSort the sort of the set elements
     * @return the set sort
     */
    Sort mkSetSort(Sort elemSort) const;

    /**
     * Create an uninterpreted sort.
     * @param symbol the name of the sort
     * @return the uninterpreted sort
     */
    Sort mkSortSort(const std::string& symbol) const;

    /**
     * Create a tuple sort.
     * @param sorts of the elements of the tuple
     * @return the tuple sort
     */
    Sort mkTupleSort(const std::vector<Sort>& sorts) const;

    /* .................................................................... */
    /* Create Terms                                                         */
    /* .................................................................... */

    /**
     * Create a unary term of given kind.
     * @param kind the kind of the term
     * @param child the child of the term
     * @return the Term
     */
    Term mkTerm(Kind kind,
                Term child);

    /**
     * Create binary term of given kind.
     * @param kind the kind of the term
     * @param child1 the first child of the term
     * @param child2 the second child of the term
     * @return the Term
     */
    Term mkTerm(Kind kind,
                Term child1,
                Term child2);

    /**
     * Create ternary term of given kind.
     * @param kind the kind of the term
     * @param child1 the first child of the term
     * @param child2 the second child of the term
     * @param child3 the third child of the term
     * @return the Term
     */
    Term mkTerm(Kind kind,
                Term child1,
                Term child2,
                Term child3);

    /**
     * Create n-ary term of given kind.
     * @param kind the kind of the term
     * @param children the children of the term
     * @return the Term
     */
    Term mkTerm(Kind kind,
                const std::vector<Term>& children);

    /**
     * Create term with no children from a given operator term.
     * Create operator terms with mkOpTerm().
     * @param the operator term
     * @return the Term
     */
    Term mkTerm(Term opTerm) const;

    /**
     * Create unary term from a given operator term.
     * Create operator terms with mkOpTerm().
     * @param the operator term
     * @child the child of the term
     * @return the Term
     */
    Term mkTerm(Term opTerm,
                Term child) const;

    /**
     * Create binary term from a given operator term.
     * Create operator terms with mkOpTerm().
     * @param the operator term
     * @child1 the first child of the term
     * @child2 the second child of the term
     * @return the Term
     */
    Term mkTerm(Term opTerm,
                Term child1,
                Term child2) const;

    /**
     * Create ternary term from a given operator term.
     * Create operator terms with mkOpTerm().
     * @param the operator term
     * @child1 the first child of the term
     * @child2 the second child of the term
     * @child3 the third child of the term
     * @return the Term
     */
    Term mkTerm(Term opTerm,
                Term child1,
                Term child2,
                Term child3) const;

    /**
     * Create n-ary term from a given operator term.
     * Create operator terms with mkOpTerm().
     * @param the operator term
     * @children the children of the term
     * @return the Term
     */
    Term mkTerm(Term opTerm,
                const std::vector<Term>& children) const;

    /* .................................................................... */
    /* Create Operator Terms                                                */
    /* .................................................................... */

    /**
     * Create operator term of kind:
     *   - CHAIN_OP
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the operator
     * @param k the kind argument to this operator
     */
    Term mkOpTerm(Kind kind, Kind k);

    /**
     * Create operator of kind:
     *   - RECORD_UPDATE_OP
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the operator
     * @param arg the string argument to this operator
     */
    Term mkOpTerm(Kind kind, const std::string& arg);

    /**
     * Create operator of kind:
     *   - DIVISIBLE_OP
     *   - BITVECTOR_REPEAT_OP
     *   - BITVECTOR_ZERO_EXTEND_OP
     *   - BITVECTOR_SIGN_EXTEND_OP
     *   - BITVECTOR_ROTATE_LEFT_OP
     *   - BITVECTOR_ROTATE_RIGHT_OP
     *   - INT_TO_BITVECTOR_OP
     *   - FLOATINGPOINT_TO_UBV_OP
     *   - FLOATINGPOINT_TO_UBV_TOTAL_OP
     *   - FLOATINGPOINT_TO_SBV_OP
     *   - FLOATINGPOINT_TO_SBV_TOTAL_OP
     *   - TUPLE_UPDATE_OP
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the operator
     * @param arg the uint32_t argument to this operator
     */
    Term mkOpTerm(Kind kind, uint32_t arg);

    /**
     * Create operator of Kind:
     *   - BITVECTOR_EXTRACT_OP
     *   - FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP
     *   - FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP
     *   - FLOATINGPOINT_TO_FP_REAL_OP
     *   - FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP
     *   - FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP
     *   - FLOATINGPOINT_TO_FP_GENERIC_OP
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the operator
     * @param arg1 the first uint32_t argument to this operator
     * @param arg2 the second uint32_t argument to this operator
     */
    Term mkOpTerm(Kind kind, uint32_t arg1, uint32_t arg2);

    /* .................................................................... */
    /* Create Constants                                                     */
    /* .................................................................... */

    /**
     * Create a Boolean true constant.
     * @return the true constant
     */
    Term mkTrue() const;

    /**
     * Create a Boolean false constant.
     * @return the false constant
     */
    Term mkFalse() const;

    /**
     * Create a Boolean constant.
     * @return the Boolean constant
     * @param val the value of the constant
     */
    Term mkBoolean(bool val) const;

    /**
     * Create an Integer constant.
     * @param s the string represetntation of the constant
     * @param base the base of the string representation
     * @return the Integer constant
     */
    Term mkInteger(const char* s, uint32_t base = 10) const;

    /**
     * Create an Integer constant.
     * @param s the string represetntation of the constant
     * @param base the base of the string representation
     * @return the Integer constant
     */
    Term mkInteger(const std::string& s, uint32_t base = 10) const;

    /**
     * Create an Integer constant.
     * @param val the value of the constant
     * @return the Integer constant
     */
    Term mkInteger(int32_t val) const;

    /**
     * Create an Integer constant.
     * @param val the value of the constant
     * @return the Integer constant
     */
    Term mkInteger(uint32_t val) const;

    /**
     * Create an Integer constant.
     * @param val the value of the constant
     * @return the Integer constant
     */
    Term mkInteger(int64_t val) const;

    /**
     * Create an Integer constant.
     * @param val the value of the constant
     * @return the Integer constant
     */
    Term mkInteger(uint64_t val) const;

    /**
     * Create a constant representing the number Pi.
     * @return a constant representing Pi
     */
    Term mkPi() const;

    /**
     * Create an Real constant.
     * @param s the string represetntation of the constant
     * @param base the base of the string representation
     * @return the Real constant
     */
    Term mkReal(const char* s, uint32_t base = 10) const;

    /**
     * Create an Real constant.
     * @param s the string represetntation of the constant
     * @param base the base of the string representation
     * @return the Real constant
     */
    Term mkReal(const std::string& s, uint32_t base = 10) const;

    /**
     * Create an Real constant.
     * @param val the value of the constant
     * @return the Real constant
     */
    Term mkReal(int32_t val) const;

    /**
     * Create an Real constant.
     * @param val the value of the constant
     * @return the Real constant
     */
    Term mkReal(int64_t val) const;

    /**
     * Create an Real constant.
     * @param val the value of the constant
     * @return the Real constant
     */
    Term mkReal(uint32_t val) const;

    /**
     * Create an Real constant.
     * @param val the value of the constant
     * @return the Real constant
     */
    Term mkReal(uint64_t val) const;

    /**
     * Create an Rational constant.
     * @param num the value of the numerator
     * @param den the value of the denominator
     * @return the Rational constant
     */
    Term mkRational(int32_t num, int32_t den) const;

    /**
     * Create an Rational constant.
     * @param num the value of the numerator
     * @param den the value of the denominator
     * @return the Rational constant
     */
    Term mkRational(int64_t num, int64_t den) const;

    /**
     * Create an Rational constant.
     * @param num the value of the numerator
     * @param den the value of the denominator
     * @return the Rational constant
     */
    Term mkRational(uint32_t num, uint32_t den) const;

    /**
     * Create an Rational constant.
     * @param num the value of the numerator
     * @param den the value of the denominator
     * @return the Rational constant
     */
    Term mkRational(uint64_t num, uint64_t den) const;

    /**
     * Create a RegExp constant.
     * @return the RegExp constant
     */
    Term mkRegExp() const;

    /**
     * Create a RegExp constant.
     * @param type ???
     * @return the RegExp constant
     */
    Term mkRegExp(int32_t type) const;

    /**
     * Create a constant representing an empty set of the given sort.
     * @param s the sort of the set elements.
     * @return the empty set constant
     */
    Term mkEmptySet(Sort s) const;

    /**
     * Create a String constant.
     * @param s the string this constant represents
     * @return the String constant
     */
    Term mkString(const char* s) const;

    /**
     * Create a String constant.
     * @param s the string this constant represents
     * @return the String constant
     */
    Term mkString(const std::string& s) const;

    /**
     * Create a String constant.
     * @param c the character this constant represents
     * @return the String constant
     */
    Term mkString(const unsigned char c) const;

    /**
     * Create a String constant.
     * @param s a list of unsigned values this constant represents as string
     * @return the String constant
     */
    Term mkString(const std::vector<unsigned>& s) const;

    /**
     * Create a universe set of the given sort.
     * @param sort the sort of the set elements
     * @return the universe set constant
     */
    Term mkUniverseSet(Sort sort) const;

    /**
     * Create a bit-vector constant of given size with value 0.
     * @param size the bit-width of the bit-vector sort
     * @return the bit-vector constant
     */
    Term mkBitVector(uint32_t size) const;

    /**
     * Create a bit-vector constant of given size and value.
     * @param size the bit-width of the bit-vector sort
     * @param val the value of the constant
     * @return the bit-vector constant
     */
    Term mkBitVector(uint32_t size, uint32_t val) const;

    /**
     * Create a bit-vector constant of given size and value.
     * @param size the bit-width of the bit-vector sort
     * @param val the value of the constant
     * @return the bit-vector constant
     */
    Term mkBitVector(uint32_t size, uint64_t val) const;

    /**
     * Create a bit-vector constant from a given string.
     * @param s the string represetntation of the constant
     * @param base the base of the string representation
     * @return the bit-vector constant
     */
    Term mkBitVector(const char* s, uint32_t base = 2) const;

    /**
     * Create a bit-vector constant from a given string.
     * @param s the string represetntation of the constant
     * @param base the base of the string representation
     * @return the bit-vector constant
     */
    Term mkBitVector(std::string& s, uint32_t base = 2) const;

    /**
     * Create constant of kind:
     *   - CONST_REGEXP
     *   - REGEXP_EMPTY
     *   - REGEXP_SIGMA
     *   - SEP_NIL
     * @param kind the kind of the constant
     */
    Term mkConst(Kind kind) const;

    /**
     * Create constant of kind:
     *   - CONST_ROUNDINGMODE
     * @param rm the floating point rounding mode this constant represents
     */
    Term mkConst(RoundingMode rm) const;

    /*
     * Create constant of kind:
     *   - EMPTYSET
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg the argument to this kind
     */
    Term mkConst(Kind kind, Sort arg) const;

    /**
     * Create constant of kind:
     *   - UNINTERPRETED_CONSTANT
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg1 the first argument to this kind
     * @param arg2 the second argument to this kind
     */
    Term mkConst(Kind kind, Sort arg1, int32_t arg2) const;

    /**
     * Create constant of kind:
     *   - BOOLEAN
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg the argument to this kind
     */
    Term mkConst(Kind kind, bool arg) const;

    /**
     * Create constant of kind:
     *   - CONST_STRING
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg the argument to this kind
     */
    Term mkConst(Kind kind, const char* arg) const;

    /**
     * Create constant of kind:
     *   - CONST_STRING
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg the argument to this kind
     */
    Term mkConst(Kind kind, const std::string& arg) const;

    /**
     * Create constant of kind:
     *   - ABSTRACT_VALUE
     *   - CONST_RATIONAL (for integers, reals)
     *   - CONST_BITVECTOR
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg1 the first argument to this kind
     * @param arg2 the second argument to this kind
     */
    Term mkConst(Kind kind, const char* arg1, uint32_t arg2 = 10) const;

    /**
     * Create constant of kind:
     *   - ABSTRACT_VALUE
     *   - CONST_RATIONAL (for integers, reals)
     *   - CONST_BITVECTOR
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg1 the first argument to this kind
     * @param arg2 the second argument to this kind
     */
    Term mkConst(Kind kind, const std::string& arg1, uint32_t arg2 = 10) const;

    /**
     * Create constant of kind:
     *   - ABSTRACT_VALUE
     *   - CONST_RATIONAL (for integers, reals)
     *   - CONST_BITVECTOR
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg the argument to this kind
     */
    Term mkConst(Kind kind, uint32_t arg) const;

    /**
     * Create constant of kind:
     *   - ABSTRACT_VALUE
     *   - CONST_RATIONAL (for integers, reals)
     *   - CONST_REGEXP
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg the argument to this kind
     */
    Term mkConst(Kind kind, int32_t arg) const;

    /**
     * Create constant of kind:
     *   - ABSTRACT_VALUE
     *   - CONST_RATIONAL (for integers, reals)
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg the argument to this kind
     */
    Term mkConst(Kind kind, int64_t arg) const;

    /**
     * Create constant of kind:
     *   - ABSTRACT_VALUE
     *   - CONST_RATIONAL (for integers, reals)
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg the argument to this kind
     */
    Term mkConst(Kind kind, uint64_t arg) const;

    /**
     * Create constant of kind:
     *   - CONST_RATIONAL (for rationals)
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg1 the first argument to this kind
     * @param arg2 the second argument to this kind
     */
    Term mkConst(Kind kind, int32_t arg1, int32_t arg2) const;

    /**
     * Create constant of kind:
     *   - CONST_RATIONAL (for rationals)
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg1 the first argument to this kind
     * @param arg2 the second argument to this kind
     */
    Term mkConst(Kind kind, int64_t arg1, int64_t arg2) const;

    /**
     * Create constant of kind:
     *   - CONST_RATIONAL (for rationals)
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg1 the first argument to this kind
     * @param arg2 the second argument to this kind
     */
    Term mkConst(Kind kind, uint32_t arg1, uint32_t arg2) const;

    /**
     * Create constant of kind:
     *   - CONST_RATIONAL (for rationals)
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg1 the first argument to this kind
     * @param arg2 the second argument to this kind
     */
    Term mkConst(Kind kind, uint64_t arg1, uint64_t arg2) const;

    /**
     * Create constant of kind:
     *   - CONST_BITVECTOR
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg1 the first argument to this kind
     * @param arg2 the second argument to this kind
     */
    Term mkConst(Kind kind, uint32_t arg1, uint64_t arg2) const;

    /**
     * Create constant of kind:
     *   - CONST_FLOATINGPOINT
     * See enum Kind for a description of the parameters.
     * @param kind the kind of the constant
     * @param arg1 the first argument to this kind
     * @param arg2 the second argument to this kind
     * @param arg3 the third argument to this kind
     */
#if 0
    Term mkConst(Kind kind, uint32_t arg1, uint32_t arg2, double arg3) const;
    Term mkConst(Kind kind,
                 uint32_t arg1,
                 uint32_t arg2,
                 const std::string& arg3) const;
#endif
    Term mkConst(Kind kind,
                 uint32_t arg1,
                 uint32_t arg2,
                 Term arg3) const;

    /* .................................................................... */
    /* Create Variables                                                     */
    /* .................................................................... */

    /**
     * Create variable.
     * @param symbol the name of the variable
     * @param sort the sort of the variable
     * @return the variable
     */
    Term mkVar(const std::string& symbol, Sort sort) const;

    /**
     * Create variable.
     * @param sort the sort of the variable
     * @return the variable
     */
    Term mkVar(Sort sort) const;

    /**
     * Create bound variable.
     * @param symbol the name of the variable
     * @param sort the sort of the variable
     * @return the variable
     */
    Term mkBoundVar(const std::string& symbol, Sort sort) const;

    /**
     * Create bound variable.
     * @param sort the sort of the variable
     * @return the variable
     */
    Term mkBoundVar(Sort sort) const;


    /* .................................................................... */
    /* Formula Handling                                                     */
    /* .................................................................... */

    /**
     * Simplify a formula without doing "much" work.  Does not involve
     * the SAT Engine in the simplification, but uses the current
     * definitions, assertions, and the current partial model, if one
     * has been constructed.  It also involves theory normalization.
     * @param t the formula to simplify
     * @return the simplified formula
     */
    Term simplify(const Term& t);

    /**
     * Assert a formula.
     * SMT-LIB: ( assert <term> )
     * @param term the formula to assert
     */
    void assertFormula(Term term) const;

    /**
     * Check satisfiability.
     * SMT-LIB: ( check-sat )
     * @return the result of the satisfiability check.
     */
    Result checkSat() const;

    /**
     * Check satisfiability assuming the given formula.
     * SMT-LIB: ( check-sat-assuming ( <prop_literal> ) )
     * @param assumption the formula to assume
     * @return the result of the satisfiability check.
     */
    Result checkSatAssuming(Term assumption) const;

    /**
     * Check satisfiability assuming the given formulas.
     * SMT-LIB: ( check-sat-assuming ( <prop_literal>+ ) )
     * @param assumptions the formulas to assume
     * @return the result of the satisfiability check.
     */
    Result checkSatAssuming(const std::vector<Term>& assumptions) const;

    /**
     * Check validity.
     * @return the result of the validity check.
     */
    Result checkValid() const;

    /**
     * Check validity assuming the given formula.
     * @param assumption the formula to assume
     * @return the result of the validity check.
     */
    Result checkValidAssuming(Term assumption) const;

    /**
     * Check validity assuming the given formulas.
     * @param assumptions the formulas to assume
     * @return the result of the validity check.
     */
    Result checkValidAssuming(const std::vector<Term>& assumptions) const;

    /**
     * Declare first-order constant (0-arity function symbol).
     * SMT-LIB: ( declare-const <symbol> <sort> )
     * SMT-LIB: ( declare-fun <symbol> ( ) <sort> )
     * This command corresponds to mkVar().
     * @param symbol the name of the first-order constant
     * @param sort the sort of the first-order constant
     * @return the first-order constant
     */
    Term declareConst(const std::string& symbol, Sort sort) const;

    /**
     * Declare 0-arity function symbol.
     * SMT-LIB: ( declare-fun <symbol> ( ) <sort> )
     * @param symbol the name of the function
     * @param sort the sort of the return value of this function
     * @return the function
     */
    Term declareFun(const std::string& symbol, Sort sort) const;

    /**
     * Declare n-ary function symbol.
     * SMT-LIB: ( declare-fun <symbol> ( <sort>* ) <sort> )
     * @param symbol the name of the function
     * @param sorts the sorts of the parameters to this function
     * @param sort the sort of the return value of this function
     * @return the function
     */
    Term declareFun(const std::string& symbol,
                    const std::vector<Sort>& sorts,
                    Sort sort) const;

    /**
     * Declare uninterpreted sort.
     * SMT-LIB: ( declare-sort <symbol> <numeral> )
     * @param symbol the name of the sort
     * @param arity the arity of the sort
     * @return the sort
     */
    Sort declareSort(const std::string& symbol, uint32_t arity) const;

    /**
     * Define n-ary function.
     * SMT-LIB: ( define-fun <function_def> )
     * @param symbol the name of the function
     * @param bound_vars the parameters to this function
     * @param sort the sort of the return value of this function
     * @param term the function body
     * @return the function
     */
    Term defineFun(const std::string& symbol,
                   const std::vector<Term>& bound_vars,
                   Sort sort,
                   Term term) const;
    /**
     * Define n-ary function.
     * SMT-LIB: ( define-fun <function_def> )
     * Create parameter 'fun' with mkVar().
     * @param fun the sorted function
     * @param bound_vars the parameters to this function
     * @param term the function body
     * @return the function
     */
    Term defineFun(Term fun,
                   const std::vector<Term>& bound_vars,
                   Term term) const;

    /**
     * Define recursive function.
     * SMT-LIB: ( define-fun-rec <function_def> )
     * @param symbol the name of the function
     * @param bound_vars the parameters to this function
     * @param sort the sort of the return value of this function
     * @param term the function body
     * @return the function
     */
    Term defineFunRec(const std::string& symbol,
                      const std::vector<Term>& bound_vars,
                      Sort sort,
                      Term term) const;

    /**
     * Define recursive function.
     * SMT-LIB: ( define-fun-rec <function_def> )
     * Create parameter 'fun' with mkVar().
     * @param fun the sorted function
     * @param bound_vars the parameters to this function
     * @param term the function body
     * @return the function
     */
    Term defineFunRec(Term fun,
                      const std::vector<Term>& bound_vars,
                      Term term) const;

    /**
     * Define recursive functions.
     * SMT-LIB: ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
     * Create elements of parameter 'funs' with mkVar().
     * @param funs the sorted functions
     * @param bound_vars the list of parameters to the functions
     * @param term the list of function bodies of the functions
     * @return the function
     */
    void defineFunsRec(const std::vector<Term>& funs,
                       const std::vector<std::vector<Term>>& bound_vars,
                       const std::vector<Term>& terms) const;

    /**
     * Echo a given string to the given output stream.
     * SMT-LIB: ( echo <std::string> )
     * @param out the output stream
     * @param str the string to echo
     */
    void echo(std::ostream& out, const std::string& str) const;

    /**
     * Get the list of asserted formulas.
     * SMT-LIB: ( get-assertions )
     * @return the list of asserted formulas
     */
    std::vector<Term> getAssertions() const;

    /**
     * Get the assignment of asserted formulas.
     * SMT-LIB: ( get-assignment )
     * Requires to enable option 'produce-assignments'.
     * @return a list of formula-assignment pairs
     */
    std::vector<std::pair<Term, Term>> getAssignment() const;

    /**
     * Get info from the solver.
     * SMT-LIB: ( get-info <info_flag> )
     * @return the info
     */
    std::string getInfo(const std::string& flag) const;

    /**
     * Get the value of a given option.
     * SMT-LIB: ( get-option <keyword> )
     * @param option the option for which the value is queried
     * @return a string representation of the option value
     */
    std::string getOption(const std::string& option) const;

    /**
     * Get the set of unsat ("failed") assumptions.
     * SMT-LIB: ( get-unsat-assumptions )
     * Requires to enable option 'produce-unsat-assumptions'.
     * @return the set of unsat assumptions.
     */
    std::vector<Term> getUnsatAssumptions() const;

    /**
     * Get the unsatisfiable core.
     * SMT-LIB: ( get-unsat-core )
     * Requires to enable option 'produce-unsat-cores'.
     * @return a set of terms representing the unsatisfiable core
     */
    std::vector<Term> getUnsatCore() const;

    /**
     * Get the value of the given term.
     * SMT-LIB: ( get-value ( <term> ) )
     * @param term the term for which the value is queried
     * @return the value of the given term
     */
    Term getValue(Term term) const;
    /**
     * Get the values of the given terms.
     * SMT-LIB: ( get-value ( <term>+ ) )
     * @param terms the terms for which the value is queried
     * @return the values of the given terms
     */
    std::vector<Term> getValue(const std::vector<Term>& terms) const;

    /**
     * Pop (a) level(s) from the assertion stack.
     * SMT-LIB: ( pop <numeral> )
     * @param nscopes the number of levels to pop
     */
    void pop(uint32_t nscopes = 1) const;

    /**
     * Print the model of a satisfiable query to the given output stream.
     * Requires to enable option 'produce-models'.
     * @param out the output stream
     */
    void printModel(std::ostream& out) const;

    /**
     * Push (a) level(s) to the assertion stack.
     * SMT-LIB: ( push <numeral> )
     * @param nscopes the number of levels to push
     */
    void push(uint32_t nscopes = 1) const;

    /**
     * Reset the solver.
     * SMT-LIB: ( reset )
     */
    void reset() const;

    /**
     * Remove all assertions.
     * SMT-LIB: ( reset-assertions )
     */
    void resetAssertions() const;

    /**
     * Set info.
     * SMT-LIB: ( set-info <attribute> )
     * @param keyword the info flag
     * @param value the value of the info flag
     */
    void setInfo(const std::string& keyword, const std::string& value) const;

    /**
     * Set logic.
     * SMT-LIB: ( set-logic <symbol> )
     * @param logic the logic to set
     */
    void setLogic(const std::string& logic) const;

    /**
     * Set option.
     * SMT-LIB: ( set-option <option> )
     * @param option the option name
     * @param value the option value
     */
    void setOption(const std::string& option, const std::string& value) const;

   private:

    /* Helper to convert a vector of internal types to sorts. */
    std::vector<Type> sortVectorToTypes(const std::vector<Sort>& vector) const;
    /* Helper to convert a vector of sorts to internal types. */
    std::vector<Expr> termVectorToExprs(const std::vector<Term>& vector) const;

    /* The expression manager of this solver. */
    std::unique_ptr<ExprManager> d_exprMgr;
    /* The SMT engine of this solver. */
    std::unique_ptr<SmtEngine> d_smtEngine;
    /* The options of this solver. */
    std::unique_ptr<Options> d_opts;
    /* The random number generator of this solver. */
    std::unique_ptr<Random> d_rng;

};

}  // namespace api
}  // namespace CVC4
#endif

/*********************                                                        */
/*! \file cvc4cpp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The CVC4 C++ API.
 **
 ** The CVC4 C++ API.
 **/

#include "api/cvc4cpp.h"

#include "base/cvc4_assert.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "options/main_options.h"
#include "options/options.h"
#include "smt/smt_engine.h"
#include "util/random.h"
#include "util/result.h"
#include "util/utility.h"

#include <sstream>

namespace CVC4 {
namespace api {

/* -------------------------------------------------------------------------- */
/* Result                                                                     */
/* -------------------------------------------------------------------------- */

Result::Result(const CVC4::Result& r) : d_result(new CVC4::Result(r)) {}

bool Result::isSat(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_SAT
         && d_result->isSat() == CVC4::Result::SAT;
}

bool Result::isUnsat(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_SAT
         && d_result->isSat() == CVC4::Result::UNSAT;
}

bool Result::isSatUnknown(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_SAT
         && d_result->isSat() == CVC4::Result::SAT_UNKNOWN;
}

bool Result::isValid(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_VALIDITY
         && d_result->isValid() == CVC4::Result::VALID;
}

bool Result::isInvalid(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_VALIDITY
         && d_result->isValid() == CVC4::Result::INVALID;
}

bool Result::isValidUnknown(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_VALIDITY
         && d_result->isValid() == CVC4::Result::VALIDITY_UNKNOWN;
}

bool Result::operator==(const Result& r) const
{
  return *d_result == *r.d_result;
}

bool Result::operator!=(const Result& r) const
{
  return *d_result != *r.d_result;
}

std::string Result::getUnknownExplanation(void) const
{
  std::stringstream ss;
  ss << d_result->whyUnknown();
  return ss.str();
}

std::string Result::toString(void) const { return d_result->toString(); }

std::ostream& operator<<(std::ostream& out, const Result& r)
{
  out << r.toString();
  return out;
}

/* -------------------------------------------------------------------------- */
/* Kind                                                                       */
/* -------------------------------------------------------------------------- */

/* Mapping from external (API) kind to internal kind. */
const static std::unordered_map<Kind, CVC4::Kind, KindHashFunction> s_kinds{
    {INTERNAL_KIND, CVC4::Kind::UNDEFINED_KIND},
    {UNDEFINED_KIND, CVC4::Kind::UNDEFINED_KIND},
    {NULL_EXPR, CVC4::Kind::NULL_EXPR},
    /* Builtin ------------------------------------------------------------- */
    {UNINTERPRETED_CONSTANT, CVC4::Kind::UNINTERPRETED_CONSTANT},
    {ABSTRACT_VALUE, CVC4::Kind::ABSTRACT_VALUE},
    {FUNCTION, CVC4::Kind::FUNCTION},
    {APPLY, CVC4::Kind::APPLY},
    {EQUAL, CVC4::Kind::EQUAL},
    {DISTINCT, CVC4::Kind::DISTINCT},
    {VARIABLE, CVC4::Kind::VARIABLE},
    {BOUND_VARIABLE, CVC4::Kind::BOUND_VARIABLE},
    {LAMBDA, CVC4::Kind::LAMBDA},
    {CHOICE, CVC4::Kind::CHOICE},
    {CHAIN, CVC4::Kind::CHAIN},
    {CHAIN_OP, CVC4::Kind::CHAIN_OP},
    /* Boolean ------------------------------------------------------------- */
    {CONST_BOOLEAN, CVC4::Kind::CONST_BOOLEAN},
    {NOT, CVC4::Kind::NOT},
    {AND, CVC4::Kind::AND},
    {IMPLIES, CVC4::Kind::IMPLIES},
    {OR, CVC4::Kind::OR},
    {XOR, CVC4::Kind::XOR},
    {ITE, CVC4::Kind::ITE},
    /* UF ------------------------------------------------------------------ */
    {APPLY_UF, CVC4::Kind::APPLY_UF},
    {CARDINALITY_CONSTRAINT, CVC4::Kind::CARDINALITY_CONSTRAINT},
    {HO_APPLY, CVC4::Kind::HO_APPLY},
    /* Arithmetic ---------------------------------------------------------- */
    {PLUS, CVC4::Kind::PLUS},
    {MULT, CVC4::Kind::MULT},
    {MINUS, CVC4::Kind::MINUS},
    {UMINUS, CVC4::Kind::UMINUS},
    {DIVISION, CVC4::Kind::DIVISION},
    {DIVISION_TOTAL, CVC4::Kind::DIVISION_TOTAL},
    {INTS_DIVISION, CVC4::Kind::INTS_DIVISION},
    {INTS_DIVISION_TOTAL, CVC4::Kind::INTS_DIVISION_TOTAL},
    {INTS_MODULUS, CVC4::Kind::INTS_MODULUS},
    {INTS_MODULUS_TOTAL, CVC4::Kind::INTS_MODULUS_TOTAL},
    {ABS, CVC4::Kind::ABS},
    {DIVISIBLE, CVC4::Kind::DIVISIBLE},
    {POW, CVC4::Kind::POW},
    {EXPONENTIAL, CVC4::Kind::EXPONENTIAL},
    {SINE, CVC4::Kind::SINE},
    {COSINE, CVC4::Kind::COSINE},
    {TANGENT, CVC4::Kind::TANGENT},
    {COSECANT, CVC4::Kind::COSECANT},
    {SECANT, CVC4::Kind::SECANT},
    {COTANGENT, CVC4::Kind::COTANGENT},
    {ARCSINE, CVC4::Kind::ARCSINE},
    {ARCCOSINE, CVC4::Kind::ARCCOSINE},
    {ARCTANGENT, CVC4::Kind::ARCTANGENT},
    {ARCCOSECANT, CVC4::Kind::ARCCOSECANT},
    {ARCSECANT, CVC4::Kind::ARCSECANT},
    {ARCCOTANGENT, CVC4::Kind::ARCCOTANGENT},
    {SQRT, CVC4::Kind::SQRT},
    {DIVISIBLE_OP, CVC4::Kind::DIVISIBLE_OP},
    {CONST_RATIONAL, CVC4::Kind::CONST_RATIONAL},
    {LT, CVC4::Kind::LT},
    {LEQ, CVC4::Kind::LEQ},
    {GT, CVC4::Kind::GT},
    {GEQ, CVC4::Kind::GEQ},
    {IS_INTEGER, CVC4::Kind::IS_INTEGER},
    {TO_INTEGER, CVC4::Kind::TO_INTEGER},
    {TO_REAL, CVC4::Kind::TO_REAL},
    {PI, CVC4::Kind::PI},
    /* BV ------------------------------------------------------------------ */
    {CONST_BITVECTOR, CVC4::Kind::CONST_BITVECTOR},
    {BITVECTOR_CONCAT, CVC4::Kind::BITVECTOR_CONCAT},
    {BITVECTOR_AND, CVC4::Kind::BITVECTOR_AND},
    {BITVECTOR_OR, CVC4::Kind::BITVECTOR_OR},
    {BITVECTOR_XOR, CVC4::Kind::BITVECTOR_XOR},
    {BITVECTOR_NOT, CVC4::Kind::BITVECTOR_NOT},
    {BITVECTOR_NAND, CVC4::Kind::BITVECTOR_NAND},
    {BITVECTOR_NOR, CVC4::Kind::BITVECTOR_NOR},
    {BITVECTOR_XNOR, CVC4::Kind::BITVECTOR_XNOR},
    {BITVECTOR_COMP, CVC4::Kind::BITVECTOR_COMP},
    {BITVECTOR_MULT, CVC4::Kind::BITVECTOR_MULT},
    {BITVECTOR_PLUS, CVC4::Kind::BITVECTOR_PLUS},
    {BITVECTOR_SUB, CVC4::Kind::BITVECTOR_SUB},
    {BITVECTOR_NEG, CVC4::Kind::BITVECTOR_NEG},
    {BITVECTOR_UDIV, CVC4::Kind::BITVECTOR_UDIV},
    {BITVECTOR_UREM, CVC4::Kind::BITVECTOR_UREM},
    {BITVECTOR_SDIV, CVC4::Kind::BITVECTOR_SDIV},
    {BITVECTOR_SREM, CVC4::Kind::BITVECTOR_SREM},
    {BITVECTOR_SMOD, CVC4::Kind::BITVECTOR_SMOD},
    {BITVECTOR_UDIV_TOTAL, CVC4::Kind::BITVECTOR_UDIV_TOTAL},
    {BITVECTOR_UREM_TOTAL, CVC4::Kind::BITVECTOR_UREM_TOTAL},
    {BITVECTOR_SHL, CVC4::Kind::BITVECTOR_SHL},
    {BITVECTOR_LSHR, CVC4::Kind::BITVECTOR_LSHR},
    {BITVECTOR_ASHR, CVC4::Kind::BITVECTOR_ASHR},
    {BITVECTOR_ULT, CVC4::Kind::BITVECTOR_ULT},
    {BITVECTOR_ULE, CVC4::Kind::BITVECTOR_ULE},
    {BITVECTOR_UGT, CVC4::Kind::BITVECTOR_UGT},
    {BITVECTOR_UGE, CVC4::Kind::BITVECTOR_UGE},
    {BITVECTOR_SLT, CVC4::Kind::BITVECTOR_SLT},
    {BITVECTOR_SLE, CVC4::Kind::BITVECTOR_SLE},
    {BITVECTOR_SGT, CVC4::Kind::BITVECTOR_SGT},
    {BITVECTOR_SGE, CVC4::Kind::BITVECTOR_SGE},
    {BITVECTOR_ULTBV, CVC4::Kind::BITVECTOR_ULTBV},
    {BITVECTOR_SLTBV, CVC4::Kind::BITVECTOR_SLTBV},
    {BITVECTOR_ITE, CVC4::Kind::BITVECTOR_ITE},
    {BITVECTOR_REDOR, CVC4::Kind::BITVECTOR_REDOR},
    {BITVECTOR_REDAND, CVC4::Kind::BITVECTOR_REDAND},
    {BITVECTOR_EXTRACT_OP, CVC4::Kind::BITVECTOR_EXTRACT_OP},
    {BITVECTOR_REPEAT_OP, CVC4::Kind::BITVECTOR_REPEAT_OP},
    {BITVECTOR_ZERO_EXTEND_OP, CVC4::Kind::BITVECTOR_ZERO_EXTEND_OP},
    {BITVECTOR_SIGN_EXTEND_OP, CVC4::Kind::BITVECTOR_SIGN_EXTEND_OP},
    {BITVECTOR_ROTATE_LEFT_OP, CVC4::Kind::BITVECTOR_ROTATE_LEFT_OP},
    {BITVECTOR_ROTATE_RIGHT_OP, CVC4::Kind::BITVECTOR_ROTATE_RIGHT_OP},
    {BITVECTOR_EXTRACT, CVC4::Kind::BITVECTOR_EXTRACT},
    {BITVECTOR_REPEAT, CVC4::Kind::BITVECTOR_REPEAT},
    {BITVECTOR_ZERO_EXTEND, CVC4::Kind::BITVECTOR_ZERO_EXTEND},
    {BITVECTOR_SIGN_EXTEND, CVC4::Kind::BITVECTOR_SIGN_EXTEND},
    {BITVECTOR_ROTATE_LEFT, CVC4::Kind::BITVECTOR_ROTATE_LEFT},
    {BITVECTOR_ROTATE_RIGHT, CVC4::Kind::BITVECTOR_ROTATE_RIGHT},
    {INT_TO_BITVECTOR_OP, CVC4::Kind::INT_TO_BITVECTOR_OP},
    {INT_TO_BITVECTOR, CVC4::Kind::INT_TO_BITVECTOR},
    {BITVECTOR_TO_NAT, CVC4::Kind::BITVECTOR_TO_NAT},
    /* FP ------------------------------------------------------------------ */
    {CONST_FLOATINGPOINT, CVC4::Kind::CONST_FLOATINGPOINT},
    {CONST_ROUNDINGMODE, CVC4::Kind::CONST_ROUNDINGMODE},
    {FLOATINGPOINT_FP, CVC4::Kind::FLOATINGPOINT_FP},
    {FLOATINGPOINT_EQ, CVC4::Kind::FLOATINGPOINT_EQ},
    {FLOATINGPOINT_ABS, CVC4::Kind::FLOATINGPOINT_ABS},
    {FLOATINGPOINT_NEG, CVC4::Kind::FLOATINGPOINT_NEG},
    {FLOATINGPOINT_PLUS, CVC4::Kind::FLOATINGPOINT_PLUS},
    {FLOATINGPOINT_SUB, CVC4::Kind::FLOATINGPOINT_SUB},
    {FLOATINGPOINT_MULT, CVC4::Kind::FLOATINGPOINT_MULT},
    {FLOATINGPOINT_DIV, CVC4::Kind::FLOATINGPOINT_DIV},
    {FLOATINGPOINT_FMA, CVC4::Kind::FLOATINGPOINT_FMA},
    {FLOATINGPOINT_SQRT, CVC4::Kind::FLOATINGPOINT_SQRT},
    {FLOATINGPOINT_REM, CVC4::Kind::FLOATINGPOINT_REM},
    {FLOATINGPOINT_RTI, CVC4::Kind::FLOATINGPOINT_RTI},
    {FLOATINGPOINT_MIN, CVC4::Kind::FLOATINGPOINT_MIN},
    {FLOATINGPOINT_MAX, CVC4::Kind::FLOATINGPOINT_MAX},
    {FLOATINGPOINT_LEQ, CVC4::Kind::FLOATINGPOINT_LEQ},
    {FLOATINGPOINT_LT, CVC4::Kind::FLOATINGPOINT_LT},
    {FLOATINGPOINT_GEQ, CVC4::Kind::FLOATINGPOINT_GEQ},
    {FLOATINGPOINT_GT, CVC4::Kind::FLOATINGPOINT_GT},
    {FLOATINGPOINT_ISN, CVC4::Kind::FLOATINGPOINT_ISN},
    {FLOATINGPOINT_ISSN, CVC4::Kind::FLOATINGPOINT_ISSN},
    {FLOATINGPOINT_ISZ, CVC4::Kind::FLOATINGPOINT_ISZ},
    {FLOATINGPOINT_ISINF, CVC4::Kind::FLOATINGPOINT_ISINF},
    {FLOATINGPOINT_ISNAN, CVC4::Kind::FLOATINGPOINT_ISNAN},
    {FLOATINGPOINT_ISNEG, CVC4::Kind::FLOATINGPOINT_ISNEG},
    {FLOATINGPOINT_ISPOS, CVC4::Kind::FLOATINGPOINT_ISPOS},
    {FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP,
     CVC4::Kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP},
    {FLOATINGPOINT_TO_FP_IEEE_BITVECTOR,
     CVC4::Kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR},
    {FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP,
     CVC4::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP},
    {FLOATINGPOINT_TO_FP_FLOATINGPOINT,
     CVC4::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT},
    {FLOATINGPOINT_TO_FP_REAL_OP, CVC4::Kind::FLOATINGPOINT_TO_FP_REAL_OP},
    {FLOATINGPOINT_TO_FP_REAL, CVC4::Kind::FLOATINGPOINT_TO_FP_REAL},
    {FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP,
     CVC4::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP},
    {FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
     CVC4::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR},
    {FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP,
     CVC4::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP},
    {FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
     CVC4::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR},
    {FLOATINGPOINT_TO_FP_GENERIC_OP,
     CVC4::Kind::FLOATINGPOINT_TO_FP_GENERIC_OP},
    {FLOATINGPOINT_TO_FP_GENERIC, CVC4::Kind::FLOATINGPOINT_TO_FP_GENERIC},
    {FLOATINGPOINT_TO_UBV_OP, CVC4::Kind::FLOATINGPOINT_TO_UBV_OP},
    {FLOATINGPOINT_TO_UBV, CVC4::Kind::FLOATINGPOINT_TO_UBV},
    {FLOATINGPOINT_TO_UBV_TOTAL_OP, CVC4::Kind::FLOATINGPOINT_TO_UBV_TOTAL_OP},
    {FLOATINGPOINT_TO_UBV_TOTAL, CVC4::Kind::FLOATINGPOINT_TO_UBV_TOTAL},
    {FLOATINGPOINT_TO_SBV_OP, CVC4::Kind::FLOATINGPOINT_TO_SBV_OP},
    {FLOATINGPOINT_TO_SBV, CVC4::Kind::FLOATINGPOINT_TO_SBV},
    {FLOATINGPOINT_TO_SBV_TOTAL_OP, CVC4::Kind::FLOATINGPOINT_TO_SBV_TOTAL_OP},
    {FLOATINGPOINT_TO_SBV_TOTAL, CVC4::Kind::FLOATINGPOINT_TO_SBV_TOTAL},
    {FLOATINGPOINT_TO_REAL, CVC4::Kind::FLOATINGPOINT_TO_REAL},
    {FLOATINGPOINT_TO_REAL_TOTAL, CVC4::Kind::FLOATINGPOINT_TO_REAL_TOTAL},
    /* Arrays -------------------------------------------------------------- */
    {SELECT, CVC4::Kind::SELECT},
    {STORE, CVC4::Kind::STORE},
    {STORE_ALL, CVC4::Kind::STORE_ALL},
    /* Datatypes ----------------------------------------------------------- */
    {APPLY_SELECTOR, CVC4::Kind::APPLY_SELECTOR},
    {APPLY_CONSTRUCTOR, CVC4::Kind::APPLY_CONSTRUCTOR},
    {APPLY_SELECTOR_TOTAL, CVC4::Kind::APPLY_SELECTOR_TOTAL},
    {APPLY_TESTER, CVC4::Kind::APPLY_TESTER},
    {TUPLE_UPDATE_OP, CVC4::Kind::TUPLE_UPDATE_OP},
    {TUPLE_UPDATE, CVC4::Kind::TUPLE_UPDATE},
    {RECORD_UPDATE_OP, CVC4::Kind::RECORD_UPDATE_OP},
    {RECORD_UPDATE, CVC4::Kind::RECORD_UPDATE},
    /* Separation Logic ---------------------------------------------------- */
    {SEP_NIL, CVC4::Kind::SEP_NIL},
    {SEP_EMP, CVC4::Kind::SEP_EMP},
    {SEP_PTO, CVC4::Kind::SEP_PTO},
    {SEP_STAR, CVC4::Kind::SEP_STAR},
    {SEP_WAND, CVC4::Kind::SEP_WAND},
    /* Sets ---------------------------------------------------------------- */
    {EMPTYSET, CVC4::Kind::EMPTYSET},
    {UNION, CVC4::Kind::UNION},
    {INTERSECTION, CVC4::Kind::INTERSECTION},
    {SETMINUS, CVC4::Kind::SETMINUS},
    {SUBSET, CVC4::Kind::SUBSET},
    {MEMBER, CVC4::Kind::MEMBER},
    {SINGLETON, CVC4::Kind::SINGLETON},
    {INSERT, CVC4::Kind::INSERT},
    {CARD, CVC4::Kind::CARD},
    {COMPLEMENT, CVC4::Kind::COMPLEMENT},
    {UNIVERSE_SET, CVC4::Kind::UNIVERSE_SET},
    {JOIN, CVC4::Kind::JOIN},
    {PRODUCT, CVC4::Kind::PRODUCT},
    {TRANSPOSE, CVC4::Kind::TRANSPOSE},
    {TCLOSURE, CVC4::Kind::TCLOSURE},
    {JOIN_IMAGE, CVC4::Kind::JOIN_IMAGE},
    {IDEN, CVC4::Kind::IDEN},
    /* Strings ------------------------------------------------------------- */
    {STRING_CONCAT, CVC4::Kind::STRING_CONCAT},
    {STRING_IN_REGEXP, CVC4::Kind::STRING_IN_REGEXP},
    {STRING_LENGTH, CVC4::Kind::STRING_LENGTH},
    {STRING_SUBSTR, CVC4::Kind::STRING_SUBSTR},
    {STRING_CHARAT, CVC4::Kind::STRING_CHARAT},
    {STRING_STRCTN, CVC4::Kind::STRING_STRCTN},
    {STRING_STRIDOF, CVC4::Kind::STRING_STRIDOF},
    {STRING_STRREPL, CVC4::Kind::STRING_STRREPL},
    {STRING_PREFIX, CVC4::Kind::STRING_PREFIX},
    {STRING_SUFFIX, CVC4::Kind::STRING_SUFFIX},
    {STRING_ITOS, CVC4::Kind::STRING_ITOS},
    {STRING_STOI, CVC4::Kind::STRING_STOI},
    {CONST_STRING, CVC4::Kind::CONST_STRING},
    {STRING_TO_REGEXP, CVC4::Kind::STRING_TO_REGEXP},
    {REGEXP_CONCAT, CVC4::Kind::REGEXP_CONCAT},
    {REGEXP_UNION, CVC4::Kind::REGEXP_UNION},
    {REGEXP_INTER, CVC4::Kind::REGEXP_INTER},
    {REGEXP_STAR, CVC4::Kind::REGEXP_STAR},
    {REGEXP_PLUS, CVC4::Kind::REGEXP_PLUS},
    {REGEXP_OPT, CVC4::Kind::REGEXP_OPT},
    {REGEXP_RANGE, CVC4::Kind::REGEXP_RANGE},
    {REGEXP_LOOP, CVC4::Kind::REGEXP_LOOP},
    {REGEXP_EMPTY, CVC4::Kind::REGEXP_EMPTY},
    {REGEXP_SIGMA, CVC4::Kind::REGEXP_SIGMA},
    /* Quantifiers --------------------------------------------------------- */
    {FORALL, CVC4::Kind::FORALL},
    {EXISTS, CVC4::Kind::EXISTS},
    {LAST_KIND, CVC4::Kind::LAST_KIND},
};

/* Mapping from internal kind to external (API) kind. */
const static std::unordered_map<CVC4::Kind, Kind, CVC4::kind::KindHashFunction>
    s_kinds_internal{
        {CVC4::Kind::UNDEFINED_KIND, UNDEFINED_KIND},
        {CVC4::Kind::NULL_EXPR, NULL_EXPR},
        /* Builtin --------------------------------------------------------- */
        {CVC4::Kind::UNINTERPRETED_CONSTANT, UNINTERPRETED_CONSTANT},
        {CVC4::Kind::ABSTRACT_VALUE, ABSTRACT_VALUE},
        {CVC4::Kind::FUNCTION, FUNCTION},
        {CVC4::Kind::APPLY, APPLY},
        {CVC4::Kind::EQUAL, EQUAL},
        {CVC4::Kind::DISTINCT, DISTINCT},
        {CVC4::Kind::VARIABLE, VARIABLE},
        {CVC4::Kind::BOUND_VARIABLE, BOUND_VARIABLE},
        {CVC4::Kind::LAMBDA, LAMBDA},
        {CVC4::Kind::CHOICE, CHOICE},
        {CVC4::Kind::CHAIN, CHAIN},
        {CVC4::Kind::CHAIN_OP, CHAIN_OP},
        /* Boolean --------------------------------------------------------- */
        {CVC4::Kind::CONST_BOOLEAN, CONST_BOOLEAN},
        {CVC4::Kind::NOT, NOT},
        {CVC4::Kind::AND, AND},
        {CVC4::Kind::IMPLIES, IMPLIES},
        {CVC4::Kind::OR, OR},
        {CVC4::Kind::XOR, XOR},
        {CVC4::Kind::ITE, ITE},
        /* UF -------------------------------------------------------------- */
        {CVC4::Kind::APPLY_UF, APPLY_UF},
        {CVC4::Kind::CARDINALITY_CONSTRAINT, CARDINALITY_CONSTRAINT},
        {CVC4::Kind::HO_APPLY, HO_APPLY},
        /* Arithmetic ------------------------------------------------------ */
        {CVC4::Kind::PLUS, PLUS},
        {CVC4::Kind::MULT, MULT},
        {CVC4::Kind::MINUS, MINUS},
        {CVC4::Kind::UMINUS, UMINUS},
        {CVC4::Kind::DIVISION, DIVISION},
        {CVC4::Kind::DIVISION_TOTAL, DIVISION_TOTAL},
        {CVC4::Kind::INTS_DIVISION, INTS_DIVISION},
        {CVC4::Kind::INTS_DIVISION_TOTAL, INTS_DIVISION_TOTAL},
        {CVC4::Kind::INTS_MODULUS, INTS_MODULUS},
        {CVC4::Kind::INTS_MODULUS_TOTAL, INTS_MODULUS_TOTAL},
        {CVC4::Kind::ABS, ABS},
        {CVC4::Kind::DIVISIBLE, DIVISIBLE},
        {CVC4::Kind::POW, POW},
        {CVC4::Kind::EXPONENTIAL, EXPONENTIAL},
        {CVC4::Kind::SINE, SINE},
        {CVC4::Kind::COSINE, COSINE},
        {CVC4::Kind::TANGENT, TANGENT},
        {CVC4::Kind::COSECANT, COSECANT},
        {CVC4::Kind::SECANT, SECANT},
        {CVC4::Kind::COTANGENT, COTANGENT},
        {CVC4::Kind::ARCSINE, ARCSINE},
        {CVC4::Kind::ARCCOSINE, ARCCOSINE},
        {CVC4::Kind::ARCTANGENT, ARCTANGENT},
        {CVC4::Kind::ARCCOSECANT, ARCCOSECANT},
        {CVC4::Kind::ARCSECANT, ARCSECANT},
        {CVC4::Kind::ARCCOTANGENT, ARCCOTANGENT},
        {CVC4::Kind::SQRT, SQRT},
        {CVC4::Kind::DIVISIBLE_OP, DIVISIBLE_OP},
        {CVC4::Kind::CONST_RATIONAL, CONST_RATIONAL},
        {CVC4::Kind::LT, LT},
        {CVC4::Kind::LEQ, LEQ},
        {CVC4::Kind::GT, GT},
        {CVC4::Kind::GEQ, GEQ},
        {CVC4::Kind::IS_INTEGER, IS_INTEGER},
        {CVC4::Kind::TO_INTEGER, TO_INTEGER},
        {CVC4::Kind::TO_REAL, TO_REAL},
        {CVC4::Kind::PI, PI},
        /* BV -------------------------------------------------------------- */
        {CVC4::Kind::CONST_BITVECTOR, CONST_BITVECTOR},
        {CVC4::Kind::BITVECTOR_CONCAT, BITVECTOR_CONCAT},
        {CVC4::Kind::BITVECTOR_AND, BITVECTOR_AND},
        {CVC4::Kind::BITVECTOR_OR, BITVECTOR_OR},
        {CVC4::Kind::BITVECTOR_XOR, BITVECTOR_XOR},
        {CVC4::Kind::BITVECTOR_NOT, BITVECTOR_NOT},
        {CVC4::Kind::BITVECTOR_NAND, BITVECTOR_NAND},
        {CVC4::Kind::BITVECTOR_NOR, BITVECTOR_NOR},
        {CVC4::Kind::BITVECTOR_XNOR, BITVECTOR_XNOR},
        {CVC4::Kind::BITVECTOR_COMP, BITVECTOR_COMP},
        {CVC4::Kind::BITVECTOR_MULT, BITVECTOR_MULT},
        {CVC4::Kind::BITVECTOR_PLUS, BITVECTOR_PLUS},
        {CVC4::Kind::BITVECTOR_SUB, BITVECTOR_SUB},
        {CVC4::Kind::BITVECTOR_NEG, BITVECTOR_NEG},
        {CVC4::Kind::BITVECTOR_UDIV, BITVECTOR_UDIV},
        {CVC4::Kind::BITVECTOR_UREM, BITVECTOR_UREM},
        {CVC4::Kind::BITVECTOR_SDIV, BITVECTOR_SDIV},
        {CVC4::Kind::BITVECTOR_SREM, BITVECTOR_SREM},
        {CVC4::Kind::BITVECTOR_SMOD, BITVECTOR_SMOD},
        {CVC4::Kind::BITVECTOR_UDIV_TOTAL, BITVECTOR_UDIV_TOTAL},
        {CVC4::Kind::BITVECTOR_UREM_TOTAL, BITVECTOR_UREM_TOTAL},
        {CVC4::Kind::BITVECTOR_SHL, BITVECTOR_SHL},
        {CVC4::Kind::BITVECTOR_LSHR, BITVECTOR_LSHR},
        {CVC4::Kind::BITVECTOR_ASHR, BITVECTOR_ASHR},
        {CVC4::Kind::BITVECTOR_ULT, BITVECTOR_ULT},
        {CVC4::Kind::BITVECTOR_ULE, BITVECTOR_ULE},
        {CVC4::Kind::BITVECTOR_UGT, BITVECTOR_UGT},
        {CVC4::Kind::BITVECTOR_UGE, BITVECTOR_UGE},
        {CVC4::Kind::BITVECTOR_SLT, BITVECTOR_SLT},
        {CVC4::Kind::BITVECTOR_SLE, BITVECTOR_SLE},
        {CVC4::Kind::BITVECTOR_SGT, BITVECTOR_SGT},
        {CVC4::Kind::BITVECTOR_SGE, BITVECTOR_SGE},
        {CVC4::Kind::BITVECTOR_ULTBV, BITVECTOR_ULTBV},
        {CVC4::Kind::BITVECTOR_SLTBV, BITVECTOR_SLTBV},
        {CVC4::Kind::BITVECTOR_ITE, BITVECTOR_ITE},
        {CVC4::Kind::BITVECTOR_REDOR, BITVECTOR_REDOR},
        {CVC4::Kind::BITVECTOR_REDAND, BITVECTOR_REDAND},
        {CVC4::Kind::BITVECTOR_EXTRACT_OP, BITVECTOR_EXTRACT_OP},
        {CVC4::Kind::BITVECTOR_REPEAT_OP, BITVECTOR_REPEAT_OP},
        {CVC4::Kind::BITVECTOR_ZERO_EXTEND_OP, BITVECTOR_ZERO_EXTEND_OP},
        {CVC4::Kind::BITVECTOR_SIGN_EXTEND_OP, BITVECTOR_SIGN_EXTEND_OP},
        {CVC4::Kind::BITVECTOR_ROTATE_LEFT_OP, BITVECTOR_ROTATE_LEFT_OP},
        {CVC4::Kind::BITVECTOR_ROTATE_RIGHT_OP, BITVECTOR_ROTATE_RIGHT_OP},
        {CVC4::Kind::BITVECTOR_EXTRACT, BITVECTOR_EXTRACT},
        {CVC4::Kind::BITVECTOR_REPEAT, BITVECTOR_REPEAT},
        {CVC4::Kind::BITVECTOR_ZERO_EXTEND, BITVECTOR_ZERO_EXTEND},
        {CVC4::Kind::BITVECTOR_SIGN_EXTEND, BITVECTOR_SIGN_EXTEND},
        {CVC4::Kind::BITVECTOR_ROTATE_LEFT, BITVECTOR_ROTATE_LEFT},
        {CVC4::Kind::BITVECTOR_ROTATE_RIGHT, BITVECTOR_ROTATE_RIGHT},
        {CVC4::Kind::INT_TO_BITVECTOR_OP, INT_TO_BITVECTOR_OP},
        {CVC4::Kind::INT_TO_BITVECTOR, INT_TO_BITVECTOR},
        {CVC4::Kind::BITVECTOR_TO_NAT, BITVECTOR_TO_NAT},
        /* FP -------------------------------------------------------------- */
        {CVC4::Kind::CONST_FLOATINGPOINT, CONST_FLOATINGPOINT},
        {CVC4::Kind::CONST_ROUNDINGMODE, CONST_ROUNDINGMODE},
        {CVC4::Kind::FLOATINGPOINT_FP, FLOATINGPOINT_FP},
        {CVC4::Kind::FLOATINGPOINT_EQ, FLOATINGPOINT_EQ},
        {CVC4::Kind::FLOATINGPOINT_ABS, FLOATINGPOINT_ABS},
        {CVC4::Kind::FLOATINGPOINT_NEG, FLOATINGPOINT_NEG},
        {CVC4::Kind::FLOATINGPOINT_PLUS, FLOATINGPOINT_PLUS},
        {CVC4::Kind::FLOATINGPOINT_SUB, FLOATINGPOINT_SUB},
        {CVC4::Kind::FLOATINGPOINT_MULT, FLOATINGPOINT_MULT},
        {CVC4::Kind::FLOATINGPOINT_DIV, FLOATINGPOINT_DIV},
        {CVC4::Kind::FLOATINGPOINT_FMA, FLOATINGPOINT_FMA},
        {CVC4::Kind::FLOATINGPOINT_SQRT, FLOATINGPOINT_SQRT},
        {CVC4::Kind::FLOATINGPOINT_REM, FLOATINGPOINT_REM},
        {CVC4::Kind::FLOATINGPOINT_RTI, FLOATINGPOINT_RTI},
        {CVC4::Kind::FLOATINGPOINT_MIN, FLOATINGPOINT_MIN},
        {CVC4::Kind::FLOATINGPOINT_MAX, FLOATINGPOINT_MAX},
        {CVC4::Kind::FLOATINGPOINT_LEQ, FLOATINGPOINT_LEQ},
        {CVC4::Kind::FLOATINGPOINT_LT, FLOATINGPOINT_LT},
        {CVC4::Kind::FLOATINGPOINT_GEQ, FLOATINGPOINT_GEQ},
        {CVC4::Kind::FLOATINGPOINT_GT, FLOATINGPOINT_GT},
        {CVC4::Kind::FLOATINGPOINT_ISN, FLOATINGPOINT_ISN},
        {CVC4::Kind::FLOATINGPOINT_ISSN, FLOATINGPOINT_ISSN},
        {CVC4::Kind::FLOATINGPOINT_ISZ, FLOATINGPOINT_ISZ},
        {CVC4::Kind::FLOATINGPOINT_ISINF, FLOATINGPOINT_ISINF},
        {CVC4::Kind::FLOATINGPOINT_ISNAN, FLOATINGPOINT_ISNAN},
        {CVC4::Kind::FLOATINGPOINT_ISNEG, FLOATINGPOINT_ISNEG},
        {CVC4::Kind::FLOATINGPOINT_ISPOS, FLOATINGPOINT_ISPOS},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP,
         FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR,
         FLOATINGPOINT_TO_FP_IEEE_BITVECTOR},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP,
         FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT,
         FLOATINGPOINT_TO_FP_FLOATINGPOINT},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_REAL_OP, FLOATINGPOINT_TO_FP_REAL_OP},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_REAL, FLOATINGPOINT_TO_FP_REAL},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP,
         FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
         FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP,
         FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
         FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_GENERIC_OP,
         FLOATINGPOINT_TO_FP_GENERIC_OP},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_GENERIC, FLOATINGPOINT_TO_FP_GENERIC},
        {CVC4::Kind::FLOATINGPOINT_TO_UBV_OP, FLOATINGPOINT_TO_UBV_OP},
        {CVC4::Kind::FLOATINGPOINT_TO_UBV, FLOATINGPOINT_TO_UBV},
        {CVC4::Kind::FLOATINGPOINT_TO_UBV_TOTAL_OP,
         FLOATINGPOINT_TO_UBV_TOTAL_OP},
        {CVC4::Kind::FLOATINGPOINT_TO_UBV_TOTAL, FLOATINGPOINT_TO_UBV_TOTAL},
        {CVC4::Kind::FLOATINGPOINT_TO_SBV_OP, FLOATINGPOINT_TO_SBV_OP},
        {CVC4::Kind::FLOATINGPOINT_TO_SBV, FLOATINGPOINT_TO_SBV},
        {CVC4::Kind::FLOATINGPOINT_TO_SBV_TOTAL_OP,
         FLOATINGPOINT_TO_SBV_TOTAL_OP},
        {CVC4::Kind::FLOATINGPOINT_TO_SBV_TOTAL, FLOATINGPOINT_TO_SBV_TOTAL},
        {CVC4::Kind::FLOATINGPOINT_TO_REAL, FLOATINGPOINT_TO_REAL},
        {CVC4::Kind::FLOATINGPOINT_TO_REAL_TOTAL, FLOATINGPOINT_TO_REAL_TOTAL},
        /* Arrays ---------------------------------------------------------- */
        {CVC4::Kind::SELECT, SELECT},
        {CVC4::Kind::STORE, STORE},
        {CVC4::Kind::STORE_ALL, STORE_ALL},
        /* Datatypes ------------------------------------------------------- */
        {CVC4::Kind::APPLY_SELECTOR, APPLY_SELECTOR},
        {CVC4::Kind::APPLY_CONSTRUCTOR, APPLY_CONSTRUCTOR},
        {CVC4::Kind::APPLY_SELECTOR_TOTAL, APPLY_SELECTOR_TOTAL},
        {CVC4::Kind::APPLY_TESTER, APPLY_TESTER},
        {CVC4::Kind::TUPLE_UPDATE_OP, TUPLE_UPDATE_OP},
        {CVC4::Kind::TUPLE_UPDATE, TUPLE_UPDATE},
        {CVC4::Kind::RECORD_UPDATE_OP, RECORD_UPDATE_OP},
        {CVC4::Kind::RECORD_UPDATE, RECORD_UPDATE},
        /* Separation Logic ------------------------------------------------ */
        {CVC4::Kind::SEP_NIL, SEP_NIL},
        {CVC4::Kind::SEP_EMP, SEP_EMP},
        {CVC4::Kind::SEP_PTO, SEP_PTO},
        {CVC4::Kind::SEP_STAR, SEP_STAR},
        {CVC4::Kind::SEP_WAND, SEP_WAND},
        /* Sets ------------------------------------------------------------ */
        {CVC4::Kind::EMPTYSET, EMPTYSET},
        {CVC4::Kind::UNION, UNION},
        {CVC4::Kind::INTERSECTION, INTERSECTION},
        {CVC4::Kind::SETMINUS, SETMINUS},
        {CVC4::Kind::SUBSET, SUBSET},
        {CVC4::Kind::MEMBER, MEMBER},
        {CVC4::Kind::SINGLETON, SINGLETON},
        {CVC4::Kind::INSERT, INSERT},
        {CVC4::Kind::CARD, CARD},
        {CVC4::Kind::COMPLEMENT, COMPLEMENT},
        {CVC4::Kind::UNIVERSE_SET, UNIVERSE_SET},
        {CVC4::Kind::JOIN, JOIN},
        {CVC4::Kind::PRODUCT, PRODUCT},
        {CVC4::Kind::TRANSPOSE, TRANSPOSE},
        {CVC4::Kind::TCLOSURE, TCLOSURE},
        {CVC4::Kind::JOIN_IMAGE, JOIN_IMAGE},
        {CVC4::Kind::IDEN, IDEN},
        /* Strings --------------------------------------------------------- */
        {CVC4::Kind::STRING_CONCAT, STRING_CONCAT},
        {CVC4::Kind::STRING_IN_REGEXP, STRING_IN_REGEXP},
        {CVC4::Kind::STRING_LENGTH, STRING_LENGTH},
        {CVC4::Kind::STRING_SUBSTR, STRING_SUBSTR},
        {CVC4::Kind::STRING_CHARAT, STRING_CHARAT},
        {CVC4::Kind::STRING_STRCTN, STRING_STRCTN},
        {CVC4::Kind::STRING_STRIDOF, STRING_STRIDOF},
        {CVC4::Kind::STRING_STRREPL, STRING_STRREPL},
        {CVC4::Kind::STRING_PREFIX, STRING_PREFIX},
        {CVC4::Kind::STRING_SUFFIX, STRING_SUFFIX},
        {CVC4::Kind::STRING_ITOS, STRING_ITOS},
        {CVC4::Kind::STRING_STOI, STRING_STOI},
        {CVC4::Kind::CONST_STRING, CONST_STRING},
        {CVC4::Kind::STRING_TO_REGEXP, STRING_TO_REGEXP},
        {CVC4::Kind::REGEXP_CONCAT, REGEXP_CONCAT},
        {CVC4::Kind::REGEXP_UNION, REGEXP_UNION},
        {CVC4::Kind::REGEXP_INTER, REGEXP_INTER},
        {CVC4::Kind::REGEXP_STAR, REGEXP_STAR},
        {CVC4::Kind::REGEXP_PLUS, REGEXP_PLUS},
        {CVC4::Kind::REGEXP_OPT, REGEXP_OPT},
        {CVC4::Kind::REGEXP_RANGE, REGEXP_RANGE},
        {CVC4::Kind::REGEXP_LOOP, REGEXP_LOOP},
        {CVC4::Kind::REGEXP_EMPTY, REGEXP_EMPTY},
        {CVC4::Kind::REGEXP_SIGMA, REGEXP_SIGMA},
        /* Quantifiers ----------------------------------------------------- */
        {CVC4::Kind::FORALL, FORALL},
        {CVC4::Kind::EXISTS, EXISTS},
        /* ----------------------------------------------------------------- */
        {CVC4::Kind::LAST_KIND, LAST_KIND},
    };

namespace {
Kind intToExtKind(CVC4::Kind k)
{
  auto it = s_kinds_internal.find(k);
  if (it == s_kinds_internal.end())
  {
    return INTERNAL_KIND;
  }
  return it->second;
}

CVC4::Kind extToIntKind(Kind k)
{
  auto it = s_kinds.find(k);
  if (it == s_kinds.end())
  {
    return CVC4::Kind::UNDEFINED_KIND;
  }
  return it->second;
}
}  // namespace

std::ostream& operator<<(std::ostream& out, Kind k)
{
  switch (k)
  {
    case INTERNAL_KIND: out << "INTERNAL_KIND"; break;
    default: out << extToIntKind(k);
  }
  return out;
}

size_t KindHashFunction::operator()(Kind k) const { return k; }

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

Sort::Sort(const CVC4::Type& t) : d_type(new CVC4::Type(t)) {}

Sort::~Sort() {}

Sort& Sort::operator=(const Sort& s)
{
  // CHECK: valid sort s?
  if (this != &s)
  {
    *d_type = *s.d_type;
  }
  return *this;
}

bool Sort::operator==(const Sort& s) const
{
  // CHECK: valid sort s?
  return *d_type == *s.d_type;
}

bool Sort::operator!=(const Sort& s) const
{
  // CHECK: valid sort s?
  return *d_type != *s.d_type;
}

bool Sort::isBoolean() const
{
  // CHECK: valid sort s?
  return d_type->isBoolean();
}

bool Sort::isInteger() const
{
  // CHECK: valid sort s?
  return d_type->isInteger();
}

bool Sort::isReal() const
{
  // CHECK: valid sort s?
  return d_type->isReal();
}

bool Sort::isString() const
{
  // CHECK: valid sort s?
  return d_type->isString();
}

bool Sort::isRegExp() const
{
  // CHECK: valid sort s?
  return d_type->isRegExp();
}

bool Sort::isRoundingMode() const
{
  // CHECK: valid sort s?
  return d_type->isRoundingMode();
}

bool Sort::isBitVector() const
{
  // CHECK: valid sort s?
  return d_type->isBitVector();
}

bool Sort::isFloatingPoint() const
{
  // CHECK: valid sort s?
  return d_type->isFloatingPoint();
}

bool Sort::isDatatype() const
{
  // CHECK: valid sort s?
  return d_type->isDatatype();
}

bool Sort::isFunction() const
{
  // CHECK: valid sort s?
  return d_type->isFunction();
}

bool Sort::isPredicate() const
{
  // CHECK: valid sort s?
  return d_type->isPredicate();
}

bool Sort::isTuple() const
{
  // CHECK: valid sort s?
  return d_type->isTuple();
}

bool Sort::isRecord() const
{
  // CHECK: valid sort s?
  return d_type->isRecord();
}

bool Sort::isArray() const
{
  // CHECK: valid sort s?
  return d_type->isArray();
}

bool Sort::isSet() const
{
  // CHECK: valid sort s?
  return d_type->isSet();
}

bool Sort::isUninterpretedSort() const
{
  // CHECK: valid sort s?
  return d_type->isSort();
}

bool Sort::isSortConstructor() const
{
  // CHECK: valid sort s?
  return d_type->isSortConstructor();
}

Datatype Sort::getDatatype() const
{
  // CHECK: is this a datatype sort?
  DatatypeType* type = static_cast<DatatypeType*>(d_type.get());
  return type->getDatatype();
}

Sort Sort::instantiate(const std::vector<Sort>& params) const
{
  // CHECK: Is this a datatype/sort constructor sort?
  std::vector<Type> tparams;
  for (const Sort& s : params)
  {
    tparams.push_back(*s.d_type.get());
  }
  if (d_type->isDatatype())
  {
    // CHECK: is parametric?
    DatatypeType* type = static_cast<DatatypeType*>(d_type.get());
    return type->instantiate(tparams);
  }
  Assert(d_type->isSortConstructor());
  return static_cast<SortConstructorType*>(d_type.get())->instantiate(tparams);
}

std::string Sort::toString() const
{
  // CHECK: valid sort s?
  return d_type->toString();
}

std::ostream& operator<<(std::ostream& out, const Sort& s)
{
  out << s.toString();
  return out;
}

size_t SortHashFunction::operator()(const Sort& s) const
{
  return TypeHashFunction()(*s.d_type);
}

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

Term::Term() : d_expr(new CVC4::Expr()) {}

Term::Term(const CVC4::Expr& e) : d_expr(new CVC4::Expr(e)) {}

Term::~Term() {}

Term& Term::operator=(const Term& t)
{
  // CHECK: expr managers must match
  if (this != &t)
  {
    *d_expr = *t.d_expr;
  }
  return *this;
}

bool Term::operator==(const Term& t) const
{
  // CHECK: expr managers must match
  return *d_expr == *t.d_expr;
}

bool Term::operator!=(const Term& t) const
{
  // CHECK: expr managers must match
  return *d_expr != *t.d_expr;
}

Kind Term::getKind() const { return intToExtKind(d_expr->getKind()); }

Sort Term::getSort() const { return Sort(d_expr->getType()); }

bool Term::isNull() const { return d_expr->isNull(); }

Term Term::notTerm() const { return d_expr->notExpr(); }

Term Term::andTerm(const Term& t) const { return d_expr->andExpr(*t.d_expr); }

Term Term::orTerm(const Term& t) const { return d_expr->orExpr(*t.d_expr); }

Term Term::xorTerm(const Term& t) const { return d_expr->xorExpr(*t.d_expr); }

Term Term::iffTerm(const Term& t) const { return d_expr->iffExpr(*t.d_expr); }

Term Term::impTerm(const Term& t) const { return d_expr->impExpr(*t.d_expr); }

Term Term::iteTerm(const Term& then_t, const Term& else_t) const
{
  return d_expr->iteExpr(*then_t.d_expr, *else_t.d_expr);
}

std::string Term::toString() const { return d_expr->toString(); }

Term::const_iterator::const_iterator() : d_iterator(nullptr) {}

Term::const_iterator::const_iterator(void* it) : d_iterator(it) {}

Term::const_iterator::const_iterator(const const_iterator& it)
    : d_iterator(nullptr)
{
  if (it.d_iterator != nullptr)
  {
    d_iterator = new CVC4::Expr::const_iterator(
        *static_cast<CVC4::Expr::const_iterator*>(it.d_iterator));
  }
}

Term::const_iterator& Term::const_iterator::operator=(const const_iterator& it)
{
  delete static_cast<CVC4::Expr::const_iterator*>(d_iterator);
  d_iterator = new CVC4::Expr::const_iterator(
      *static_cast<CVC4::Expr::const_iterator*>(it.d_iterator));
  return *this;
}

Term::const_iterator::~const_iterator()
{
  delete static_cast<CVC4::Expr::const_iterator*>(d_iterator);
}

bool Term::const_iterator::operator==(const const_iterator& it) const
{
  if (d_iterator == nullptr || it.d_iterator == nullptr)
  {
    return false;
  }
  return *static_cast<CVC4::Expr::const_iterator*>(d_iterator)
         == *static_cast<CVC4::Expr::const_iterator*>(it.d_iterator);
}

bool Term::const_iterator::operator!=(const const_iterator& it) const
{
  return !(*this == it);
}

Term::const_iterator& Term::const_iterator::operator++()
{
  Assert(d_iterator != nullptr);
  ++*static_cast<CVC4::Expr::const_iterator*>(d_iterator);
  return *this;
}

Term::const_iterator Term::const_iterator::operator++(int)
{
  Assert(d_iterator != nullptr);
  const_iterator it = *this;
  ++*static_cast<CVC4::Expr::const_iterator*>(d_iterator);
  return it;
}

Term Term::const_iterator::operator*() const
{
  Assert(d_iterator != nullptr);
  return Term(**static_cast<CVC4::Expr::const_iterator*>(d_iterator));
}

Term::const_iterator Term::begin() const
{
  return Term::const_iterator(new CVC4::Expr::const_iterator(d_expr->begin()));
}

Term::const_iterator Term::end() const
{
  return Term::const_iterator(new CVC4::Expr::const_iterator(d_expr->end()));
}

std::ostream& operator<<(std::ostream& out, const Term& t)
{
  out << t.toString();
  return out;
}

std::ostream& operator<<(std::ostream& out, const std::vector<Term>& vector)
{
  container_to_stream(out, vector);
  return out;
}

std::ostream& operator<<(std::ostream& out, const std::set<Term>& set)
{
  container_to_stream(out, set);
  return out;
}

std::ostream& operator<<(
    std::ostream& out,
    const std::unordered_set<Term, TermHashFunction>& unordered_set)
{
  container_to_stream(out, unordered_set);
  return out;
}

template <typename V>
std::ostream& operator<<(std::ostream& out, const std::map<Term, V>& map)
{
  container_to_stream(out, map);
  return out;
}

template <typename V>
std::ostream& operator<<(
    std::ostream& out,
    const std::unordered_map<Term, V, TermHashFunction>& unordered_map)
{
  container_to_stream(out, unordered_map);
  return out;
}

size_t TermHashFunction::operator()(const Term& t) const
{
  return ExprHashFunction()(*t.d_expr);
}

/* -------------------------------------------------------------------------- */
/* OpTerm                                                                     */
/* -------------------------------------------------------------------------- */

OpTerm::OpTerm() : d_expr(new CVC4::Expr()) {}

OpTerm::OpTerm(const CVC4::Expr& e) : d_expr(new CVC4::Expr(e)) {}

OpTerm::~OpTerm() {}

OpTerm& OpTerm::operator=(const OpTerm& t)
{
  // CHECK: expr managers must match
  if (this != &t)
  {
    *d_expr = *t.d_expr;
  }
  return *this;
}

bool OpTerm::operator==(const OpTerm& t) const
{
  // CHECK: expr managers must match
  return *d_expr == *t.d_expr;
}

bool OpTerm::operator!=(const OpTerm& t) const
{
  // CHECK: expr managers must match
  return *d_expr != *t.d_expr;
}

Kind OpTerm::getKind() const { return intToExtKind(d_expr->getKind()); }

Sort OpTerm::getSort() const { return Sort(d_expr->getType()); }

bool OpTerm::isNull() const { return d_expr->isNull(); }

std::string OpTerm::toString() const { return d_expr->toString(); }

std::ostream& operator<<(std::ostream& out, const OpTerm& t)
{
  out << t.toString();
  return out;
}

size_t OpTermHashFunction::operator()(const OpTerm& t) const
{
  return ExprHashFunction()(*t.d_expr);
}

/* -------------------------------------------------------------------------- */
/* Datatypes                                                                  */
/* -------------------------------------------------------------------------- */

/* DatatypeSelectorDecl ----------------------------------------------------- */

DatatypeSelectorDecl::DatatypeSelectorDecl(const std::string& name, Sort sort)
    : d_name(name), d_sort(sort)
{
}

DatatypeSelectorDecl::DatatypeSelectorDecl(const std::string& name,
                                           DatatypeDeclSelfSort sort)
    : d_name(name), d_sort(Sort(CVC4::Type()))
{
}

std::string DatatypeSelectorDecl::toString() const
{
  std::stringstream ss;
  ss << d_name << ": " << d_sort;
  return ss.str();
}

std::ostream& operator<<(std::ostream& out, const DatatypeDecl& dtdecl)
{
  out << dtdecl.toString();
  return out;
}

/* DatatypeConstructorDecl -------------------------------------------------- */

DatatypeConstructorDecl::DatatypeConstructorDecl(const std::string& name)
    : d_ctor(new CVC4::DatatypeConstructor(name))
{
}

void DatatypeConstructorDecl::addSelector(const DatatypeSelectorDecl& stor)
{
  CVC4::Type t = *stor.d_sort.d_type;
  if (t.isNull())
  {
    d_ctor->addArg(stor.d_name, DatatypeSelfType());
  }
  else
  {
    d_ctor->addArg(stor.d_name, t);
  }
}

std::string DatatypeConstructorDecl::toString() const
{
  std::stringstream ss;
  ss << *d_ctor;
  return ss.str();
}

std::ostream& operator<<(std::ostream& out,
                         const DatatypeConstructorDecl& ctordecl)
{
  out << ctordecl.toString();
  return out;
}

/* DatatypeDecl ------------------------------------------------------------- */

DatatypeDecl::DatatypeDecl(const std::string& name, bool isCoDatatype)
    : d_dtype(new CVC4::Datatype(name, isCoDatatype))
{
}

DatatypeDecl::DatatypeDecl(const std::string& name,
                           Sort param,
                           bool isCoDatatype)
    : d_dtype(new CVC4::Datatype(
          name, std::vector<Type>{*param.d_type}, isCoDatatype))
{
}

DatatypeDecl::DatatypeDecl(const std::string& name,
                           const std::vector<Sort>& params,
                           bool isCoDatatype)
{
  std::vector<Type> tparams;
  for (const Sort& s : params)
  {
    tparams.push_back(*s.d_type);
  }
  d_dtype = std::shared_ptr<CVC4::Datatype>(
      new CVC4::Datatype(name, tparams, isCoDatatype));
}

DatatypeDecl::~DatatypeDecl() {}

void DatatypeDecl::addConstructor(const DatatypeConstructorDecl& ctor)
{
  d_dtype->addConstructor(*ctor.d_ctor);
}

std::string DatatypeDecl::toString() const
{
  std::stringstream ss;
  ss << *d_dtype;
  return ss.str();
}

std::ostream& operator<<(std::ostream& out,
                         const DatatypeSelectorDecl& stordecl)
{
  out << stordecl.toString();
  return out;
}

/* DatatypeSelector --------------------------------------------------------- */

DatatypeSelector::DatatypeSelector() { d_stor = nullptr; }

DatatypeSelector::DatatypeSelector(const CVC4::DatatypeConstructorArg& stor)
    : d_stor(new CVC4::DatatypeConstructorArg(stor))
{
}

DatatypeSelector::~DatatypeSelector() {}

std::string DatatypeSelector::toString() const
{
  std::stringstream ss;
  ss << *d_stor;
  return ss.str();
}

std::ostream& operator<<(std::ostream& out, const DatatypeSelector& stor)
{
  out << stor.toString();
  return out;
}

/* DatatypeConstructor ------------------------------------------------------ */

DatatypeConstructor::DatatypeConstructor() { d_ctor = nullptr; }

DatatypeConstructor::DatatypeConstructor(const CVC4::DatatypeConstructor& ctor)
    : d_ctor(new CVC4::DatatypeConstructor(ctor))
{
}

DatatypeConstructor::~DatatypeConstructor() {}

DatatypeSelector DatatypeConstructor::operator[](const std::string& name) const
{
  // CHECK: selector with name exists?
  // CHECK: is resolved?
  return (*d_ctor)[name];
}

DatatypeSelector DatatypeConstructor::getSelector(const std::string& name) const
{
  // CHECK: cons with name exists?
  // CHECK: is resolved?
  return (*d_ctor)[name];
}

Term DatatypeConstructor::getSelectorTerm(const std::string& name) const
{
  // CHECK: cons with name exists?
  // CHECK: is resolved?
  return d_ctor->getSelector(name);
}

DatatypeConstructor::const_iterator DatatypeConstructor::begin() const
{
  return DatatypeConstructor::const_iterator(*d_ctor, true);
}

DatatypeConstructor::const_iterator DatatypeConstructor::end() const
{
  return DatatypeConstructor::const_iterator(*d_ctor, false);
}

DatatypeConstructor::const_iterator::const_iterator(
    const CVC4::DatatypeConstructor& ctor, bool begin)
{
  d_int_stors = ctor.getArgs();
  const std::vector<CVC4::DatatypeConstructorArg>* sels =
      static_cast<const std::vector<CVC4::DatatypeConstructorArg>*>(
          d_int_stors);
  for (const auto& s : *sels)
  {
    /* Can not use emplace_back here since constructor is private. */
    d_stors.push_back(DatatypeSelector(s));
  }
  d_idx = begin ? 0 : sels->size();
}

DatatypeConstructor::const_iterator& DatatypeConstructor::const_iterator::
operator=(const DatatypeConstructor::const_iterator& it)
{
  d_int_stors = it.d_int_stors;
  d_stors = it.d_stors;
  d_idx = it.d_idx;
  return *this;
}

const DatatypeSelector& DatatypeConstructor::const_iterator::operator*() const
{
  return d_stors[d_idx];
}

const DatatypeSelector* DatatypeConstructor::const_iterator::operator->() const
{
  return &d_stors[d_idx];
}

DatatypeConstructor::const_iterator& DatatypeConstructor::const_iterator::
operator++()
{
  ++d_idx;
  return *this;
}

DatatypeConstructor::const_iterator DatatypeConstructor::const_iterator::
operator++(int)
{
  DatatypeConstructor::const_iterator it(*this);
  ++d_idx;
  return it;
}

bool DatatypeConstructor::const_iterator::operator==(
    const DatatypeConstructor::const_iterator& other) const
{
  return d_int_stors == other.d_int_stors && d_idx == other.d_idx;
}

bool DatatypeConstructor::const_iterator::operator!=(
    const DatatypeConstructor::const_iterator& other) const
{
  return d_int_stors != other.d_int_stors || d_idx != other.d_idx;
}

std::string DatatypeConstructor::toString() const
{
  std::stringstream ss;
  ss << *d_ctor;
  return ss.str();
}

std::ostream& operator<<(std::ostream& out, const DatatypeConstructor& ctor)
{
  out << ctor.toString();
  return out;
}

/* Datatype ----------------------------------------------------------------- */

Datatype::Datatype(const CVC4::Datatype& dtype)
    : d_dtype(new CVC4::Datatype(dtype))
{
}

Datatype::~Datatype() {}

DatatypeConstructor Datatype::operator[](const std::string& name) const
{
  // CHECK: cons with name exists?
  // CHECK: is resolved?
  return (*d_dtype)[name];
}

DatatypeConstructor Datatype::getConstructor(const std::string& name) const
{
  // CHECK: cons with name exists?
  // CHECK: is resolved?
  return (*d_dtype)[name];
}

Term Datatype::getConstructorTerm(const std::string& name) const
{
  // CHECK: cons with name exists?
  // CHECK: is resolved?
  return d_dtype->getConstructor(name);
}

Datatype::const_iterator Datatype::begin() const
{
  return Datatype::const_iterator(*d_dtype, true);
}

Datatype::const_iterator Datatype::end() const
{
  return Datatype::const_iterator(*d_dtype, false);
}

Datatype::const_iterator::const_iterator(const CVC4::Datatype& dtype,
                                         bool begin)
{
  d_int_ctors = dtype.getConstructors();
  const std::vector<CVC4::DatatypeConstructor>* cons =
      static_cast<const std::vector<CVC4::DatatypeConstructor>*>(d_int_ctors);
  for (const auto& c : *cons)
  {
    /* Can not use emplace_back here since constructor is private. */
    d_ctors.push_back(DatatypeConstructor(c));
  }
  d_idx = begin ? 0 : cons->size();
}

Datatype::const_iterator& Datatype::const_iterator::operator=(
    const Datatype::const_iterator& it)
{
  d_int_ctors = it.d_int_ctors;
  d_ctors = it.d_ctors;
  d_idx = it.d_idx;
  return *this;
}

const DatatypeConstructor& Datatype::const_iterator::operator*() const
{
  return d_ctors[d_idx];
}

const DatatypeConstructor* Datatype::const_iterator::operator->() const
{
  return &d_ctors[d_idx];
}

Datatype::const_iterator& Datatype::const_iterator::operator++()
{
  ++d_idx;
  return *this;
}

Datatype::const_iterator Datatype::const_iterator::operator++(int)
{
  Datatype::const_iterator it(*this);
  ++d_idx;
  return it;
}

bool Datatype::const_iterator::operator==(
    const Datatype::const_iterator& other) const
{
  return d_int_ctors == other.d_int_ctors && d_idx == other.d_idx;
}

bool Datatype::const_iterator::operator!=(
    const Datatype::const_iterator& other) const
{
  return d_int_ctors != other.d_int_ctors || d_idx != other.d_idx;
}

/* -------------------------------------------------------------------------- */
/* Rounding Mode for Floating Points                                          */
/* -------------------------------------------------------------------------- */

const static std::
    unordered_map<RoundingMode, CVC4::RoundingMode, RoundingModeHashFunction>
        s_rmodes{
            {ROUND_NEAREST_TIES_TO_EVEN,
             CVC4::RoundingMode::roundNearestTiesToEven},
            {ROUND_TOWARD_POSITIVE, CVC4::RoundingMode::roundTowardPositive},
            {ROUND_TOWARD_NEGATIVE, CVC4::RoundingMode::roundTowardNegative},
            {ROUND_TOWARD_ZERO, CVC4::RoundingMode::roundTowardZero},
            {ROUND_NEAREST_TIES_TO_AWAY,
             CVC4::RoundingMode::roundNearestTiesToAway},
        };

const static std::unordered_map<CVC4::RoundingMode,
                                RoundingMode,
                                CVC4::RoundingModeHashFunction>
    s_rmodes_internal{
        {CVC4::RoundingMode::roundNearestTiesToEven,
         ROUND_NEAREST_TIES_TO_EVEN},
        {CVC4::RoundingMode::roundTowardPositive, ROUND_TOWARD_POSITIVE},
        {CVC4::RoundingMode::roundTowardNegative, ROUND_TOWARD_NEGATIVE},
        {CVC4::RoundingMode::roundTowardZero, ROUND_TOWARD_ZERO},
        {CVC4::RoundingMode::roundNearestTiesToAway,
         ROUND_NEAREST_TIES_TO_AWAY},
    };

size_t RoundingModeHashFunction::operator()(const RoundingMode& rm) const
{
  return size_t(rm);
}

/* -------------------------------------------------------------------------- */
/* Solver                                                                     */
/* -------------------------------------------------------------------------- */

Solver::Solver(Options* opts) : d_opts(new Options())
{
  if (opts) d_opts->copyValues(*opts);
  d_exprMgr = std::unique_ptr<ExprManager>(new ExprManager(*d_opts));
  d_smtEngine = std::unique_ptr<SmtEngine>(new SmtEngine(d_exprMgr.get()));
  d_rng = std::unique_ptr<Random>(new Random((*d_opts)[options::seed]));
}

Solver::~Solver() {}

/* Sorts Handling                                                             */
/* -------------------------------------------------------------------------- */

Sort Solver::getBooleanSort(void) const { return d_exprMgr->booleanType(); }

Sort Solver::getIntegerSort(void) const { return d_exprMgr->integerType(); }

Sort Solver::getRealSort(void) const { return d_exprMgr->realType(); }

Sort Solver::getRegExpSort(void) const { return d_exprMgr->regExpType(); }

Sort Solver::getStringSort(void) const { return d_exprMgr->stringType(); }

Sort Solver::getRoundingmodeSort(void) const
{
  return d_exprMgr->roundingModeType();
}

/* Create sorts ------------------------------------------------------- */

Sort Solver::mkArraySort(Sort indexSort, Sort elemSort) const
{
  // CHECK: indexSort exists
  // CHECK: elemSort exists
  return d_exprMgr->mkArrayType(*indexSort.d_type, *elemSort.d_type);
}

Sort Solver::mkBitVectorSort(uint32_t size) const
{
  // CHECK: size > 0
  return d_exprMgr->mkBitVectorType(size);
}

Sort Solver::mkDatatypeSort(DatatypeDecl dtypedecl) const
{
  // CHECK: num constructors > 0
  return d_exprMgr->mkDatatypeType(*dtypedecl.d_dtype);
}

Sort Solver::mkFunctionSort(Sort domain, Sort range) const
{
  // CHECK: domain exists
  // CHECK: range exists
  // CHECK:
  // domain.isFirstClass()
  // else "can not create function type for domain type that is not
  //       first class"
  // CHECK:
  // range.isFirstClass()
  // else "can not create function type for range type that is not
  //       first class"
  // CHECK:
  // !range.isFunction()
  // else "must flatten function types"
  return d_exprMgr->mkFunctionType(*domain.d_type, *range.d_type);
}

Sort Solver::mkFunctionSort(const std::vector<Sort>& argSorts, Sort range) const
{
  // CHECK: for all s in argSorts, s exists
  // CHECK: range exists
  // CHECK: argSorts.size() >= 1
  // CHECK:
  // for (unsigned i = 0; i < argSorts.size(); ++ i)
  //   argSorts[i].isFirstClass()
  // else "can not create function type for argument type that is not
  //       first class"
  // CHECK:
  // range.isFirstClass()
  // else "can not create function type for range type that is not
  //       first class"
  // CHECK:
  // !range.isFunction()
  // else "must flatten function types"
  std::vector<Type> argTypes = sortVectorToTypes(argSorts);
  return d_exprMgr->mkFunctionType(argTypes, *range.d_type);
}

Sort Solver::mkParamSort(const std::string& symbol) const
{
  return d_exprMgr->mkSort(symbol, ExprManager::SORT_FLAG_PLACEHOLDER);
}

Sort Solver::mkPredicateSort(const std::vector<Sort>& sorts) const
{
  // CHECK: for all s in sorts, s exists
  // CHECK: sorts.size() >= 1
  // CHECK:
  // for (unsigned i = 0; i < sorts.size(); ++ i)
  //   sorts[i].isFirstClass()
  // else "can not create predicate type for argument type that is not
  //       first class"
  std::vector<Type> types = sortVectorToTypes(sorts);
  return d_exprMgr->mkPredicateType(types);
}

Sort Solver::mkRecordSort(
    const std::vector<std::pair<std::string, Sort>>& fields) const
{
  std::vector<std::pair<std::string, Type>> f;
  for (const auto& p : fields)
  {
    f.emplace_back(p.first, *p.second.d_type);
  }
  return d_exprMgr->mkRecordType(Record(f));
}

Sort Solver::mkSetSort(Sort elemSort) const
{
  return d_exprMgr->mkSetType(*elemSort.d_type);
}

Sort Solver::mkUninterpretedSort(const std::string& symbol) const
{
  return d_exprMgr->mkSort(symbol);
}

Sort Solver::mkTupleSort(const std::vector<Sort>& sorts) const
{
  // CHECK: for all s in sorts, s exists
  // CHECK:
  // for (unsigned i = 0; i < sorts.size(); ++ i)
  //   !sorts[i].isFunctionLike()
  // else "function-like types in tuples not allowed"
  std::vector<Type> types = sortVectorToTypes(sorts);
  return d_exprMgr->mkTupleType(types);
}

std::vector<Type> Solver::sortVectorToTypes(
    const std::vector<Sort>& sorts) const
{
  std::vector<Type> res;
  for (const Sort& s : sorts)
  {
    res.push_back(*s.d_type);
  }
  return res;
}

/* Create consts                                                              */
/* -------------------------------------------------------------------------- */

Term Solver::mkTrue(void) const { return d_exprMgr->mkConst<bool>(true); }

Term Solver::mkFalse(void) const { return d_exprMgr->mkConst<bool>(false); }

Term Solver::mkBoolean(bool val) const { return d_exprMgr->mkConst<bool>(val); }

Term Solver::mkInteger(const char* s, uint32_t base) const
{
  return d_exprMgr->mkConst(Rational(s, base));
}

Term Solver::mkInteger(const std::string& s, uint32_t base) const
{
  return d_exprMgr->mkConst(Rational(s, base));
}

Term Solver::mkInteger(int32_t val) const
{
  return d_exprMgr->mkConst(Rational(val));
}

Term Solver::mkInteger(uint32_t val) const
{
  return d_exprMgr->mkConst(Rational(val));
}

Term Solver::mkInteger(int64_t val) const
{
  return d_exprMgr->mkConst(Rational(val));
}

Term Solver::mkInteger(uint64_t val) const
{
  return d_exprMgr->mkConst(Rational(val));
}

Term Solver::mkPi() const
{
  return d_exprMgr->mkNullaryOperator(d_exprMgr->realType(), CVC4::kind::PI);
}

Term Solver::mkReal(const char* s, uint32_t base) const
{
  return d_exprMgr->mkConst(Rational(s, base));
}

Term Solver::mkReal(const std::string& s, uint32_t base) const
{
  return d_exprMgr->mkConst(Rational(s, base));
}

Term Solver::mkReal(int32_t val) const
{
  return d_exprMgr->mkConst(Rational(val));
}

Term Solver::mkReal(int64_t val) const
{
  return d_exprMgr->mkConst(Rational(val));
}

Term Solver::mkReal(uint32_t val) const
{
  return d_exprMgr->mkConst(Rational(val));
}

Term Solver::mkReal(uint64_t val) const
{
  return d_exprMgr->mkConst(Rational(val));
}

Term Solver::mkReal(int32_t num, int32_t den) const
{
  return d_exprMgr->mkConst(Rational(num, den));
}

Term Solver::mkReal(int64_t num, int64_t den) const
{
  return d_exprMgr->mkConst(Rational(num, den));
}

Term Solver::mkReal(uint32_t num, uint32_t den) const
{
  return d_exprMgr->mkConst(Rational(num, den));
}

Term Solver::mkReal(uint64_t num, uint64_t den) const
{
  return d_exprMgr->mkConst(Rational(num, den));
}

Term Solver::mkRegexpEmpty() const
{
  return d_exprMgr->mkExpr(CVC4::kind::REGEXP_EMPTY, std::vector<Expr>());
}

Term Solver::mkRegexpSigma() const
{
  return d_exprMgr->mkExpr(CVC4::kind::REGEXP_SIGMA, std::vector<Expr>());
}

Term Solver::mkEmptySet(Sort s) const
{
  return d_exprMgr->mkConst(EmptySet(*s.d_type));
}

Term Solver::mkSepNil(Sort sort) const
{
  return d_exprMgr->mkNullaryOperator(*sort.d_type, CVC4::kind::SEP_NIL);
}

Term Solver::mkString(const char* s) const
{
  return d_exprMgr->mkConst(String(s));
}

Term Solver::mkString(const std::string& s) const
{
  return d_exprMgr->mkConst(String(s));
}

Term Solver::mkString(const unsigned char c) const
{
  return d_exprMgr->mkConst(String(c));
}

Term Solver::mkString(const std::vector<unsigned>& s) const
{
  return d_exprMgr->mkConst(String(s));
}

Term Solver::mkUniverseSet(Sort sort) const
{
  return d_exprMgr->mkNullaryOperator(*sort.d_type, CVC4::kind::UNIVERSE_SET);
}

Term Solver::mkBitVector(uint32_t size) const
{
  return d_exprMgr->mkConst(BitVector(size));
}

Term Solver::mkBitVector(uint32_t size, uint32_t val) const
{
  return d_exprMgr->mkConst(BitVector(size, val));
}

Term Solver::mkBitVector(uint32_t size, uint64_t val) const
{
  return d_exprMgr->mkConst(BitVector(size, val));
}

Term Solver::mkBitVector(const char* s, uint32_t base) const
{
  return d_exprMgr->mkConst(BitVector(s, base));
}

Term Solver::mkBitVector(std::string& s, uint32_t base) const
{
  return d_exprMgr->mkConst(BitVector(s, base));
}

Term Solver::mkConst(RoundingMode rm) const
{
  // CHECK: kind == CONST_ROUNDINGMODE
  // CHECK: valid rm?
  return d_exprMgr->mkConst(s_rmodes.at(rm));
}

Term Solver::mkConst(Kind kind, Sort arg) const
{
  // CHECK: kind == EMPTYSET
  return d_exprMgr->mkConst(CVC4::EmptySet(*arg.d_type));
}

Term Solver::mkConst(Kind kind, Sort arg1, int32_t arg2) const
{
  // CHECK: kind == UNINTERPRETED_CONSTANT
  return d_exprMgr->mkConst(CVC4::UninterpretedConstant(*arg1.d_type, arg2));
}

Term Solver::mkConst(Kind kind, bool arg) const
{
  // CHECK: kind == CONST_BOOLEAN
  return d_exprMgr->mkConst<bool>(arg);
}

Term Solver::mkConst(Kind kind, const char* arg) const
{
  // CHECK: kind == CONST_STRING
  return d_exprMgr->mkConst(CVC4::String(arg));
}

Term Solver::mkConst(Kind kind, const std::string& arg) const
{
  // CHECK: kind == CONST_STRING
  return d_exprMgr->mkConst(CVC4::String(arg));
}

Term Solver::mkConst(Kind kind, const char* arg1, uint32_t arg2) const
{
  // CHECK: kind == ABSTRACT_VALUE
  //           || kind == CONST_RATIONAL
  //           || kind == CONST_BITVECTOR
  if (kind == ABSTRACT_VALUE)
  {
    return d_exprMgr->mkConst(CVC4::AbstractValue(Integer(arg1, arg2)));
  }
  if (kind == CONST_RATIONAL)
  {
    return d_exprMgr->mkConst(CVC4::Rational(arg1, arg2));
  }
  return d_exprMgr->mkConst(CVC4::BitVector(arg1, arg2));
}

Term Solver::mkConst(Kind kind, const std::string& arg1, uint32_t arg2) const
{
  // CHECK: kind == ABSTRACT_VALUE
  //           || kind == CONST_RATIONAL
  //           || kind == CONST_BITVECTOR
  if (kind == ABSTRACT_VALUE)
  {
    return d_exprMgr->mkConst(CVC4::AbstractValue(Integer(arg1, arg2)));
  }
  if (kind == CONST_RATIONAL)
  {
    return d_exprMgr->mkConst(CVC4::Rational(arg1, arg2));
  }
  return d_exprMgr->mkConst(CVC4::BitVector(arg1, arg2));
}

Term Solver::mkConst(Kind kind, uint32_t arg) const
{
  // CHECK: kind == ABSTRACT_VALUE
  //           || kind == CONST_RATIONAL
  //           || kind == CONST_BITVECTOR
  if (kind == ABSTRACT_VALUE)
  {
    return d_exprMgr->mkConst(CVC4::AbstractValue(Integer(arg)));
  }
  if (kind == CONST_RATIONAL)
  {
    return d_exprMgr->mkConst(CVC4::Rational(arg));
  }
  return d_exprMgr->mkConst(CVC4::BitVector(arg));
}

Term Solver::mkConst(Kind kind, int32_t arg) const
{
  // CHECK: kind == ABSTRACT_VALUE
  //           || kind == CONST_RATIONAL
  if (kind == ABSTRACT_VALUE)
  {
    return d_exprMgr->mkConst(CVC4::AbstractValue(Integer(arg)));
  }
  return d_exprMgr->mkConst(CVC4::Rational(arg));
}

Term Solver::mkConst(Kind kind, int64_t arg) const
{
  // CHECK: kind == ABSTRACT_VALUE
  //           || kind == CONST_RATIONAL
  if (kind == ABSTRACT_VALUE)
  {
    return d_exprMgr->mkConst(CVC4::AbstractValue(Integer(arg)));
  }
  return d_exprMgr->mkConst(CVC4::Rational(arg));
}

Term Solver::mkConst(Kind kind, uint64_t arg) const
{
  // CHECK: kind == ABSTRACT_VALUE
  //           || kind == CONST_RATIONAL
  if (kind == ABSTRACT_VALUE)
  {
    return d_exprMgr->mkConst(CVC4::AbstractValue(Integer(arg)));
  }
  return d_exprMgr->mkConst(CVC4::Rational(arg));
}

Term Solver::mkConst(Kind kind, uint32_t arg1, uint32_t arg2) const
{
  // CHECK: kind == CONST_RATIONAL
  return d_exprMgr->mkConst(CVC4::Rational(arg1, arg2));
}

Term Solver::mkConst(Kind kind, int32_t arg1, int32_t arg2) const
{
  // CHECK: kind == CONST_RATIONAL
  return d_exprMgr->mkConst(CVC4::Rational(arg1, arg2));
}

Term Solver::mkConst(Kind kind, int64_t arg1, int64_t arg2) const
{
  // CHECK: kind == CONST_RATIONAL
  return d_exprMgr->mkConst(CVC4::Rational(arg1, arg2));
}

Term Solver::mkConst(Kind kind, uint64_t arg1, uint64_t arg2) const
{
  // CHECK: kind == CONST_RATIONAL
  return d_exprMgr->mkConst(CVC4::Rational(arg1, arg2));
}

Term Solver::mkConst(Kind kind, uint32_t arg1, uint64_t arg2) const
{
  // CHECK: kind == CONST_BITVECTOR
  return d_exprMgr->mkConst(CVC4::BitVector(arg1, arg2));
}

Term Solver::mkConst(Kind kind, uint32_t arg1, uint32_t arg2, Term arg3) const
{
  // CHECK: kind == CONST_FLOATINGPOINT
  // CHECK: arg 3 is bit-vector constant
  return d_exprMgr->mkConst(
      CVC4::FloatingPoint(arg1, arg2, arg3.d_expr->getConst<BitVector>()));
}

/* Create variables                                                           */
/* -------------------------------------------------------------------------- */

Term Solver::mkVar(const std::string& symbol, Sort sort) const
{
  // CHECK: sort exists?
  return d_exprMgr->mkVar(symbol, *sort.d_type);
}

Term Solver::mkVar(Sort sort) const
{
  // CHECK: sort exists?
  return d_exprMgr->mkVar(*sort.d_type);
}

Term Solver::mkBoundVar(const std::string& symbol, Sort sort) const
{
  // CHECK: sort exists?
  return d_exprMgr->mkBoundVar(symbol, *sort.d_type);
}

Term Solver::mkBoundVar(Sort sort) const
{
  // CHECK: sort exists?
  return d_exprMgr->mkBoundVar(*sort.d_type);
}

/* Create terms                                                               */
/* -------------------------------------------------------------------------- */

Term Solver::mkTerm(Kind kind) const
{
  // CHECK: kind == PI
  //          || kind == REGEXP_EMPTY
  //          || kind == REGEXP_SIGMA
  if (kind == REGEXP_EMPTY || kind == REGEXP_SIGMA)
  {
    return d_exprMgr->mkExpr(extToIntKind(kind), std::vector<Expr>());
  }
  Assert(kind == PI);
  return d_exprMgr->mkNullaryOperator(d_exprMgr->realType(), CVC4::kind::PI);
}

Term Solver::mkTerm(Kind kind, Sort sort) const
{
  // CHECK: kind == SEP_NIL
  //          || kind == UNIVERSE_SET
  return d_exprMgr->mkNullaryOperator(*sort.d_type, extToIntKind(kind));
}

Term Solver::mkTerm(Kind kind, Term child) const
{
  // CHECK:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(child.getExprManager())
  // CHECK:
  // const Metakind mk = kind::metaKindOf(kind);
  // mk != kind::metakind::PARAMETERIZED && mk != kind::metakind::OPERATOR
  // else "Only operator-style expressions are made with mkExpr(); "
  //      "to make variables and constants, see mkVar(), mkBoundVar(), "
  //      "and mkConst()."
  // CHECK:
  // const unsigned n = 1 - (mk == kind::metakind::PARAMETERIZED ? 1 : 0);
  // n < minArity(kind) || n > maxArity(kind)
  // else "Exprs with kind %s must have at least %u children and "
  //      "at most %u children (the one under construction has %u)"
  return d_exprMgr->mkExpr(extToIntKind(kind), *child.d_expr);
}

Term Solver::mkTerm(Kind kind, Term child1, Term child2) const
{
  // CHECK:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(child1.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(child2.getExprManager())
  // CHECK:
  // const Metakind mk = kind::metaKindOf(kind);
  // mk != kind::metakind::PARAMETERIZED && mk != kind::metakind::OPERATOR
  // else "Only operator-style expressions are made with mkExpr(); "
  //      "to make variables and constants, see mkVar(), mkBoundVar(), "
  //      "and mkConst()."
  // CHECK:
  // const unsigned n = 2 - (mk == kind::metakind::PARAMETERIZED ? 1 : 0);
  // n < minArity(kind) || n > maxArity(kind)
  // else "Exprs with kind %s must have at least %u children and "
  //      "at most %u children (the one under construction has %u)"
  return d_exprMgr->mkExpr(extToIntKind(kind), *child1.d_expr, *child2.d_expr);
}

Term Solver::mkTerm(Kind kind, Term child1, Term child2, Term child3) const
{
  // CHECK:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(child1.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(child2.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(child3.getExprManager())
  // CHECK:
  // const Metakind mk = kind::metaKindOf(kind);
  // mk != kind::metakind::PARAMETERIZED && mk != kind::metakind::OPERATOR
  // else "Only operator-style expressions are made with mkExpr(); "
  //      "to make variables and constants, see mkVar(), mkBoundVar(), "
  //      "and mkConst()."
  // CHECK:
  // const unsigned n = 3 - (mk == kind::metakind::PARAMETERIZED ? 1 : 0);
  // n < minArity(kind) || n > maxArity(kind)
  // else "Exprs with kind %s must have at least %u children and "
  //      "at most %u children (the one under construction has %u)"
  std::vector<Expr> echildren{*child1.d_expr, *child2.d_expr, *child3.d_expr};
  CVC4::Kind k = extToIntKind(kind);
  return kind::isAssociative(k) ? d_exprMgr->mkAssociative(k, echildren)
                                : d_exprMgr->mkExpr(k, echildren);
}

Term Solver::mkTerm(Kind kind, const std::vector<Term>& children) const
{
  // CHECK:
  // for c in children:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(c.getExprManager())
  // CHECK:
  // const Metakind mk = kind::metaKindOf(kind);
  // mk != kind::metakind::PARAMETERIZED && mk != kind::metakind::OPERATOR
  // else "Only operator-style expressions are made with mkExpr(); "
  //      "to make variables and constants, see mkVar(), mkBoundVar(), "
  //      "and mkConst()."
  // CHECK:
  // const unsigned n = children.size() - (mk == kind::metakind::PARAMETERIZED ?
  // 1 : 0); n < minArity(kind) || n > maxArity(kind) else "Exprs with kind %s
  // must have at least %u children and "
  //      "at most %u children (the one under construction has %u)"
  std::vector<Expr> echildren = termVectorToExprs(children);
  CVC4::Kind k = extToIntKind(kind);
  return kind::isAssociative(k) ? d_exprMgr->mkAssociative(k, echildren)
                                : d_exprMgr->mkExpr(k, echildren);
}

Term Solver::mkTerm(OpTerm opTerm) const
{
  // CHECK:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(opExpr.getExprManager())
  // CHECK:
  // const Kind kind = NodeManager::opToKind(opExpr.getNode());
  // opExpr.getKind() != kind::BUILTIN
  // && kind::metaKindOf(kind) != kind::metakind::PARAMETERIZED
  // else "This Expr constructor is for parameterized kinds only"
  return d_exprMgr->mkExpr(*opTerm.d_expr);
}

Term Solver::mkTerm(OpTerm opTerm, Term child) const
{
  // CHECK:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(opExpr.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(child.getExprManager())
  // CHECK:
  // const Kind kind = NodeManager::opToKind(opExpr.getNode());
  // opExpr.getKind() != kind::BUILTIN
  // && kind::metaKindOf(kind) != kind::metakind::PARAMETERIZED
  // else "This Expr constructor is for parameterized kinds only"
  // CHECK:
  // const unsigned n = 1 - (mk == kind::metakind::PARAMETERIZED ? 1 : 0);
  // n < minArity(kind) || n > maxArity(kind)
  // else "Exprs with kind %s must have at least %u children and "
  //      "at most %u children (the one under construction has %u)"
  return d_exprMgr->mkExpr(*opTerm.d_expr, *child.d_expr);
}

Term Solver::mkTerm(OpTerm opTerm, Term child1, Term child2) const
{
  // CHECK:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(opExpr.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(child1.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(child2.getExprManager())
  // CHECK:
  // const Kind kind = NodeManager::opToKind(opExpr.getNode());
  // opExpr.getKind() != kind::BUILTIN
  // && kind::metaKindOf(kind) != kind::metakind::PARAMETERIZED
  // else "This Expr constructor is for parameterized kinds only"
  // CHECK:
  // const unsigned n = 2 - (mk == kind::metakind::PARAMETERIZED ? 1 : 0);
  // n < minArity(kind) || n > maxArity(kind)
  // else "Exprs with kind %s must have at least %u children and "
  //      "at most %u children (the one under construction has %u)"
  return d_exprMgr->mkExpr(*opTerm.d_expr, *child1.d_expr, *child2.d_expr);
}

Term Solver::mkTerm(OpTerm opTerm, Term child1, Term child2, Term child3) const
{
  // CHECK:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(opExpr.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(child1.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(child2.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(child3.getExprManager())
  // CHECK:
  // const Kind kind = NodeManager::opToKind(opExpr.getNode());
  // opExpr.getKind() != kind::BUILTIN
  // && kind::metaKindOf(kind) != kind::metakind::PARAMETERIZED
  // else "This Expr constructor is for parameterized kinds only"
  // CHECK:
  // const unsigned n = 3 - (mk == kind::metakind::PARAMETERIZED ? 1 : 0);
  // n < minArity(kind) || n > maxArity(kind)
  // else "Exprs with kind %s must have at least %u children and "
  //      "at most %u children (the one under construction has %u)"
  return d_exprMgr->mkExpr(
      *opTerm.d_expr, *child1.d_expr, *child2.d_expr, *child3.d_expr);
}

Term Solver::mkTerm(OpTerm opTerm, const std::vector<Term>& children) const
{
  // CHECK:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(opExpr.getExprManager())
  // for c in children:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(c.getExprManager())
  // CHECK:
  // const Kind kind = NodeManager::opToKind(opExpr.getNode());
  // opExpr.getKind() != kind::BUILTIN
  // && kind::metaKindOf(kind) != kind::metakind::PARAMETERIZED
  // else "This Expr constructor is for parameterized kinds only"
  // CHECK:
  // const unsigned n = children.size() - (mk == kind::metakind::PARAMETERIZED ?
  // 1 : 0); n < minArity(kind) || n > maxArity(kind) else "Exprs with kind %s
  // must have at least %u children and "
  //      "at most %u children (the one under construction has %u)"
  std::vector<Expr> echildren = termVectorToExprs(children);
  return d_exprMgr->mkExpr(*opTerm.d_expr, echildren);
}

std::vector<Expr> Solver::termVectorToExprs(
    const std::vector<Term>& terms) const
{
  std::vector<Expr> res;
  for (const Term& t : terms)
  {
    res.push_back(*t.d_expr);
  }
  return res;
}

/* Create operator terms                                                      */
/* -------------------------------------------------------------------------- */

OpTerm Solver::mkOpTerm(Kind kind, Kind k)
{
  // CHECK: kind == CHAIN_OP
  return d_exprMgr->mkConst(CVC4::Chain(extToIntKind(k)));
}

OpTerm Solver::mkOpTerm(Kind kind, const std::string& arg)
{
  // CHECK:
  // kind == RECORD_UPDATE_OP
  return d_exprMgr->mkConst(CVC4::RecordUpdate(arg));
}

OpTerm Solver::mkOpTerm(Kind kind, uint32_t arg)
{
  OpTerm res;
  switch (kind)
  {
    case DIVISIBLE_OP: res = d_exprMgr->mkConst(CVC4::Divisible(arg)); break;
    case BITVECTOR_REPEAT_OP:
      res = d_exprMgr->mkConst(CVC4::BitVectorRepeat(arg));
      break;
    case BITVECTOR_ZERO_EXTEND_OP:
      res = d_exprMgr->mkConst(CVC4::BitVectorZeroExtend(arg));
      break;
    case BITVECTOR_SIGN_EXTEND_OP:
      res = d_exprMgr->mkConst(CVC4::BitVectorSignExtend(arg));
      break;
    case BITVECTOR_ROTATE_LEFT_OP:
      res = d_exprMgr->mkConst(CVC4::BitVectorRotateLeft(arg));
      break;
    case BITVECTOR_ROTATE_RIGHT_OP:
      res = d_exprMgr->mkConst(CVC4::BitVectorRotateRight(arg));
      break;
    case INT_TO_BITVECTOR_OP:
      res = d_exprMgr->mkConst(CVC4::IntToBitVector(arg));
      break;
    case FLOATINGPOINT_TO_UBV_OP:
      res = d_exprMgr->mkConst(CVC4::FloatingPointToUBV(arg));
      break;
    case FLOATINGPOINT_TO_UBV_TOTAL_OP:
      res = d_exprMgr->mkConst(CVC4::FloatingPointToUBVTotal(arg));
      break;
    case FLOATINGPOINT_TO_SBV_OP:
      res = d_exprMgr->mkConst(CVC4::FloatingPointToSBV(arg));
      break;
    case FLOATINGPOINT_TO_SBV_TOTAL_OP:
      res = d_exprMgr->mkConst(CVC4::FloatingPointToSBVTotal(arg));
      break;
    case TUPLE_UPDATE_OP:
      res = d_exprMgr->mkConst(CVC4::TupleUpdate(arg));
      break;
    default:
      // CHECK: kind valid?
      Assert(!res.isNull());
  }
  return res;
}

OpTerm Solver::mkOpTerm(Kind kind, uint32_t arg1, uint32_t arg2)
{
  OpTerm res;
  switch (kind)
  {
    case BITVECTOR_EXTRACT_OP:
      res = d_exprMgr->mkConst(CVC4::BitVectorExtract(arg1, arg2));
      break;
    case FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP:
      res =
          d_exprMgr->mkConst(CVC4::FloatingPointToFPIEEEBitVector(arg1, arg2));
      break;
    case FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP:
      res =
          d_exprMgr->mkConst(CVC4::FloatingPointToFPFloatingPoint(arg1, arg2));
      break;
    case FLOATINGPOINT_TO_FP_REAL_OP:
      res = d_exprMgr->mkConst(CVC4::FloatingPointToFPReal(arg1, arg2));
      break;
    case FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP:
      res = d_exprMgr->mkConst(
          CVC4::FloatingPointToFPSignedBitVector(arg1, arg2));
      break;
    case FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP:
      res = d_exprMgr->mkConst(
          CVC4::FloatingPointToFPUnsignedBitVector(arg1, arg2));
      break;
    case FLOATINGPOINT_TO_FP_GENERIC_OP:
      res = d_exprMgr->mkConst(CVC4::FloatingPointToFPGeneric(arg1, arg2));
      break;
    default:
      // CHECK: kind valid?
      Assert(!res.isNull());
  }
  return res;
}

/* Non-SMT-LIB commands                                                       */
/* -------------------------------------------------------------------------- */

Term Solver::simplify(const Term& t)
{
  return d_smtEngine->simplify(*t.d_expr);
}

Result Solver::checkValid(void) const
{
  // CHECK:
  // if d_queryMade -> incremental enabled
  CVC4::Result r = d_smtEngine->query();
  return Result(r);
}

Result Solver::checkValidAssuming(Term assumption) const
{
  // CHECK:
  // if assumptions.size() > 0:  incremental enabled?
  CVC4::Result r = d_smtEngine->query(*assumption.d_expr);
  return Result(r);
}

Result Solver::checkValidAssuming(const std::vector<Term>& assumptions) const
{
  // CHECK:
  // if assumptions.size() > 0:  incremental enabled?
  std::vector<Expr> eassumptions = termVectorToExprs(assumptions);
  CVC4::Result r = d_smtEngine->query(eassumptions);
  return Result(r);
}

/* SMT-LIB commands                                                           */
/* -------------------------------------------------------------------------- */

/**
 *  ( assert <term> )
 */
void Solver::assertFormula(Term term) const
{
  // CHECK:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(expr.getExprManager())
  d_smtEngine->assertFormula(*term.d_expr);
}

/**
 *  ( check-sat )
 */
Result Solver::checkSat(void) const
{
  // CHECK:
  // if d_queryMade -> incremental enabled
  CVC4::Result r = d_smtEngine->checkSat();
  return Result(r);
}

/**
 *  ( check-sat-assuming ( <prop_literal> ) )
 */
Result Solver::checkSatAssuming(Term assumption) const
{
  // CHECK:
  // if assumptions.size() > 0:  incremental enabled?
  CVC4::Result r = d_smtEngine->checkSat(*assumption.d_expr);
  return Result(r);
}

/**
 *  ( check-sat-assuming ( <prop_literal>* ) )
 */
Result Solver::checkSatAssuming(const std::vector<Term>& assumptions) const
{
  // CHECK:
  // if assumptions.size() > 0:  incremental enabled?
  std::vector<Expr> eassumptions = termVectorToExprs(assumptions);
  CVC4::Result r = d_smtEngine->checkSat(eassumptions);
  return Result(r);
}

/**
 *  ( declare-const <symbol> <sort> )
 */
Term Solver::declareConst(const std::string& symbol, Sort sort) const
{
  // CHECK: sort exists
  return d_exprMgr->mkVar(symbol, *sort.d_type);
}

/**
 *  ( declare-datatype <symbol> <datatype_decl> )
 */
Sort Solver::declareDatatype(
    const std::string& symbol,
    const std::vector<DatatypeConstructorDecl>& ctors) const
{
  DatatypeDecl dtdecl(symbol);
  for (const DatatypeConstructorDecl& ctor : ctors)
  {
    dtdecl.addConstructor(ctor);
  }
  return mkDatatypeSort(dtdecl);
}

}  // namespace api
}  // namespace CVC4

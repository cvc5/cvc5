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
#include "base/cvc4_check.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node_manager.h"
#include "expr/type.h"
#include "options/main_options.h"
#include "options/options.h"
#include "smt/model.h"
#include "smt/smt_engine.h"
#include "util/random.h"
#include "util/result.h"
#include "util/utility.h"

#include <sstream>

namespace CVC4 {
namespace api {

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

bool isDefinedKind(Kind k) { return k > UNDEFINED_KIND && k < LAST_KIND; }

bool isDefinedIntKind(CVC4::Kind k)
{
  return k != CVC4::Kind::UNDEFINED_KIND && k != CVC4::Kind::LAST_KIND;
}

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

uint32_t minArity(Kind k)
{
  Assert(isDefinedKind(k));
  Assert(isDefinedIntKind(extToIntKind(k)));
  return CVC4::ExprManager::minArity(extToIntKind(k));
}

uint32_t maxArity(Kind k)
{
  Assert(isDefinedKind(k));
  Assert(isDefinedIntKind(extToIntKind(k)));
  return CVC4::ExprManager::maxArity(extToIntKind(k));
}
}  // namespace

std::string kindToString(Kind k)
{
  return k == INTERNAL_KIND ? "INTERNAL_KIND"
                            : CVC4::kind::kindToString(extToIntKind(k));
}

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
/* API guard helpers                                                          */
/* -------------------------------------------------------------------------- */

namespace {

class CVC4ApiExceptionStream
{
 public:
  CVC4ApiExceptionStream() {}
  /* Note: This needs to be explicitly set to 'noexcept(false)' since it is
   * a destructor that throws an exception and in C++11 all destructors
   * default to noexcept(true) (else this triggers a call to std::terminate). */
  ~CVC4ApiExceptionStream() noexcept(false)
  {
    if (!std::uncaught_exception())
    {
      throw CVC4ApiException(d_stream.str());
    }
  }

  std::ostream& ostream() { return d_stream; }

 private:
  std::stringstream d_stream;
};

#define CVC4_API_CHECK(cond) \
  CVC4_PREDICT_FALSE(cond)   \
  ? (void)0 : OstreamVoider() & CVC4ApiExceptionStream().ostream()

#define CVC4_API_KIND_CHECK(kind)     \
  CVC4_API_CHECK(isDefinedKind(kind)) \
      << "Invalid kind '" << kindToString(kind) << "'";

#define CVC4_API_KIND_CHECK_EXPECTED(cond, kind) \
  CVC4_PREDICT_FALSE(cond)                       \
  ? (void)0                                      \
  : OstreamVoider()                              \
          & CVC4ApiExceptionStream().ostream()   \
                << "Invalid kind '" << kindToString(kind) << "', expected "

#define CVC4_API_ARG_CHECK_EXPECTED(cond, arg)                      \
  CVC4_PREDICT_FALSE(cond)                                          \
  ? (void)0                                                         \
  : OstreamVoider()                                                 \
          & CVC4ApiExceptionStream().ostream()                      \
                << "Invalid argument '" << arg << "' for '" << #arg \
                << "', expected "

#define CVC4_API_ARG_SIZE_CHECK_EXPECTED(cond, arg) \
  CVC4_PREDICT_FALSE(cond)                          \
  ? (void)0                                         \
  : OstreamVoider()                                 \
          & CVC4ApiExceptionStream().ostream()      \
                << "Invalid size of argument '" << #arg << "', expected "

#define CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(cond, what, arg, idx)         \
  CVC4_PREDICT_FALSE(cond)                                                 \
  ? (void)0                                                                \
  : OstreamVoider()                                                        \
          & CVC4ApiExceptionStream().ostream()                             \
                << "Invalid " << what << "'" << arg << "' at index" << idx \
                << ", expected "
}  // namespace

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

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::Result Result::getResult(void) const { return *d_result; }

std::ostream& operator<<(std::ostream& out, const Result& r)
{
  out << r.toString();
  return out;
}

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

Sort::Sort(const CVC4::Type& t) : d_type(new CVC4::Type(t)) {}

Sort::~Sort() {}

Sort& Sort::operator=(const Sort& s)
{
  if (this != &s)
  {
    *d_type = *s.d_type;
  }
  return *this;
}

bool Sort::operator==(const Sort& s) const { return *d_type == *s.d_type; }

bool Sort::operator!=(const Sort& s) const { return *d_type != *s.d_type; }

bool Sort::isBoolean() const { return d_type->isBoolean(); }

bool Sort::isInteger() const { return d_type->isInteger(); }

bool Sort::isReal() const { return d_type->isReal(); }

bool Sort::isString() const { return d_type->isString(); }

bool Sort::isRegExp() const { return d_type->isRegExp(); }

bool Sort::isRoundingMode() const { return d_type->isRoundingMode(); }

bool Sort::isBitVector() const { return d_type->isBitVector(); }

bool Sort::isFloatingPoint() const { return d_type->isFloatingPoint(); }

bool Sort::isDatatype() const { return d_type->isDatatype(); }

bool Sort::isParametricDatatype() const
{
  if (!d_type->isDatatype()) return false;
  DatatypeType* type = static_cast<DatatypeType*>(d_type.get());
  return type->isParametric();
}

bool Sort::isFunction() const { return d_type->isFunction(); }

bool Sort::isPredicate() const { return d_type->isPredicate(); }

bool Sort::isTuple() const { return d_type->isTuple(); }

bool Sort::isRecord() const { return d_type->isRecord(); }

bool Sort::isArray() const { return d_type->isArray(); }

bool Sort::isSet() const { return d_type->isSet(); }

bool Sort::isUninterpretedSort() const { return d_type->isSort(); }

bool Sort::isSortConstructor() const { return d_type->isSortConstructor(); }

bool Sort::isFirstClass() const { return d_type->isFirstClass(); }

bool Sort::isFunctionLike() const { return d_type->isFunctionLike(); }

Datatype Sort::getDatatype() const
{
  CVC4_API_CHECK(isDatatype()) << "Expected datatype sort.";
  DatatypeType* type = static_cast<DatatypeType*>(d_type.get());
  return type->getDatatype();
}

Sort Sort::instantiate(const std::vector<Sort>& params) const
{
  CVC4_API_CHECK(isParametricDatatype() || isSortConstructor())
      << "Expected parametric datatype or sort constructor sort.";
  std::vector<Type> tparams;
  for (const Sort& s : params)
  {
    tparams.push_back(*s.d_type.get());
  }
  if (d_type->isDatatype())
  {
    DatatypeType* type = static_cast<DatatypeType*>(d_type.get());
    return type->instantiate(tparams);
  }
  Assert(d_type->isSortConstructor());
  return static_cast<SortConstructorType*>(d_type.get())->instantiate(tparams);
}

std::string Sort::toString() const { return d_type->toString(); }

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::Type Sort::getType(void) const { return *d_type; }

/* Function sort ------------------------------------------------------- */

size_t Sort::getFunctionArity() const
{
  CVC4_API_CHECK(isFunction()) << "Not a function sort.";
  return static_cast<FunctionType*>(d_type.get())->getArity();
}

std::vector<Sort> Sort::getFunctionDomainSorts() const
{
  CVC4_API_CHECK(isFunction()) << "Not a function sort.";
  std::vector<CVC4::Type> types =
      static_cast<FunctionType*>(d_type.get())->getArgTypes();
  return typeVectorToSorts(types);
}

Sort Sort::getFunctionCodomainSort() const
{
  CVC4_API_CHECK(isFunction()) << "Not a function sort.";
  return static_cast<FunctionType*>(d_type.get())->getRangeType();
}

/* Array sort ---------------------------------------------------------- */

Sort Sort::getArrayIndexSort() const
{
  CVC4_API_CHECK(isArray()) << "Not an array sort.";
  return static_cast<ArrayType*>(d_type.get())->getIndexType();
}

Sort Sort::getArrayElementSort() const
{
  CVC4_API_CHECK(isArray()) << "Not an array sort.";
  return static_cast<ArrayType*>(d_type.get())->getConstituentType();
}

/* Set sort ------------------------------------------------------------ */

Sort Sort::getSetElementSort() const
{
  CVC4_API_CHECK(isSet()) << "Not a set sort.";
  return static_cast<SetType*>(d_type.get())->getElementType();
}

/* Uninterpreted sort -------------------------------------------------- */

std::string Sort::getUninterpretedSortName() const
{
  CVC4_API_CHECK(isUninterpretedSort()) << "Not an uninterpreted sort.";
  return static_cast<SortType*>(d_type.get())->getName();
}

bool Sort::isUninterpretedSortParameterized() const
{
  CVC4_API_CHECK(isUninterpretedSort()) << "Not an uninterpreted sort.";
  return static_cast<SortType*>(d_type.get())->isParameterized();
}

std::vector<Sort> Sort::getUninterpretedSortParamSorts() const
{
  CVC4_API_CHECK(isUninterpretedSort()) << "Not an uninterpreted sort.";
  std::vector<CVC4::Type> types =
      static_cast<SortType*>(d_type.get())->getParamTypes();
  return typeVectorToSorts(types);
}

/* Sort constructor sort ----------------------------------------------- */

std::string Sort::getSortConstructorName() const
{
  CVC4_API_CHECK(isSortConstructor()) << "Not a sort constructor sort.";
  return static_cast<SortConstructorType*>(d_type.get())->getName();
}

size_t Sort::getSortConstructorArity() const
{
  CVC4_API_CHECK(isSortConstructor()) << "Not a sort constructor sort.";
  return static_cast<SortConstructorType*>(d_type.get())->getArity();
}

/* Bit-vector sort ----------------------------------------------------- */

uint32_t Sort::getBVSize() const
{
  CVC4_API_CHECK(isBitVector()) << "Not a bit-vector sort.";
  return static_cast<BitVectorType*>(d_type.get())->getSize();
}

/* Floating-point sort ------------------------------------------------- */

uint32_t Sort::getFPExponentSize() const
{
  CVC4_API_CHECK(isFloatingPoint()) << "Not a floating-point sort.";
  return static_cast<FloatingPointType*>(d_type.get())->getExponentSize();
}

uint32_t Sort::getFPSignificandSize() const
{
  CVC4_API_CHECK(isFloatingPoint()) << "Not a floating-point sort.";
  return static_cast<FloatingPointType*>(d_type.get())->getSignificandSize();
}

/* Datatype sort ------------------------------------------------------- */

std::vector<Sort> Sort::getDatatypeParamSorts() const
{
  CVC4_API_CHECK(isParametricDatatype()) << "Not a parametric datatype sort.";
  std::vector<CVC4::Type> types =
      static_cast<DatatypeType*>(d_type.get())->getParamTypes();
  return typeVectorToSorts(types);
}

size_t Sort::getDatatypeArity() const
{
  CVC4_API_CHECK(isDatatype()) << "Not a datatype sort.";
  return static_cast<DatatypeType*>(d_type.get())->getArity();
}

/* Tuple sort ---------------------------------------------------------- */

size_t Sort::getTupleLength() const
{
  CVC4_API_CHECK(isTuple()) << "Not a tuple sort.";
  return static_cast<DatatypeType*>(d_type.get())->getTupleLength();
}

std::vector<Sort> Sort::getTupleSorts() const
{
  CVC4_API_CHECK(isTuple()) << "Not a tuple sort.";
  std::vector<CVC4::Type> types =
      static_cast<DatatypeType*>(d_type.get())->getTupleTypes();
  return typeVectorToSorts(types);
}

/* --------------------------------------------------------------------- */

std::vector<Sort> Sort::typeVectorToSorts(
    const std::vector<CVC4::Type>& types) const
{
  std::vector<Sort> res;
  for (const CVC4::Type& t : types)
  {
    res.push_back(Sort(t));
  }
  return res;
}

/* --------------------------------------------------------------------- */

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
  if (this != &t)
  {
    *d_expr = *t.d_expr;
  }
  return *this;
}

bool Term::operator==(const Term& t) const { return *d_expr == *t.d_expr; }

bool Term::operator!=(const Term& t) const { return *d_expr != *t.d_expr; }

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

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::Expr Term::getExpr(void) const { return *d_expr; }

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
  if (this != &t)
  {
    *d_expr = *t.d_expr;
  }
  return *this;
}

bool OpTerm::operator==(const OpTerm& t) const { return *d_expr == *t.d_expr; }

bool OpTerm::operator!=(const OpTerm& t) const { return *d_expr != *t.d_expr; }

Kind OpTerm::getKind() const { return intToExtKind(d_expr->getKind()); }

Sort OpTerm::getSort() const { return Sort(d_expr->getType()); }

bool OpTerm::isNull() const { return d_expr->isNull(); }

std::string OpTerm::toString() const { return d_expr->toString(); }

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::Expr OpTerm::getExpr(void) const { return *d_expr; }

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

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::DatatypeConstructor DatatypeConstructorDecl::getDatatypeConstructor(
    void) const
{
  return *d_ctor;
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

size_t DatatypeDecl::getNumConstructors() const
{
  return d_dtype->getNumConstructors();
}

bool DatatypeDecl::isParametric() const { return d_dtype->isParametric(); }

std::string DatatypeDecl::toString() const
{
  std::stringstream ss;
  ss << *d_dtype;
  return ss.str();
}

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::Datatype DatatypeDecl::getDatatype(void) const { return *d_dtype; }

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

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::DatatypeConstructorArg DatatypeSelector::getDatatypeConstructorArg(
    void) const
{
  return *d_stor;
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

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::DatatypeConstructor DatatypeConstructor::getDatatypeConstructor(
    void) const
{
  return *d_ctor;
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

size_t Datatype::getNumConstructors() const
{
  return d_dtype->getNumConstructors();
}

bool Datatype::isParametric() const { return d_dtype->isParametric(); }

Datatype::const_iterator Datatype::begin() const
{
  return Datatype::const_iterator(*d_dtype, true);
}

Datatype::const_iterator Datatype::end() const
{
  return Datatype::const_iterator(*d_dtype, false);
}

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::Datatype Datatype::getDatatype(void) const { return *d_dtype; }

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

Solver::Solver(Options* opts)
{
  Options* o = opts == nullptr ? new Options() : opts;
  d_exprMgr.reset(new ExprManager(*o));
  d_smtEngine.reset(new SmtEngine(d_exprMgr.get()));
  d_rng.reset(new Random((*o)[options::seed]));
  if (opts == nullptr) delete o;
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
  return d_exprMgr->mkArrayType(*indexSort.d_type, *elemSort.d_type);
}

Sort Solver::mkBitVectorSort(uint32_t size) const
{
  CVC4_API_ARG_CHECK_EXPECTED(size > 0, size) << "size > 0";
  return d_exprMgr->mkBitVectorType(size);
}

Sort Solver::mkFloatingPointSort(uint32_t exp, uint32_t sig) const
{
  CVC4_API_ARG_CHECK_EXPECTED(exp > 0, exp) << "exponent size > 0";
  CVC4_API_ARG_CHECK_EXPECTED(sig > 0, sig) << "significand size > 0";
  return d_exprMgr->mkFloatingPointType(exp, sig);
}

Sort Solver::mkDatatypeSort(DatatypeDecl dtypedecl) const
{
  CVC4_API_ARG_CHECK_EXPECTED(dtypedecl.getNumConstructors() > 0, dtypedecl)
      << "a datatype declaration with at least one constructor";
  return d_exprMgr->mkDatatypeType(*dtypedecl.d_dtype);
}

Sort Solver::mkFunctionSort(Sort domain, Sort codomain) const
{
  CVC4_API_ARG_CHECK_EXPECTED(domain.isFirstClass(), domain)
      << "first-class sort as domain sort for function sort";
  CVC4_API_ARG_CHECK_EXPECTED(codomain.isFirstClass(), codomain)
      << "first-class sort as codomain sort for function sort";
  Assert(!codomain.isFunction()); /* A function sort is not first-class. */
  return d_exprMgr->mkFunctionType(*domain.d_type, *codomain.d_type);
}

Sort Solver::mkFunctionSort(const std::vector<Sort>& sorts, Sort codomain) const
{
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(sorts.size() >= 1, sorts)
      << "at least one parameter sort for function sort";
  for (size_t i = 0, size = sorts.size(); i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        sorts[i].isFirstClass(), "parameter sort", sorts[i], i)
        << "first-class sort as parameter sort for function sort";
  }
  CVC4_API_ARG_CHECK_EXPECTED(codomain.isFirstClass(), codomain)
      << "first-class sort as codomain sort for function sort";
  Assert(!codomain.isFunction()); /* A function sort is not first-class. */
  std::vector<Type> argTypes = sortVectorToTypes(sorts);
  return d_exprMgr->mkFunctionType(argTypes, *codomain.d_type);
}

Sort Solver::mkParamSort(const std::string& symbol) const
{
  return d_exprMgr->mkSort(symbol, ExprManager::SORT_FLAG_PLACEHOLDER);
}

Sort Solver::mkPredicateSort(const std::vector<Sort>& sorts) const
{
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(sorts.size() >= 1, sorts)
      << "at least one parameter sort for predicate sort";
  for (size_t i = 0, size = sorts.size(); i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        sorts[i].isFirstClass(), "parameter sort", sorts[i], i)
        << "first-class sort as parameter sort for predicate sort";
  }
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

Sort Solver::mkSortConstructorSort(const std::string& symbol,
                                   size_t arity) const
{
  return d_exprMgr->mkSortConstructor(symbol, arity);
}

Sort Solver::mkTupleSort(const std::vector<Sort>& sorts) const
{
  for (size_t i = 0, size = sorts.size(); i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !sorts[i].isFunctionLike(), "parameter sort", sorts[i], i)
        << "non-function-like sort as parameter sort for tuple sort";
  }
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
  return d_exprMgr->mkConst(String(std::string(1, c)));
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
  return d_exprMgr->mkConst(s_rmodes.at(rm));
}

Term Solver::mkConst(Kind kind, Sort arg) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == EMPTYSET, kind) << "EMPTY_SET";
  return d_exprMgr->mkConst(CVC4::EmptySet(*arg.d_type));
}

Term Solver::mkConst(Kind kind, Sort arg1, int32_t arg2) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == UNINTERPRETED_CONSTANT, kind)
      << "UNINTERPRETED_CONSTANT";
  return d_exprMgr->mkConst(CVC4::UninterpretedConstant(*arg1.d_type, arg2));
}

Term Solver::mkConst(Kind kind, bool arg) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == CONST_BOOLEAN, kind) << "CONST_BOOLEAN";
  return d_exprMgr->mkConst<bool>(arg);
}

Term Solver::mkConst(Kind kind, const char* arg) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == CONST_STRING, kind) << "CONST_STRING";
  return d_exprMgr->mkConst(CVC4::String(arg));
}

Term Solver::mkConst(Kind kind, const std::string& arg) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == CONST_STRING, kind) << "CONST_STRING";
  return d_exprMgr->mkConst(CVC4::String(arg));
}

Term Solver::mkConst(Kind kind, const char* arg1, uint32_t arg2) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == ABSTRACT_VALUE || kind == CONST_RATIONAL
                                   || kind == CONST_BITVECTOR,
                               kind)
      << "ABSTRACT_VALUE or CONST_RATIONAL or CONST_BITVECTOR";
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
  CVC4_API_KIND_CHECK_EXPECTED(kind == ABSTRACT_VALUE || kind == CONST_RATIONAL
                                   || kind == CONST_BITVECTOR,
                               kind)
      << "ABSTRACT_VALUE or CONST_RATIONAL or CONST_BITVECTOR";
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
  CVC4_API_KIND_CHECK_EXPECTED(kind == ABSTRACT_VALUE || kind == CONST_RATIONAL
                                   || kind == CONST_BITVECTOR,
                               kind)
      << "ABSTRACT_VALUE or CONST_RATIONAL or CONST_BITVECTOR";
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
  CVC4_API_KIND_CHECK_EXPECTED(kind == ABSTRACT_VALUE || kind == CONST_RATIONAL,
                               kind)
      << "ABSTRACT_VALUE or CONST_RATIONAL";
  if (kind == ABSTRACT_VALUE)
  {
    return d_exprMgr->mkConst(CVC4::AbstractValue(Integer(arg)));
  }
  return d_exprMgr->mkConst(CVC4::Rational(arg));
}

Term Solver::mkConst(Kind kind, int64_t arg) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == ABSTRACT_VALUE || kind == CONST_RATIONAL,
                               kind)
      << "ABSTRACT_VALUE or CONST_RATIONAL";
  if (kind == ABSTRACT_VALUE)
  {
    return d_exprMgr->mkConst(CVC4::AbstractValue(Integer(arg)));
  }
  return d_exprMgr->mkConst(CVC4::Rational(arg));
}

Term Solver::mkConst(Kind kind, uint64_t arg) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == ABSTRACT_VALUE || kind == CONST_RATIONAL,
                               kind)
      << "ABSTRACT_VALUE or CONST_RATIONAL";
  if (kind == ABSTRACT_VALUE)
  {
    return d_exprMgr->mkConst(CVC4::AbstractValue(Integer(arg)));
  }
  return d_exprMgr->mkConst(CVC4::Rational(arg));
}

Term Solver::mkConst(Kind kind, uint32_t arg1, uint32_t arg2) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == CONST_RATIONAL, kind)
      << "CONST_RATIONAL";
  return d_exprMgr->mkConst(CVC4::Rational(arg1, arg2));
}

Term Solver::mkConst(Kind kind, int32_t arg1, int32_t arg2) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == CONST_RATIONAL, kind)
      << "CONST_RATIONAL";
  return d_exprMgr->mkConst(CVC4::Rational(arg1, arg2));
}

Term Solver::mkConst(Kind kind, int64_t arg1, int64_t arg2) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == CONST_RATIONAL, kind)
      << "CONST_RATIONAL";
  return d_exprMgr->mkConst(CVC4::Rational(arg1, arg2));
}

Term Solver::mkConst(Kind kind, uint64_t arg1, uint64_t arg2) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == CONST_RATIONAL, kind)
      << "CONST_RATIONAL";
  return d_exprMgr->mkConst(CVC4::Rational(arg1, arg2));
}

Term Solver::mkConst(Kind kind, uint32_t arg1, uint64_t arg2) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == CONST_BITVECTOR, kind)
      << "CONST_BITVECTOR";
  return d_exprMgr->mkConst(CVC4::BitVector(arg1, arg2));
}

Term Solver::mkConst(Kind kind, uint32_t arg1, uint32_t arg2, Term arg3) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == CONST_FLOATINGPOINT, kind)
      << "CONST_FLOATINGPOINT";
  CVC4_API_ARG_CHECK_EXPECTED(
      arg3.getSort().isBitVector() && arg3.d_expr->isConst(), arg3)
      << "bit-vector constant";
  return d_exprMgr->mkConst(
      CVC4::FloatingPoint(arg1, arg2, arg3.d_expr->getConst<BitVector>()));
}

/* Create variables                                                           */
/* -------------------------------------------------------------------------- */

Term Solver::mkVar(const std::string& symbol, Sort sort) const
{
  return d_exprMgr->mkVar(symbol, *sort.d_type);
}

Term Solver::mkVar(Sort sort) const { return d_exprMgr->mkVar(*sort.d_type); }

Term Solver::mkBoundVar(const std::string& symbol, Sort sort) const
{
  return d_exprMgr->mkBoundVar(symbol, *sort.d_type);
}

Term Solver::mkBoundVar(Sort sort) const
{
  return d_exprMgr->mkBoundVar(*sort.d_type);
}

/* Create terms                                                               */
/* -------------------------------------------------------------------------- */

void Solver::checkMkTerm(Kind kind, uint32_t nchildren) const
{
  CVC4_API_KIND_CHECK(kind);
  Assert(isDefinedIntKind(extToIntKind(kind)));
  const CVC4::kind::MetaKind mk = kind::metaKindOf(extToIntKind(kind));
  CVC4_API_KIND_CHECK_EXPECTED(
      mk == kind::metakind::PARAMETERIZED || mk == kind::metakind::OPERATOR,
      kind)
      << "Only operator-style terms are created with mkTerm(), "
         "to create variables and constants see mkVar(), mkBoundVar(), "
         "and mkConst().";
  if (nchildren)
  {
    const uint32_t n =
        nchildren - (mk == CVC4::kind::metakind::PARAMETERIZED ? 1 : 0);
    CVC4_API_KIND_CHECK_EXPECTED(n >= minArity(kind) && n <= maxArity(kind),
                                 kind)
        << "Terms with kind " << kindToString(kind) << " must have at least "
        << minArity(kind) << " children and at most " << maxArity(kind)
        << " children (the one under construction has " << n << ")";
  }
}

void Solver::checkMkOpTerm(OpTerm opTerm, uint32_t nchildren) const
{
  const Kind kind = opTerm.getKind();
  Assert(isDefinedIntKind(extToIntKind(kind)));
  const CVC4::Kind int_kind = extToIntKind(kind);
  const CVC4::Kind int_op_kind =
      NodeManager::operatorToKind(opTerm.d_expr->getNode());
  CVC4_API_ARG_CHECK_EXPECTED(int_kind == kind::BUILTIN
                                  || CVC4::kind::metaKindOf(int_op_kind)
                                         == kind::metakind::PARAMETERIZED,
                              opTerm)
      << "This term constructor is for parameterized kinds only";
  if (nchildren)
  {
    uint32_t min_arity = ExprManager::minArity(int_op_kind);
    uint32_t max_arity = ExprManager::maxArity(int_op_kind);
    CVC4_API_KIND_CHECK_EXPECTED(
        nchildren >= min_arity && nchildren <= max_arity, kind)
        << "Terms with kind " << kindToString(kind) << " must have at least "
        << min_arity << " children and at most " << max_arity
        << " children (the one under construction has " << nchildren << ")";
  }
}

Term Solver::mkTerm(Kind kind) const
{
  CVC4_API_KIND_CHECK_EXPECTED(
      kind == PI || kind == REGEXP_EMPTY || kind == REGEXP_SIGMA, kind)
      << "PI or REGEXP_EMPTY or REGEXP_SIGMA";
  if (kind == REGEXP_EMPTY || kind == REGEXP_SIGMA)
  {
    CVC4::Kind k = extToIntKind(kind);
    Assert(isDefinedIntKind(k));
    return d_exprMgr->mkExpr(k, std::vector<Expr>());
  }
  Assert(kind == PI);
  return d_exprMgr->mkNullaryOperator(d_exprMgr->realType(), CVC4::kind::PI);
}

Term Solver::mkTerm(Kind kind, Sort sort) const
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == SEP_NIL || kind == UNIVERSE_SET, kind)
      << "SEP_NIL or UNIVERSE_SET";
  return d_exprMgr->mkNullaryOperator(*sort.d_type, extToIntKind(kind));
}

Term Solver::mkTerm(Kind kind, Term child) const
{
  checkMkTerm(kind, 1);
  return d_exprMgr->mkExpr(extToIntKind(kind), *child.d_expr);
}

Term Solver::mkTerm(Kind kind, Term child1, Term child2) const
{
  checkMkTerm(kind, 2);
  return d_exprMgr->mkExpr(extToIntKind(kind), *child1.d_expr, *child2.d_expr);
}

Term Solver::mkTerm(Kind kind, Term child1, Term child2, Term child3) const
{
  checkMkTerm(kind, 3);
  std::vector<Expr> echildren{*child1.d_expr, *child2.d_expr, *child3.d_expr};
  CVC4::Kind k = extToIntKind(kind);
  Assert(isDefinedIntKind(k));
  return kind::isAssociative(k) ? d_exprMgr->mkAssociative(k, echildren)
                                : d_exprMgr->mkExpr(k, echildren);
}

Term Solver::mkTerm(Kind kind, const std::vector<Term>& children) const
{
  checkMkTerm(kind, children.size());
  std::vector<Expr> echildren = termVectorToExprs(children);
  CVC4::Kind k = extToIntKind(kind);
  Assert(isDefinedIntKind(k));
  return kind::isAssociative(k) ? d_exprMgr->mkAssociative(k, echildren)
                                : d_exprMgr->mkExpr(k, echildren);
}

Term Solver::mkTerm(OpTerm opTerm) const
{
  checkMkOpTerm(opTerm, 0);
  return d_exprMgr->mkExpr(*opTerm.d_expr);
}

Term Solver::mkTerm(OpTerm opTerm, Term child) const
{
  checkMkOpTerm(opTerm, 1);
  return d_exprMgr->mkExpr(*opTerm.d_expr, *child.d_expr);
}

Term Solver::mkTerm(OpTerm opTerm, Term child1, Term child2) const
{
  checkMkOpTerm(opTerm, 2);
  return d_exprMgr->mkExpr(*opTerm.d_expr, *child1.d_expr, *child2.d_expr);
}

Term Solver::mkTerm(OpTerm opTerm, Term child1, Term child2, Term child3) const
{
  checkMkOpTerm(opTerm, 3);
  return d_exprMgr->mkExpr(
      *opTerm.d_expr, *child1.d_expr, *child2.d_expr, *child3.d_expr);
}

Term Solver::mkTerm(OpTerm opTerm, const std::vector<Term>& children) const
{
  checkMkOpTerm(opTerm, children.size());
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
  CVC4_API_KIND_CHECK_EXPECTED(kind == CHAIN_OP, kind) << "CHAIN_OP";
  return d_exprMgr->mkConst(CVC4::Chain(extToIntKind(k)));
}

OpTerm Solver::mkOpTerm(Kind kind, const std::string& arg)
{
  CVC4_API_KIND_CHECK_EXPECTED(kind == RECORD_UPDATE_OP, kind)
      << "RECORD_UPDATE_OP";
  return d_exprMgr->mkConst(CVC4::RecordUpdate(arg));
}

OpTerm Solver::mkOpTerm(Kind kind, uint32_t arg)
{
  CVC4_API_KIND_CHECK(kind);
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
      CVC4_API_KIND_CHECK_EXPECTED(false, kind)
          << "operator kind with uint32_t argument";
  }
  Assert(!res.isNull());
  return res;
}

OpTerm Solver::mkOpTerm(Kind kind, uint32_t arg1, uint32_t arg2)
{
  CVC4_API_KIND_CHECK(kind);
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
      CVC4_API_KIND_CHECK_EXPECTED(false, kind)
          << "operator kind with two uint32_t arguments";
  }
  Assert(!res.isNull());
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

/**
 *  ( declare-fun <symbol> () <sort> )
 */
Term Solver::declareFun(const std::string& symbol, Sort sort) const
{
  Type type = *sort.d_type;
  return d_exprMgr->mkVar(symbol, type);
}

/**
 *  ( declare-fun <symbol> ( <sort>* ) <sort> )
 */
Term Solver::declareFun(const std::string& symbol,
                        const std::vector<Sort>& sorts,
                        Sort sort) const
{
  for (size_t i = 0, size = sorts.size(); i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        sorts[i].isFirstClass(), "parameter sort", sorts[i], i)
        << "first-class sort as parameter sort for function sort";
  }
  CVC4_API_ARG_CHECK_EXPECTED(sort.isFirstClass(), sort)
      << "first-class sort as function codomain sort";
  Assert(!sort.isFunction()); /* A function sort is not first-class. */
  Type type = *sort.d_type;
  if (!sorts.empty())
  {
    std::vector<Type> types = sortVectorToTypes(sorts);
    type = d_exprMgr->mkFunctionType(types, type);
  }
  return d_exprMgr->mkVar(symbol, type);
}

/**
 *  ( declare-sort <symbol> <numeral> )
 */
Sort Solver::declareSort(const std::string& symbol, uint32_t arity) const
{
  if (arity == 0) return d_exprMgr->mkSort(symbol);
  return d_exprMgr->mkSortConstructor(symbol, arity);
}

/**
 *  ( define-fun <function_def> )
 */
Term Solver::defineFun(const std::string& symbol,
                       const std::vector<Term>& bound_vars,
                       Sort sort,
                       Term term) const
{
  // CHECK:
  // for bv in bound_vars:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(bv.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(expr.getExprManager())
  // CHECK: not recursive
  CVC4_API_ARG_CHECK_EXPECTED(sort.isFirstClass(), sort)
      << "first-class sort as codomain sort for function sort";
  // CHECK:
  // for v in bound_vars: is bound var
  std::vector<Type> domain_types;
  for (size_t i = 0, size = bound_vars.size(); i < size; ++i)
  {
    CVC4::Type t = bound_vars[i].d_expr->getType();
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        t.isFirstClass(), "sort of parameter", bound_vars[i], i)
        << "first-class sort of parameter of defined function";
    domain_types.push_back(t);
  }
  CVC4_API_CHECK(sort == term.getSort())
      << "Invalid sort of function body '" << term << "', expected '" << sort
      << "'";
  Type type = *sort.d_type;
  if (!domain_types.empty())
  {
    type = d_exprMgr->mkFunctionType(domain_types, type);
  }
  Expr fun = d_exprMgr->mkVar(symbol, type);
  std::vector<Expr> ebound_vars = termVectorToExprs(bound_vars);
  d_smtEngine->defineFunction(fun, ebound_vars, *term.d_expr);
  return fun;
}

Term Solver::defineFun(Term fun,
                       const std::vector<Term>& bound_vars,
                       Term term) const
{
  // CHECK:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(bv.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(expr.getExprManager())
  CVC4_API_ARG_CHECK_EXPECTED(fun.getSort().isFunction(), fun) << "function";
  std::vector<Sort> domain_sorts = fun.getSort().getFunctionDomainSorts();
  size_t size = bound_vars.size();
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(size == domain_sorts.size(), bound_vars)
      << "'" << domain_sorts.size() << "'";
  for (size_t i = 0; i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        domain_sorts[i] == bound_vars[i].getSort(),
        "sort of parameter",
        bound_vars[i],
        i)
        << "'" << domain_sorts[i] << "'";
  }
  Sort codomain = fun.getSort().getFunctionCodomainSort();
  CVC4_API_CHECK(codomain == term.getSort())
      << "Invalid sort of function body '" << term << "', expected '"
      << codomain << "'";

  // CHECK: not recursive
  // CHECK:
  // for v in bound_vars: is bound var
  std::vector<Expr> ebound_vars = termVectorToExprs(bound_vars);
  d_smtEngine->defineFunction(*fun.d_expr, ebound_vars, *term.d_expr);
  return fun;
}

/**
 *  ( define-fun-rec <function_def> )
 */
Term Solver::defineFunRec(const std::string& symbol,
                          const std::vector<Term>& bound_vars,
                          Sort sort,
                          Term term) const
{
  // CHECK:
  // for bv in bound_vars:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(bv.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(expr.getExprManager())
  CVC4_API_ARG_CHECK_EXPECTED(sort.isFirstClass(), sort)
      << "first-class sort as function codomain sort";
  Assert(!sort.isFunction()); /* A function sort is not first-class. */
  // CHECK:
  // for v in bound_vars: is bound var
  std::vector<Type> domain_types;
  for (size_t i = 0, size = bound_vars.size(); i < size; ++i)
  {
    CVC4::Type t = bound_vars[i].d_expr->getType();
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        t.isFirstClass(), "sort of parameter", bound_vars[i], i)
        << "first-class sort of parameter of defined function";
    domain_types.push_back(t);
  }
  CVC4_API_CHECK(sort == term.getSort())
      << "Invalid sort of function body '" << term << "', expected '" << sort
      << "'";
  Type type = *sort.d_type;
  if (!domain_types.empty())
  {
    type = d_exprMgr->mkFunctionType(domain_types, type);
  }
  Expr fun = d_exprMgr->mkVar(symbol, type);
  std::vector<Expr> ebound_vars = termVectorToExprs(bound_vars);
  d_smtEngine->defineFunctionRec(fun, ebound_vars, *term.d_expr);
  return fun;
}

Term Solver::defineFunRec(Term fun,
                          const std::vector<Term>& bound_vars,
                          Term term) const
{
  // CHECK:
  // for bv in bound_vars:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(bv.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(expr.getExprManager())
  CVC4_API_ARG_CHECK_EXPECTED(fun.getSort().isFunction(), fun) << "function";
  std::vector<Sort> domain_sorts = fun.getSort().getFunctionDomainSorts();
  size_t size = bound_vars.size();
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(size == domain_sorts.size(), bound_vars)
      << "'" << domain_sorts.size() << "'";
  for (size_t i = 0; i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        domain_sorts[i] == bound_vars[i].getSort(),
        "sort of parameter",
        bound_vars[i],
        i)
        << "'" << domain_sorts[i] << "'";
  }
  Sort codomain = fun.getSort().getFunctionCodomainSort();
  CVC4_API_CHECK(codomain == term.getSort())
      << "Invalid sort of function body '" << term << "', expected '"
      << codomain << "'";
  // CHECK:
  // for v in bound_vars: is bound var
  std::vector<Expr> ebound_vars = termVectorToExprs(bound_vars);
  d_smtEngine->defineFunctionRec(*fun.d_expr, ebound_vars, *term.d_expr);
  return fun;
}

/**
 *  ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
 */
void Solver::defineFunsRec(const std::vector<Term>& funs,
                           const std::vector<std::vector<Term>>& bound_vars,
                           const std::vector<Term>& terms) const
{
  // CHECK:
  // for f in funs:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(f.getExprManager())
  // for bv in bound_vars:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(bv.getExprManager())
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(expr.getExprManager())
  size_t funs_size = funs.size();
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(funs_size == bound_vars.size(), bound_vars)
      << "'" << funs_size << "'";
  for (size_t j = 0; j < funs_size; ++j)
  {
    const Term& fun = funs[j];
    const std::vector<Term>& bvars = bound_vars[j];
    const Term& term = terms[j];

    CVC4_API_ARG_CHECK_EXPECTED(fun.getSort().isFunction(), fun) << "function";
    std::vector<Sort> domain_sorts = fun.getSort().getFunctionDomainSorts();
    size_t size = bvars.size();
    CVC4_API_ARG_SIZE_CHECK_EXPECTED(size == domain_sorts.size(), bvars)
        << "'" << domain_sorts.size() << "'";
    for (size_t i = 0; i < size; ++i)
    {
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
          domain_sorts[i] == bvars[i].getSort(),
          "sort of parameter",
          bvars[i],
          i)
          << "'" << domain_sorts[i] << "' in parameter bound_vars[" << j << "]";
    }
    Sort codomain = fun.getSort().getFunctionCodomainSort();
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        codomain == term.getSort(), "sort of function body", term, j)
        << "'" << codomain << "'";
  }
  // CHECK:
  // for bv in bound_vars (for v in bv): is bound var
  std::vector<Expr> efuns = termVectorToExprs(funs);
  std::vector<std::vector<Expr>> ebound_vars;
  for (const auto& v : bound_vars)
  {
    ebound_vars.push_back(termVectorToExprs(v));
  }
  std::vector<Expr> exprs = termVectorToExprs(terms);
  d_smtEngine->defineFunctionsRec(efuns, ebound_vars, exprs);
}

/**
 *  ( echo <std::string> )
 */
void Solver::echo(std::ostream& out, const std::string& str) const
{
  out << str;
}

/**
 *  ( get-assertions )
 */
std::vector<Term> Solver::getAssertions(void) const
{
  std::vector<Expr> assertions = d_smtEngine->getAssertions();
  /* Can not use
   *   return std::vector<Term>(assertions.begin(), assertions.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const Expr& e : assertions)
  {
    res.push_back(Term(e));
  }
  return res;
}

/**
 *  ( get-assignment )
 */
std::vector<std::pair<Term, Term>> Solver::getAssignment(void) const
{
  // CHECK: produce-models set
  // CHECK: result sat
  std::vector<std::pair<Expr, Expr>> assignment = d_smtEngine->getAssignment();
  std::vector<std::pair<Term, Term>> res;
  for (const auto& p : assignment)
  {
    res.emplace_back(Term(p.first), Term(p.second));
  }
  return res;
}

/**
 *  ( get-info <info_flag> )
 */
std::string Solver::getInfo(const std::string& flag) const
{
  // CHECK: flag valid?
  return d_smtEngine->getInfo(flag).toString();
}

/**
 *  ( get-option <keyword> )
 */
std::string Solver::getOption(const std::string& option) const
{
  // CHECK: option exists?
  SExpr res = d_smtEngine->getOption(option);
  return res.toString();
}

/**
 *  ( get-unsat-assumptions )
 */
std::vector<Term> Solver::getUnsatAssumptions(void) const
{
  // CHECK: incremental?
  // CHECK: option produce-unsat-assumptions set?
  // CHECK: last check sat/valid result is unsat/invalid
  std::vector<Expr> uassumptions = d_smtEngine->getUnsatAssumptions();
  /* Can not use
   *   return std::vector<Term>(uassumptions.begin(), uassumptions.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const Expr& e : uassumptions)
  {
    res.push_back(Term(e));
  }
  return res;
}

/**
 *  ( get-unsat-core )
 */
std::vector<Term> Solver::getUnsatCore(void) const
{
  // CHECK: result unsat?
  UnsatCore core = d_smtEngine->getUnsatCore();
  /* Can not use
   *   return std::vector<Term>(core.begin(), core.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const Expr& e : core)
  {
    res.push_back(Term(e));
  }
  return res;
}

/**
 *  ( get-value ( <term> ) )
 */
Term Solver::getValue(Term term) const
{
  // CHECK:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(expr.getExprManager())
  return d_smtEngine->getValue(*term.d_expr);
}

/**
 *  ( get-value ( <term>+ ) )
 */
std::vector<Term> Solver::getValue(const std::vector<Term>& terms) const
{
  // CHECK:
  // for e in exprs:
  // NodeManager::fromExprManager(d_exprMgr)
  // == NodeManager::fromExprManager(e.getExprManager())
  std::vector<Term> res;
  for (const Term& t : terms)
  {
    /* Can not use emplace_back here since constructor is private. */
    res.push_back(Term(d_smtEngine->getValue(*t.d_expr)));
  }
  return res;
}

/**
 *  ( pop <numeral> )
 */
void Solver::pop(uint32_t nscopes) const
{
  // CHECK: incremental enabled?
  // CHECK: nscopes <= d_smtEngine->d_userLevels.size()
  for (uint32_t n = 0; n < nscopes; ++n)
  {
    d_smtEngine->pop();
  }
}

void Solver::printModel(std::ostream& out) const
{
  // CHECK: produce-models?
  out << *d_smtEngine->getModel();
}

/**
 *  ( push <numeral> )
 */
void Solver::push(uint32_t nscopes) const
{
  // CHECK: incremental enabled?
  for (uint32_t n = 0; n < nscopes; ++n)
  {
    d_smtEngine->push();
  }
}

/**
 *  ( reset )
 */
void Solver::reset(void) const { d_smtEngine->reset(); }

/**
 *  ( reset-assertions )
 */
void Solver::resetAssertions(void) const { d_smtEngine->resetAssertions(); }

/**
 *  ( set-info <attribute> )
 */
void Solver::setInfo(const std::string& keyword, const std::string& value) const
{
  // CHECK:
  // if keyword == "cvc4-logic": value must be string
  // if keyword == "status": must be sat, unsat or unknown
  // if keyword == "smt-lib-version": supported?
  d_smtEngine->setInfo(keyword, value);
}

/**
 *  ( set-logic <symbol> )
 */
void Solver::setLogic(const std::string& logic) const
{
  // CHECK: !d_smtEngine->d_fullyInited
  d_smtEngine->setLogic(logic);
}

/**
 *  ( set-option <option> )
 */
void Solver::setOption(const std::string& option,
                       const std::string& value) const
{
  // CHECK: option exists?
  // CHECK: !d_smtEngine->d_fullInited, else option can't be set
  d_smtEngine->setOption(option, value);
}

/**
 * !!! This is only temporarily available until the parser is fully migrated to
 * the new API. !!!
 */
ExprManager* Solver::getExprManager(void) const { return d_exprMgr.get(); }

/**
 * !!! This is only temporarily available until the parser is fully migrated to
 * the new API. !!!
 */
SmtEngine* Solver::getSmtEngine(void) const { return d_smtEngine.get(); }

}  // namespace api
}  // namespace CVC4

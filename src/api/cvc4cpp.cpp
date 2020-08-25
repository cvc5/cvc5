/*********************                                                        */
/*! \file cvc4cpp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Makai Mann, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The CVC4 C++ API.
 **
 ** The CVC4 C++ API.
 **
 ** A brief note on how to guard API functions:
 **
 ** In general, we think of API guards as a fence -- they are supposed to make
 ** sure that no invalid arguments get passed into internal realms of CVC4.
 ** Thus we always want to catch such cases on the API level (and can then
 ** assert internally that no invalid argument is passed in).
 **
 ** The only special case is when we use 3rd party back-ends we have no control
 ** over, and which throw (invalid_argument) exceptions anyways. In this case,
 ** we do not replicate argument checks but delegate them to the back-end,
 ** catch thrown exceptions, and raise a CVC4ApiException.
 **
 ** Our Integer implementation, e.g., is such a special case since we support
 ** two different back end implementations (GMP, CLN). Be aware that they do
 ** not fully agree on what is (in)valid input, which requires extra checks for
 ** consistent behavior (see Solver::mkRealFromStrHelper for an example).
 **/

#include "api/cvc4cpp.h"

#include <cstring>
#include <sstream>

#include "base/check.h"
#include "base/configuration.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/sequence.h"
#include "expr/type.h"
#include "options/main_options.h"
#include "options/options.h"
#include "options/smt_options.h"
#include "smt/model.h"
#include "smt/smt_engine.h"
#include "smt/smt_mode.h"
#include "theory/logic_info.h"
#include "theory/theory_model.h"
#include "util/random.h"
#include "util/result.h"
#include "util/utility.h"

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
    {EQUAL, CVC4::Kind::EQUAL},
    {DISTINCT, CVC4::Kind::DISTINCT},
    {CONSTANT, CVC4::Kind::VARIABLE},
    {VARIABLE, CVC4::Kind::BOUND_VARIABLE},
    {LAMBDA, CVC4::Kind::LAMBDA},
    {WITNESS, CVC4::Kind::WITNESS},
    /* Boolean ------------------------------------------------------------- */
    {CONST_BOOLEAN, CVC4::Kind::CONST_BOOLEAN},
    {NOT, CVC4::Kind::NOT},
    {AND, CVC4::Kind::AND},
    {IMPLIES, CVC4::Kind::IMPLIES},
    {OR, CVC4::Kind::OR},
    {XOR, CVC4::Kind::XOR},
    {ITE, CVC4::Kind::ITE},
    {MATCH, CVC4::Kind::MATCH},
    {MATCH_CASE, CVC4::Kind::MATCH_CASE},
    {MATCH_BIND_CASE, CVC4::Kind::MATCH_BIND_CASE},
    /* UF ------------------------------------------------------------------ */
    {APPLY_UF, CVC4::Kind::APPLY_UF},
    {CARDINALITY_CONSTRAINT, CVC4::Kind::CARDINALITY_CONSTRAINT},
    {CARDINALITY_VALUE, CVC4::Kind::CARDINALITY_VALUE},
    {HO_APPLY, CVC4::Kind::HO_APPLY},
    /* Arithmetic ---------------------------------------------------------- */
    {PLUS, CVC4::Kind::PLUS},
    {MULT, CVC4::Kind::MULT},
    {IAND, CVC4::Kind::IAND},
    {MINUS, CVC4::Kind::MINUS},
    {UMINUS, CVC4::Kind::UMINUS},
    {DIVISION, CVC4::Kind::DIVISION},
    {INTS_DIVISION, CVC4::Kind::INTS_DIVISION},
    {INTS_MODULUS, CVC4::Kind::INTS_MODULUS},
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
    {BITVECTOR_EXTRACT, CVC4::Kind::BITVECTOR_EXTRACT},
    {BITVECTOR_REPEAT, CVC4::Kind::BITVECTOR_REPEAT},
    {BITVECTOR_ZERO_EXTEND, CVC4::Kind::BITVECTOR_ZERO_EXTEND},
    {BITVECTOR_SIGN_EXTEND, CVC4::Kind::BITVECTOR_SIGN_EXTEND},
    {BITVECTOR_ROTATE_LEFT, CVC4::Kind::BITVECTOR_ROTATE_LEFT},
    {BITVECTOR_ROTATE_RIGHT, CVC4::Kind::BITVECTOR_ROTATE_RIGHT},
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
    {FLOATINGPOINT_TO_FP_FLOATINGPOINT,
     CVC4::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT},
    {FLOATINGPOINT_TO_FP_REAL, CVC4::Kind::FLOATINGPOINT_TO_FP_REAL},
    {FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
     CVC4::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR},
    {FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
     CVC4::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR},
    {FLOATINGPOINT_TO_FP_GENERIC, CVC4::Kind::FLOATINGPOINT_TO_FP_GENERIC},
    {FLOATINGPOINT_TO_UBV, CVC4::Kind::FLOATINGPOINT_TO_UBV},
    {FLOATINGPOINT_TO_SBV, CVC4::Kind::FLOATINGPOINT_TO_SBV},
    {FLOATINGPOINT_TO_REAL, CVC4::Kind::FLOATINGPOINT_TO_REAL},
    /* Arrays -------------------------------------------------------------- */
    {SELECT, CVC4::Kind::SELECT},
    {STORE, CVC4::Kind::STORE},
    {CONST_ARRAY, CVC4::Kind::STORE_ALL},
    {EQ_RANGE, CVC4::Kind::EQ_RANGE},
    /* Datatypes ----------------------------------------------------------- */
    {APPLY_SELECTOR, CVC4::Kind::APPLY_SELECTOR},
    {APPLY_CONSTRUCTOR, CVC4::Kind::APPLY_CONSTRUCTOR},
    {APPLY_TESTER, CVC4::Kind::APPLY_TESTER},
    {TUPLE_UPDATE, CVC4::Kind::TUPLE_UPDATE},
    {RECORD_UPDATE, CVC4::Kind::RECORD_UPDATE},
    {DT_SIZE, CVC4::Kind::DT_SIZE},
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
    {COMPREHENSION, CVC4::Kind::COMPREHENSION},
    {CHOOSE, CVC4::Kind::CHOOSE},
    /* Strings ------------------------------------------------------------- */
    {STRING_CONCAT, CVC4::Kind::STRING_CONCAT},
    {STRING_IN_REGEXP, CVC4::Kind::STRING_IN_REGEXP},
    {STRING_LENGTH, CVC4::Kind::STRING_LENGTH},
    {STRING_SUBSTR, CVC4::Kind::STRING_SUBSTR},
    {STRING_UPDATE, CVC4::Kind::STRING_UPDATE},
    {STRING_CHARAT, CVC4::Kind::STRING_CHARAT},
    {STRING_CONTAINS, CVC4::Kind::STRING_STRCTN},
    {STRING_INDEXOF, CVC4::Kind::STRING_STRIDOF},
    {STRING_REPLACE, CVC4::Kind::STRING_STRREPL},
    {STRING_REPLACE_ALL, CVC4::Kind::STRING_STRREPLALL},
    {STRING_REPLACE_RE, CVC4::Kind::STRING_REPLACE_RE},
    {STRING_REPLACE_RE_ALL, CVC4::Kind::STRING_REPLACE_RE_ALL},
    {STRING_TOLOWER, CVC4::Kind::STRING_TOLOWER},
    {STRING_TOUPPER, CVC4::Kind::STRING_TOUPPER},
    {STRING_REV, CVC4::Kind::STRING_REV},
    {STRING_FROM_CODE, CVC4::Kind::STRING_FROM_CODE},
    {STRING_TO_CODE, CVC4::Kind::STRING_TO_CODE},
    {STRING_LT, CVC4::Kind::STRING_LT},
    {STRING_LEQ, CVC4::Kind::STRING_LEQ},
    {STRING_PREFIX, CVC4::Kind::STRING_PREFIX},
    {STRING_SUFFIX, CVC4::Kind::STRING_SUFFIX},
    {STRING_IS_DIGIT, CVC4::Kind::STRING_IS_DIGIT},
    {STRING_FROM_INT, CVC4::Kind::STRING_ITOS},
    {STRING_TO_INT, CVC4::Kind::STRING_STOI},
    {CONST_STRING, CVC4::Kind::CONST_STRING},
    {STRING_TO_REGEXP, CVC4::Kind::STRING_TO_REGEXP},
    {REGEXP_CONCAT, CVC4::Kind::REGEXP_CONCAT},
    {REGEXP_UNION, CVC4::Kind::REGEXP_UNION},
    {REGEXP_INTER, CVC4::Kind::REGEXP_INTER},
    {REGEXP_DIFF, CVC4::Kind::REGEXP_DIFF},
    {REGEXP_STAR, CVC4::Kind::REGEXP_STAR},
    {REGEXP_PLUS, CVC4::Kind::REGEXP_PLUS},
    {REGEXP_OPT, CVC4::Kind::REGEXP_OPT},
    {REGEXP_RANGE, CVC4::Kind::REGEXP_RANGE},
    {REGEXP_REPEAT, CVC4::Kind::REGEXP_REPEAT},
    {REGEXP_LOOP, CVC4::Kind::REGEXP_LOOP},
    {REGEXP_EMPTY, CVC4::Kind::REGEXP_EMPTY},
    {REGEXP_SIGMA, CVC4::Kind::REGEXP_SIGMA},
    {REGEXP_COMPLEMENT, CVC4::Kind::REGEXP_COMPLEMENT},
    // maps to the same kind as the string versions
    {SEQ_CONCAT, CVC4::Kind::STRING_CONCAT},
    {SEQ_LENGTH, CVC4::Kind::STRING_LENGTH},
    {SEQ_EXTRACT, CVC4::Kind::STRING_SUBSTR},
    {SEQ_UPDATE, CVC4::Kind::STRING_UPDATE},
    {SEQ_AT, CVC4::Kind::STRING_CHARAT},
    {SEQ_CONTAINS, CVC4::Kind::STRING_STRCTN},
    {SEQ_INDEXOF, CVC4::Kind::STRING_STRIDOF},
    {SEQ_REPLACE, CVC4::Kind::STRING_STRREPL},
    {SEQ_REPLACE_ALL, CVC4::Kind::STRING_STRREPLALL},
    {SEQ_REV, CVC4::Kind::STRING_REV},
    {SEQ_PREFIX, CVC4::Kind::STRING_PREFIX},
    {SEQ_SUFFIX, CVC4::Kind::STRING_SUFFIX},
    {CONST_SEQUENCE, CVC4::Kind::CONST_SEQUENCE},
    {SEQ_UNIT, CVC4::Kind::SEQ_UNIT},
    {SEQ_NTH, CVC4::Kind::SEQ_NTH},
    /* Quantifiers --------------------------------------------------------- */
    {FORALL, CVC4::Kind::FORALL},
    {EXISTS, CVC4::Kind::EXISTS},
    {BOUND_VAR_LIST, CVC4::Kind::BOUND_VAR_LIST},
    {INST_CLOSURE, CVC4::Kind::INST_CLOSURE},
    {INST_PATTERN, CVC4::Kind::INST_PATTERN},
    {INST_NO_PATTERN, CVC4::Kind::INST_NO_PATTERN},
    {INST_ATTRIBUTE, CVC4::Kind::INST_ATTRIBUTE},
    {INST_PATTERN_LIST, CVC4::Kind::INST_PATTERN_LIST},
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
        {CVC4::Kind::EQUAL, EQUAL},
        {CVC4::Kind::DISTINCT, DISTINCT},
        {CVC4::Kind::VARIABLE, CONSTANT},
        {CVC4::Kind::BOUND_VARIABLE, VARIABLE},
        {CVC4::Kind::LAMBDA, LAMBDA},
        {CVC4::Kind::WITNESS, WITNESS},
        /* Boolean --------------------------------------------------------- */
        {CVC4::Kind::CONST_BOOLEAN, CONST_BOOLEAN},
        {CVC4::Kind::NOT, NOT},
        {CVC4::Kind::AND, AND},
        {CVC4::Kind::IMPLIES, IMPLIES},
        {CVC4::Kind::OR, OR},
        {CVC4::Kind::XOR, XOR},
        {CVC4::Kind::ITE, ITE},
        {CVC4::Kind::MATCH, MATCH},
        {CVC4::Kind::MATCH_CASE, MATCH_CASE},
        {CVC4::Kind::MATCH_BIND_CASE, MATCH_BIND_CASE},
        /* UF -------------------------------------------------------------- */
        {CVC4::Kind::APPLY_UF, APPLY_UF},
        {CVC4::Kind::CARDINALITY_CONSTRAINT, CARDINALITY_CONSTRAINT},
        {CVC4::Kind::CARDINALITY_VALUE, CARDINALITY_VALUE},
        {CVC4::Kind::HO_APPLY, HO_APPLY},
        /* Arithmetic ------------------------------------------------------ */
        {CVC4::Kind::PLUS, PLUS},
        {CVC4::Kind::MULT, MULT},
        {CVC4::Kind::IAND, IAND},
        {CVC4::Kind::MINUS, MINUS},
        {CVC4::Kind::UMINUS, UMINUS},
        {CVC4::Kind::DIVISION, DIVISION},
        {CVC4::Kind::DIVISION_TOTAL, INTERNAL_KIND},
        {CVC4::Kind::INTS_DIVISION, INTS_DIVISION},
        {CVC4::Kind::INTS_DIVISION_TOTAL, INTERNAL_KIND},
        {CVC4::Kind::INTS_MODULUS, INTS_MODULUS},
        {CVC4::Kind::INTS_MODULUS_TOTAL, INTERNAL_KIND},
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
        {CVC4::Kind::DIVISIBLE_OP, DIVISIBLE},
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
        {CVC4::Kind::BITVECTOR_UDIV_TOTAL, INTERNAL_KIND},
        {CVC4::Kind::BITVECTOR_UREM_TOTAL, INTERNAL_KIND},
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
        {CVC4::Kind::BITVECTOR_EXTRACT_OP, BITVECTOR_EXTRACT},
        {CVC4::Kind::BITVECTOR_REPEAT_OP, BITVECTOR_REPEAT},
        {CVC4::Kind::BITVECTOR_ZERO_EXTEND_OP, BITVECTOR_ZERO_EXTEND},
        {CVC4::Kind::BITVECTOR_SIGN_EXTEND_OP, BITVECTOR_SIGN_EXTEND},
        {CVC4::Kind::BITVECTOR_ROTATE_LEFT_OP, BITVECTOR_ROTATE_LEFT},
        {CVC4::Kind::BITVECTOR_ROTATE_RIGHT_OP, BITVECTOR_ROTATE_RIGHT},
        {CVC4::Kind::BITVECTOR_EXTRACT, BITVECTOR_EXTRACT},
        {CVC4::Kind::BITVECTOR_REPEAT, BITVECTOR_REPEAT},
        {CVC4::Kind::BITVECTOR_ZERO_EXTEND, BITVECTOR_ZERO_EXTEND},
        {CVC4::Kind::BITVECTOR_SIGN_EXTEND, BITVECTOR_SIGN_EXTEND},
        {CVC4::Kind::BITVECTOR_ROTATE_LEFT, BITVECTOR_ROTATE_LEFT},
        {CVC4::Kind::BITVECTOR_ROTATE_RIGHT, BITVECTOR_ROTATE_RIGHT},
        {CVC4::Kind::INT_TO_BITVECTOR_OP, INT_TO_BITVECTOR},
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
         FLOATINGPOINT_TO_FP_IEEE_BITVECTOR},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR,
         FLOATINGPOINT_TO_FP_IEEE_BITVECTOR},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP,
         FLOATINGPOINT_TO_FP_FLOATINGPOINT},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT,
         FLOATINGPOINT_TO_FP_FLOATINGPOINT},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_REAL_OP, FLOATINGPOINT_TO_FP_REAL},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_REAL, FLOATINGPOINT_TO_FP_REAL},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP,
         FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
         FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP,
         FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
         FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_GENERIC_OP,
         FLOATINGPOINT_TO_FP_GENERIC},
        {CVC4::Kind::FLOATINGPOINT_TO_FP_GENERIC, FLOATINGPOINT_TO_FP_GENERIC},
        {CVC4::Kind::FLOATINGPOINT_TO_UBV_OP, FLOATINGPOINT_TO_UBV},
        {CVC4::Kind::FLOATINGPOINT_TO_UBV, FLOATINGPOINT_TO_UBV},
        {CVC4::Kind::FLOATINGPOINT_TO_UBV_TOTAL_OP, INTERNAL_KIND},
        {CVC4::Kind::FLOATINGPOINT_TO_UBV_TOTAL, INTERNAL_KIND},
        {CVC4::Kind::FLOATINGPOINT_TO_SBV_OP, FLOATINGPOINT_TO_SBV},
        {CVC4::Kind::FLOATINGPOINT_TO_SBV, FLOATINGPOINT_TO_SBV},
        {CVC4::Kind::FLOATINGPOINT_TO_SBV_TOTAL_OP, INTERNAL_KIND},
        {CVC4::Kind::FLOATINGPOINT_TO_SBV_TOTAL, INTERNAL_KIND},
        {CVC4::Kind::FLOATINGPOINT_TO_REAL, FLOATINGPOINT_TO_REAL},
        {CVC4::Kind::FLOATINGPOINT_TO_REAL_TOTAL, INTERNAL_KIND},
        /* Arrays ---------------------------------------------------------- */
        {CVC4::Kind::SELECT, SELECT},
        {CVC4::Kind::STORE, STORE},
        {CVC4::Kind::STORE_ALL, CONST_ARRAY},
        /* Datatypes ------------------------------------------------------- */
        {CVC4::Kind::APPLY_SELECTOR, APPLY_SELECTOR},
        {CVC4::Kind::APPLY_CONSTRUCTOR, APPLY_CONSTRUCTOR},
        {CVC4::Kind::APPLY_SELECTOR_TOTAL, INTERNAL_KIND},
        {CVC4::Kind::APPLY_TESTER, APPLY_TESTER},
        {CVC4::Kind::TUPLE_UPDATE_OP, TUPLE_UPDATE},
        {CVC4::Kind::TUPLE_UPDATE, TUPLE_UPDATE},
        {CVC4::Kind::RECORD_UPDATE_OP, RECORD_UPDATE},
        {CVC4::Kind::RECORD_UPDATE, RECORD_UPDATE},
        {CVC4::Kind::DT_SIZE, DT_SIZE},
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
        {CVC4::Kind::COMPREHENSION, COMPREHENSION},
        {CVC4::Kind::CHOOSE, CHOOSE},
        /* Strings --------------------------------------------------------- */
        {CVC4::Kind::STRING_CONCAT, STRING_CONCAT},
        {CVC4::Kind::STRING_IN_REGEXP, STRING_IN_REGEXP},
        {CVC4::Kind::STRING_LENGTH, STRING_LENGTH},
        {CVC4::Kind::STRING_SUBSTR, STRING_SUBSTR},
        {CVC4::Kind::STRING_UPDATE, STRING_UPDATE},
        {CVC4::Kind::STRING_CHARAT, STRING_CHARAT},
        {CVC4::Kind::STRING_STRCTN, STRING_CONTAINS},
        {CVC4::Kind::STRING_STRIDOF, STRING_INDEXOF},
        {CVC4::Kind::STRING_STRREPL, STRING_REPLACE},
        {CVC4::Kind::STRING_STRREPLALL, STRING_REPLACE_ALL},
        {CVC4::Kind::STRING_REPLACE_RE, STRING_REPLACE_RE},
        {CVC4::Kind::STRING_REPLACE_RE_ALL, STRING_REPLACE_RE_ALL},
        {CVC4::Kind::STRING_TOLOWER, STRING_TOLOWER},
        {CVC4::Kind::STRING_TOUPPER, STRING_TOUPPER},
        {CVC4::Kind::STRING_REV, STRING_REV},
        {CVC4::Kind::STRING_FROM_CODE, STRING_FROM_CODE},
        {CVC4::Kind::STRING_TO_CODE, STRING_TO_CODE},
        {CVC4::Kind::STRING_LT, STRING_LT},
        {CVC4::Kind::STRING_LEQ, STRING_LEQ},
        {CVC4::Kind::STRING_PREFIX, STRING_PREFIX},
        {CVC4::Kind::STRING_SUFFIX, STRING_SUFFIX},
        {CVC4::Kind::STRING_IS_DIGIT, STRING_IS_DIGIT},
        {CVC4::Kind::STRING_ITOS, STRING_FROM_INT},
        {CVC4::Kind::STRING_STOI, STRING_TO_INT},
        {CVC4::Kind::CONST_STRING, CONST_STRING},
        {CVC4::Kind::STRING_TO_REGEXP, STRING_TO_REGEXP},
        {CVC4::Kind::REGEXP_CONCAT, REGEXP_CONCAT},
        {CVC4::Kind::REGEXP_UNION, REGEXP_UNION},
        {CVC4::Kind::REGEXP_INTER, REGEXP_INTER},
        {CVC4::Kind::REGEXP_DIFF, REGEXP_DIFF},
        {CVC4::Kind::REGEXP_STAR, REGEXP_STAR},
        {CVC4::Kind::REGEXP_PLUS, REGEXP_PLUS},
        {CVC4::Kind::REGEXP_OPT, REGEXP_OPT},
        {CVC4::Kind::REGEXP_RANGE, REGEXP_RANGE},
        {CVC4::Kind::REGEXP_REPEAT, REGEXP_REPEAT},
        {CVC4::Kind::REGEXP_LOOP, REGEXP_LOOP},
        {CVC4::Kind::REGEXP_EMPTY, REGEXP_EMPTY},
        {CVC4::Kind::REGEXP_SIGMA, REGEXP_SIGMA},
        {CVC4::Kind::REGEXP_COMPLEMENT, REGEXP_COMPLEMENT},
        {CVC4::Kind::CONST_SEQUENCE, CONST_SEQUENCE},
        {CVC4::Kind::SEQ_UNIT, SEQ_UNIT},
        {CVC4::Kind::SEQ_NTH, SEQ_NTH},
        /* Quantifiers ----------------------------------------------------- */
        {CVC4::Kind::FORALL, FORALL},
        {CVC4::Kind::EXISTS, EXISTS},
        {CVC4::Kind::BOUND_VAR_LIST, BOUND_VAR_LIST},
        {CVC4::Kind::INST_CLOSURE, INST_CLOSURE},
        {CVC4::Kind::INST_PATTERN, INST_PATTERN},
        {CVC4::Kind::INST_NO_PATTERN, INST_NO_PATTERN},
        {CVC4::Kind::INST_ATTRIBUTE, INST_ATTRIBUTE},
        {CVC4::Kind::INST_PATTERN_LIST, INST_PATTERN_LIST},
        /* ----------------------------------------------------------------- */
        {CVC4::Kind::LAST_KIND, LAST_KIND},
    };

/* Set of kinds for indexed operators */
const static std::unordered_set<Kind, KindHashFunction> s_indexed_kinds(
    {RECORD_UPDATE,
     DIVISIBLE,
     IAND,
     BITVECTOR_REPEAT,
     BITVECTOR_ZERO_EXTEND,
     BITVECTOR_SIGN_EXTEND,
     BITVECTOR_ROTATE_LEFT,
     BITVECTOR_ROTATE_RIGHT,
     INT_TO_BITVECTOR,
     FLOATINGPOINT_TO_UBV,
     FLOATINGPOINT_TO_SBV,
     TUPLE_UPDATE,
     BITVECTOR_EXTRACT,
     FLOATINGPOINT_TO_FP_IEEE_BITVECTOR,
     FLOATINGPOINT_TO_FP_FLOATINGPOINT,
     FLOATINGPOINT_TO_FP_REAL,
     FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
     FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
     FLOATINGPOINT_TO_FP_GENERIC});

namespace {

bool isDefinedKind(Kind k) { return k > UNDEFINED_KIND && k < LAST_KIND; }

/** Returns true if the internal kind is one where the API term structure
 *  differs from internal structure. This happens for APPLY_* kinds.
 *  The API takes a "higher-order" perspective and treats functions as well
 *  as datatype constructors/selectors/testers as terms
 *  but interally they are not
 */
bool isApplyKind(CVC4::Kind k)
{
  return (k == CVC4::Kind::APPLY_UF || k == CVC4::Kind::APPLY_CONSTRUCTOR
          || k == CVC4::Kind::APPLY_SELECTOR || k == CVC4::Kind::APPLY_TESTER);
}

#ifdef CVC4_ASSERTIONS
bool isDefinedIntKind(CVC4::Kind k)
{
  return k != CVC4::Kind::UNDEFINED_KIND && k != CVC4::Kind::LAST_KIND;
}
#endif

uint32_t minArity(Kind k)
{
  Assert(isDefinedKind(k));
  Assert(isDefinedIntKind(extToIntKind(k)));
  uint32_t min = CVC4::ExprManager::minArity(extToIntKind(k));

  // At the API level, we treat functions/constructors/selectors/testers as
  // normal terms instead of making them part of the operator
  if (isApplyKind(extToIntKind(k)))
  {
    min++;
  }
  return min;
}

uint32_t maxArity(Kind k)
{
  Assert(isDefinedKind(k));
  Assert(isDefinedIntKind(extToIntKind(k)));
  uint32_t max = CVC4::ExprManager::maxArity(extToIntKind(k));

  // At the API level, we treat functions/constructors/selectors/testers as
  // normal terms instead of making them part of the operator
  if (isApplyKind(extToIntKind(k))
      && max != std::numeric_limits<uint32_t>::max())  // be careful not to
                                                       // overflow
  {
    max++;
  }
  return max;
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
  CVC4_PREDICT_TRUE(cond)    \
  ? (void)0 : OstreamVoider() & CVC4ApiExceptionStream().ostream()

#define CVC4_API_CHECK_NOT_NULL                     \
  CVC4_API_CHECK(!isNullHelper())                   \
      << "Invalid call to '" << __PRETTY_FUNCTION__ \
      << "', expected non-null object";

#define CVC4_API_ARG_CHECK_NOT_NULL(arg) \
  CVC4_API_CHECK(!arg.isNull()) << "Invalid null argument for '" << #arg << "'";

#define CVC4_API_ARG_CHECK_NOT_NULLPTR(arg) \
  CVC4_API_CHECK(arg != nullptr)            \
      << "Invalid null argument for '" << #arg << "'";

#define CVC4_API_KIND_CHECK(kind)     \
  CVC4_API_CHECK(isDefinedKind(kind)) \
      << "Invalid kind '" << kindToString(kind) << "'";

#define CVC4_API_KIND_CHECK_EXPECTED(cond, kind) \
  CVC4_PREDICT_TRUE(cond)                        \
  ? (void)0                                      \
  : OstreamVoider()                              \
          & CVC4ApiExceptionStream().ostream()   \
                << "Invalid kind '" << kindToString(kind) << "', expected "

#define CVC4_API_ARG_CHECK_EXPECTED(cond, arg)                      \
  CVC4_PREDICT_TRUE(cond)                                           \
  ? (void)0                                                         \
  : OstreamVoider()                                                 \
          & CVC4ApiExceptionStream().ostream()                      \
                << "Invalid argument '" << arg << "' for '" << #arg \
                << "', expected "

#define CVC4_API_ARG_SIZE_CHECK_EXPECTED(cond, arg) \
  CVC4_PREDICT_TRUE(cond)                           \
  ? (void)0                                         \
  : OstreamVoider()                                 \
          & CVC4ApiExceptionStream().ostream()      \
                << "Invalid size of argument '" << #arg << "', expected "

#define CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(cond, what, arg, idx)           \
  CVC4_PREDICT_TRUE(cond)                                                    \
  ? (void)0                                                                  \
  : OstreamVoider()                                                          \
          & CVC4ApiExceptionStream().ostream()                               \
                << "Invalid " << what << " '" << arg << "' at index " << idx \
                << ", expected "

#define CVC4_API_SOLVER_TRY_CATCH_BEGIN \
  try                                   \
  {
#define CVC4_API_SOLVER_TRY_CATCH_END                                          \
  }                                                                            \
  catch (const CVC4::Exception& e) { throw CVC4ApiException(e.getMessage()); } \
  catch (const std::invalid_argument& e) { throw CVC4ApiException(e.what()); }

#define CVC4_API_SOLVER_CHECK_SORT(sort) \
  CVC4_API_CHECK(this == sort.d_solver)  \
      << "Given sort is not associated with this solver";

#define CVC4_API_SOLVER_CHECK_TERM(term) \
  CVC4_API_CHECK(this == term.d_solver)  \
      << "Given term is not associated with this solver";

#define CVC4_API_SOLVER_CHECK_OP(op)  \
  CVC4_API_CHECK(this == op.d_solver) \
      << "Given operator is not associated with this solver";

}  // namespace

/* -------------------------------------------------------------------------- */
/* Result                                                                     */
/* -------------------------------------------------------------------------- */

Result::Result(const CVC4::Result& r) : d_result(new CVC4::Result(r)) {}

Result::Result() : d_result(new CVC4::Result()) {}

bool Result::isNull() const
{
  return d_result->getType() == CVC4::Result::TYPE_NONE;
}

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

bool Result::isEntailed(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_ENTAILMENT
         && d_result->isEntailed() == CVC4::Result::ENTAILED;
}

bool Result::isNotEntailed(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_ENTAILMENT
         && d_result->isEntailed() == CVC4::Result::NOT_ENTAILED;
}

bool Result::isEntailmentUnknown(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_ENTAILMENT
         && d_result->isEntailed() == CVC4::Result::ENTAILMENT_UNKNOWN;
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

Sort::Sort(const Solver* slv, const CVC4::Type& t)
    : d_solver(slv), d_type(new CVC4::Type(t))
{
}

Sort::Sort() : d_solver(nullptr), d_type(new CVC4::Type()) {}

Sort::~Sort() {}

/* Helpers                                                                    */
/* -------------------------------------------------------------------------- */

/* Split out to avoid nested API calls (problematic with API tracing).        */
/* .......................................................................... */

bool Sort::isNullHelper() const { return d_type->isNull(); }

bool Sort::operator==(const Sort& s) const { return *d_type == *s.d_type; }

bool Sort::operator!=(const Sort& s) const { return *d_type != *s.d_type; }

bool Sort::operator<(const Sort& s) const { return *d_type < *s.d_type; }

bool Sort::operator>(const Sort& s) const { return *d_type > *s.d_type; }

bool Sort::operator<=(const Sort& s) const { return *d_type <= *s.d_type; }

bool Sort::operator>=(const Sort& s) const { return *d_type >= *s.d_type; }

bool Sort::isNull() const { return isNullHelper(); }

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
  return DatatypeType(*d_type).isParametric();
}

bool Sort::isConstructor() const { return d_type->isConstructor(); }
bool Sort::isSelector() const { return d_type->isSelector(); }
bool Sort::isTester() const { return d_type->isTester(); }

bool Sort::isFunction() const { return d_type->isFunction(); }

bool Sort::isPredicate() const { return d_type->isPredicate(); }

bool Sort::isTuple() const { return d_type->isTuple(); }

bool Sort::isRecord() const { return d_type->isRecord(); }

bool Sort::isArray() const { return d_type->isArray(); }

bool Sort::isSet() const { return d_type->isSet(); }

bool Sort::isSequence() const { return d_type->isSequence(); }

bool Sort::isUninterpretedSort() const { return d_type->isSort(); }

bool Sort::isSortConstructor() const { return d_type->isSortConstructor(); }

bool Sort::isFirstClass() const { return d_type->isFirstClass(); }

bool Sort::isFunctionLike() const { return d_type->isFunctionLike(); }

bool Sort::isSubsortOf(Sort s) const { return d_type->isSubtypeOf(*s.d_type); }

bool Sort::isComparableTo(Sort s) const
{
  return d_type->isComparableTo(*s.d_type);
}

Datatype Sort::getDatatype() const
{
  CVC4_API_CHECK(isDatatype()) << "Expected datatype sort.";
  return Datatype(d_solver, DatatypeType(*d_type).getDatatype());
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
    return Sort(d_solver, DatatypeType(*d_type).instantiate(tparams));
  }
  Assert(d_type->isSortConstructor());
  return Sort(d_solver, SortConstructorType(*d_type).instantiate(tparams));
}

std::string Sort::toString() const { return d_type->toString(); }

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::Type Sort::getType(void) const { return *d_type; }

/* Constructor sort ------------------------------------------------------- */

size_t Sort::getConstructorArity() const
{
  CVC4_API_CHECK(isConstructor()) << "Not a function sort: " << (*this);
  return ConstructorType(*d_type).getArity();
}

std::vector<Sort> Sort::getConstructorDomainSorts() const
{
  CVC4_API_CHECK(isConstructor()) << "Not a function sort: " << (*this);
  std::vector<CVC4::Type> types = ConstructorType(*d_type).getArgTypes();
  return typeVectorToSorts(d_solver, types);
}

Sort Sort::getConstructorCodomainSort() const
{
  CVC4_API_CHECK(isConstructor()) << "Not a function sort: " << (*this);
  return Sort(d_solver, ConstructorType(*d_type).getRangeType());
}

/* Function sort ------------------------------------------------------- */

size_t Sort::getFunctionArity() const
{
  CVC4_API_CHECK(isFunction()) << "Not a function sort: " << (*this);
  return FunctionType(*d_type).getArity();
}

std::vector<Sort> Sort::getFunctionDomainSorts() const
{
  CVC4_API_CHECK(isFunction()) << "Not a function sort: " << (*this);
  std::vector<CVC4::Type> types = FunctionType(*d_type).getArgTypes();
  return typeVectorToSorts(d_solver, types);
}

Sort Sort::getFunctionCodomainSort() const
{
  CVC4_API_CHECK(isFunction()) << "Not a function sort" << (*this);
  return Sort(d_solver, FunctionType(*d_type).getRangeType());
}

/* Array sort ---------------------------------------------------------- */

Sort Sort::getArrayIndexSort() const
{
  CVC4_API_CHECK(isArray()) << "Not an array sort.";
  return Sort(d_solver, ArrayType(*d_type).getIndexType());
}

Sort Sort::getArrayElementSort() const
{
  CVC4_API_CHECK(isArray()) << "Not an array sort.";
  return Sort(d_solver, ArrayType(*d_type).getConstituentType());
}

/* Set sort ------------------------------------------------------------ */

Sort Sort::getSetElementSort() const
{
  CVC4_API_CHECK(isSet()) << "Not a set sort.";
  return Sort(d_solver, SetType(*d_type).getElementType());
}

/* Set sort ------------------------------------------------------------ */

Sort Sort::getSequenceElementSort() const
{
  CVC4_API_CHECK(isSequence()) << "Not a sequence sort.";
  return Sort(d_solver, SequenceType(*d_type).getElementType());
}

/* Uninterpreted sort -------------------------------------------------- */

std::string Sort::getUninterpretedSortName() const
{
  CVC4_API_CHECK(isUninterpretedSort()) << "Not an uninterpreted sort.";
  return SortType(*d_type).getName();
}

bool Sort::isUninterpretedSortParameterized() const
{
  CVC4_API_CHECK(isUninterpretedSort()) << "Not an uninterpreted sort.";
  return SortType(*d_type).isParameterized();
}

std::vector<Sort> Sort::getUninterpretedSortParamSorts() const
{
  CVC4_API_CHECK(isUninterpretedSort()) << "Not an uninterpreted sort.";
  std::vector<CVC4::Type> types = SortType(*d_type).getParamTypes();
  return typeVectorToSorts(d_solver, types);
}

/* Sort constructor sort ----------------------------------------------- */

std::string Sort::getSortConstructorName() const
{
  CVC4_API_CHECK(isSortConstructor()) << "Not a sort constructor sort.";
  return SortConstructorType(*d_type).getName();
}

size_t Sort::getSortConstructorArity() const
{
  CVC4_API_CHECK(isSortConstructor()) << "Not a sort constructor sort.";
  return SortConstructorType(*d_type).getArity();
}

/* Bit-vector sort ----------------------------------------------------- */

uint32_t Sort::getBVSize() const
{
  CVC4_API_CHECK(isBitVector()) << "Not a bit-vector sort.";
  return BitVectorType(*d_type).getSize();
}

/* Floating-point sort ------------------------------------------------- */

uint32_t Sort::getFPExponentSize() const
{
  CVC4_API_CHECK(isFloatingPoint()) << "Not a floating-point sort.";
  return FloatingPointType(*d_type).getExponentSize();
}

uint32_t Sort::getFPSignificandSize() const
{
  CVC4_API_CHECK(isFloatingPoint()) << "Not a floating-point sort.";
  return FloatingPointType(*d_type).getSignificandSize();
}

/* Datatype sort ------------------------------------------------------- */

std::vector<Sort> Sort::getDatatypeParamSorts() const
{
  CVC4_API_CHECK(isParametricDatatype()) << "Not a parametric datatype sort.";
  std::vector<CVC4::Type> types = DatatypeType(*d_type).getParamTypes();
  return typeVectorToSorts(d_solver, types);
}

size_t Sort::getDatatypeArity() const
{
  CVC4_API_CHECK(isDatatype()) << "Not a datatype sort.";
  return DatatypeType(*d_type).getArity();
}

/* Tuple sort ---------------------------------------------------------- */

size_t Sort::getTupleLength() const
{
  CVC4_API_CHECK(isTuple()) << "Not a tuple sort.";
  return DatatypeType(*d_type).getTupleLength();
}

std::vector<Sort> Sort::getTupleSorts() const
{
  CVC4_API_CHECK(isTuple()) << "Not a tuple sort.";
  std::vector<CVC4::Type> types = DatatypeType(*d_type).getTupleTypes();
  return typeVectorToSorts(d_solver, types);
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
/* Op                                                                     */
/* -------------------------------------------------------------------------- */

Op::Op() : d_solver(nullptr), d_kind(NULL_EXPR), d_node(new CVC4::Node()) {}

Op::Op(const Solver* slv, const Kind k)
    : d_solver(slv), d_kind(k), d_node(new CVC4::Node())
{
}

Op::Op(const Solver* slv, const Kind k, const CVC4::Expr& e)
    : d_solver(slv), d_kind(k), d_node(new CVC4::Node(Node::fromExpr(e)))
{
}

Op::Op(const Solver* slv, const Kind k, const CVC4::Node& n)
    : d_solver(slv), d_kind(k), d_node(new CVC4::Node(n))
{
}

Op::~Op()
{
  if (d_solver != nullptr)
  {
    // Ensure that the correct node manager is in scope when the node is
    // destroyed.
    NodeManagerScope scope(d_solver->getNodeManager());
    d_node.reset();
  }
}

/* Helpers                                                                    */
/* -------------------------------------------------------------------------- */

/* Split out to avoid nested API calls (problematic with API tracing).        */
/* .......................................................................... */

bool Op::isNullHelper() const
{
  return (d_node->isNull() && (d_kind == NULL_EXPR));
}

bool Op::isIndexedHelper() const { return !d_node->isNull(); }

/* Public methods                                                             */
bool Op::operator==(const Op& t) const
{
  if (d_node->isNull() && t.d_node->isNull())
  {
    return (d_kind == t.d_kind);
  }
  else if (d_node->isNull() || t.d_node->isNull())
  {
    return false;
  }
  return (d_kind == t.d_kind) && (*d_node == *t.d_node);
}

bool Op::operator!=(const Op& t) const { return !(*this == t); }

Kind Op::getKind() const
{
  CVC4_API_CHECK(d_kind != NULL_EXPR) << "Expecting a non-null Kind";
  return d_kind;
}

bool Op::isNull() const { return isNullHelper(); }

bool Op::isIndexed() const { return isIndexedHelper(); }

template <>
std::string Op::getIndices() const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(!d_node->isNull())
      << "Expecting a non-null internal expression. This Op is not indexed.";

  std::string i;
  Kind k = intToExtKind(d_node->getKind());

  if (k == DIVISIBLE)
  {
    // DIVISIBLE returns a string index to support
    // arbitrary precision integers
    CVC4::Integer _int = d_node->getConst<Divisible>().k;
    i = _int.toString();
  }
  else if (k == RECORD_UPDATE)
  {
    i = d_node->getConst<RecordUpdate>().getField();
  }
  else
  {
    CVC4_API_CHECK(false) << "Can't get string index from"
                          << " kind " << kindToString(k);
  }

  return i;
}

template <>
uint32_t Op::getIndices() const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(!d_node->isNull())
      << "Expecting a non-null internal expression. This Op is not indexed.";

  uint32_t i = 0;
  Kind k = intToExtKind(d_node->getKind());
  switch (k)
  {
    case BITVECTOR_REPEAT:
      i = d_node->getConst<BitVectorRepeat>().d_repeatAmount;
      break;
    case BITVECTOR_ZERO_EXTEND:
      i = d_node->getConst<BitVectorZeroExtend>().d_zeroExtendAmount;
      break;
    case BITVECTOR_SIGN_EXTEND:
      i = d_node->getConst<BitVectorSignExtend>().d_signExtendAmount;
      break;
    case BITVECTOR_ROTATE_LEFT:
      i = d_node->getConst<BitVectorRotateLeft>().d_rotateLeftAmount;
      break;
    case BITVECTOR_ROTATE_RIGHT:
      i = d_node->getConst<BitVectorRotateRight>().d_rotateRightAmount;
      break;
    case INT_TO_BITVECTOR: i = d_node->getConst<IntToBitVector>().d_size; break;
    case IAND: i = d_node->getConst<IntAnd>().d_size; break;
    case FLOATINGPOINT_TO_UBV:
      i = d_node->getConst<FloatingPointToUBV>().bvs.d_size;
      break;
    case FLOATINGPOINT_TO_SBV:
      i = d_node->getConst<FloatingPointToSBV>().bvs.d_size;
      break;
    case TUPLE_UPDATE: i = d_node->getConst<TupleUpdate>().getIndex(); break;
    default:
      CVC4ApiExceptionStream().ostream() << "Can't get uint32_t index from"
                                         << " kind " << kindToString(k);
  }
  return i;
}

template <>
std::pair<uint32_t, uint32_t> Op::getIndices() const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(!d_node->isNull())
      << "Expecting a non-null internal expression. This Op is not indexed.";

  std::pair<uint32_t, uint32_t> indices;
  Kind k = intToExtKind(d_node->getKind());

  // using if/else instead of case statement because want local variables
  if (k == BITVECTOR_EXTRACT)
  {
    CVC4::BitVectorExtract ext = d_node->getConst<BitVectorExtract>();
    indices = std::make_pair(ext.d_high, ext.d_low);
  }
  else if (k == FLOATINGPOINT_TO_FP_IEEE_BITVECTOR)
  {
    CVC4::FloatingPointToFPIEEEBitVector ext =
        d_node->getConst<FloatingPointToFPIEEEBitVector>();
    indices = std::make_pair(ext.t.exponent(), ext.t.significand());
  }
  else if (k == FLOATINGPOINT_TO_FP_FLOATINGPOINT)
  {
    CVC4::FloatingPointToFPFloatingPoint ext =
        d_node->getConst<FloatingPointToFPFloatingPoint>();
    indices = std::make_pair(ext.t.exponent(), ext.t.significand());
  }
  else if (k == FLOATINGPOINT_TO_FP_REAL)
  {
    CVC4::FloatingPointToFPReal ext = d_node->getConst<FloatingPointToFPReal>();
    indices = std::make_pair(ext.t.exponent(), ext.t.significand());
  }
  else if (k == FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR)
  {
    CVC4::FloatingPointToFPSignedBitVector ext =
        d_node->getConst<FloatingPointToFPSignedBitVector>();
    indices = std::make_pair(ext.t.exponent(), ext.t.significand());
  }
  else if (k == FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR)
  {
    CVC4::FloatingPointToFPUnsignedBitVector ext =
        d_node->getConst<FloatingPointToFPUnsignedBitVector>();
    indices = std::make_pair(ext.t.exponent(), ext.t.significand());
  }
  else if (k == FLOATINGPOINT_TO_FP_GENERIC)
  {
    CVC4::FloatingPointToFPGeneric ext =
        d_node->getConst<FloatingPointToFPGeneric>();
    indices = std::make_pair(ext.t.exponent(), ext.t.significand());
  }
  else
  {
    CVC4_API_CHECK(false) << "Can't get pair<uint32_t, uint32_t> indices from"
                          << " kind " << kindToString(k);
  }
  return indices;
}

std::string Op::toString() const
{
  CVC4_API_CHECK_NOT_NULL;
  if (d_node->isNull())
  {
    return kindToString(d_kind);
  }
  else
  {
    CVC4_API_CHECK(!d_node->isNull())
        << "Expecting a non-null internal expression";
    return d_node->toString();
  }
}

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::Expr Op::getExpr(void) const
{
  if (d_node->isNull()) return Expr();
  NodeManagerScope scope(d_solver->getNodeManager());
  return d_node->toExpr();
}

std::ostream& operator<<(std::ostream& out, const Op& t)
{
  out << t.toString();
  return out;
}

size_t OpHashFunction::operator()(const Op& t) const
{
  if (t.isIndexedHelper())
  {
    return ExprHashFunction()(t.d_node->toExpr());
  }
  else
  {
    return KindHashFunction()(t.d_kind);
  }
}

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

Term::Term() : d_solver(nullptr), d_node(new CVC4::Node()) {}

Term::Term(const Solver* slv, const CVC4::Expr& e) : d_solver(slv)
{
  // Ensure that we create the node in the correct node manager.
  NodeManagerScope scope(d_solver->getNodeManager());
  d_node.reset(new CVC4::Node(e));
}

Term::Term(const Solver* slv, const CVC4::Node& n) : d_solver(slv)
{
  // Ensure that we create the node in the correct node manager.
  NodeManagerScope scope(d_solver->getNodeManager());
  d_node.reset(new CVC4::Node(n));
}

Term::~Term()
{
  if (d_solver != nullptr)
  {
    // Ensure that the correct node manager is in scope when the node is
    // destroyed.
    NodeManagerScope scope(d_solver->getNodeManager());
    d_node.reset();
  }
}

bool Term::isNullHelper() const
{
  /* Split out to avoid nested API calls (problematic with API tracing). */
  return d_node->isNull();
}

Kind Term::getKindHelper() const
{
  // Sequence kinds do not exist internally, so we must convert their internal
  // (string) versions back to sequence. All operators where this is
  // necessary are such that their first child is of sequence type, which
  // we check here.
  if (getNumChildren() > 0 && (*this)[0].getSort().isSequence())
  {
    switch (d_node->getKind())
    {
      case CVC4::Kind::STRING_CONCAT: return SEQ_CONCAT;
      case CVC4::Kind::STRING_LENGTH: return SEQ_LENGTH;
      case CVC4::Kind::STRING_SUBSTR: return SEQ_EXTRACT;
      case CVC4::Kind::STRING_UPDATE: return SEQ_UPDATE;
      case CVC4::Kind::STRING_CHARAT: return SEQ_AT;
      case CVC4::Kind::STRING_STRCTN: return SEQ_CONTAINS;
      case CVC4::Kind::STRING_STRIDOF: return SEQ_INDEXOF;
      case CVC4::Kind::STRING_STRREPL: return SEQ_REPLACE;
      case CVC4::Kind::STRING_STRREPLALL: return SEQ_REPLACE_ALL;
      case CVC4::Kind::STRING_REV: return SEQ_REV;
      case CVC4::Kind::STRING_PREFIX: return SEQ_PREFIX;
      case CVC4::Kind::STRING_SUFFIX: return SEQ_SUFFIX;
      default:
        // fall through to conversion below
        break;
    }
  }

  return intToExtKind(d_node->getKind());
}

bool Term::operator==(const Term& t) const { return *d_node == *t.d_node; }

bool Term::operator!=(const Term& t) const { return *d_node != *t.d_node; }

bool Term::operator<(const Term& t) const { return *d_node < *t.d_node; }

bool Term::operator>(const Term& t) const { return *d_node > *t.d_node; }

bool Term::operator<=(const Term& t) const { return *d_node <= *t.d_node; }

bool Term::operator>=(const Term& t) const { return *d_node >= *t.d_node; }

size_t Term::getNumChildren() const
{
  CVC4_API_CHECK_NOT_NULL;
  // special case for apply kinds
  if (isApplyKind(d_node->getKind()))
  {
    return d_node->getNumChildren() + 1;
  }
  return d_node->getNumChildren();
}

Term Term::operator[](size_t index) const
{
  CVC4_API_CHECK_NOT_NULL;
  // special cases for apply kinds
  if (isApplyKind(d_node->getKind()))
  {
    CVC4_API_CHECK(d_node->hasOperator())
        << "Expected apply kind to have operator when accessing child of Term";
    if (index == 0)
    {
      // return the operator
      return Term(d_solver, d_node->getOperator().toExpr());
    }
    // otherwise we are looking up child at (index-1)
    index--;
  }
  return Term(d_solver, (*d_node)[index].toExpr());
}

uint64_t Term::getId() const
{
  CVC4_API_CHECK_NOT_NULL;
  return d_node->getId();
}

Kind Term::getKind() const
{
  CVC4_API_CHECK_NOT_NULL;
  return getKindHelper();
}

Sort Term::getSort() const
{
  CVC4_API_CHECK_NOT_NULL;
  NodeManagerScope scope(d_solver->getNodeManager());
  return Sort(d_solver, d_node->getType().toType());
}

Term Term::substitute(Term e, Term replacement) const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(!e.isNull())
      << "Expected non-null term to replace in substitute";
  CVC4_API_CHECK(!replacement.isNull())
      << "Expected non-null term as replacement in substitute";
  CVC4_API_CHECK(e.getSort().isComparableTo(replacement.getSort()))
      << "Expecting terms of comparable sort in substitute";
  return Term(d_solver,
              d_node->substitute(TNode(*e.d_node), TNode(*replacement.d_node)));
}

Term Term::substitute(const std::vector<Term> es,
                      const std::vector<Term>& replacements) const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(es.size() == replacements.size())
      << "Expecting vectors of the same arity in substitute";
  for (unsigned i = 0, nterms = es.size(); i < nterms; i++)
  {
    CVC4_API_CHECK(!es[i].isNull())
        << "Expected non-null term to replace in substitute";
    CVC4_API_CHECK(!replacements[i].isNull())
        << "Expected non-null term as replacement in substitute";
    CVC4_API_CHECK(es[i].getSort().isComparableTo(replacements[i].getSort()))
        << "Expecting terms of comparable sort in substitute";
  }

  std::vector<Node> nodes = termVectorToNodes(es);
  std::vector<Node> nodeReplacements = termVectorToNodes(replacements);
  return Term(d_solver,
              d_node->substitute(nodes.begin(),
                                 nodes.end(),
                                 nodeReplacements.begin(),
                                 nodeReplacements.end()));
}

bool Term::hasOp() const
{
  CVC4_API_CHECK_NOT_NULL;
  return d_node->hasOperator();
}

Op Term::getOp() const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(d_node->hasOperator())
      << "Expecting Term to have an Op when calling getOp()";

  // special cases for parameterized operators that are not indexed operators
  // the API level differs from the internal structure
  // indexed operators are stored in Ops
  // whereas functions and datatype operators are terms, and the Op
  // is one of the APPLY_* kinds
  if (isApplyKind(d_node->getKind()))
  {
    return Op(d_solver, intToExtKind(d_node->getKind()));
  }
  else if (d_node->getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    // it's an indexed operator
    // so we should return the indexed op
    CVC4::Node op = d_node->getOperator();
    return Op(d_solver, intToExtKind(d_node->getKind()), op);
  }
  // Notice this is the only case where getKindHelper is used, since the
  // cases above do have special cases for intToExtKind.
  return Op(d_solver, getKindHelper());
}

bool Term::isNull() const { return isNullHelper(); }

bool Term::isConst() const
{
  CVC4_API_CHECK_NOT_NULL;
  return d_node->isConst();
}

Term Term::getConstArrayBase() const
{
  CVC4::ExprManagerScope exmgrs(*(d_solver->getExprManager()));
  CVC4_API_CHECK_NOT_NULL;
  // CONST_ARRAY kind maps to STORE_ALL internal kind
  CVC4_API_CHECK(d_node->getKind() == CVC4::Kind::STORE_ALL)
      << "Expecting a CONST_ARRAY Term when calling getConstArrayBase()";
  return Term(d_solver, d_node->getConst<ArrayStoreAll>().getValue());
}

std::vector<Term> Term::getConstSequenceElements() const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(d_node->getKind() == CVC4::Kind::CONST_SEQUENCE)
      << "Expecting a CONST_SEQUENCE Term when calling "
         "getConstSequenceElements()";
  const std::vector<Node>& elems = d_node->getConst<Sequence>().getVec();
  std::vector<Term> terms;
  for (const Node& t : elems)
  {
    terms.push_back(Term(d_solver, t));
  }
  return terms;
}

Term Term::notTerm() const
{
  CVC4_API_CHECK_NOT_NULL;
  try
  {
    Node res = d_node->notNode();
    (void)res.getType(true); /* kick off type checking */
    return Term(d_solver, res);
  }
  catch (const CVC4::TypeCheckingExceptionPrivate& e)
  {
    throw CVC4ApiException(e.getMessage());
  }
}

Term Term::andTerm(const Term& t) const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_ARG_CHECK_NOT_NULL(t);
  try
  {
    Node res = d_node->andNode(*t.d_node);
    (void)res.getType(true); /* kick off type checking */
    return Term(d_solver, res);
  }
  catch (const CVC4::TypeCheckingExceptionPrivate& e)
  {
    throw CVC4ApiException(e.getMessage());
  }
}

Term Term::orTerm(const Term& t) const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_ARG_CHECK_NOT_NULL(t);
  try
  {
    Node res = d_node->orNode(*t.d_node);
    (void)res.getType(true); /* kick off type checking */
    return Term(d_solver, res);
  }
  catch (const CVC4::TypeCheckingExceptionPrivate& e)
  {
    throw CVC4ApiException(e.getMessage());
  }
}

Term Term::xorTerm(const Term& t) const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_ARG_CHECK_NOT_NULL(t);
  try
  {
    Node res = d_node->xorNode(*t.d_node);
    (void)res.getType(true); /* kick off type checking */
    return Term(d_solver, res);
  }
  catch (const CVC4::TypeCheckingExceptionPrivate& e)
  {
    throw CVC4ApiException(e.getMessage());
  }
}

Term Term::eqTerm(const Term& t) const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_ARG_CHECK_NOT_NULL(t);
  try
  {
    Node res = d_node->eqNode(*t.d_node);
    (void)res.getType(true); /* kick off type checking */
    return Term(d_solver, res);
  }
  catch (const CVC4::TypeCheckingExceptionPrivate& e)
  {
    throw CVC4ApiException(e.getMessage());
  }
}

Term Term::impTerm(const Term& t) const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_ARG_CHECK_NOT_NULL(t);
  try
  {
    Node res = d_node->impNode(*t.d_node);
    (void)res.getType(true); /* kick off type checking */
    return Term(d_solver, res);
  }
  catch (const CVC4::TypeCheckingExceptionPrivate& e)
  {
    throw CVC4ApiException(e.getMessage());
  }
}

Term Term::iteTerm(const Term& then_t, const Term& else_t) const
{
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_ARG_CHECK_NOT_NULL(then_t);
  CVC4_API_ARG_CHECK_NOT_NULL(else_t);
  try
  {
    Node res = d_node->iteNode(*then_t.d_node, *else_t.d_node);
    (void)res.getType(true); /* kick off type checking */
    return Term(d_solver, res);
  }
  catch (const CVC4::TypeCheckingExceptionPrivate& e)
  {
    throw CVC4ApiException(e.getMessage());
  }
}

std::string Term::toString() const { return d_node->toString(); }

Term::const_iterator::const_iterator()
    : d_solver(nullptr), d_origNode(nullptr), d_pos(0)
{
}

Term::const_iterator::const_iterator(const Solver* slv,
                                     const std::shared_ptr<CVC4::Node>& n,
                                     uint32_t p)
    : d_solver(slv), d_origNode(n), d_pos(p)
{
}

Term::const_iterator::const_iterator(const const_iterator& it)
    : d_solver(nullptr), d_origNode(nullptr)
{
  if (it.d_origNode != nullptr)
  {
    d_solver = it.d_solver;
    d_origNode = it.d_origNode;
    d_pos = it.d_pos;
  }
}

Term::const_iterator& Term::const_iterator::operator=(const const_iterator& it)
{
  d_solver = it.d_solver;
  d_origNode = it.d_origNode;
  d_pos = it.d_pos;
  return *this;
}

bool Term::const_iterator::operator==(const const_iterator& it) const
{
  if (d_origNode == nullptr || it.d_origNode == nullptr)
  {
    return false;
  }
  return (d_solver == it.d_solver && *d_origNode == *it.d_origNode)
         && (d_pos == it.d_pos);
}

bool Term::const_iterator::operator!=(const const_iterator& it) const
{
  return !(*this == it);
}

Term::const_iterator& Term::const_iterator::operator++()
{
  Assert(d_origNode != nullptr);
  ++d_pos;
  return *this;
}

Term::const_iterator Term::const_iterator::operator++(int)
{
  Assert(d_origNode != nullptr);
  const_iterator it = *this;
  ++d_pos;
  return it;
}

Term Term::const_iterator::operator*() const
{
  Assert(d_origNode != nullptr);
  // this term has an extra child (mismatch between API and internal structure)
  // the extra child will be the first child
  bool extra_child = isApplyKind(d_origNode->getKind());

  if (!d_pos && extra_child)
  {
    return Term(d_solver, d_origNode->getOperator());
  }
  else
  {
    uint32_t idx = d_pos;
    if (extra_child)
    {
      Assert(idx > 0);
      --idx;
    }
    Assert(idx >= 0);
    return Term(d_solver, (*d_origNode)[idx]);
  }
}

Term::const_iterator Term::begin() const
{
  return Term::const_iterator(d_solver, d_node, 0);
}

Term::const_iterator Term::end() const
{
  int endpos = d_node->getNumChildren();
  // special cases for APPLY_*
  // the API differs from the internal structure
  // the API takes a "higher-order" perspective and the applied
  //   function or datatype constructor/selector/tester is a Term
  // which means it needs to be one of the children, even though
  //   internally it is not
  if (isApplyKind(d_node->getKind()))
  {
    // one more child if this is a UF application (count the UF as a child)
    ++endpos;
  }
  return Term::const_iterator(d_solver, d_node, endpos);
}

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::Expr Term::getExpr(void) const
{
  if (d_node->isNull())
  {
    return Expr();
  }
  NodeManagerScope scope(d_solver->getNodeManager());
  return d_node->toExpr();
}

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
const CVC4::Node& Term::getNode(void) const { return *d_node; }

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
  return ExprHashFunction()(t.d_node->toExpr());
}

/* -------------------------------------------------------------------------- */
/* Datatypes                                                                  */
/* -------------------------------------------------------------------------- */

/* DatatypeConstructorDecl -------------------------------------------------- */

DatatypeConstructorDecl::DatatypeConstructorDecl()
    : d_solver(nullptr), d_ctor(nullptr)
{
}

DatatypeConstructorDecl::DatatypeConstructorDecl(const Solver* slv,
                                                 const std::string& name)
    : d_solver(slv), d_ctor(new CVC4::DatatypeConstructor(name))
{
}

void DatatypeConstructorDecl::addSelector(const std::string& name, Sort sort)
{
  CVC4_API_ARG_CHECK_EXPECTED(!sort.isNull(), sort)
      << "non-null range sort for selector";
  d_ctor->addArg(name, *sort.d_type);
}

void DatatypeConstructorDecl::addSelectorSelf(const std::string& name)
{
  d_ctor->addArg(name, DatatypeSelfType());
}

std::string DatatypeConstructorDecl::toString() const
{
  std::stringstream ss;
  ss << *d_ctor;
  return ss.str();
}

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
const CVC4::DatatypeConstructor&
DatatypeConstructorDecl::getDatatypeConstructor(void) const
{
  return *d_ctor;
}

std::ostream& operator<<(std::ostream& out,
                         const DatatypeConstructorDecl& ctordecl)
{
  out << ctordecl.toString();
  return out;
}

std::ostream& operator<<(std::ostream& out,
                         const std::vector<DatatypeConstructorDecl>& vector)
{
  container_to_stream(out, vector);
  return out;
}

/* DatatypeDecl ------------------------------------------------------------- */

DatatypeDecl::DatatypeDecl() : d_solver(nullptr), d_dtype(nullptr) {}

DatatypeDecl::DatatypeDecl(const Solver* slv,
                           const std::string& name,
                           bool isCoDatatype)
    : d_solver(slv),
      d_dtype(new CVC4::Datatype(slv->getExprManager(), name, isCoDatatype))
{
}

DatatypeDecl::DatatypeDecl(const Solver* slv,
                           const std::string& name,
                           Sort param,
                           bool isCoDatatype)
    : d_solver(slv),
      d_dtype(new CVC4::Datatype(slv->getExprManager(),
                                 name,
                                 std::vector<Type>{*param.d_type},
                                 isCoDatatype))
{
}

DatatypeDecl::DatatypeDecl(const Solver* slv,
                           const std::string& name,
                           const std::vector<Sort>& params,
                           bool isCoDatatype)
    : d_solver(slv)
{
  std::vector<Type> tparams;
  for (const Sort& p : params)
  {
    tparams.push_back(*p.d_type);
  }
  d_dtype = std::shared_ptr<CVC4::Datatype>(
      new CVC4::Datatype(slv->getExprManager(), name, tparams, isCoDatatype));
}

bool DatatypeDecl::isNullHelper() const { return !d_dtype; }

DatatypeDecl::~DatatypeDecl() {}

void DatatypeDecl::addConstructor(const DatatypeConstructorDecl& ctor)
{
  CVC4_API_CHECK_NOT_NULL;
  d_dtype->addConstructor(*ctor.d_ctor);
}

size_t DatatypeDecl::getNumConstructors() const
{
  CVC4_API_CHECK_NOT_NULL;
  return d_dtype->getNumConstructors();
}

bool DatatypeDecl::isParametric() const
{
  CVC4_API_CHECK_NOT_NULL;
  return d_dtype->isParametric();
}

std::string DatatypeDecl::toString() const
{
  CVC4_API_CHECK_NOT_NULL;
  std::stringstream ss;
  ss << *d_dtype;
  return ss.str();
}

std::string DatatypeDecl::getName() const
{
  CVC4_API_CHECK_NOT_NULL;
  return d_dtype->getName();
}

bool DatatypeDecl::isNull() const { return isNullHelper(); }

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
CVC4::Datatype& DatatypeDecl::getDatatype(void) const { return *d_dtype; }

std::ostream& operator<<(std::ostream& out, const DatatypeDecl& dtdecl)
{
  out << dtdecl.toString();
  return out;
}

/* DatatypeSelector --------------------------------------------------------- */

DatatypeSelector::DatatypeSelector() : d_solver(nullptr), d_stor(nullptr) {}

DatatypeSelector::DatatypeSelector(const Solver* slv,
                                   const CVC4::DatatypeConstructorArg& stor)
    : d_solver(slv), d_stor(new CVC4::DatatypeConstructorArg(stor))
{
  CVC4_API_CHECK(d_stor->isResolved()) << "Expected resolved datatype selector";
}

DatatypeSelector::~DatatypeSelector() {}

std::string DatatypeSelector::getName() const { return d_stor->getName(); }

Term DatatypeSelector::getSelectorTerm() const
{
  Term sel = Term(d_solver, d_stor->getSelector());
  return sel;
}

Sort DatatypeSelector::getRangeSort() const
{
  return Sort(d_solver, d_stor->getRangeType());
}

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

DatatypeConstructor::DatatypeConstructor() : d_solver(nullptr), d_ctor(nullptr)
{
}

DatatypeConstructor::DatatypeConstructor(const Solver* slv,
                                         const CVC4::DatatypeConstructor& ctor)
    : d_solver(slv), d_ctor(new CVC4::DatatypeConstructor(ctor))
{
  CVC4_API_CHECK(d_ctor->isResolved())
      << "Expected resolved datatype constructor";
}

DatatypeConstructor::~DatatypeConstructor() {}

std::string DatatypeConstructor::getName() const { return d_ctor->getName(); }

Term DatatypeConstructor::getConstructorTerm() const
{
  Term ctor = Term(d_solver, d_ctor->getConstructor());
  return ctor;
}

Term DatatypeConstructor::getSpecializedConstructorTerm(Sort retSort) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  
  NodeManager* nm = d_solver->getNodeManager();
  Node ret = nm->mkNode(kind::APPLY_TYPE_ASCRIPTION,
                           nm->mkConst(AscriptionType(
                               d_ctor
                                   ->getSpecializedConstructorType(
                                       retSort.getType()))),
                           d_ctor->getConstructor());
  (void)ret.getType(true); /* kick off type checking */
  // apply type ascription to the operator
  Term sctor =
      api::Term(d_solver,
                ret);
  return sctor;
  
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term DatatypeConstructor::getTesterTerm() const
{
  Term tst = Term(d_solver, d_ctor->getTester());
  return tst;
}

size_t DatatypeConstructor::getNumSelectors() const
{
  return d_ctor->getNumArgs();
}

DatatypeSelector DatatypeConstructor::operator[](size_t index) const
{
  return DatatypeSelector(d_solver, (*d_ctor)[index]);
}

DatatypeSelector DatatypeConstructor::operator[](const std::string& name) const
{
  return getSelectorForName(name);
}

DatatypeSelector DatatypeConstructor::getSelector(const std::string& name) const
{
  return getSelectorForName(name);
}

Term DatatypeConstructor::getSelectorTerm(const std::string& name) const
{
  DatatypeSelector sel = getSelector(name);
  return sel.getSelectorTerm();
}

DatatypeConstructor::const_iterator DatatypeConstructor::begin() const
{
  return DatatypeConstructor::const_iterator(d_solver, *d_ctor, true);
}

DatatypeConstructor::const_iterator DatatypeConstructor::end() const
{
  return DatatypeConstructor::const_iterator(d_solver, *d_ctor, false);
}

DatatypeConstructor::const_iterator::const_iterator(
    const Solver* slv, const CVC4::DatatypeConstructor& ctor, bool begin)
{
  d_solver = slv;
  d_int_stors = ctor.getArgs();

  const std::vector<CVC4::DatatypeConstructorArg>* sels =
      static_cast<const std::vector<CVC4::DatatypeConstructorArg>*>(
          d_int_stors);
  for (const auto& s : *sels)
  {
    /* Can not use emplace_back here since constructor is private. */
    d_stors.push_back(DatatypeSelector(d_solver, s));
  }
  d_idx = begin ? 0 : sels->size();
}

DatatypeConstructor::const_iterator::const_iterator()
    : d_solver(nullptr), d_int_stors(nullptr), d_idx(0)
{
}

DatatypeConstructor::const_iterator&
DatatypeConstructor::const_iterator::operator=(
    const DatatypeConstructor::const_iterator& it)
{
  d_solver = it.d_solver;
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

DatatypeConstructor::const_iterator&
DatatypeConstructor::const_iterator::operator++()
{
  ++d_idx;
  return *this;
}

DatatypeConstructor::const_iterator
DatatypeConstructor::const_iterator::operator++(int)
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
const CVC4::DatatypeConstructor& DatatypeConstructor::getDatatypeConstructor(
    void) const
{
  return *d_ctor;
}

DatatypeSelector DatatypeConstructor::getSelectorForName(
    const std::string& name) const
{
  bool foundSel = false;
  size_t index = 0;
  for (size_t i = 0, nsels = getNumSelectors(); i < nsels; i++)
  {
    if ((*d_ctor)[i].getName() == name)
    {
      index = i;
      foundSel = true;
      break;
    }
  }
  CVC4_API_CHECK(foundSel) << "No selector " << name << " for constructor "
                           << getName() << " exists";
  return DatatypeSelector(d_solver, (*d_ctor)[index]);
}

std::ostream& operator<<(std::ostream& out, const DatatypeConstructor& ctor)
{
  out << ctor.toString();
  return out;
}

/* Datatype ----------------------------------------------------------------- */

Datatype::Datatype(const Solver* slv, const CVC4::Datatype& dtype)
    : d_solver(slv), d_dtype(new CVC4::Datatype(dtype))
{
  CVC4_API_CHECK(d_dtype->isResolved()) << "Expected resolved datatype";
}

Datatype::Datatype() : d_solver(nullptr), d_dtype(nullptr) {}

Datatype::~Datatype() {}

DatatypeConstructor Datatype::operator[](size_t idx) const
{
  CVC4_API_CHECK(idx < getNumConstructors()) << "Index out of bounds.";
  return DatatypeConstructor(d_solver, (*d_dtype)[idx]);
}

DatatypeConstructor Datatype::operator[](const std::string& name) const
{
  return getConstructorForName(name);
}

DatatypeConstructor Datatype::getConstructor(const std::string& name) const
{
  return getConstructorForName(name);
}

Term Datatype::getConstructorTerm(const std::string& name) const
{
  DatatypeConstructor ctor = getConstructor(name);
  return ctor.getConstructorTerm();
}

std::string Datatype::getName() const { return d_dtype->getName(); }

size_t Datatype::getNumConstructors() const
{
  return d_dtype->getNumConstructors();
}

bool Datatype::isParametric() const { return d_dtype->isParametric(); }
bool Datatype::isCodatatype() const { return d_dtype->isCodatatype(); }

bool Datatype::isTuple() const { return d_dtype->isTuple(); }

bool Datatype::isRecord() const { return d_dtype->isRecord(); }

bool Datatype::isFinite() const { return d_dtype->isFinite(); }
bool Datatype::isWellFounded() const { return d_dtype->isWellFounded(); }
bool Datatype::hasNestedRecursion() const
{
  return d_dtype->hasNestedRecursion();
}

std::string Datatype::toString() const { return d_dtype->getName(); }

Datatype::const_iterator Datatype::begin() const
{
  return Datatype::const_iterator(d_solver, *d_dtype, true);
}

Datatype::const_iterator Datatype::end() const
{
  return Datatype::const_iterator(d_solver, *d_dtype, false);
}

// !!! This is only temporarily available until the parser is fully migrated
// to the new API. !!!
const CVC4::Datatype& Datatype::getDatatype(void) const { return *d_dtype; }

DatatypeConstructor Datatype::getConstructorForName(
    const std::string& name) const
{
  bool foundCons = false;
  size_t index = 0;
  for (size_t i = 0, ncons = getNumConstructors(); i < ncons; i++)
  {
    if ((*d_dtype)[i].getName() == name)
    {
      index = i;
      foundCons = true;
      break;
    }
  }
  CVC4_API_CHECK(foundCons) << "No constructor " << name << " for datatype "
                            << getName() << " exists";
  return DatatypeConstructor(d_solver, (*d_dtype)[index]);
}

Datatype::const_iterator::const_iterator(const Solver* slv,
                                         const CVC4::Datatype& dtype,
                                         bool begin)
    : d_solver(slv), d_int_ctors(dtype.getConstructors())
{
  const std::vector<CVC4::DatatypeConstructor>* cons =
      static_cast<const std::vector<CVC4::DatatypeConstructor>*>(d_int_ctors);
  for (const auto& c : *cons)
  {
    /* Can not use emplace_back here since constructor is private. */
    d_ctors.push_back(DatatypeConstructor(d_solver, c));
  }
  d_idx = begin ? 0 : cons->size();
}

Datatype::const_iterator::const_iterator()
    : d_solver(nullptr), d_int_ctors(nullptr), d_idx(0)
{
}

Datatype::const_iterator& Datatype::const_iterator::operator=(
    const Datatype::const_iterator& it)
{
  d_solver = it.d_solver;
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
/* Grammar                                                                    */
/* -------------------------------------------------------------------------- */

Grammar::Grammar()
    : d_solver(nullptr),
      d_sygusVars(),
      d_ntSyms(),
      d_ntsToTerms(0),
      d_allowConst(),
      d_allowVars(),
      d_isResolved(false)
{
}

Grammar::Grammar(const Solver* slv,
                 const std::vector<Term>& sygusVars,
                 const std::vector<Term>& ntSymbols)
    : d_solver(slv),
      d_sygusVars(sygusVars),
      d_ntSyms(ntSymbols),
      d_ntsToTerms(ntSymbols.size()),
      d_allowConst(),
      d_allowVars(),
      d_isResolved(false)
{
  for (Term ntsymbol : d_ntSyms)
  {
    d_ntsToTerms.emplace(ntsymbol, std::vector<Term>());
  }
}

void Grammar::addRule(Term ntSymbol, Term rule)
{
  CVC4_API_CHECK(!d_isResolved) << "Grammar cannot be modified after passing "
                                   "it as an argument to synthFun/synthInv";
  CVC4_API_ARG_CHECK_NOT_NULL(ntSymbol);
  CVC4_API_ARG_CHECK_NOT_NULL(rule);
  CVC4_API_ARG_CHECK_EXPECTED(
      d_ntsToTerms.find(ntSymbol) != d_ntsToTerms.cend(), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  CVC4_API_CHECK(ntSymbol.d_node->getType() == rule.d_node->getType())
      << "Expected ntSymbol and rule to have the same sort";

  d_ntsToTerms[ntSymbol].push_back(rule);
}

void Grammar::addRules(Term ntSymbol, std::vector<Term> rules)
{
  CVC4_API_CHECK(!d_isResolved) << "Grammar cannot be modified after passing "
                                   "it as an argument to synthFun/synthInv";
  CVC4_API_ARG_CHECK_NOT_NULL(ntSymbol);
  CVC4_API_ARG_CHECK_EXPECTED(
      d_ntsToTerms.find(ntSymbol) != d_ntsToTerms.cend(), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";

  for (size_t i = 0, n = rules.size(); i < n; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !rules[i].isNull(), "parameter rule", rules[i], i)
        << "non-null term";
    CVC4_API_CHECK(ntSymbol.d_node->getType() == rules[i].d_node->getType())
        << "Expected ntSymbol and rule at index " << i
        << " to have the same sort";
  }

  d_ntsToTerms[ntSymbol].insert(
      d_ntsToTerms[ntSymbol].cend(), rules.cbegin(), rules.cend());
}

void Grammar::addAnyConstant(Term ntSymbol)
{
  CVC4_API_CHECK(!d_isResolved) << "Grammar cannot be modified after passing "
                                   "it as an argument to synthFun/synthInv";
  CVC4_API_ARG_CHECK_NOT_NULL(ntSymbol);
  CVC4_API_ARG_CHECK_EXPECTED(
      d_ntsToTerms.find(ntSymbol) != d_ntsToTerms.cend(), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";

  d_allowConst.insert(ntSymbol);
}

void Grammar::addAnyVariable(Term ntSymbol)
{
  CVC4_API_CHECK(!d_isResolved) << "Grammar cannot be modified after passing "
                                   "it as an argument to synthFun/synthInv";
  CVC4_API_ARG_CHECK_NOT_NULL(ntSymbol);
  CVC4_API_ARG_CHECK_EXPECTED(
      d_ntsToTerms.find(ntSymbol) != d_ntsToTerms.cend(), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";

  d_allowVars.insert(ntSymbol);
}

/**
 * this function concatinates the outputs of calling f on each element between
 * first and last, seperated by sep.
 * @param first the beginning of the range
 * @param last the end of the range
 * @param f the function to call on each element in the range, its output must
 *          be overloaded for operator<<
 * @param sep the string to add between successive calls to f
 */
template <typename Iterator, typename Function>
std::string join(Iterator first, Iterator last, Function f, std::string sep)
{
  std::stringstream ss;
  Iterator i = first;

  if (i != last)
  {
    ss << f(*i);
    ++i;
  }

  while (i != last)
  {
    ss << sep << f(*i);
    ++i;
  }

  return ss.str();
}

std::string Grammar::toString() const
{
  std::stringstream ss;
  ss << "  ("  // pre-declaration
     << join(
            d_ntSyms.cbegin(),
            d_ntSyms.cend(),
            [](const Term& t) {
              std::stringstream s;
              s << '(' << t << ' ' << t.getSort() << ')';
              return s.str();
            },
            " ")
     << ")\n  ("  // grouped rule listing
     << join(
            d_ntSyms.cbegin(),
            d_ntSyms.cend(),
            [this](const Term& t) {
              bool allowConst = d_allowConst.find(t) != d_allowConst.cend(),
                   allowVars = d_allowVars.find(t) != d_allowVars.cend();
              const std::vector<Term>& rules = d_ntsToTerms.at(t);
              std::stringstream s;
              s << '(' << t << ' ' << t.getSort() << " ("
                << (allowConst ? "(Constant " + t.getSort().toString() + ")"
                               : "")
                << (allowConst && allowVars ? " " : "")
                << (allowVars ? "(Var " + t.getSort().toString() + ")" : "")
                << ((allowConst || allowVars) && !rules.empty() ? " " : "")
                << join(
                       rules.cbegin(),
                       rules.cend(),
                       [](const Term& rule) { return rule.toString(); },
                       " ")
                << "))";
              return s.str();
            },
            "\n   ")
     << ')';

  return ss.str();
}

Sort Grammar::resolve()
{
  d_isResolved = true;

  Term bvl;

  if (!d_sygusVars.empty())
  {
    bvl = Term(d_solver,
               d_solver->getExprManager()->mkExpr(
                   CVC4::kind::BOUND_VAR_LIST, termVectorToExprs(d_sygusVars)));
  }

  std::unordered_map<Term, Sort, TermHashFunction> ntsToUnres(d_ntSyms.size());

  for (Term ntsymbol : d_ntSyms)
  {
    // make the unresolved type, used for referencing the final version of
    // the ntsymbol's datatype
    ntsToUnres[ntsymbol] =
        Sort(d_solver, d_solver->getExprManager()->mkSort(ntsymbol.toString()));
  }

  std::vector<CVC4::Datatype> datatypes;
  std::set<Type> unresTypes;

  datatypes.reserve(d_ntSyms.size());

  for (const Term& ntSym : d_ntSyms)
  {
    // make the datatype, which encodes terms generated by this non-terminal
    DatatypeDecl dtDecl(d_solver, ntSym.toString());

    for (const Term& consTerm : d_ntsToTerms[ntSym])
    {
      addSygusConstructorTerm(dtDecl, consTerm, ntsToUnres);
    }

    if (d_allowVars.find(ntSym) != d_allowVars.cend())
    {
      addSygusConstructorVariables(
          dtDecl, Sort(d_solver, ntSym.d_node->getType().toType()));
    }

    bool aci = d_allowConst.find(ntSym) != d_allowConst.end();
    Type btt = ntSym.d_node->getType().toType();
    dtDecl.d_dtype->setSygus(btt, bvl.d_node->toExpr(), aci, false);

    // We can be in a case where the only rule specified was (Variable T)
    // and there are no variables of type T, in which case this is a bogus
    // grammar. This results in the error below.
    CVC4_API_CHECK(dtDecl.d_dtype->getNumConstructors() != 0)
        << "Grouped rule listing for " << *dtDecl.d_dtype
        << " produced an empty rule list";

    datatypes.push_back(*dtDecl.d_dtype);
    unresTypes.insert(*ntsToUnres[ntSym].d_type);
  }

  std::vector<DatatypeType> datatypeTypes =
      d_solver->getExprManager()->mkMutualDatatypeTypes(
          datatypes, unresTypes, ExprManager::DATATYPE_FLAG_PLACEHOLDER);

  // return is the first datatype
  return Sort(d_solver, datatypeTypes[0]);
}

void Grammar::addSygusConstructorTerm(
    DatatypeDecl& dt,
    Term term,
    const std::unordered_map<Term, Sort, TermHashFunction>& ntsToUnres) const
{
  // At this point, we should know that dt is well founded, and that its
  // builtin sygus operators are well-typed.
  // Now, purify each occurrence of a non-terminal symbol in term, replace by
  // free variables. These become arguments to constructors. Notice we must do
  // a tree traversal in this function, since unique paths to the same term
  // should be treated as distinct terms.
  // Notice that let expressions are forbidden in the input syntax of term, so
  // this does not lead to exponential behavior with respect to input size.
  std::vector<Term> args;
  std::vector<Sort> cargs;
  Term op = purifySygusGTerm(term, args, cargs, ntsToUnres);
  std::stringstream ssCName;
  ssCName << op.getKind();
  if (!args.empty())
  {
    Term lbvl = Term(d_solver,
                     d_solver->getExprManager()->mkExpr(
                         CVC4::kind::BOUND_VAR_LIST, termVectorToExprs(args)));
    // its operator is a lambda
    op = Term(
        d_solver,
        d_solver->getExprManager()->mkExpr(
            CVC4::kind::LAMBDA, {lbvl.d_node->toExpr(), op.d_node->toExpr()}));
  }
  dt.d_dtype->addSygusConstructor(
      op.d_node->toExpr(), ssCName.str(), sortVectorToTypes(cargs));
}

Term Grammar::purifySygusGTerm(
    Term term,
    std::vector<Term>& args,
    std::vector<Sort>& cargs,
    const std::unordered_map<Term, Sort, TermHashFunction>& ntsToUnres) const
{
  std::unordered_map<Term, Sort, TermHashFunction>::const_iterator itn =
      ntsToUnres.find(term);
  if (itn != ntsToUnres.cend())
  {
    Term ret =
        Term(d_solver,
             d_solver->getNodeManager()->mkBoundVar(term.d_node->getType()));
    args.push_back(ret);
    cargs.push_back(itn->second);
    return ret;
  }
  std::vector<Term> pchildren;
  bool childChanged = false;
  for (unsigned i = 0, nchild = term.d_node->getNumChildren(); i < nchild; i++)
  {
    Term ptermc = purifySygusGTerm(
        Term(d_solver, (*term.d_node)[i]), args, cargs, ntsToUnres);
    pchildren.push_back(ptermc);
    childChanged =
        childChanged || ptermc.d_node->toExpr() != (term.d_node->toExpr())[i];
  }
  if (!childChanged)
  {
    return term;
  }

  Node nret;

  if (term.d_node->getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    // it's an indexed operator so we should provide the op
    NodeBuilder<> nb(term.d_node->getKind());
    nb << term.d_node->getOperator();
    nb.append(termVectorToNodes(pchildren));
    nret = nb.constructNode();
  }
  else
  {
    nret = d_solver->getNodeManager()->mkNode(term.d_node->getKind(),
                                              termVectorToNodes(pchildren));
  }

  return Term(d_solver, nret);
}

void Grammar::addSygusConstructorVariables(DatatypeDecl& dt, Sort sort) const
{
  Assert(!sort.isNull());
  // each variable of appropriate type becomes a sygus constructor in dt.
  for (unsigned i = 0, size = d_sygusVars.size(); i < size; i++)
  {
    Term v = d_sygusVars[i];
    if (v.d_node->getType().toType() == *sort.d_type)
    {
      std::stringstream ss;
      ss << v;
      std::vector<Sort> cargs;
      dt.d_dtype->addSygusConstructor(
          v.d_node->toExpr(), ss.str(), sortVectorToTypes(cargs));
    }
  }
}

std::ostream& operator<<(std::ostream& out, const Grammar& g)
{
  return out << g.toString();
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
  d_exprMgr.reset(new ExprManager);
  d_smtEngine.reset(new SmtEngine(d_exprMgr.get(), opts));
  d_smtEngine->setSolver(this);
  Options& o = d_smtEngine->getOptions();
  d_rng.reset(new Random(o[options::seed]));
}

Solver::~Solver() {}

/* Helpers                                                                    */
/* -------------------------------------------------------------------------- */

/* Split out to avoid nested API calls (problematic with API tracing).        */
/* .......................................................................... */

template <typename T>
Term Solver::mkValHelper(T t) const
{
  NodeManagerScope scope(getNodeManager());
  Node res = getNodeManager()->mkConst(t);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
}

Term Solver::mkRealFromStrHelper(const std::string& s) const
{
  /* CLN and GMP handle this case differently, CLN interprets it as 0, GMP
   * throws an std::invalid_argument exception. For consistency, we treat it
   * as invalid. */
  CVC4_API_ARG_CHECK_EXPECTED(s != ".", s)
      << "a string representing an integer, real or rational value.";

  CVC4::Rational r = s.find('/') != std::string::npos
                         ? CVC4::Rational(s)
                         : CVC4::Rational::fromDecimal(s);
  return mkValHelper<CVC4::Rational>(r);
}

Term Solver::mkBVFromIntHelper(uint32_t size, uint64_t val) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(size > 0, size) << "a bit-width > 0";

  return mkValHelper<CVC4::BitVector>(CVC4::BitVector(size, val));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkBVFromStrHelper(const std::string& s, uint32_t base) const
{
  CVC4_API_ARG_CHECK_EXPECTED(!s.empty(), s) << "a non-empty string";
  CVC4_API_ARG_CHECK_EXPECTED(base == 2 || base == 10 || base == 16, base)
      << "base 2, 10, or 16";

  return mkValHelper<CVC4::BitVector>(CVC4::BitVector(s, base));
}

Term Solver::mkBVFromStrHelper(uint32_t size,
                               const std::string& s,
                               uint32_t base) const
{
  CVC4_API_ARG_CHECK_EXPECTED(!s.empty(), s) << "a non-empty string";
  CVC4_API_ARG_CHECK_EXPECTED(base == 2 || base == 10 || base == 16, base)
      << "base 2, 10, or 16";

  Integer val(s, base);

  if (val.strictlyNegative())
  {
    CVC4_API_CHECK(val >= -Integer("2", 10).pow(size - 1))
        << "Overflow in bitvector construction (specified bitvector size "
        << size << " too small to hold value " << s << ")";
  }
  else
  {
    CVC4_API_CHECK(val.modByPow2(size) == val)
        << "Overflow in bitvector construction (specified bitvector size "
        << size << " too small to hold value " << s << ")";
  }

  return mkValHelper<CVC4::BitVector>(CVC4::BitVector(size, val));
}

Term Solver::mkCharFromStrHelper(const std::string& s) const
{
  CVC4_API_CHECK(s.find_first_not_of("0123456789abcdefABCDEF", 0)
                     == std::string::npos
                 && s.size() <= 5 && s.size() > 0)
      << "Unexpected string for hexidecimal character " << s;
  uint32_t val = static_cast<uint32_t>(std::stoul(s, 0, 16));
  CVC4_API_CHECK(val < String::num_codes())
      << "Not a valid code point for hexidecimal character " << s;
  std::vector<unsigned> cpts;
  cpts.push_back(val);
  return mkValHelper<CVC4::String>(CVC4::String(cpts));
}

Term Solver::mkTermFromKind(Kind kind) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK_EXPECTED(
      kind == PI || kind == REGEXP_EMPTY || kind == REGEXP_SIGMA, kind)
      << "PI or REGEXP_EMPTY or REGEXP_SIGMA";

  Expr res;
  if (kind == REGEXP_EMPTY || kind == REGEXP_SIGMA)
  {
    CVC4::Kind k = extToIntKind(kind);
    Assert(isDefinedIntKind(k));
    res = d_exprMgr->mkExpr(k, std::vector<Expr>());
  }
  else
  {
    Assert(kind == PI);
    res = d_exprMgr->mkNullaryOperator(d_exprMgr->realType(), CVC4::kind::PI);
  }
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkTermHelper(Kind kind, const std::vector<Term>& children) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  for (size_t i = 0, size = children.size(); i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !children[i].isNull(), "child term", children[i], i)
        << "non-null term";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == children[i].d_solver, "child term", children[i], i)
        << "a child term associated to this solver object";
  }

  std::vector<Expr> echildren = termVectorToExprs(children);
  CVC4::Kind k = extToIntKind(kind);
  Assert(isDefinedIntKind(k))
      << "Not a defined internal kind : " << k << " " << kind;

  Expr res;
  if (echildren.size() > 2)
  {
    if (kind == INTS_DIVISION || kind == XOR || kind == MINUS
        || kind == DIVISION || kind == BITVECTOR_XNOR || kind == HO_APPLY)
    {
      // left-associative, but CVC4 internally only supports 2 args
      res = d_exprMgr->mkLeftAssociative(k, echildren);
    }
    else if (kind == IMPLIES)
    {
      // right-associative, but CVC4 internally only supports 2 args
      res = d_exprMgr->mkRightAssociative(k, echildren);
    }
    else if (kind == EQUAL || kind == LT || kind == GT || kind == LEQ
             || kind == GEQ)
    {
      // "chainable", but CVC4 internally only supports 2 args
      res = d_exprMgr->mkChain(k, echildren);
    }
    else if (kind::isAssociative(k))
    {
      // mkAssociative has special treatment for associative operators with lots
      // of children
      res = d_exprMgr->mkAssociative(k, echildren);
    }
    else
    {
      // default case, must check kind
      checkMkTerm(kind, children.size());
      res = d_exprMgr->mkExpr(k, echildren);
    }
  }
  else if (kind::isAssociative(k))
  {
    // associative case, same as above
    res = d_exprMgr->mkAssociative(k, echildren);
  }
  else
  {
    // default case, same as above
    checkMkTerm(kind, children.size());
    res = d_exprMgr->mkExpr(k, echildren);
  }

  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

std::vector<Sort> Solver::mkDatatypeSortsInternal(
    std::vector<DatatypeDecl>& dtypedecls,
    std::set<Sort>& unresolvedSorts) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;

  std::vector<CVC4::Datatype> datatypes;
  for (size_t i = 0, ndts = dtypedecls.size(); i < ndts; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(this == dtypedecls[i].d_solver,
                                         "datatype declaration",
                                         dtypedecls[i],
                                         i)
        << "a datatype declaration associated to this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(dtypedecls[i].getNumConstructors() > 0,
                                         "datatype declaration",
                                         dtypedecls[i],
                                         i)
        << "a datatype declaration with at least one constructor";
    datatypes.push_back(dtypedecls[i].getDatatype());
  }
  for (auto& sort : unresolvedSorts)
  {
    CVC4_API_SOLVER_CHECK_SORT(sort);
  }
  std::set<Type> utypes = sortSetToTypes(unresolvedSorts);
  std::vector<CVC4::DatatypeType> dtypes =
      d_exprMgr->mkMutualDatatypeTypes(datatypes, utypes);
  std::vector<Sort> retTypes;
  for (CVC4::DatatypeType t : dtypes)
  {
    retTypes.push_back(Sort(this, t));
  }
  return retTypes;

  CVC4_API_SOLVER_TRY_CATCH_END;
}

/* Helpers for converting vectors.                                            */
/* .......................................................................... */

std::vector<Type> Solver::sortVectorToTypes(
    const std::vector<Sort>& sorts) const
{
  std::vector<Type> res;
  for (const Sort& s : sorts)
  {
    CVC4_API_SOLVER_CHECK_SORT(s);
    res.push_back(*s.d_type);
  }
  return res;
}

std::vector<Expr> Solver::termVectorToExprs(
    const std::vector<Term>& terms) const
{
  std::vector<Expr> res;
  for (const Term& t : terms)
  {
    CVC4_API_SOLVER_CHECK_TERM(t);
    res.push_back(t.d_node->toExpr());
  }
  return res;
}

/* Helpers for mkTerm checks.                                                 */
/* .......................................................................... */

void Solver::checkMkTerm(Kind kind, uint32_t nchildren) const
{
  CVC4_API_KIND_CHECK(kind);
  Assert(isDefinedIntKind(extToIntKind(kind)));
  const CVC4::kind::MetaKind mk = kind::metaKindOf(extToIntKind(kind));
  CVC4_API_KIND_CHECK_EXPECTED(
      mk == kind::metakind::PARAMETERIZED || mk == kind::metakind::OPERATOR,
      kind)
      << "Only operator-style terms are created with mkTerm(), "
         "to create variables, constants and values see mkVar(), mkConst() "
         "and the respective theory-specific functions to create values, "
         "e.g., mkBitVector().";
  CVC4_API_KIND_CHECK_EXPECTED(
      nchildren >= minArity(kind) && nchildren <= maxArity(kind), kind)
      << "Terms with kind " << kindToString(kind) << " must have at least "
      << minArity(kind) << " children and at most " << maxArity(kind)
      << " children (the one under construction has " << nchildren << ")";
}

/* Sorts Handling                                                             */
/* -------------------------------------------------------------------------- */

Sort Solver::getNullSort(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return Sort(this, Type());
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::getBooleanSort(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return Sort(this, d_exprMgr->booleanType());
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::getIntegerSort(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return Sort(this, d_exprMgr->integerType());
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::getRealSort(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return Sort(this, d_exprMgr->realType());
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::getRegExpSort(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return Sort(this, d_exprMgr->regExpType());
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::getStringSort(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return Sort(this, d_exprMgr->stringType());
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::getRoundingmodeSort(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return Sort(this, d_exprMgr->roundingModeType());
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/* Create sorts ------------------------------------------------------- */

Sort Solver::mkArraySort(Sort indexSort, Sort elemSort) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!indexSort.isNull(), indexSort)
      << "non-null index sort";
  CVC4_API_ARG_CHECK_EXPECTED(!elemSort.isNull(), elemSort)
      << "non-null element sort";
  CVC4_API_SOLVER_CHECK_SORT(indexSort);
  CVC4_API_SOLVER_CHECK_SORT(elemSort);

  return Sort(this,
              d_exprMgr->mkArrayType(*indexSort.d_type, *elemSort.d_type));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::mkBitVectorSort(uint32_t size) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(size > 0, size) << "size > 0";

  return Sort(this, d_exprMgr->mkBitVectorType(size));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::mkFloatingPointSort(uint32_t exp, uint32_t sig) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(exp > 0, exp) << "exponent size > 0";
  CVC4_API_ARG_CHECK_EXPECTED(sig > 0, sig) << "significand size > 0";

  return Sort(this, d_exprMgr->mkFloatingPointType(exp, sig));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::mkDatatypeSort(DatatypeDecl dtypedecl) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(this == dtypedecl.d_solver)
      << "Given datatype declaration is not associated with this solver";
  CVC4_API_ARG_CHECK_EXPECTED(dtypedecl.getNumConstructors() > 0, dtypedecl)
      << "a datatype declaration with at least one constructor";

  return Sort(this, d_exprMgr->mkDatatypeType(*dtypedecl.d_dtype));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

std::vector<Sort> Solver::mkDatatypeSorts(
    std::vector<DatatypeDecl>& dtypedecls) const
{
  std::set<Sort> unresolvedSorts;
  return mkDatatypeSortsInternal(dtypedecls, unresolvedSorts);
}

std::vector<Sort> Solver::mkDatatypeSorts(std::vector<DatatypeDecl>& dtypedecls,
                                          std::set<Sort>& unresolvedSorts) const
{
  return mkDatatypeSortsInternal(dtypedecls, unresolvedSorts);
}

Sort Solver::mkFunctionSort(Sort domain, Sort codomain) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!codomain.isNull(), codomain)
      << "non-null codomain sort";
  CVC4_API_SOLVER_CHECK_SORT(domain);
  CVC4_API_SOLVER_CHECK_SORT(codomain);
  CVC4_API_ARG_CHECK_EXPECTED(domain.isFirstClass(), domain)
      << "first-class sort as domain sort for function sort";
  CVC4_API_ARG_CHECK_EXPECTED(codomain.isFirstClass(), codomain)
      << "first-class sort as codomain sort for function sort";
  Assert(!codomain.isFunction()); /* A function sort is not first-class. */

  return Sort(this,
              d_exprMgr->mkFunctionType(*domain.d_type, *codomain.d_type));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::mkFunctionSort(const std::vector<Sort>& sorts, Sort codomain) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(sorts.size() >= 1, sorts)
      << "at least one parameter sort for function sort";
  for (size_t i = 0, size = sorts.size(); i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !sorts[i].isNull(), "parameter sort", sorts[i], i)
        << "non-null sort";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == sorts[i].d_solver, "parameter sort", sorts[i], i)
        << "sort associated to this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        sorts[i].isFirstClass(), "parameter sort", sorts[i], i)
        << "first-class sort as parameter sort for function sort";
  }
  CVC4_API_ARG_CHECK_EXPECTED(!codomain.isNull(), codomain)
      << "non-null codomain sort";
  CVC4_API_SOLVER_CHECK_SORT(codomain);
  CVC4_API_ARG_CHECK_EXPECTED(codomain.isFirstClass(), codomain)
      << "first-class sort as codomain sort for function sort";
  Assert(!codomain.isFunction()); /* A function sort is not first-class. */

  std::vector<Type> argTypes = sortVectorToTypes(sorts);
  return Sort(this, d_exprMgr->mkFunctionType(argTypes, *codomain.d_type));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::mkParamSort(const std::string& symbol) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return Sort(this,
              d_exprMgr->mkSort(symbol, ExprManager::SORT_FLAG_PLACEHOLDER));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::mkPredicateSort(const std::vector<Sort>& sorts) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(sorts.size() >= 1, sorts)
      << "at least one parameter sort for predicate sort";
  for (size_t i = 0, size = sorts.size(); i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !sorts[i].isNull(), "parameter sort", sorts[i], i)
        << "non-null sort";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == sorts[i].d_solver, "parameter sort", sorts[i], i)
        << "sort associated to this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        sorts[i].isFirstClass(), "parameter sort", sorts[i], i)
        << "first-class sort as parameter sort for predicate sort";
  }
  std::vector<Type> types = sortVectorToTypes(sorts);

  return Sort(this, d_exprMgr->mkPredicateType(types));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::mkRecordSort(
    const std::vector<std::pair<std::string, Sort>>& fields) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  std::vector<std::pair<std::string, Type>> f;
  size_t i = 0;
  for (const auto& p : fields)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !p.second.isNull(), "parameter sort", p.second, i)
        << "non-null sort";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == p.second.d_solver, "parameter sort", p.second, i)
        << "sort associated to this solver object";
    i += 1;
    f.emplace_back(p.first, *p.second.d_type);
  }

  return Sort(this, d_exprMgr->mkRecordType(Record(f)));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::mkSetSort(Sort elemSort) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!elemSort.isNull(), elemSort)
      << "non-null element sort";
  CVC4_API_SOLVER_CHECK_SORT(elemSort);

  return Sort(this, d_exprMgr->mkSetType(*elemSort.d_type));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::mkSequenceSort(Sort elemSort) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!elemSort.isNull(), elemSort)
      << "non-null element sort";
  CVC4_API_SOLVER_CHECK_SORT(elemSort);

  return Sort(this, d_exprMgr->mkSequenceType(*elemSort.d_type));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::mkUninterpretedSort(const std::string& symbol) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return Sort(this, d_exprMgr->mkSort(symbol));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::mkSortConstructorSort(const std::string& symbol,
                                   size_t arity) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(arity > 0, arity) << "an arity > 0";

  return Sort(this, d_exprMgr->mkSortConstructor(symbol, arity));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Sort Solver::mkTupleSort(const std::vector<Sort>& sorts) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  for (size_t i = 0, size = sorts.size(); i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !sorts[i].isNull(), "parameter sort", sorts[i], i)
        << "non-null sort";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == sorts[i].d_solver, "parameter sort", sorts[i], i)
        << "sort associated to this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !sorts[i].isFunctionLike(), "parameter sort", sorts[i], i)
        << "non-function-like sort as parameter sort for tuple sort";
  }
  std::vector<Type> types = sortVectorToTypes(sorts);

  return Sort(this, d_exprMgr->mkTupleType(types));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

/* Create consts                                                              */
/* -------------------------------------------------------------------------- */

Term Solver::mkTrue(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return Term(this, d_exprMgr->mkConst<bool>(true));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkFalse(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return Term(this, d_exprMgr->mkConst<bool>(false));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkBoolean(bool val) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return Term(this, d_exprMgr->mkConst<bool>(val));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkPi() const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;

  Expr res =
      d_exprMgr->mkNullaryOperator(d_exprMgr->realType(), CVC4::kind::PI);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkReal(const std::string& s) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return mkRealFromStrHelper(s);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkReal(int64_t val) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return mkValHelper<CVC4::Rational>(CVC4::Rational(val));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkReal(int64_t num, int64_t den) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return mkValHelper<CVC4::Rational>(CVC4::Rational(num, den));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkRegexpEmpty() const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;

  Expr res =
      d_exprMgr->mkExpr(CVC4::kind::REGEXP_EMPTY, std::vector<CVC4::Expr>());
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkRegexpSigma() const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;

  Expr res =
      d_exprMgr->mkExpr(CVC4::kind::REGEXP_SIGMA, std::vector<CVC4::Expr>());
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkEmptySet(Sort s) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(s.isNull() || s.isSet(), s)
      << "null sort or set sort";
  CVC4_API_ARG_CHECK_EXPECTED(s.isNull() || this == s.d_solver, s)
      << "set sort associated to this solver object";

  return mkValHelper<CVC4::EmptySet>(
      CVC4::EmptySet(TypeNode::fromType(*s.d_type)));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkSepNil(Sort sort) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!sort.isNull(), sort) << "non-null sort";
  CVC4_API_SOLVER_CHECK_SORT(sort);

  Expr res = d_exprMgr->mkNullaryOperator(*sort.d_type, CVC4::kind::SEP_NIL);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkString(const std::string& s, bool useEscSequences) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return mkValHelper<CVC4::String>(CVC4::String(s, useEscSequences));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkString(const unsigned char c) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return mkValHelper<CVC4::String>(CVC4::String(std::string(1, c)));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkString(const std::vector<unsigned>& s) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return mkValHelper<CVC4::String>(CVC4::String(s));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkChar(const std::string& s) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return mkCharFromStrHelper(s);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkEmptySequence(Sort sort) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!sort.isNull(), sort) << "non-null sort";
  CVC4_API_SOLVER_CHECK_SORT(sort);

  std::vector<Node> seq;
  Expr res =
      d_exprMgr->mkConst(Sequence(TypeNode::fromType(*sort.d_type), seq));
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkUniverseSet(Sort sort) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!sort.isNull(), sort) << "non-null sort";
  CVC4_API_SOLVER_CHECK_SORT(sort);

  Expr res =
      d_exprMgr->mkNullaryOperator(*sort.d_type, CVC4::kind::UNIVERSE_SET);
  // TODO(#2771): Reenable?
  // (void)res->getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkBitVector(uint32_t size, uint64_t val) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return mkBVFromIntHelper(size, val);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkBitVector(const std::string& s, uint32_t base) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return mkBVFromStrHelper(s, base);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkBitVector(uint32_t size,
                         const std::string& s,
                         uint32_t base) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return mkBVFromStrHelper(size, s, base);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkConstArray(Sort sort, Term val) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_ARG_CHECK_NOT_NULL(sort);
  CVC4_API_ARG_CHECK_NOT_NULL(val);
  CVC4_API_SOLVER_CHECK_SORT(sort);
  CVC4_API_SOLVER_CHECK_TERM(val);
  CVC4_API_CHECK(sort.isArray()) << "Not an array sort.";
  CVC4_API_CHECK(sort.getArrayElementSort().isComparableTo(val.getSort()))
      << "Value does not match element sort.";
  Term res = mkValHelper<CVC4::ArrayStoreAll>(CVC4::ArrayStoreAll(
      TypeNode::fromType(*sort.d_type), Node::fromExpr(val.d_node->toExpr())));
  return res;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkPosInf(uint32_t exp, uint32_t sig) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";

  return mkValHelper<CVC4::FloatingPoint>(
      FloatingPoint::makeInf(FloatingPointSize(exp, sig), false));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkNegInf(uint32_t exp, uint32_t sig) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";

  return mkValHelper<CVC4::FloatingPoint>(
      FloatingPoint::makeInf(FloatingPointSize(exp, sig), true));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkNaN(uint32_t exp, uint32_t sig) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";

  return mkValHelper<CVC4::FloatingPoint>(
      FloatingPoint::makeNaN(FloatingPointSize(exp, sig)));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkPosZero(uint32_t exp, uint32_t sig) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";

  return mkValHelper<CVC4::FloatingPoint>(
      FloatingPoint::makeZero(FloatingPointSize(exp, sig), false));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkNegZero(uint32_t exp, uint32_t sig) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";

  return mkValHelper<CVC4::FloatingPoint>(
      FloatingPoint::makeZero(FloatingPointSize(exp, sig), true));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkRoundingMode(RoundingMode rm) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return mkValHelper<CVC4::RoundingMode>(s_rmodes.at(rm));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkUninterpretedConst(Sort sort, int32_t index) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!sort.isNull(), sort) << "non-null sort";
  CVC4_API_SOLVER_CHECK_SORT(sort);

  return mkValHelper<CVC4::UninterpretedConstant>(
      CVC4::UninterpretedConstant(TypeNode::fromType(*sort.d_type), index));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkAbstractValue(const std::string& index) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!index.empty(), index) << "a non-empty string";

  CVC4::Integer idx(index, 10);
  CVC4_API_ARG_CHECK_EXPECTED(idx > 0, index)
      << "a string representing an integer > 0";
  return Term(this, getNodeManager()->mkConst(CVC4::AbstractValue(idx)));
  // do not call getType(), for abstract values, type can not be computed
  // until it is substituted away
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkAbstractValue(uint64_t index) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(index > 0, index) << "an integer > 0";

  return Term(this,
              getNodeManager()->mkConst(CVC4::AbstractValue(Integer(index))));
  // do not call getType(), for abstract values, type can not be computed
  // until it is substituted away
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkFloatingPoint(uint32_t exp, uint32_t sig, Term val) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";
  CVC4_API_ARG_CHECK_EXPECTED(exp > 0, exp) << "a value > 0";
  CVC4_API_ARG_CHECK_EXPECTED(sig > 0, sig) << "a value > 0";
  uint32_t bw = exp + sig;
  CVC4_API_ARG_CHECK_EXPECTED(bw == val.getSort().getBVSize(), val)
      << "a bit-vector constant with bit-width '" << bw << "'";
  CVC4_API_ARG_CHECK_EXPECTED(!val.isNull(), val) << "non-null term";
  CVC4_API_SOLVER_CHECK_TERM(val);
  CVC4_API_ARG_CHECK_EXPECTED(
      val.getSort().isBitVector() && val.d_node->isConst(), val)
      << "bit-vector constant";

  return mkValHelper<CVC4::FloatingPoint>(
      CVC4::FloatingPoint(exp, sig, val.d_node->getConst<BitVector>()));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

/* Create constants                                                           */
/* -------------------------------------------------------------------------- */

Term Solver::mkConst(Sort sort, const std::string& symbol) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!sort.isNull(), sort) << "non-null sort";
  CVC4_API_SOLVER_CHECK_SORT(sort);

  Expr res = symbol.empty() ? d_exprMgr->mkVar(*sort.d_type)
                            : d_exprMgr->mkVar(symbol, *sort.d_type);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

/* Create variables                                                           */
/* -------------------------------------------------------------------------- */

Term Solver::mkVar(Sort sort, const std::string& symbol) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!sort.isNull(), sort) << "non-null sort";
  CVC4_API_SOLVER_CHECK_SORT(sort);

  Expr res = symbol.empty() ? d_exprMgr->mkBoundVar(*sort.d_type)
                            : d_exprMgr->mkBoundVar(symbol, *sort.d_type);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

/* Create datatype constructor declarations                                   */
/* -------------------------------------------------------------------------- */

DatatypeConstructorDecl Solver::mkDatatypeConstructorDecl(
    const std::string& name)
{
  return DatatypeConstructorDecl(this, name);
}

/* Create datatype declarations                                               */
/* -------------------------------------------------------------------------- */

DatatypeDecl Solver::mkDatatypeDecl(const std::string& name, bool isCoDatatype)
{
  return DatatypeDecl(this, name, isCoDatatype);
}

DatatypeDecl Solver::mkDatatypeDecl(const std::string& name,
                                    Sort param,
                                    bool isCoDatatype)
{
  return DatatypeDecl(this, name, param, isCoDatatype);
}

DatatypeDecl Solver::mkDatatypeDecl(const std::string& name,
                                    const std::vector<Sort>& params,
                                    bool isCoDatatype)
{
  return DatatypeDecl(this, name, params, isCoDatatype);
}

/* Create terms                                                               */
/* -------------------------------------------------------------------------- */

Term Solver::mkTerm(Kind kind) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return mkTermFromKind(kind);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkTerm(Kind kind, Term child) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!child.isNull(), child) << "non-null term";
  CVC4_API_SOLVER_CHECK_TERM(child);
  checkMkTerm(kind, 1);

  Node res = getNodeManager()->mkNode(extToIntKind(kind), *child.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkTerm(Kind kind, Term child1, Term child2) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!child1.isNull(), child1) << "non-null term";
  CVC4_API_ARG_CHECK_EXPECTED(!child2.isNull(), child2) << "non-null term";
  CVC4_API_SOLVER_CHECK_TERM(child1);
  CVC4_API_SOLVER_CHECK_TERM(child2);
  checkMkTerm(kind, 2);

  Node res = getNodeManager()->mkNode(
      extToIntKind(kind), *child1.d_node, *child2.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkTerm(Kind kind, Term child1, Term child2, Term child3) const
{
  // need to use internal term call to check e.g. associative construction
  return mkTermHelper(kind, std::vector<Term>{child1, child2, child3});
}

Term Solver::mkTerm(Kind kind, const std::vector<Term>& children) const
{
  return mkTermHelper(kind, children);
}

Term Solver::mkTerm(Op op) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_OP(op);
  checkMkTerm(op.d_kind, 0);

  Term res;
  if (op.isIndexedHelper())
  {
    const CVC4::Kind int_kind = extToIntKind(op.d_kind);
    res = Term(this, getNodeManager()->mkNode(int_kind, *op.d_node));
  }
  else
  {
    res = mkTermFromKind(op.d_kind);
  }

  (void)res.d_node->getType(true); /* kick off type checking */
  return res;

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkTerm(Op op, Term child) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_OP(op);
  CVC4_API_ARG_CHECK_EXPECTED(!child.isNull(), child) << "non-null term";
  CVC4_API_SOLVER_CHECK_TERM(child);
  checkMkTerm(op.d_kind, 1);

  const CVC4::Kind int_kind = extToIntKind(op.d_kind);
  Node res;
  if (op.isIndexedHelper())
  {
    res = getNodeManager()->mkNode(int_kind, *op.d_node, *child.d_node);
  }
  else
  {
    res = getNodeManager()->mkNode(int_kind, *child.d_node);
  }

  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkTerm(Op op, Term child1, Term child2) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_OP(op);
  CVC4_API_ARG_CHECK_EXPECTED(!child1.isNull(), child1) << "non-null term";
  CVC4_API_ARG_CHECK_EXPECTED(!child2.isNull(), child2) << "non-null term";
  CVC4_API_SOLVER_CHECK_TERM(child1);
  CVC4_API_SOLVER_CHECK_TERM(child2);
  checkMkTerm(op.d_kind, 2);

  const CVC4::Kind int_kind = extToIntKind(op.d_kind);
  Node res;
  if (op.isIndexedHelper())
  {
    res = getNodeManager()->mkNode(
        int_kind, *op.d_node, *child1.d_node, *child2.d_node);
  }
  else
  {
    res = getNodeManager()->mkNode(int_kind, *child1.d_node, *child2.d_node);
  }

  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkTerm(Op op, Term child1, Term child2, Term child3) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_OP(op);
  CVC4_API_ARG_CHECK_EXPECTED(!child1.isNull(), child1) << "non-null term";
  CVC4_API_ARG_CHECK_EXPECTED(!child2.isNull(), child2) << "non-null term";
  CVC4_API_ARG_CHECK_EXPECTED(!child3.isNull(), child3) << "non-null term";
  CVC4_API_SOLVER_CHECK_TERM(child1);
  CVC4_API_SOLVER_CHECK_TERM(child2);
  CVC4_API_SOLVER_CHECK_TERM(child3);
  checkMkTerm(op.d_kind, 3);

  const CVC4::Kind int_kind = extToIntKind(op.d_kind);
  Node res;
  if (op.isIndexedHelper())
  {
    res = getNodeManager()->mkNode(
        int_kind, *op.d_node, *child1.d_node, *child2.d_node, *child3.d_node);
  }
  else
  {
    res = getNodeManager()->mkNode(
        int_kind, *child1.d_node, *child2.d_node, *child3.d_node);
  }

  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkTerm(Op op, const std::vector<Term>& children) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_OP(op);
  checkMkTerm(op.d_kind, children.size());
  for (size_t i = 0, size = children.size(); i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !children[i].isNull(), "child term", children[i], i)
        << "non-null term";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == children[i].d_solver, "child term", children[i], i)
        << "child term associated to this solver object";
  }

  const CVC4::Kind int_kind = extToIntKind(op.d_kind);
  std::vector<Node> echildren = termVectorToNodes(children);
  Node res;
  if (op.isIndexedHelper())
  {
    NodeBuilder<> nb(int_kind);
    nb << *op.d_node;
    nb.append(echildren);
    res = nb.constructNode();
  }
  else
  {
    res = getNodeManager()->mkNode(int_kind, echildren);
  }

  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::mkTuple(const std::vector<Sort>& sorts,
                     const std::vector<Term>& terms) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(sorts.size() == terms.size())
      << "Expected the same number of sorts and elements";
  std::vector<CVC4::Node> args;
  for (size_t i = 0, size = sorts.size(); i < size; i++)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == terms[i].d_solver, "child term", terms[i], i)
        << "child term associated to this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == sorts[i].d_solver, "child sort", sorts[i], i)
        << "child sort associated to this solver object";
    args.push_back(*(ensureTermSort(terms[i], sorts[i])).d_node);
  }

  Sort s = mkTupleSort(sorts);
  Datatype dt = s.getDatatype();
  NodeBuilder<> nb(extToIntKind(APPLY_CONSTRUCTOR));
  nb << *dt[0].getConstructorTerm().d_node;
  nb.append(args);
  Node res = nb.constructNode();
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

/* Create operators                                                           */
/* -------------------------------------------------------------------------- */

Op Solver::mkOp(Kind kind) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(s_indexed_kinds.find(kind) == s_indexed_kinds.end())
      << "Expected a kind for a non-indexed operator.";
  return Op(this, kind);
  CVC4_API_SOLVER_TRY_CATCH_END
}

Op Solver::mkOp(Kind kind, const std::string& arg) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK_EXPECTED((kind == RECORD_UPDATE) || (kind == DIVISIBLE),
                               kind)
      << "RECORD_UPDATE or DIVISIBLE";
  Op res;
  if (kind == RECORD_UPDATE)
  {
    res = Op(this,
             kind,
             *mkValHelper<CVC4::RecordUpdate>(CVC4::RecordUpdate(arg)).d_node);
  }
  else
  {
    /* CLN and GMP handle this case differently, CLN interprets it as 0, GMP
     * throws an std::invalid_argument exception. For consistency, we treat it
     * as invalid. */
    CVC4_API_ARG_CHECK_EXPECTED(arg != ".", arg)
        << "a string representing an integer, real or rational value.";
    res = Op(this,
             kind,
             *mkValHelper<CVC4::Divisible>(CVC4::Divisible(CVC4::Integer(arg)))
                  .d_node);
  }
  return res;

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Op Solver::mkOp(Kind kind, uint32_t arg) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK(kind);

  Op res;
  switch (kind)
  {
    case DIVISIBLE:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::Divisible>(CVC4::Divisible(arg)).d_node);
      break;
    case BITVECTOR_REPEAT:
      res = Op(this,
               kind,
               mkValHelper<CVC4::BitVectorRepeat>(CVC4::BitVectorRepeat(arg))
                   .d_node->toExpr());
      break;
    case BITVECTOR_ZERO_EXTEND:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::BitVectorZeroExtend>(
                    CVC4::BitVectorZeroExtend(arg))
                    .d_node);
      break;
    case BITVECTOR_SIGN_EXTEND:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::BitVectorSignExtend>(
                    CVC4::BitVectorSignExtend(arg))
                    .d_node);
      break;
    case BITVECTOR_ROTATE_LEFT:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::BitVectorRotateLeft>(
                    CVC4::BitVectorRotateLeft(arg))
                    .d_node);
      break;
    case BITVECTOR_ROTATE_RIGHT:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::BitVectorRotateRight>(
                    CVC4::BitVectorRotateRight(arg))
                    .d_node);
      break;
    case INT_TO_BITVECTOR:
      res = Op(
          this,
          kind,
          *mkValHelper<CVC4::IntToBitVector>(CVC4::IntToBitVector(arg)).d_node);
      break;
    case IAND:
      res =
          Op(this, kind, *mkValHelper<CVC4::IntAnd>(CVC4::IntAnd(arg)).d_node);
      break;
    case FLOATINGPOINT_TO_UBV:
      res = Op(
          this,
          kind,
          *mkValHelper<CVC4::FloatingPointToUBV>(CVC4::FloatingPointToUBV(arg))
               .d_node);
      break;
    case FLOATINGPOINT_TO_SBV:
      res = Op(
          this,
          kind,
          *mkValHelper<CVC4::FloatingPointToSBV>(CVC4::FloatingPointToSBV(arg))
               .d_node);
      break;
    case TUPLE_UPDATE:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::TupleUpdate>(CVC4::TupleUpdate(arg)).d_node);
      break;
    case REGEXP_REPEAT:
      res =
          Op(this,
             kind,
             *mkValHelper<CVC4::RegExpRepeat>(CVC4::RegExpRepeat(arg)).d_node);
      break;
    default:
      CVC4_API_KIND_CHECK_EXPECTED(false, kind)
          << "operator kind with uint32_t argument";
  }
  Assert(!res.isNull());
  return res;

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Op Solver::mkOp(Kind kind, uint32_t arg1, uint32_t arg2) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK(kind);

  Op res;
  switch (kind)
  {
    case BITVECTOR_EXTRACT:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::BitVectorExtract>(
                    CVC4::BitVectorExtract(arg1, arg2))
                    .d_node);
      break;
    case FLOATINGPOINT_TO_FP_IEEE_BITVECTOR:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::FloatingPointToFPIEEEBitVector>(
                    CVC4::FloatingPointToFPIEEEBitVector(arg1, arg2))
                    .d_node);
      break;
    case FLOATINGPOINT_TO_FP_FLOATINGPOINT:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::FloatingPointToFPFloatingPoint>(
                    CVC4::FloatingPointToFPFloatingPoint(arg1, arg2))
                    .d_node);
      break;
    case FLOATINGPOINT_TO_FP_REAL:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::FloatingPointToFPReal>(
                    CVC4::FloatingPointToFPReal(arg1, arg2))
                    .d_node);
      break;
    case FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::FloatingPointToFPSignedBitVector>(
                    CVC4::FloatingPointToFPSignedBitVector(arg1, arg2))
                    .d_node);
      break;
    case FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::FloatingPointToFPUnsignedBitVector>(
                    CVC4::FloatingPointToFPUnsignedBitVector(arg1, arg2))
                    .d_node);
      break;
    case FLOATINGPOINT_TO_FP_GENERIC:
      res = Op(this,
               kind,
               *mkValHelper<CVC4::FloatingPointToFPGeneric>(
                    CVC4::FloatingPointToFPGeneric(arg1, arg2))
                    .d_node);
      break;
    case REGEXP_LOOP:
      res = Op(
          this,
          kind,
          *mkValHelper<CVC4::RegExpLoop>(CVC4::RegExpLoop(arg1, arg2)).d_node);
      break;
    default:
      CVC4_API_KIND_CHECK_EXPECTED(false, kind)
          << "operator kind with two uint32_t arguments";
  }
  Assert(!res.isNull());
  return res;

  CVC4_API_SOLVER_TRY_CATCH_END;
}

/* Non-SMT-LIB commands                                                       */
/* -------------------------------------------------------------------------- */

Term Solver::simplify(const Term& term)
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_ARG_CHECK_NOT_NULL(term);
  CVC4_API_SOLVER_CHECK_TERM(term);

  return Term(this, d_smtEngine->simplify(term.d_node->toExpr()));

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Result Solver::checkEntailed(Term term) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(!d_smtEngine->isQueryMade()
                 || d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  CVC4_API_ARG_CHECK_NOT_NULL(term);
  CVC4_API_SOLVER_CHECK_TERM(term);

  CVC4::Result r = d_smtEngine->checkEntailed(term.d_node->toExpr());
  return Result(r);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Result Solver::checkEntailed(const std::vector<Term>& terms) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(!d_smtEngine->isQueryMade()
                 || d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  for (const Term& term : terms)
  {
    CVC4_API_SOLVER_CHECK_TERM(term);
    CVC4_API_ARG_CHECK_NOT_NULL(term);
  }

  std::vector<Expr> exprs = termVectorToExprs(terms);
  CVC4::Result r = d_smtEngine->checkEntailed(exprs);
  return Result(r);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

/* SMT-LIB commands                                                           */
/* -------------------------------------------------------------------------- */

/**
 *  ( assert <term> )
 */
void Solver::assertFormula(Term term) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(term);
  CVC4_API_ARG_CHECK_NOT_NULL(term);
  d_smtEngine->assertFormula(*term.d_node);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( check-sat )
 */
Result Solver::checkSat(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(!d_smtEngine->isQueryMade()
                 || d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  CVC4::Result r = d_smtEngine->checkSat();
  return Result(r);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( check-sat-assuming ( <prop_literal> ) )
 */
Result Solver::checkSatAssuming(Term assumption) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(!d_smtEngine->isQueryMade()
                 || d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  CVC4_API_SOLVER_CHECK_TERM(assumption);
  CVC4::Result r = d_smtEngine->checkSat(assumption.d_node->toExpr());
  return Result(r);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( check-sat-assuming ( <prop_literal>* ) )
 */
Result Solver::checkSatAssuming(const std::vector<Term>& assumptions) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(!d_smtEngine->isQueryMade() || assumptions.size() == 0
                 || d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  for (const Term& term : assumptions)
  {
    CVC4_API_SOLVER_CHECK_TERM(term);
    CVC4_API_ARG_CHECK_NOT_NULL(term);
  }
  std::vector<Expr> eassumptions = termVectorToExprs(assumptions);
  CVC4::Result r = d_smtEngine->checkSat(eassumptions);
  return Result(r);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( declare-datatype <symbol> <datatype_decl> )
 */
Sort Solver::declareDatatype(
    const std::string& symbol,
    const std::vector<DatatypeConstructorDecl>& ctors) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(ctors.size() > 0, ctors)
      << "a datatype declaration with at least one constructor";
  DatatypeDecl dtdecl(this, symbol);
  for (size_t i = 0, size = ctors.size(); i < size; i++)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(this == ctors[i].d_solver,
                                         "datatype constructor declaration",
                                         ctors[i],
                                         i)
        << "datatype constructor declaration associated to this solver object";
    dtdecl.addConstructor(ctors[i]);
  }
  return Sort(this, d_exprMgr->mkDatatypeType(*dtdecl.d_dtype));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( declare-fun <symbol> ( <sort>* ) <sort> )
 */
Term Solver::declareFun(const std::string& symbol,
                        const std::vector<Sort>& sorts,
                        Sort sort) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  for (size_t i = 0, size = sorts.size(); i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == sorts[i].d_solver, "parameter sort", sorts[i], i)
        << "parameter sort associated to this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        sorts[i].isFirstClass(), "parameter sort", sorts[i], i)
        << "first-class sort as parameter sort for function sort";
  }
  CVC4_API_ARG_CHECK_EXPECTED(sort.isFirstClass(), sort)
      << "first-class sort as function codomain sort";
  CVC4_API_SOLVER_CHECK_SORT(sort);
  Assert(!sort.isFunction()); /* A function sort is not first-class. */
  Type type = *sort.d_type;
  if (!sorts.empty())
  {
    std::vector<Type> types = sortVectorToTypes(sorts);
    type = d_exprMgr->mkFunctionType(types, type);
  }
  return Term(this, d_exprMgr->mkVar(symbol, type));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( declare-sort <symbol> <numeral> )
 */
Sort Solver::declareSort(const std::string& symbol, uint32_t arity) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  if (arity == 0) return Sort(this, d_exprMgr->mkSort(symbol));
  return Sort(this, d_exprMgr->mkSortConstructor(symbol, arity));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( define-fun <function_def> )
 */
Term Solver::defineFun(const std::string& symbol,
                       const std::vector<Term>& bound_vars,
                       Sort sort,
                       Term term,
                       bool global) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(sort.isFirstClass(), sort)
      << "first-class sort as codomain sort for function sort";
  std::vector<Type> domain_types;
  for (size_t i = 0, size = bound_vars.size(); i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == bound_vars[i].d_solver, "bound variable", bound_vars[i], i)
        << "bound variable associated to this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        bound_vars[i].d_node->getKind() == CVC4::Kind::BOUND_VARIABLE,
        "bound variable",
        bound_vars[i],
        i)
        << "a bound variable";
    CVC4::Type t = bound_vars[i].d_node->getType().toType();
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        t.isFirstClass(), "sort of parameter", bound_vars[i], i)
        << "first-class sort of parameter of defined function";
    domain_types.push_back(t);
  }
  CVC4_API_SOLVER_CHECK_SORT(sort);
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
  d_smtEngine->defineFunction(fun, ebound_vars, term.d_node->toExpr(), global);
  return Term(this, fun);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::defineFun(Term fun,
                       const std::vector<Term>& bound_vars,
                       Term term,
                       bool global) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;

  if (fun.getSort().isFunction())
  {
    std::vector<Sort> domain_sorts = fun.getSort().getFunctionDomainSorts();
    size_t size = bound_vars.size();
    CVC4_API_ARG_SIZE_CHECK_EXPECTED(size == domain_sorts.size(), bound_vars)
        << "'" << domain_sorts.size() << "'";
    for (size_t i = 0; i < size; ++i)
    {
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
          this == bound_vars[i].d_solver, "bound variable", bound_vars[i], i)
          << "bound variable associated to this solver object";
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
          bound_vars[i].d_node->getKind() == CVC4::Kind::BOUND_VARIABLE,
          "bound variable",
          bound_vars[i],
          i)
          << "a bound variable";
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
  }
  else
  {
    CVC4_API_ARG_CHECK_EXPECTED(bound_vars.size() == 0, fun)
        << "function or nullary symbol";
  }

  CVC4_API_SOLVER_CHECK_TERM(term);

  std::vector<Expr> ebound_vars = termVectorToExprs(bound_vars);
  d_smtEngine->defineFunction(
      fun.d_node->toExpr(), ebound_vars, term.d_node->toExpr(), global);
  return fun;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( define-fun-rec <function_def> )
 */
Term Solver::defineFunRec(const std::string& symbol,
                          const std::vector<Term>& bound_vars,
                          Sort sort,
                          Term term,
                          bool global) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;

  CVC4_API_CHECK(d_smtEngine->getUserLogicInfo().isQuantified())
      << "recursive function definitions require a logic with quantifiers";
  CVC4_API_CHECK(
      d_smtEngine->getUserLogicInfo().isTheoryEnabled(theory::THEORY_UF))
      << "recursive function definitions require a logic with uninterpreted "
         "functions";

  CVC4_API_ARG_CHECK_EXPECTED(sort.isFirstClass(), sort)
      << "first-class sort as function codomain sort";
  Assert(!sort.isFunction()); /* A function sort is not first-class. */
  std::vector<Type> domain_types;
  for (size_t i = 0, size = bound_vars.size(); i < size; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == bound_vars[i].d_solver, "bound variable", bound_vars[i], i)
        << "bound variable associated to this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        bound_vars[i].d_node->getKind() == CVC4::Kind::BOUND_VARIABLE,
        "bound variable",
        bound_vars[i],
        i)
        << "a bound variable";
    CVC4::Type t = bound_vars[i].d_node->getType().toType();
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        t.isFirstClass(), "sort of parameter", bound_vars[i], i)
        << "first-class sort of parameter of defined function";
    domain_types.push_back(t);
  }
  CVC4_API_SOLVER_CHECK_SORT(sort);
  CVC4_API_CHECK(sort == term.getSort())
      << "Invalid sort of function body '" << term << "', expected '" << sort
      << "'";
  CVC4_API_SOLVER_CHECK_TERM(term);
  Type type = *sort.d_type;
  if (!domain_types.empty())
  {
    type = d_exprMgr->mkFunctionType(domain_types, type);
  }
  Expr fun = d_exprMgr->mkVar(symbol, type);
  std::vector<Expr> ebound_vars = termVectorToExprs(bound_vars);
  d_smtEngine->defineFunctionRec(
      fun, ebound_vars, term.d_node->toExpr(), global);
  return Term(this, fun);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::defineFunRec(Term fun,
                          const std::vector<Term>& bound_vars,
                          Term term,
                          bool global) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;

  CVC4_API_CHECK(d_smtEngine->getUserLogicInfo().isQuantified())
      << "recursive function definitions require a logic with quantifiers";
  CVC4_API_CHECK(
      d_smtEngine->getUserLogicInfo().isTheoryEnabled(theory::THEORY_UF))
      << "recursive function definitions require a logic with uninterpreted "
         "functions";

  if (fun.getSort().isFunction())
  {
    std::vector<Sort> domain_sorts = fun.getSort().getFunctionDomainSorts();
    size_t size = bound_vars.size();
    CVC4_API_ARG_SIZE_CHECK_EXPECTED(size == domain_sorts.size(), bound_vars)
        << "'" << domain_sorts.size() << "'";
    for (size_t i = 0; i < size; ++i)
    {
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
          this == bound_vars[i].d_solver, "bound variable", bound_vars[i], i)
          << "bound variable associated to this solver object";
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
          bound_vars[i].d_node->getKind() == CVC4::Kind::BOUND_VARIABLE,
          "bound variable",
          bound_vars[i],
          i)
          << "a bound variable";
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
  }
  else
  {
    CVC4_API_ARG_CHECK_EXPECTED(bound_vars.size() == 0, fun)
        << "function or nullary symbol";
  }

  CVC4_API_SOLVER_CHECK_TERM(term);
  std::vector<Expr> ebound_vars = termVectorToExprs(bound_vars);
  d_smtEngine->defineFunctionRec(
      fun.d_node->toExpr(), ebound_vars, term.d_node->toExpr(), global);
  return fun;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
 */
void Solver::defineFunsRec(const std::vector<Term>& funs,
                           const std::vector<std::vector<Term>>& bound_vars,
                           const std::vector<Term>& terms,
                           bool global) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;

  CVC4_API_CHECK(d_smtEngine->getUserLogicInfo().isQuantified())
      << "recursive function definitions require a logic with quantifiers";
  CVC4_API_CHECK(
      d_smtEngine->getUserLogicInfo().isTheoryEnabled(theory::THEORY_UF))
      << "recursive function definitions require a logic with uninterpreted "
         "functions";

  size_t funs_size = funs.size();
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(funs_size == bound_vars.size(), bound_vars)
      << "'" << funs_size << "'";
  for (size_t j = 0; j < funs_size; ++j)
  {
    const Term& fun = funs[j];
    const std::vector<Term>& bvars = bound_vars[j];
    const Term& term = terms[j];

    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == fun.d_solver, "function", fun, j)
        << "function associated to this solver object";
    CVC4_API_SOLVER_CHECK_TERM(term);

    if (fun.getSort().isFunction())
    {
      std::vector<Sort> domain_sorts = fun.getSort().getFunctionDomainSorts();
      size_t size = bvars.size();
      CVC4_API_ARG_SIZE_CHECK_EXPECTED(size == domain_sorts.size(), bvars)
          << "'" << domain_sorts.size() << "'";
      for (size_t i = 0; i < size; ++i)
      {
        for (size_t k = 0, nbvars = bvars.size(); k < nbvars; ++k)
        {
          CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
              this == bvars[k].d_solver, "bound variable", bvars[k], k)
              << "bound variable associated to this solver object";
          CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
              bvars[k].d_node->getKind() == CVC4::Kind::BOUND_VARIABLE,
              "bound variable",
              bvars[k],
              k)
              << "a bound variable";
        }
        CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
            domain_sorts[i] == bvars[i].getSort(),
            "sort of parameter",
            bvars[i],
            i)
            << "'" << domain_sorts[i] << "' in parameter bound_vars[" << j
            << "]";
      }
      Sort codomain = fun.getSort().getFunctionCodomainSort();
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
          codomain == term.getSort(), "sort of function body", term, j)
          << "'" << codomain << "'";
    }
    else
    {
      CVC4_API_ARG_CHECK_EXPECTED(bvars.size() == 0, fun)
          << "function or nullary symbol";
    }
  }
  std::vector<Expr> efuns = termVectorToExprs(funs);
  std::vector<std::vector<Expr>> ebound_vars;
  for (const auto& v : bound_vars)
  {
    ebound_vars.push_back(termVectorToExprs(v));
  }
  std::vector<Expr> exprs = termVectorToExprs(terms);
  d_smtEngine->defineFunctionsRec(efuns, ebound_vars, exprs, global);
  CVC4_API_SOLVER_TRY_CATCH_END;
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
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  std::vector<Expr> assertions = d_smtEngine->getAssertions();
  /* Can not use
   *   return std::vector<Term>(assertions.begin(), assertions.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const Expr& e : assertions)
  {
    res.push_back(Term(this, e));
  }
  return res;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( get-assignment )
 */
std::vector<std::pair<Term, Term>> Solver::getAssignment(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::produceAssignments])
      << "Cannot get assignment unless assignment generation is enabled "
         "(try --produce-assignments)";
  std::vector<std::pair<Expr, Expr>> assignment = d_smtEngine->getAssignment();
  std::vector<std::pair<Term, Term>> res;
  for (const auto& p : assignment)
  {
    res.emplace_back(Term(this, p.first), Term(this, p.second));
  }
  return res;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( get-info <info_flag> )
 */
std::string Solver::getInfo(const std::string& flag) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(d_smtEngine->isValidGetInfoFlag(flag))
      << "Unrecognized flag for getInfo.";

  return d_smtEngine->getInfo(flag).toString();
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( get-option <keyword> )
 */
std::string Solver::getOption(const std::string& option) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  SExpr res = d_smtEngine->getOption(option);
  return res.toString();
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( get-unsat-assumptions )
 */
std::vector<Term> Solver::getUnsatAssumptions(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot get unsat assumptions unless incremental solving is enabled "
         "(try --incremental)";
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::unsatAssumptions])
      << "Cannot get unsat assumptions unless explicitly enabled "
         "(try --produce-unsat-assumptions)";
  CVC4_API_CHECK(d_smtEngine->getSmtMode() == SmtMode::UNSAT)
      << "Cannot get unsat assumptions unless in unsat mode.";

  std::vector<Node> uassumptions = d_smtEngine->getUnsatAssumptions();
  /* Can not use
   *   return std::vector<Term>(uassumptions.begin(), uassumptions.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const Node& e : uassumptions)
  {
    res.push_back(Term(this, e.toExpr()));
  }
  return res;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( get-unsat-core )
 */
std::vector<Term> Solver::getUnsatCore(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::unsatCores])
      << "Cannot get unsat core unless explicitly enabled "
         "(try --produce-unsat-cores)";
  CVC4_API_CHECK(d_smtEngine->getSmtMode() == SmtMode::UNSAT)
      << "Cannot get unsat core unless in unsat mode.";
  UnsatCore core = d_smtEngine->getUnsatCore();
  /* Can not use
   *   return std::vector<Term>(core.begin(), core.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const Expr& e : core)
  {
    res.push_back(Term(this, e));
  }
  return res;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( get-value ( <term> ) )
 */
Term Solver::getValue(Term term) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(term);
  return Term(this, d_smtEngine->getValue(*term.d_node));
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( get-value ( <term>+ ) )
 */
std::vector<Term> Solver::getValue(const std::vector<Term>& terms) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::produceModels])
      << "Cannot get value unless model generation is enabled "
         "(try --produce-models)";
  CVC4_API_CHECK(d_smtEngine->getSmtMode() != SmtMode::UNSAT)
      << "Cannot get value when in unsat mode.";
  std::vector<Term> res;
  for (size_t i = 0, n = terms.size(); i < n; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == terms[i].d_solver, "term", terms[i], i)
        << "term associated to this solver object";
    /* Can not use emplace_back here since constructor is private. */
    res.push_back(Term(this, d_smtEngine->getValue(terms[i].d_node->toExpr())));
  }
  return res;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::getSeparationHeap() const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(
      d_smtEngine->getLogicInfo().isTheoryEnabled(theory::THEORY_SEP))
      << "Cannot obtain separation logic expressions if not using the "
         "separation logic theory.";
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::produceModels])
      << "Cannot get separation heap term unless model generation is enabled "
         "(try --produce-models)";
  CVC4_API_CHECK(d_smtEngine->getSmtMode() != SmtMode::UNSAT)
      << "Cannot get separtion heap term when in unsat mode.";

  theory::TheoryModel* m =
      d_smtEngine->getAvailableModel("get separation logic heap and nil");
  Expr heap, nil;
  bool hasHeapModel = m->getHeapModel(heap, nil);
  CVC4_API_CHECK(hasHeapModel)
      << "Failed to obtain heap term from theory model.";
  return Term(this, d_smtEngine->getSepHeapExpr());
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::getSeparationNilTerm() const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(
      d_smtEngine->getLogicInfo().isTheoryEnabled(theory::THEORY_SEP))
      << "Cannot obtain separation logic expressions if not using the "
         "separation logic theory.";
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::produceModels])
      << "Cannot get separation nil term unless model generation is enabled "
         "(try --produce-models)";
  CVC4_API_CHECK(d_smtEngine->getSmtMode() != SmtMode::UNSAT)
      << "Cannot get separtion nil term when in unsat mode.";

  theory::TheoryModel* m =
      d_smtEngine->getAvailableModel("get separation logic heap and nil");
  Expr heap, nil;
  bool hasHeapModel = m->getHeapModel(heap, nil);
  CVC4_API_CHECK(hasHeapModel)
      << "Failed to obtain nil term from theory model.";
  return Term(this, nil);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( pop <numeral> )
 */
void Solver::pop(uint32_t nscopes) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot pop when not solving incrementally (use --incremental)";
  CVC4_API_CHECK(nscopes <= d_smtEngine->getNumUserLevels())
      << "Cannot pop beyond first pushed context";

  for (uint32_t n = 0; n < nscopes; ++n)
  {
    d_smtEngine->pop();
  }

  CVC4_API_SOLVER_TRY_CATCH_END;
}

bool Solver::getInterpolant(Term conj, Term& output) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  Node result;
  bool success = d_smtEngine->getInterpol(*conj.d_node, result);
  if (success)
  {
    output = Term(this, result);
  }
  return success;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

bool Solver::getInterpolant(Term conj, Grammar& g, Term& output) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  Node result;
  bool success = d_smtEngine->getInterpol(
      *conj.d_node, TypeNode::fromType(*g.resolve().d_type), result);
  if (success)
  {
    output = Term(this, result);
  }
  return success;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

bool Solver::getAbduct(Term conj, Term& output) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  Node result;
  bool success = d_smtEngine->getAbduct(*conj.d_node, result);
  if (success)
  {
    output = Term(this, result);
  }
  return success;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

bool Solver::getAbduct(Term conj, Grammar& g, Term& output) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  Node result;
  bool success = d_smtEngine->getAbduct(
      *conj.d_node, TypeNode::fromType(*g.resolve().d_type), result);
  if (success)
  {
    output = Term(this, result);
  }
  return success;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

void Solver::printModel(std::ostream& out) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::produceModels])
      << "Cannot get value unless model generation is enabled "
         "(try --produce-models)";
  CVC4_API_CHECK(d_smtEngine->getSmtMode() != SmtMode::UNSAT)
      << "Cannot get value when in unsat mode.";
  out << *d_smtEngine->getModel();
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( push <numeral> )
 */
void Solver::push(uint32_t nscopes) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4::ExprManagerScope exmgrs(*(d_exprMgr.get()));
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot push when not solving incrementally (use --incremental)";

  for (uint32_t n = 0; n < nscopes; ++n)
  {
    d_smtEngine->push();
  }

  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( reset-assertions )
 */
void Solver::resetAssertions(void) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  d_smtEngine->resetAssertions();
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( set-info <attribute> )
 */
void Solver::setInfo(const std::string& keyword, const std::string& value) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(
      keyword == "source" || keyword == "category" || keyword == "difficulty"
          || keyword == "filename" || keyword == "license" || keyword == "name"
          || keyword == "notes" || keyword == "smt-lib-version"
          || keyword == "status",
      keyword)
      << "'source', 'category', 'difficulty', 'filename', 'license', 'name', "
         "'notes', 'smt-lib-version' or 'status'";
  CVC4_API_ARG_CHECK_EXPECTED(keyword != "smt-lib-version" || value == "2"
                                  || value == "2.0" || value == "2.5"
                                  || value == "2.6",
                              value)
      << "'2.0', '2.5', '2.6'";
  CVC4_API_ARG_CHECK_EXPECTED(keyword != "status" || value == "sat"
                                  || value == "unsat" || value == "unknown",
                              value)
      << "'sat', 'unsat' or 'unknown'";

  d_smtEngine->setInfo(keyword, value);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( set-logic <symbol> )
 */
void Solver::setLogic(const std::string& logic) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(!d_smtEngine->isFullyInited())
      << "Invalid call to 'setLogic', solver is already fully initialized";
  CVC4::LogicInfo logic_info(logic);
  d_smtEngine->setLogic(logic_info);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

/**
 *  ( set-option <option> )
 */
void Solver::setOption(const std::string& option,
                       const std::string& value) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(!d_smtEngine->isFullyInited())
      << "Invalid call to 'setOption', solver is already fully initialized";
  d_smtEngine->setOption(option, value);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::ensureTermSort(const Term& term, const Sort& sort) const
{
  CVC4_API_CHECK(term.getSort() == sort
                 || (term.getSort().isInteger() && sort.isReal()))
      << "Expected conversion from Int to Real";

  Sort t = term.getSort();
  if (term.getSort() == sort)
  {
    return term;
  }

  // Integers are reals, too
  Assert(t.isReal());
  Term res = term;
  if (t.isInteger())
  {
    // Must cast to Real to ensure correct type is passed to parametric type
    // constructors. We do this cast using division with 1. This has the
    // advantage wrt using TO_REAL since (constant) division is always included
    // in the theory.
    res = Term(this,
               d_exprMgr->mkExpr(extToIntKind(DIVISION),
                                 res.d_node->toExpr(),
                                 d_exprMgr->mkConst(CVC4::Rational(1))));
  }
  Assert(res.getSort() == sort);
  return res;
}

Term Solver::mkSygusVar(Sort sort, const std::string& symbol) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_NOT_NULL(sort);
  CVC4_API_SOLVER_CHECK_SORT(sort);

  Expr res = d_exprMgr->mkBoundVar(symbol, *sort.d_type);
  (void)res.getType(true); /* kick off type checking */

  d_smtEngine->declareSygusVar(symbol, res, TypeNode::fromType(*sort.d_type));

  return Term(this, res);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

Grammar Solver::mkSygusGrammar(const std::vector<Term>& boundVars,
                               const std::vector<Term>& ntSymbols) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(!ntSymbols.empty(), ntSymbols)
      << "a non-empty vector";

  for (size_t i = 0, n = boundVars.size(); i < n; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == boundVars[i].d_solver, "bound variable", boundVars[i], i)
        << "bound variable associated to this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !boundVars[i].isNull(), "bound variable", boundVars[i], i)
        << "a non-null term";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        boundVars[i].d_node->getKind() == CVC4::Kind::BOUND_VARIABLE,
        "bound variable",
        boundVars[i],
        i)
        << "a bound variable";
  }

  for (size_t i = 0, n = ntSymbols.size(); i < n; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == ntSymbols[i].d_solver, "non-terminal", ntSymbols[i], i)
        << "term associated to this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !ntSymbols[i].isNull(), "non-terminal", ntSymbols[i], i)
        << "a non-null term";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        ntSymbols[i].d_node->getKind() == CVC4::Kind::BOUND_VARIABLE,
        "non-terminal",
        ntSymbols[i],
        i)
        << "a bound variable";
  }

  return Grammar(this, boundVars, ntSymbols);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::synthFun(const std::string& symbol,
                      const std::vector<Term>& boundVars,
                      Sort sort) const
{
  return synthFunHelper(symbol, boundVars, sort);
}

Term Solver::synthFun(const std::string& symbol,
                      const std::vector<Term>& boundVars,
                      Sort sort,
                      Grammar& g) const
{
  return synthFunHelper(symbol, boundVars, sort, false, &g);
}

Term Solver::synthInv(const std::string& symbol,
                      const std::vector<Term>& boundVars) const
{
  return synthFunHelper(
      symbol, boundVars, Sort(this, d_exprMgr->booleanType()), true);
}

Term Solver::synthInv(const std::string& symbol,
                      const std::vector<Term>& boundVars,
                      Grammar& g) const
{
  return synthFunHelper(
      symbol, boundVars, Sort(this, d_exprMgr->booleanType()), true, &g);
}

Term Solver::synthFunHelper(const std::string& symbol,
                            const std::vector<Term>& boundVars,
                            const Sort& sort,
                            bool isInv,
                            Grammar* g) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_NOT_NULL(sort);

  CVC4_API_ARG_CHECK_EXPECTED(sort.d_type->isFirstClass(), sort)
      << "first-class codomain sort for function";

  std::vector<Type> varTypes;
  for (size_t i = 0, n = boundVars.size(); i < n; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == boundVars[i].d_solver, "bound variable", boundVars[i], i)
        << "bound variable associated to this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !boundVars[i].isNull(), "bound variable", boundVars[i], i)
        << "a non-null term";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        boundVars[i].d_node->getKind() == CVC4::Kind::BOUND_VARIABLE,
        "bound variable",
        boundVars[i],
        i)
        << "a bound variable";
    varTypes.push_back(boundVars[i].d_node->getType().toType());
  }
  CVC4_API_SOLVER_CHECK_SORT(sort);

  if (g != nullptr)
  {
    CVC4_API_CHECK(g->d_ntSyms[0].d_node->getType().toType() == *sort.d_type)
        << "Invalid Start symbol for Grammar g, Expected Start's sort to be "
        << *sort.d_type;
  }

  Type funType = varTypes.empty()
                     ? *sort.d_type
                     : d_exprMgr->mkFunctionType(varTypes, *sort.d_type);

  Node fun = getNodeManager()->mkBoundVar(symbol, TypeNode::fromType(funType));
  (void)fun.getType(true); /* kick off type checking */

  std::vector<Node> bvns;
  for (const Term& t : boundVars)
  {
    bvns.push_back(*t.d_node);
  }

  d_smtEngine->declareSynthFun(
      symbol,
      fun,
      TypeNode::fromType(g == nullptr ? funType : *g->resolve().d_type),
      isInv,
      bvns);

  return Term(this, fun);

  CVC4_API_SOLVER_TRY_CATCH_END;
}

void Solver::addSygusConstraint(Term term) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  NodeManagerScope scope(getNodeManager());
  CVC4_API_ARG_CHECK_NOT_NULL(term);
  CVC4_API_SOLVER_CHECK_TERM(term);
  CVC4_API_ARG_CHECK_EXPECTED(
      term.d_node->getType() == getNodeManager()->booleanType(), term)
      << "boolean term";

  d_smtEngine->assertSygusConstraint(*term.d_node);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

void Solver::addSygusInvConstraint(Term inv,
                                   Term pre,
                                   Term trans,
                                   Term post) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_NOT_NULL(inv);
  CVC4_API_SOLVER_CHECK_TERM(inv);
  CVC4_API_ARG_CHECK_NOT_NULL(pre);
  CVC4_API_SOLVER_CHECK_TERM(pre);
  CVC4_API_ARG_CHECK_NOT_NULL(trans);
  CVC4_API_SOLVER_CHECK_TERM(trans);
  CVC4_API_ARG_CHECK_NOT_NULL(post);
  CVC4_API_SOLVER_CHECK_TERM(post);

  CVC4_API_ARG_CHECK_EXPECTED(inv.d_node->getType().isFunction(), inv)
      << "a function";

  FunctionType invType = inv.d_node->getType().toType();

  CVC4_API_ARG_CHECK_EXPECTED(invType.getRangeType().isBoolean(), inv)
      << "boolean range";

  CVC4_API_CHECK(pre.d_node->getType().toType() == invType)
      << "Expected inv and pre to have the same sort";

  CVC4_API_CHECK(post.d_node->getType().toType() == invType)
      << "Expected inv and post to have the same sort";

  const std::vector<Type>& invArgTypes = invType.getArgTypes();

  std::vector<Type> expectedTypes;
  expectedTypes.reserve(2 * invType.getArity() + 1);

  for (size_t i = 0, n = invArgTypes.size(); i < 2 * n; i += 2)
  {
    expectedTypes.push_back(invArgTypes[i % n]);
    expectedTypes.push_back(invArgTypes[(i + 1) % n]);
  }

  expectedTypes.push_back(invType.getRangeType());
  FunctionType expectedTransType = d_exprMgr->mkFunctionType(expectedTypes);

  CVC4_API_CHECK(trans.d_node->toExpr().getType() == expectedTransType)
      << "Expected trans's sort to be " << invType;

  d_smtEngine->assertSygusInvConstraint(inv.d_node->toExpr(),
                                        pre.d_node->toExpr(),
                                        trans.d_node->toExpr(),
                                        post.d_node->toExpr());
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Result Solver::checkSynth() const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  return d_smtEngine->checkSynth();
  CVC4_API_SOLVER_TRY_CATCH_END;
}

Term Solver::getSynthSolution(Term term) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_NOT_NULL(term);
  CVC4_API_SOLVER_CHECK_TERM(term);

  std::map<CVC4::Node, CVC4::Node> map;
  CVC4_API_CHECK(d_smtEngine->getSynthSolutions(map))
      << "The solver is not in a state immediately preceeded by a "
         "successful call to checkSynth";

  std::map<CVC4::Node, CVC4::Node>::const_iterator it = map.find(*term.d_node);

  CVC4_API_CHECK(it != map.cend()) << "Synth solution not found for given term";

  return Term(this, it->second);
  CVC4_API_SOLVER_TRY_CATCH_END;
}

std::vector<Term> Solver::getSynthSolutions(
    const std::vector<Term>& terms) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(!terms.empty(), terms) << "non-empty vector";

  for (size_t i = 0, n = terms.size(); i < n; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == terms[i].d_solver, "parameter term", terms[i], i)
        << "parameter term associated to this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !terms[i].isNull(), "parameter term", terms[i], i)
        << "non-null term";
  }

  std::map<CVC4::Node, CVC4::Node> map;
  CVC4_API_CHECK(d_smtEngine->getSynthSolutions(map))
      << "The solver is not in a state immediately preceeded by a "
         "successful call to checkSynth";

  std::vector<Term> synthSolution;
  synthSolution.reserve(terms.size());

  for (size_t i = 0, n = terms.size(); i < n; ++i)
  {
    std::map<CVC4::Node, CVC4::Node>::const_iterator it =
        map.find(*terms[i].d_node);

    CVC4_API_CHECK(it != map.cend())
        << "Synth solution not found for term at index " << i;

    synthSolution.push_back(Term(this, it->second));
  }

  return synthSolution;
  CVC4_API_SOLVER_TRY_CATCH_END;
}

void Solver::printSynthSolution(std::ostream& out) const
{
  CVC4_API_SOLVER_TRY_CATCH_BEGIN;
  d_smtEngine->printSynthSolution(out);
  CVC4_API_SOLVER_TRY_CATCH_END;
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
NodeManager* Solver::getNodeManager(void) const
{
  return d_exprMgr->getNodeManager();
}

/**
 * !!! This is only temporarily available until the parser is fully migrated to
 * the new API. !!!
 */
SmtEngine* Solver::getSmtEngine(void) const { return d_smtEngine.get(); }

/**
 * !!! This is only temporarily available until the parser is fully migrated to
 * the new API. !!!
 */
Options& Solver::getOptions(void) { return d_smtEngine->getOptions(); }

/* -------------------------------------------------------------------------- */
/* Conversions                                                                */
/* -------------------------------------------------------------------------- */

std::vector<Expr> termVectorToExprs(const std::vector<Term>& terms)
{
  std::vector<Expr> exprs;
  for (size_t i = 0, tsize = terms.size(); i < tsize; i++)
  {
    exprs.push_back(terms[i].getExpr());
  }
  return exprs;
}

std::vector<Node> termVectorToNodes(const std::vector<Term>& terms)
{
  std::vector<Node> res;
  for (const Term& t : terms)
  {
    res.push_back(t.getNode());
  }
  return res;
}

std::vector<Type> sortVectorToTypes(const std::vector<Sort>& sorts)
{
  std::vector<Type> types;
  for (size_t i = 0, ssize = sorts.size(); i < ssize; i++)
  {
    types.push_back(sorts[i].getType());
  }
  return types;
}

std::set<Type> sortSetToTypes(const std::set<Sort>& sorts)
{
  std::set<Type> types;
  for (const Sort& s : sorts)
  {
    types.insert(s.getType());
  }
  return types;
}

std::vector<Term> exprVectorToTerms(const Solver* slv,
                                    const std::vector<Expr>& exprs)
{
  std::vector<Term> terms;
  for (size_t i = 0, esize = exprs.size(); i < esize; i++)
  {
    terms.push_back(Term(slv, exprs[i]));
  }
  return terms;
}

std::vector<Sort> typeVectorToSorts(const Solver* slv,
                                    const std::vector<Type>& types)
{
  std::vector<Sort> sorts;
  for (size_t i = 0, tsize = types.size(); i < tsize; i++)
  {
    sorts.push_back(Sort(slv, types[i]));
  }
  return sorts;
}

}  // namespace api

/* -------------------------------------------------------------------------- */
/* Kind Conversions                                                           */
/* -------------------------------------------------------------------------- */

CVC4::api::Kind intToExtKind(CVC4::Kind k)
{
  auto it = api::s_kinds_internal.find(k);
  if (it == api::s_kinds_internal.end())
  {
    return api::INTERNAL_KIND;
  }
  return it->second;
}

CVC4::Kind extToIntKind(CVC4::api::Kind k)
{
  auto it = api::s_kinds.find(k);
  if (it == api::s_kinds.end())
  {
    return CVC4::Kind::UNDEFINED_KIND;
  }
  return it->second;
}

}  // namespace CVC4

/*********************                                                        */
/*! \file cvc4cpp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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

#include "api/checks.h"
#include "base/check.h"
#include "base/configuration.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/dtype_selector.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "expr/sequence.h"
#include "expr/type_node.h"
#include "options/main_options.h"
#include "options/options.h"
#include "options/smt_options.h"
#include "proof/unsat_core.h"
#include "smt/model.h"
#include "smt/smt_engine.h"
#include "smt/smt_mode.h"
#include "theory/logic_info.h"
#include "theory/theory_model.h"
#include "util/random.h"
#include "util/result.h"
#include "util/statistics_registry.h"
#include "util/stats_histogram.h"
#include "util/utility.h"

namespace cvc5 {
namespace api {

/* -------------------------------------------------------------------------- */
/* Statistics                                                                 */
/* -------------------------------------------------------------------------- */

struct Statistics
{
  Statistics()
      : d_consts("api::CONSTANT"), d_vars("api::VARIABLE"), d_terms("api::TERM")
  {
  }
  IntegralHistogramStat<TypeConstant> d_consts;
  IntegralHistogramStat<TypeConstant> d_vars;
  IntegralHistogramStat<Kind> d_terms;
};

/* -------------------------------------------------------------------------- */
/* Kind                                                                       */
/* -------------------------------------------------------------------------- */

/* Mapping from external (API) kind to internal kind. */
const static std::unordered_map<Kind, cvc5::Kind, KindHashFunction> s_kinds{
    {INTERNAL_KIND, cvc5::Kind::UNDEFINED_KIND},
    {UNDEFINED_KIND, cvc5::Kind::UNDEFINED_KIND},
    {NULL_EXPR, cvc5::Kind::NULL_EXPR},
    /* Builtin ------------------------------------------------------------- */
    {UNINTERPRETED_CONSTANT, cvc5::Kind::UNINTERPRETED_CONSTANT},
    {ABSTRACT_VALUE, cvc5::Kind::ABSTRACT_VALUE},
    {EQUAL, cvc5::Kind::EQUAL},
    {DISTINCT, cvc5::Kind::DISTINCT},
    {CONSTANT, cvc5::Kind::VARIABLE},
    {VARIABLE, cvc5::Kind::BOUND_VARIABLE},
    {SEXPR, cvc5::Kind::SEXPR},
    {LAMBDA, cvc5::Kind::LAMBDA},
    {WITNESS, cvc5::Kind::WITNESS},
    /* Boolean ------------------------------------------------------------- */
    {CONST_BOOLEAN, cvc5::Kind::CONST_BOOLEAN},
    {NOT, cvc5::Kind::NOT},
    {AND, cvc5::Kind::AND},
    {IMPLIES, cvc5::Kind::IMPLIES},
    {OR, cvc5::Kind::OR},
    {XOR, cvc5::Kind::XOR},
    {ITE, cvc5::Kind::ITE},
    {MATCH, cvc5::Kind::MATCH},
    {MATCH_CASE, cvc5::Kind::MATCH_CASE},
    {MATCH_BIND_CASE, cvc5::Kind::MATCH_BIND_CASE},
    /* UF ------------------------------------------------------------------ */
    {APPLY_UF, cvc5::Kind::APPLY_UF},
    {CARDINALITY_CONSTRAINT, cvc5::Kind::CARDINALITY_CONSTRAINT},
    {CARDINALITY_VALUE, cvc5::Kind::CARDINALITY_VALUE},
    {HO_APPLY, cvc5::Kind::HO_APPLY},
    /* Arithmetic ---------------------------------------------------------- */
    {PLUS, cvc5::Kind::PLUS},
    {MULT, cvc5::Kind::MULT},
    {IAND, cvc5::Kind::IAND},
    {MINUS, cvc5::Kind::MINUS},
    {UMINUS, cvc5::Kind::UMINUS},
    {DIVISION, cvc5::Kind::DIVISION},
    {INTS_DIVISION, cvc5::Kind::INTS_DIVISION},
    {INTS_MODULUS, cvc5::Kind::INTS_MODULUS},
    {ABS, cvc5::Kind::ABS},
    {DIVISIBLE, cvc5::Kind::DIVISIBLE},
    {POW, cvc5::Kind::POW},
    {EXPONENTIAL, cvc5::Kind::EXPONENTIAL},
    {SINE, cvc5::Kind::SINE},
    {COSINE, cvc5::Kind::COSINE},
    {TANGENT, cvc5::Kind::TANGENT},
    {COSECANT, cvc5::Kind::COSECANT},
    {SECANT, cvc5::Kind::SECANT},
    {COTANGENT, cvc5::Kind::COTANGENT},
    {ARCSINE, cvc5::Kind::ARCSINE},
    {ARCCOSINE, cvc5::Kind::ARCCOSINE},
    {ARCTANGENT, cvc5::Kind::ARCTANGENT},
    {ARCCOSECANT, cvc5::Kind::ARCCOSECANT},
    {ARCSECANT, cvc5::Kind::ARCSECANT},
    {ARCCOTANGENT, cvc5::Kind::ARCCOTANGENT},
    {SQRT, cvc5::Kind::SQRT},
    {CONST_RATIONAL, cvc5::Kind::CONST_RATIONAL},
    {LT, cvc5::Kind::LT},
    {LEQ, cvc5::Kind::LEQ},
    {GT, cvc5::Kind::GT},
    {GEQ, cvc5::Kind::GEQ},
    {IS_INTEGER, cvc5::Kind::IS_INTEGER},
    {TO_INTEGER, cvc5::Kind::TO_INTEGER},
    {TO_REAL, cvc5::Kind::TO_REAL},
    {PI, cvc5::Kind::PI},
    /* BV ------------------------------------------------------------------ */
    {CONST_BITVECTOR, cvc5::Kind::CONST_BITVECTOR},
    {BITVECTOR_CONCAT, cvc5::Kind::BITVECTOR_CONCAT},
    {BITVECTOR_AND, cvc5::Kind::BITVECTOR_AND},
    {BITVECTOR_OR, cvc5::Kind::BITVECTOR_OR},
    {BITVECTOR_XOR, cvc5::Kind::BITVECTOR_XOR},
    {BITVECTOR_NOT, cvc5::Kind::BITVECTOR_NOT},
    {BITVECTOR_NAND, cvc5::Kind::BITVECTOR_NAND},
    {BITVECTOR_NOR, cvc5::Kind::BITVECTOR_NOR},
    {BITVECTOR_XNOR, cvc5::Kind::BITVECTOR_XNOR},
    {BITVECTOR_COMP, cvc5::Kind::BITVECTOR_COMP},
    {BITVECTOR_MULT, cvc5::Kind::BITVECTOR_MULT},
    {BITVECTOR_PLUS, cvc5::Kind::BITVECTOR_PLUS},
    {BITVECTOR_SUB, cvc5::Kind::BITVECTOR_SUB},
    {BITVECTOR_NEG, cvc5::Kind::BITVECTOR_NEG},
    {BITVECTOR_UDIV, cvc5::Kind::BITVECTOR_UDIV},
    {BITVECTOR_UREM, cvc5::Kind::BITVECTOR_UREM},
    {BITVECTOR_SDIV, cvc5::Kind::BITVECTOR_SDIV},
    {BITVECTOR_SREM, cvc5::Kind::BITVECTOR_SREM},
    {BITVECTOR_SMOD, cvc5::Kind::BITVECTOR_SMOD},
    {BITVECTOR_SHL, cvc5::Kind::BITVECTOR_SHL},
    {BITVECTOR_LSHR, cvc5::Kind::BITVECTOR_LSHR},
    {BITVECTOR_ASHR, cvc5::Kind::BITVECTOR_ASHR},
    {BITVECTOR_ULT, cvc5::Kind::BITVECTOR_ULT},
    {BITVECTOR_ULE, cvc5::Kind::BITVECTOR_ULE},
    {BITVECTOR_UGT, cvc5::Kind::BITVECTOR_UGT},
    {BITVECTOR_UGE, cvc5::Kind::BITVECTOR_UGE},
    {BITVECTOR_SLT, cvc5::Kind::BITVECTOR_SLT},
    {BITVECTOR_SLE, cvc5::Kind::BITVECTOR_SLE},
    {BITVECTOR_SGT, cvc5::Kind::BITVECTOR_SGT},
    {BITVECTOR_SGE, cvc5::Kind::BITVECTOR_SGE},
    {BITVECTOR_ULTBV, cvc5::Kind::BITVECTOR_ULTBV},
    {BITVECTOR_SLTBV, cvc5::Kind::BITVECTOR_SLTBV},
    {BITVECTOR_ITE, cvc5::Kind::BITVECTOR_ITE},
    {BITVECTOR_REDOR, cvc5::Kind::BITVECTOR_REDOR},
    {BITVECTOR_REDAND, cvc5::Kind::BITVECTOR_REDAND},
    {BITVECTOR_EXTRACT, cvc5::Kind::BITVECTOR_EXTRACT},
    {BITVECTOR_REPEAT, cvc5::Kind::BITVECTOR_REPEAT},
    {BITVECTOR_ZERO_EXTEND, cvc5::Kind::BITVECTOR_ZERO_EXTEND},
    {BITVECTOR_SIGN_EXTEND, cvc5::Kind::BITVECTOR_SIGN_EXTEND},
    {BITVECTOR_ROTATE_LEFT, cvc5::Kind::BITVECTOR_ROTATE_LEFT},
    {BITVECTOR_ROTATE_RIGHT, cvc5::Kind::BITVECTOR_ROTATE_RIGHT},
    {INT_TO_BITVECTOR, cvc5::Kind::INT_TO_BITVECTOR},
    {BITVECTOR_TO_NAT, cvc5::Kind::BITVECTOR_TO_NAT},
    /* FP ------------------------------------------------------------------ */
    {CONST_FLOATINGPOINT, cvc5::Kind::CONST_FLOATINGPOINT},
    {CONST_ROUNDINGMODE, cvc5::Kind::CONST_ROUNDINGMODE},
    {FLOATINGPOINT_FP, cvc5::Kind::FLOATINGPOINT_FP},
    {FLOATINGPOINT_EQ, cvc5::Kind::FLOATINGPOINT_EQ},
    {FLOATINGPOINT_ABS, cvc5::Kind::FLOATINGPOINT_ABS},
    {FLOATINGPOINT_NEG, cvc5::Kind::FLOATINGPOINT_NEG},
    {FLOATINGPOINT_PLUS, cvc5::Kind::FLOATINGPOINT_PLUS},
    {FLOATINGPOINT_SUB, cvc5::Kind::FLOATINGPOINT_SUB},
    {FLOATINGPOINT_MULT, cvc5::Kind::FLOATINGPOINT_MULT},
    {FLOATINGPOINT_DIV, cvc5::Kind::FLOATINGPOINT_DIV},
    {FLOATINGPOINT_FMA, cvc5::Kind::FLOATINGPOINT_FMA},
    {FLOATINGPOINT_SQRT, cvc5::Kind::FLOATINGPOINT_SQRT},
    {FLOATINGPOINT_REM, cvc5::Kind::FLOATINGPOINT_REM},
    {FLOATINGPOINT_RTI, cvc5::Kind::FLOATINGPOINT_RTI},
    {FLOATINGPOINT_MIN, cvc5::Kind::FLOATINGPOINT_MIN},
    {FLOATINGPOINT_MAX, cvc5::Kind::FLOATINGPOINT_MAX},
    {FLOATINGPOINT_LEQ, cvc5::Kind::FLOATINGPOINT_LEQ},
    {FLOATINGPOINT_LT, cvc5::Kind::FLOATINGPOINT_LT},
    {FLOATINGPOINT_GEQ, cvc5::Kind::FLOATINGPOINT_GEQ},
    {FLOATINGPOINT_GT, cvc5::Kind::FLOATINGPOINT_GT},
    {FLOATINGPOINT_ISN, cvc5::Kind::FLOATINGPOINT_ISN},
    {FLOATINGPOINT_ISSN, cvc5::Kind::FLOATINGPOINT_ISSN},
    {FLOATINGPOINT_ISZ, cvc5::Kind::FLOATINGPOINT_ISZ},
    {FLOATINGPOINT_ISINF, cvc5::Kind::FLOATINGPOINT_ISINF},
    {FLOATINGPOINT_ISNAN, cvc5::Kind::FLOATINGPOINT_ISNAN},
    {FLOATINGPOINT_ISNEG, cvc5::Kind::FLOATINGPOINT_ISNEG},
    {FLOATINGPOINT_ISPOS, cvc5::Kind::FLOATINGPOINT_ISPOS},
    {FLOATINGPOINT_TO_FP_FLOATINGPOINT,
     cvc5::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT},
    {FLOATINGPOINT_TO_FP_REAL, cvc5::Kind::FLOATINGPOINT_TO_FP_REAL},
    {FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
     cvc5::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR},
    {FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
     cvc5::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR},
    {FLOATINGPOINT_TO_FP_GENERIC, cvc5::Kind::FLOATINGPOINT_TO_FP_GENERIC},
    {FLOATINGPOINT_TO_UBV, cvc5::Kind::FLOATINGPOINT_TO_UBV},
    {FLOATINGPOINT_TO_SBV, cvc5::Kind::FLOATINGPOINT_TO_SBV},
    {FLOATINGPOINT_TO_REAL, cvc5::Kind::FLOATINGPOINT_TO_REAL},
    /* Arrays -------------------------------------------------------------- */
    {SELECT, cvc5::Kind::SELECT},
    {STORE, cvc5::Kind::STORE},
    {CONST_ARRAY, cvc5::Kind::STORE_ALL},
    {EQ_RANGE, cvc5::Kind::EQ_RANGE},
    /* Datatypes ----------------------------------------------------------- */
    {APPLY_SELECTOR, cvc5::Kind::APPLY_SELECTOR},
    {APPLY_CONSTRUCTOR, cvc5::Kind::APPLY_CONSTRUCTOR},
    {APPLY_TESTER, cvc5::Kind::APPLY_TESTER},
    {TUPLE_UPDATE, cvc5::Kind::TUPLE_UPDATE},
    {RECORD_UPDATE, cvc5::Kind::RECORD_UPDATE},
    {DT_SIZE, cvc5::Kind::DT_SIZE},
    {TUPLE_PROJECT, cvc5::Kind::TUPLE_PROJECT},
    /* Separation Logic ---------------------------------------------------- */
    {SEP_NIL, cvc5::Kind::SEP_NIL},
    {SEP_EMP, cvc5::Kind::SEP_EMP},
    {SEP_PTO, cvc5::Kind::SEP_PTO},
    {SEP_STAR, cvc5::Kind::SEP_STAR},
    {SEP_WAND, cvc5::Kind::SEP_WAND},
    /* Sets ---------------------------------------------------------------- */
    {EMPTYSET, cvc5::Kind::EMPTYSET},
    {UNION, cvc5::Kind::UNION},
    {INTERSECTION, cvc5::Kind::INTERSECTION},
    {SETMINUS, cvc5::Kind::SETMINUS},
    {SUBSET, cvc5::Kind::SUBSET},
    {MEMBER, cvc5::Kind::MEMBER},
    {SINGLETON, cvc5::Kind::SINGLETON},
    {INSERT, cvc5::Kind::INSERT},
    {CARD, cvc5::Kind::CARD},
    {COMPLEMENT, cvc5::Kind::COMPLEMENT},
    {UNIVERSE_SET, cvc5::Kind::UNIVERSE_SET},
    {JOIN, cvc5::Kind::JOIN},
    {PRODUCT, cvc5::Kind::PRODUCT},
    {TRANSPOSE, cvc5::Kind::TRANSPOSE},
    {TCLOSURE, cvc5::Kind::TCLOSURE},
    {JOIN_IMAGE, cvc5::Kind::JOIN_IMAGE},
    {IDEN, cvc5::Kind::IDEN},
    {COMPREHENSION, cvc5::Kind::COMPREHENSION},
    {CHOOSE, cvc5::Kind::CHOOSE},
    {IS_SINGLETON, cvc5::Kind::IS_SINGLETON},
    /* Bags ---------------------------------------------------------------- */
    {UNION_MAX, cvc5::Kind::UNION_MAX},
    {UNION_DISJOINT, cvc5::Kind::UNION_DISJOINT},
    {INTERSECTION_MIN, cvc5::Kind::INTERSECTION_MIN},
    {DIFFERENCE_SUBTRACT, cvc5::Kind::DIFFERENCE_SUBTRACT},
    {DIFFERENCE_REMOVE, cvc5::Kind::DIFFERENCE_REMOVE},
    {SUBBAG, cvc5::Kind::SUBBAG},
    {BAG_COUNT, cvc5::Kind::BAG_COUNT},
    {DUPLICATE_REMOVAL, cvc5::Kind::DUPLICATE_REMOVAL},
    {MK_BAG, cvc5::Kind::MK_BAG},
    {EMPTYBAG, cvc5::Kind::EMPTYBAG},
    {BAG_CARD, cvc5::Kind::BAG_CARD},
    {BAG_CHOOSE, cvc5::Kind::BAG_CHOOSE},
    {BAG_IS_SINGLETON, cvc5::Kind::BAG_IS_SINGLETON},
    {BAG_FROM_SET, cvc5::Kind::BAG_FROM_SET},
    {BAG_TO_SET, cvc5::Kind::BAG_TO_SET},
    /* Strings ------------------------------------------------------------- */
    {STRING_CONCAT, cvc5::Kind::STRING_CONCAT},
    {STRING_IN_REGEXP, cvc5::Kind::STRING_IN_REGEXP},
    {STRING_LENGTH, cvc5::Kind::STRING_LENGTH},
    {STRING_SUBSTR, cvc5::Kind::STRING_SUBSTR},
    {STRING_UPDATE, cvc5::Kind::STRING_UPDATE},
    {STRING_CHARAT, cvc5::Kind::STRING_CHARAT},
    {STRING_CONTAINS, cvc5::Kind::STRING_STRCTN},
    {STRING_INDEXOF, cvc5::Kind::STRING_STRIDOF},
    {STRING_REPLACE, cvc5::Kind::STRING_STRREPL},
    {STRING_REPLACE_ALL, cvc5::Kind::STRING_STRREPLALL},
    {STRING_REPLACE_RE, cvc5::Kind::STRING_REPLACE_RE},
    {STRING_REPLACE_RE_ALL, cvc5::Kind::STRING_REPLACE_RE_ALL},
    {STRING_TOLOWER, cvc5::Kind::STRING_TOLOWER},
    {STRING_TOUPPER, cvc5::Kind::STRING_TOUPPER},
    {STRING_REV, cvc5::Kind::STRING_REV},
    {STRING_FROM_CODE, cvc5::Kind::STRING_FROM_CODE},
    {STRING_TO_CODE, cvc5::Kind::STRING_TO_CODE},
    {STRING_LT, cvc5::Kind::STRING_LT},
    {STRING_LEQ, cvc5::Kind::STRING_LEQ},
    {STRING_PREFIX, cvc5::Kind::STRING_PREFIX},
    {STRING_SUFFIX, cvc5::Kind::STRING_SUFFIX},
    {STRING_IS_DIGIT, cvc5::Kind::STRING_IS_DIGIT},
    {STRING_FROM_INT, cvc5::Kind::STRING_ITOS},
    {STRING_TO_INT, cvc5::Kind::STRING_STOI},
    {CONST_STRING, cvc5::Kind::CONST_STRING},
    {STRING_TO_REGEXP, cvc5::Kind::STRING_TO_REGEXP},
    {REGEXP_CONCAT, cvc5::Kind::REGEXP_CONCAT},
    {REGEXP_UNION, cvc5::Kind::REGEXP_UNION},
    {REGEXP_INTER, cvc5::Kind::REGEXP_INTER},
    {REGEXP_DIFF, cvc5::Kind::REGEXP_DIFF},
    {REGEXP_STAR, cvc5::Kind::REGEXP_STAR},
    {REGEXP_PLUS, cvc5::Kind::REGEXP_PLUS},
    {REGEXP_OPT, cvc5::Kind::REGEXP_OPT},
    {REGEXP_RANGE, cvc5::Kind::REGEXP_RANGE},
    {REGEXP_REPEAT, cvc5::Kind::REGEXP_REPEAT},
    {REGEXP_LOOP, cvc5::Kind::REGEXP_LOOP},
    {REGEXP_EMPTY, cvc5::Kind::REGEXP_EMPTY},
    {REGEXP_SIGMA, cvc5::Kind::REGEXP_SIGMA},
    {REGEXP_COMPLEMENT, cvc5::Kind::REGEXP_COMPLEMENT},
    // maps to the same kind as the string versions
    {SEQ_CONCAT, cvc5::Kind::STRING_CONCAT},
    {SEQ_LENGTH, cvc5::Kind::STRING_LENGTH},
    {SEQ_EXTRACT, cvc5::Kind::STRING_SUBSTR},
    {SEQ_UPDATE, cvc5::Kind::STRING_UPDATE},
    {SEQ_AT, cvc5::Kind::STRING_CHARAT},
    {SEQ_CONTAINS, cvc5::Kind::STRING_STRCTN},
    {SEQ_INDEXOF, cvc5::Kind::STRING_STRIDOF},
    {SEQ_REPLACE, cvc5::Kind::STRING_STRREPL},
    {SEQ_REPLACE_ALL, cvc5::Kind::STRING_STRREPLALL},
    {SEQ_REV, cvc5::Kind::STRING_REV},
    {SEQ_PREFIX, cvc5::Kind::STRING_PREFIX},
    {SEQ_SUFFIX, cvc5::Kind::STRING_SUFFIX},
    {CONST_SEQUENCE, cvc5::Kind::CONST_SEQUENCE},
    {SEQ_UNIT, cvc5::Kind::SEQ_UNIT},
    {SEQ_NTH, cvc5::Kind::SEQ_NTH},
    /* Quantifiers --------------------------------------------------------- */
    {FORALL, cvc5::Kind::FORALL},
    {EXISTS, cvc5::Kind::EXISTS},
    {BOUND_VAR_LIST, cvc5::Kind::BOUND_VAR_LIST},
    {INST_PATTERN, cvc5::Kind::INST_PATTERN},
    {INST_NO_PATTERN, cvc5::Kind::INST_NO_PATTERN},
    {INST_ATTRIBUTE, cvc5::Kind::INST_ATTRIBUTE},
    {INST_PATTERN_LIST, cvc5::Kind::INST_PATTERN_LIST},
    {LAST_KIND, cvc5::Kind::LAST_KIND},
};

/* Mapping from internal kind to external (API) kind. */
const static std::unordered_map<cvc5::Kind, Kind, cvc5::kind::KindHashFunction>
    s_kinds_internal{
        {cvc5::Kind::UNDEFINED_KIND, UNDEFINED_KIND},
        {cvc5::Kind::NULL_EXPR, NULL_EXPR},
        /* Builtin --------------------------------------------------------- */
        {cvc5::Kind::UNINTERPRETED_CONSTANT, UNINTERPRETED_CONSTANT},
        {cvc5::Kind::ABSTRACT_VALUE, ABSTRACT_VALUE},
        {cvc5::Kind::EQUAL, EQUAL},
        {cvc5::Kind::DISTINCT, DISTINCT},
        {cvc5::Kind::VARIABLE, CONSTANT},
        {cvc5::Kind::BOUND_VARIABLE, VARIABLE},
        {cvc5::Kind::SEXPR, SEXPR},
        {cvc5::Kind::LAMBDA, LAMBDA},
        {cvc5::Kind::WITNESS, WITNESS},
        /* Boolean --------------------------------------------------------- */
        {cvc5::Kind::CONST_BOOLEAN, CONST_BOOLEAN},
        {cvc5::Kind::NOT, NOT},
        {cvc5::Kind::AND, AND},
        {cvc5::Kind::IMPLIES, IMPLIES},
        {cvc5::Kind::OR, OR},
        {cvc5::Kind::XOR, XOR},
        {cvc5::Kind::ITE, ITE},
        {cvc5::Kind::MATCH, MATCH},
        {cvc5::Kind::MATCH_CASE, MATCH_CASE},
        {cvc5::Kind::MATCH_BIND_CASE, MATCH_BIND_CASE},
        /* UF -------------------------------------------------------------- */
        {cvc5::Kind::APPLY_UF, APPLY_UF},
        {cvc5::Kind::CARDINALITY_CONSTRAINT, CARDINALITY_CONSTRAINT},
        {cvc5::Kind::CARDINALITY_VALUE, CARDINALITY_VALUE},
        {cvc5::Kind::HO_APPLY, HO_APPLY},
        /* Arithmetic ------------------------------------------------------ */
        {cvc5::Kind::PLUS, PLUS},
        {cvc5::Kind::MULT, MULT},
        {cvc5::Kind::IAND, IAND},
        {cvc5::Kind::MINUS, MINUS},
        {cvc5::Kind::UMINUS, UMINUS},
        {cvc5::Kind::DIVISION, DIVISION},
        {cvc5::Kind::DIVISION_TOTAL, INTERNAL_KIND},
        {cvc5::Kind::INTS_DIVISION, INTS_DIVISION},
        {cvc5::Kind::INTS_DIVISION_TOTAL, INTERNAL_KIND},
        {cvc5::Kind::INTS_MODULUS, INTS_MODULUS},
        {cvc5::Kind::INTS_MODULUS_TOTAL, INTERNAL_KIND},
        {cvc5::Kind::ABS, ABS},
        {cvc5::Kind::DIVISIBLE, DIVISIBLE},
        {cvc5::Kind::POW, POW},
        {cvc5::Kind::EXPONENTIAL, EXPONENTIAL},
        {cvc5::Kind::SINE, SINE},
        {cvc5::Kind::COSINE, COSINE},
        {cvc5::Kind::TANGENT, TANGENT},
        {cvc5::Kind::COSECANT, COSECANT},
        {cvc5::Kind::SECANT, SECANT},
        {cvc5::Kind::COTANGENT, COTANGENT},
        {cvc5::Kind::ARCSINE, ARCSINE},
        {cvc5::Kind::ARCCOSINE, ARCCOSINE},
        {cvc5::Kind::ARCTANGENT, ARCTANGENT},
        {cvc5::Kind::ARCCOSECANT, ARCCOSECANT},
        {cvc5::Kind::ARCSECANT, ARCSECANT},
        {cvc5::Kind::ARCCOTANGENT, ARCCOTANGENT},
        {cvc5::Kind::SQRT, SQRT},
        {cvc5::Kind::DIVISIBLE_OP, DIVISIBLE},
        {cvc5::Kind::CONST_RATIONAL, CONST_RATIONAL},
        {cvc5::Kind::LT, LT},
        {cvc5::Kind::LEQ, LEQ},
        {cvc5::Kind::GT, GT},
        {cvc5::Kind::GEQ, GEQ},
        {cvc5::Kind::IS_INTEGER, IS_INTEGER},
        {cvc5::Kind::TO_INTEGER, TO_INTEGER},
        {cvc5::Kind::TO_REAL, TO_REAL},
        {cvc5::Kind::PI, PI},
        /* BV -------------------------------------------------------------- */
        {cvc5::Kind::CONST_BITVECTOR, CONST_BITVECTOR},
        {cvc5::Kind::BITVECTOR_CONCAT, BITVECTOR_CONCAT},
        {cvc5::Kind::BITVECTOR_AND, BITVECTOR_AND},
        {cvc5::Kind::BITVECTOR_OR, BITVECTOR_OR},
        {cvc5::Kind::BITVECTOR_XOR, BITVECTOR_XOR},
        {cvc5::Kind::BITVECTOR_NOT, BITVECTOR_NOT},
        {cvc5::Kind::BITVECTOR_NAND, BITVECTOR_NAND},
        {cvc5::Kind::BITVECTOR_NOR, BITVECTOR_NOR},
        {cvc5::Kind::BITVECTOR_XNOR, BITVECTOR_XNOR},
        {cvc5::Kind::BITVECTOR_COMP, BITVECTOR_COMP},
        {cvc5::Kind::BITVECTOR_MULT, BITVECTOR_MULT},
        {cvc5::Kind::BITVECTOR_PLUS, BITVECTOR_PLUS},
        {cvc5::Kind::BITVECTOR_SUB, BITVECTOR_SUB},
        {cvc5::Kind::BITVECTOR_NEG, BITVECTOR_NEG},
        {cvc5::Kind::BITVECTOR_UDIV, BITVECTOR_UDIV},
        {cvc5::Kind::BITVECTOR_UREM, BITVECTOR_UREM},
        {cvc5::Kind::BITVECTOR_SDIV, BITVECTOR_SDIV},
        {cvc5::Kind::BITVECTOR_SREM, BITVECTOR_SREM},
        {cvc5::Kind::BITVECTOR_SMOD, BITVECTOR_SMOD},
        {cvc5::Kind::BITVECTOR_SHL, BITVECTOR_SHL},
        {cvc5::Kind::BITVECTOR_LSHR, BITVECTOR_LSHR},
        {cvc5::Kind::BITVECTOR_ASHR, BITVECTOR_ASHR},
        {cvc5::Kind::BITVECTOR_ULT, BITVECTOR_ULT},
        {cvc5::Kind::BITVECTOR_ULE, BITVECTOR_ULE},
        {cvc5::Kind::BITVECTOR_UGT, BITVECTOR_UGT},
        {cvc5::Kind::BITVECTOR_UGE, BITVECTOR_UGE},
        {cvc5::Kind::BITVECTOR_SLT, BITVECTOR_SLT},
        {cvc5::Kind::BITVECTOR_SLE, BITVECTOR_SLE},
        {cvc5::Kind::BITVECTOR_SGT, BITVECTOR_SGT},
        {cvc5::Kind::BITVECTOR_SGE, BITVECTOR_SGE},
        {cvc5::Kind::BITVECTOR_ULTBV, BITVECTOR_ULTBV},
        {cvc5::Kind::BITVECTOR_SLTBV, BITVECTOR_SLTBV},
        {cvc5::Kind::BITVECTOR_ITE, BITVECTOR_ITE},
        {cvc5::Kind::BITVECTOR_REDOR, BITVECTOR_REDOR},
        {cvc5::Kind::BITVECTOR_REDAND, BITVECTOR_REDAND},
        {cvc5::Kind::BITVECTOR_EXTRACT_OP, BITVECTOR_EXTRACT},
        {cvc5::Kind::BITVECTOR_REPEAT_OP, BITVECTOR_REPEAT},
        {cvc5::Kind::BITVECTOR_ZERO_EXTEND_OP, BITVECTOR_ZERO_EXTEND},
        {cvc5::Kind::BITVECTOR_SIGN_EXTEND_OP, BITVECTOR_SIGN_EXTEND},
        {cvc5::Kind::BITVECTOR_ROTATE_LEFT_OP, BITVECTOR_ROTATE_LEFT},
        {cvc5::Kind::BITVECTOR_ROTATE_RIGHT_OP, BITVECTOR_ROTATE_RIGHT},
        {cvc5::Kind::BITVECTOR_EXTRACT, BITVECTOR_EXTRACT},
        {cvc5::Kind::BITVECTOR_REPEAT, BITVECTOR_REPEAT},
        {cvc5::Kind::BITVECTOR_ZERO_EXTEND, BITVECTOR_ZERO_EXTEND},
        {cvc5::Kind::BITVECTOR_SIGN_EXTEND, BITVECTOR_SIGN_EXTEND},
        {cvc5::Kind::BITVECTOR_ROTATE_LEFT, BITVECTOR_ROTATE_LEFT},
        {cvc5::Kind::BITVECTOR_ROTATE_RIGHT, BITVECTOR_ROTATE_RIGHT},
        {cvc5::Kind::INT_TO_BITVECTOR_OP, INT_TO_BITVECTOR},
        {cvc5::Kind::INT_TO_BITVECTOR, INT_TO_BITVECTOR},
        {cvc5::Kind::BITVECTOR_TO_NAT, BITVECTOR_TO_NAT},
        /* FP -------------------------------------------------------------- */
        {cvc5::Kind::CONST_FLOATINGPOINT, CONST_FLOATINGPOINT},
        {cvc5::Kind::CONST_ROUNDINGMODE, CONST_ROUNDINGMODE},
        {cvc5::Kind::FLOATINGPOINT_FP, FLOATINGPOINT_FP},
        {cvc5::Kind::FLOATINGPOINT_EQ, FLOATINGPOINT_EQ},
        {cvc5::Kind::FLOATINGPOINT_ABS, FLOATINGPOINT_ABS},
        {cvc5::Kind::FLOATINGPOINT_NEG, FLOATINGPOINT_NEG},
        {cvc5::Kind::FLOATINGPOINT_PLUS, FLOATINGPOINT_PLUS},
        {cvc5::Kind::FLOATINGPOINT_SUB, FLOATINGPOINT_SUB},
        {cvc5::Kind::FLOATINGPOINT_MULT, FLOATINGPOINT_MULT},
        {cvc5::Kind::FLOATINGPOINT_DIV, FLOATINGPOINT_DIV},
        {cvc5::Kind::FLOATINGPOINT_FMA, FLOATINGPOINT_FMA},
        {cvc5::Kind::FLOATINGPOINT_SQRT, FLOATINGPOINT_SQRT},
        {cvc5::Kind::FLOATINGPOINT_REM, FLOATINGPOINT_REM},
        {cvc5::Kind::FLOATINGPOINT_RTI, FLOATINGPOINT_RTI},
        {cvc5::Kind::FLOATINGPOINT_MIN, FLOATINGPOINT_MIN},
        {cvc5::Kind::FLOATINGPOINT_MAX, FLOATINGPOINT_MAX},
        {cvc5::Kind::FLOATINGPOINT_LEQ, FLOATINGPOINT_LEQ},
        {cvc5::Kind::FLOATINGPOINT_LT, FLOATINGPOINT_LT},
        {cvc5::Kind::FLOATINGPOINT_GEQ, FLOATINGPOINT_GEQ},
        {cvc5::Kind::FLOATINGPOINT_GT, FLOATINGPOINT_GT},
        {cvc5::Kind::FLOATINGPOINT_ISN, FLOATINGPOINT_ISN},
        {cvc5::Kind::FLOATINGPOINT_ISSN, FLOATINGPOINT_ISSN},
        {cvc5::Kind::FLOATINGPOINT_ISZ, FLOATINGPOINT_ISZ},
        {cvc5::Kind::FLOATINGPOINT_ISINF, FLOATINGPOINT_ISINF},
        {cvc5::Kind::FLOATINGPOINT_ISNAN, FLOATINGPOINT_ISNAN},
        {cvc5::Kind::FLOATINGPOINT_ISNEG, FLOATINGPOINT_ISNEG},
        {cvc5::Kind::FLOATINGPOINT_ISPOS, FLOATINGPOINT_ISPOS},
        {cvc5::Kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP,
         FLOATINGPOINT_TO_FP_IEEE_BITVECTOR},
        {cvc5::Kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR,
         FLOATINGPOINT_TO_FP_IEEE_BITVECTOR},
        {cvc5::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP,
         FLOATINGPOINT_TO_FP_FLOATINGPOINT},
        {cvc5::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT,
         FLOATINGPOINT_TO_FP_FLOATINGPOINT},
        {cvc5::Kind::FLOATINGPOINT_TO_FP_REAL_OP, FLOATINGPOINT_TO_FP_REAL},
        {cvc5::Kind::FLOATINGPOINT_TO_FP_REAL, FLOATINGPOINT_TO_FP_REAL},
        {cvc5::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP,
         FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR},
        {cvc5::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
         FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR},
        {cvc5::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP,
         FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR},
        {cvc5::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
         FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR},
        {cvc5::Kind::FLOATINGPOINT_TO_FP_GENERIC_OP,
         FLOATINGPOINT_TO_FP_GENERIC},
        {cvc5::Kind::FLOATINGPOINT_TO_FP_GENERIC, FLOATINGPOINT_TO_FP_GENERIC},
        {cvc5::Kind::FLOATINGPOINT_TO_UBV_OP, FLOATINGPOINT_TO_UBV},
        {cvc5::Kind::FLOATINGPOINT_TO_UBV, FLOATINGPOINT_TO_UBV},
        {cvc5::Kind::FLOATINGPOINT_TO_UBV_TOTAL_OP, INTERNAL_KIND},
        {cvc5::Kind::FLOATINGPOINT_TO_UBV_TOTAL, INTERNAL_KIND},
        {cvc5::Kind::FLOATINGPOINT_TO_SBV_OP, FLOATINGPOINT_TO_SBV},
        {cvc5::Kind::FLOATINGPOINT_TO_SBV, FLOATINGPOINT_TO_SBV},
        {cvc5::Kind::FLOATINGPOINT_TO_SBV_TOTAL_OP, INTERNAL_KIND},
        {cvc5::Kind::FLOATINGPOINT_TO_SBV_TOTAL, INTERNAL_KIND},
        {cvc5::Kind::FLOATINGPOINT_TO_REAL, FLOATINGPOINT_TO_REAL},
        {cvc5::Kind::FLOATINGPOINT_TO_REAL_TOTAL, INTERNAL_KIND},
        /* Arrays ---------------------------------------------------------- */
        {cvc5::Kind::SELECT, SELECT},
        {cvc5::Kind::STORE, STORE},
        {cvc5::Kind::STORE_ALL, CONST_ARRAY},
        /* Datatypes ------------------------------------------------------- */
        {cvc5::Kind::APPLY_SELECTOR, APPLY_SELECTOR},
        {cvc5::Kind::APPLY_CONSTRUCTOR, APPLY_CONSTRUCTOR},
        {cvc5::Kind::APPLY_SELECTOR_TOTAL, INTERNAL_KIND},
        {cvc5::Kind::APPLY_TESTER, APPLY_TESTER},
        {cvc5::Kind::TUPLE_UPDATE_OP, TUPLE_UPDATE},
        {cvc5::Kind::TUPLE_UPDATE, TUPLE_UPDATE},
        {cvc5::Kind::RECORD_UPDATE_OP, RECORD_UPDATE},
        {cvc5::Kind::RECORD_UPDATE, RECORD_UPDATE},
        {cvc5::Kind::DT_SIZE, DT_SIZE},
        {cvc5::Kind::TUPLE_PROJECT, TUPLE_PROJECT},
        /* Separation Logic ------------------------------------------------ */
        {cvc5::Kind::SEP_NIL, SEP_NIL},
        {cvc5::Kind::SEP_EMP, SEP_EMP},
        {cvc5::Kind::SEP_PTO, SEP_PTO},
        {cvc5::Kind::SEP_STAR, SEP_STAR},
        {cvc5::Kind::SEP_WAND, SEP_WAND},
        /* Sets ------------------------------------------------------------ */
        {cvc5::Kind::EMPTYSET, EMPTYSET},
        {cvc5::Kind::UNION, UNION},
        {cvc5::Kind::INTERSECTION, INTERSECTION},
        {cvc5::Kind::SETMINUS, SETMINUS},
        {cvc5::Kind::SUBSET, SUBSET},
        {cvc5::Kind::MEMBER, MEMBER},
        {cvc5::Kind::SINGLETON, SINGLETON},
        {cvc5::Kind::INSERT, INSERT},
        {cvc5::Kind::CARD, CARD},
        {cvc5::Kind::COMPLEMENT, COMPLEMENT},
        {cvc5::Kind::UNIVERSE_SET, UNIVERSE_SET},
        {cvc5::Kind::JOIN, JOIN},
        {cvc5::Kind::PRODUCT, PRODUCT},
        {cvc5::Kind::TRANSPOSE, TRANSPOSE},
        {cvc5::Kind::TCLOSURE, TCLOSURE},
        {cvc5::Kind::JOIN_IMAGE, JOIN_IMAGE},
        {cvc5::Kind::IDEN, IDEN},
        {cvc5::Kind::COMPREHENSION, COMPREHENSION},
        {cvc5::Kind::CHOOSE, CHOOSE},
        {cvc5::Kind::IS_SINGLETON, IS_SINGLETON},
        /* Bags ------------------------------------------------------------ */
        {cvc5::Kind::UNION_MAX, UNION_MAX},
        {cvc5::Kind::UNION_DISJOINT, UNION_DISJOINT},
        {cvc5::Kind::INTERSECTION_MIN, INTERSECTION_MIN},
        {cvc5::Kind::DIFFERENCE_SUBTRACT, DIFFERENCE_SUBTRACT},
        {cvc5::Kind::DIFFERENCE_REMOVE, DIFFERENCE_REMOVE},
        {cvc5::Kind::SUBBAG, SUBBAG},
        {cvc5::Kind::BAG_COUNT, BAG_COUNT},
        {cvc5::Kind::DUPLICATE_REMOVAL, DUPLICATE_REMOVAL},
        {cvc5::Kind::MK_BAG, MK_BAG},
        {cvc5::Kind::EMPTYBAG, EMPTYBAG},
        {cvc5::Kind::BAG_CARD, BAG_CARD},
        {cvc5::Kind::BAG_CHOOSE, BAG_CHOOSE},
        {cvc5::Kind::BAG_IS_SINGLETON, BAG_IS_SINGLETON},
        {cvc5::Kind::BAG_FROM_SET, BAG_FROM_SET},
        {cvc5::Kind::BAG_TO_SET, BAG_TO_SET},
        /* Strings --------------------------------------------------------- */
        {cvc5::Kind::STRING_CONCAT, STRING_CONCAT},
        {cvc5::Kind::STRING_IN_REGEXP, STRING_IN_REGEXP},
        {cvc5::Kind::STRING_LENGTH, STRING_LENGTH},
        {cvc5::Kind::STRING_SUBSTR, STRING_SUBSTR},
        {cvc5::Kind::STRING_UPDATE, STRING_UPDATE},
        {cvc5::Kind::STRING_CHARAT, STRING_CHARAT},
        {cvc5::Kind::STRING_STRCTN, STRING_CONTAINS},
        {cvc5::Kind::STRING_STRIDOF, STRING_INDEXOF},
        {cvc5::Kind::STRING_STRREPL, STRING_REPLACE},
        {cvc5::Kind::STRING_STRREPLALL, STRING_REPLACE_ALL},
        {cvc5::Kind::STRING_REPLACE_RE, STRING_REPLACE_RE},
        {cvc5::Kind::STRING_REPLACE_RE_ALL, STRING_REPLACE_RE_ALL},
        {cvc5::Kind::STRING_TOLOWER, STRING_TOLOWER},
        {cvc5::Kind::STRING_TOUPPER, STRING_TOUPPER},
        {cvc5::Kind::STRING_REV, STRING_REV},
        {cvc5::Kind::STRING_FROM_CODE, STRING_FROM_CODE},
        {cvc5::Kind::STRING_TO_CODE, STRING_TO_CODE},
        {cvc5::Kind::STRING_LT, STRING_LT},
        {cvc5::Kind::STRING_LEQ, STRING_LEQ},
        {cvc5::Kind::STRING_PREFIX, STRING_PREFIX},
        {cvc5::Kind::STRING_SUFFIX, STRING_SUFFIX},
        {cvc5::Kind::STRING_IS_DIGIT, STRING_IS_DIGIT},
        {cvc5::Kind::STRING_ITOS, STRING_FROM_INT},
        {cvc5::Kind::STRING_STOI, STRING_TO_INT},
        {cvc5::Kind::CONST_STRING, CONST_STRING},
        {cvc5::Kind::STRING_TO_REGEXP, STRING_TO_REGEXP},
        {cvc5::Kind::REGEXP_CONCAT, REGEXP_CONCAT},
        {cvc5::Kind::REGEXP_UNION, REGEXP_UNION},
        {cvc5::Kind::REGEXP_INTER, REGEXP_INTER},
        {cvc5::Kind::REGEXP_DIFF, REGEXP_DIFF},
        {cvc5::Kind::REGEXP_STAR, REGEXP_STAR},
        {cvc5::Kind::REGEXP_PLUS, REGEXP_PLUS},
        {cvc5::Kind::REGEXP_OPT, REGEXP_OPT},
        {cvc5::Kind::REGEXP_RANGE, REGEXP_RANGE},
        {cvc5::Kind::REGEXP_REPEAT, REGEXP_REPEAT},
        {cvc5::Kind::REGEXP_REPEAT_OP, REGEXP_REPEAT},
        {cvc5::Kind::REGEXP_LOOP, REGEXP_LOOP},
        {cvc5::Kind::REGEXP_LOOP_OP, REGEXP_LOOP},
        {cvc5::Kind::REGEXP_EMPTY, REGEXP_EMPTY},
        {cvc5::Kind::REGEXP_SIGMA, REGEXP_SIGMA},
        {cvc5::Kind::REGEXP_COMPLEMENT, REGEXP_COMPLEMENT},
        {cvc5::Kind::CONST_SEQUENCE, CONST_SEQUENCE},
        {cvc5::Kind::SEQ_UNIT, SEQ_UNIT},
        {cvc5::Kind::SEQ_NTH, SEQ_NTH},
        /* Quantifiers ----------------------------------------------------- */
        {cvc5::Kind::FORALL, FORALL},
        {cvc5::Kind::EXISTS, EXISTS},
        {cvc5::Kind::BOUND_VAR_LIST, BOUND_VAR_LIST},
        {cvc5::Kind::INST_PATTERN, INST_PATTERN},
        {cvc5::Kind::INST_NO_PATTERN, INST_NO_PATTERN},
        {cvc5::Kind::INST_ATTRIBUTE, INST_ATTRIBUTE},
        {cvc5::Kind::INST_PATTERN_LIST, INST_PATTERN_LIST},
        /* ----------------------------------------------------------------- */
        {cvc5::Kind::LAST_KIND, LAST_KIND},
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

/** Convert a cvc5::Kind (internal) to a cvc5::api::Kind (external). */
cvc5::api::Kind intToExtKind(cvc5::Kind k)
{
  auto it = api::s_kinds_internal.find(k);
  if (it == api::s_kinds_internal.end())
  {
    return api::INTERNAL_KIND;
  }
  return it->second;
}

/** Convert a cvc5::api::Kind (external) to a cvc5::Kind (internal). */
cvc5::Kind extToIntKind(cvc5::api::Kind k)
{
  auto it = api::s_kinds.find(k);
  if (it == api::s_kinds.end())
  {
    return cvc5::Kind::UNDEFINED_KIND;
  }
  return it->second;
}

/** Return true if given kind is a defined external kind. */
bool isDefinedKind(Kind k) { return k > UNDEFINED_KIND && k < LAST_KIND; }

/**
 * Return true if the internal kind is one where the API term structure
 * differs from internal structure. This happens for APPLY_* kinds.
 * The API takes a "higher-order" perspective and treats functions as well
 * as datatype constructors/selectors/testers as terms
 * but interally they are not
 */
bool isApplyKind(cvc5::Kind k)
{
  return (k == cvc5::Kind::APPLY_UF || k == cvc5::Kind::APPLY_CONSTRUCTOR
          || k == cvc5::Kind::APPLY_SELECTOR || k == cvc5::Kind::APPLY_TESTER);
}

#ifdef CVC4_ASSERTIONS
/** Return true if given kind is a defined internal kind. */
bool isDefinedIntKind(cvc5::Kind k)
{
  return k != cvc5::Kind::UNDEFINED_KIND && k != cvc5::Kind::LAST_KIND;
}
#endif

/** Return the minimum arity of given kind. */
uint32_t minArity(Kind k)
{
  Assert(isDefinedKind(k));
  Assert(isDefinedIntKind(extToIntKind(k)));
  uint32_t min = cvc5::kind::metakind::getMinArityForKind(extToIntKind(k));

  // At the API level, we treat functions/constructors/selectors/testers as
  // normal terms instead of making them part of the operator
  if (isApplyKind(extToIntKind(k)))
  {
    min++;
  }
  return min;
}

/** Return the maximum arity of given kind. */
uint32_t maxArity(Kind k)
{
  Assert(isDefinedKind(k));
  Assert(isDefinedIntKind(extToIntKind(k)));
  uint32_t max = cvc5::kind::metakind::getMaxArityForKind(extToIntKind(k));

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
                            : cvc5::kind::kindToString(extToIntKind(k));
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
    if (std::uncaught_exceptions() == 0)
    {
      throw CVC4ApiException(d_stream.str());
    }
  }

  std::ostream& ostream() { return d_stream; }

 private:
  std::stringstream d_stream;
};

class CVC4ApiRecoverableExceptionStream
{
 public:
  CVC4ApiRecoverableExceptionStream() {}
  /* Note: This needs to be explicitly set to 'noexcept(false)' since it is
   * a destructor that throws an exception and in C++11 all destructors
   * default to noexcept(true) (else this triggers a call to std::terminate). */
  ~CVC4ApiRecoverableExceptionStream() noexcept(false)
  {
    if (std::uncaught_exceptions() == 0)
    {
      throw CVC4ApiRecoverableException(d_stream.str());
    }
  }

  std::ostream& ostream() { return d_stream; }

 private:
  std::stringstream d_stream;
};

#define CVC4_API_TRY_CATCH_BEGIN \
  try                            \
  {
#define CVC4_API_TRY_CATCH_END                                                 \
  }                                                                            \
  catch (const UnrecognizedOptionException& e)                                 \
  {                                                                            \
    throw CVC4ApiRecoverableException(e.getMessage());                         \
  }                                                                            \
  catch (const cvc5::RecoverableModalException& e)                             \
  {                                                                            \
    throw CVC4ApiRecoverableException(e.getMessage());                         \
  }                                                                            \
  catch (const cvc5::Exception& e) { throw CVC4ApiException(e.getMessage()); } \
  catch (const std::invalid_argument& e) { throw CVC4ApiException(e.what()); }

}  // namespace

/* -------------------------------------------------------------------------- */
/* Result                                                                     */
/* -------------------------------------------------------------------------- */

Result::Result(const cvc5::Result& r) : d_result(new cvc5::Result(r)) {}

Result::Result() : d_result(new cvc5::Result()) {}

bool Result::isNull() const
{
  return d_result->getType() == cvc5::Result::TYPE_NONE;
}

bool Result::isSat(void) const
{
  return d_result->getType() == cvc5::Result::TYPE_SAT
         && d_result->isSat() == cvc5::Result::SAT;
}

bool Result::isUnsat(void) const
{
  return d_result->getType() == cvc5::Result::TYPE_SAT
         && d_result->isSat() == cvc5::Result::UNSAT;
}

bool Result::isSatUnknown(void) const
{
  return d_result->getType() == cvc5::Result::TYPE_SAT
         && d_result->isSat() == cvc5::Result::SAT_UNKNOWN;
}

bool Result::isEntailed(void) const
{
  return d_result->getType() == cvc5::Result::TYPE_ENTAILMENT
         && d_result->isEntailed() == cvc5::Result::ENTAILED;
}

bool Result::isNotEntailed(void) const
{
  return d_result->getType() == cvc5::Result::TYPE_ENTAILMENT
         && d_result->isEntailed() == cvc5::Result::NOT_ENTAILED;
}

bool Result::isEntailmentUnknown(void) const
{
  return d_result->getType() == cvc5::Result::TYPE_ENTAILMENT
         && d_result->isEntailed() == cvc5::Result::ENTAILMENT_UNKNOWN;
}

bool Result::operator==(const Result& r) const
{
  return *d_result == *r.d_result;
}

bool Result::operator!=(const Result& r) const
{
  return *d_result != *r.d_result;
}

Result::UnknownExplanation Result::getUnknownExplanation(void) const
{
  cvc5::Result::UnknownExplanation expl = d_result->whyUnknown();
  switch (expl)
  {
    case cvc5::Result::REQUIRES_FULL_CHECK: return REQUIRES_FULL_CHECK;
    case cvc5::Result::INCOMPLETE: return INCOMPLETE;
    case cvc5::Result::TIMEOUT: return TIMEOUT;
    case cvc5::Result::RESOURCEOUT: return RESOURCEOUT;
    case cvc5::Result::MEMOUT: return MEMOUT;
    case cvc5::Result::INTERRUPTED: return INTERRUPTED;
    case cvc5::Result::NO_STATUS: return NO_STATUS;
    case cvc5::Result::UNSUPPORTED: return UNSUPPORTED;
    case cvc5::Result::OTHER: return OTHER;
    default: return UNKNOWN_REASON;
  }
  return UNKNOWN_REASON;
}

std::string Result::toString(void) const { return d_result->toString(); }

std::ostream& operator<<(std::ostream& out, const Result& r)
{
  out << r.toString();
  return out;
}

std::ostream& operator<<(std::ostream& out, enum Result::UnknownExplanation e)
{
  switch (e)
  {
    case Result::REQUIRES_FULL_CHECK: out << "REQUIRES_FULL_CHECK"; break;
    case Result::INCOMPLETE: out << "INCOMPLETE"; break;
    case Result::TIMEOUT: out << "TIMEOUT"; break;
    case Result::RESOURCEOUT: out << "RESOURCEOUT"; break;
    case Result::MEMOUT: out << "MEMOUT"; break;
    case Result::INTERRUPTED: out << "INTERRUPTED"; break;
    case Result::NO_STATUS: out << "NO_STATUS"; break;
    case Result::UNSUPPORTED: out << "UNSUPPORTED"; break;
    case Result::OTHER: out << "OTHER"; break;
    case Result::UNKNOWN_REASON: out << "UNKNOWN_REASON"; break;
    default: Unhandled() << e;
  }
  return out;
}

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

Sort::Sort(const Solver* slv, const cvc5::TypeNode& t)
    : d_solver(slv), d_type(new cvc5::TypeNode(t))
{
}

Sort::Sort() : d_solver(nullptr), d_type(new cvc5::TypeNode()) {}

Sort::~Sort()
{
  if (d_solver != nullptr)
  {
    // Ensure that the correct node manager is in scope when the node is
    // destroyed.
    NodeManagerScope scope(d_solver->getNodeManager());
    d_type.reset();
  }
}

std::set<TypeNode> Sort::sortSetToTypeNodes(const std::set<Sort>& sorts)
{
  std::set<TypeNode> types;
  for (const Sort& s : sorts)
  {
    types.insert(s.getTypeNode());
  }
  return types;
}

std::vector<TypeNode> Sort::sortVectorToTypeNodes(
    const std::vector<Sort>& sorts)
{
  std::vector<TypeNode> typeNodes;
  for (const Sort& sort : sorts)
  {
    typeNodes.push_back(sort.getTypeNode());
  }
  return typeNodes;
}

std::vector<Sort> Sort::typeNodeVectorToSorts(
    const Solver* slv, const std::vector<TypeNode>& types)
{
  std::vector<Sort> sorts;
  for (size_t i = 0, tsize = types.size(); i < tsize; i++)
  {
    sorts.push_back(Sort(slv, types[i]));
  }
  return sorts;
}

bool Sort::operator==(const Sort& s) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_type == *s.d_type;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::operator!=(const Sort& s) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_type != *s.d_type;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::operator<(const Sort& s) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_type < *s.d_type;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::operator>(const Sort& s) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_type > *s.d_type;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::operator<=(const Sort& s) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_type <= *s.d_type;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::operator>=(const Sort& s) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_type >= *s.d_type;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isNull() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isBoolean() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isBoolean();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isInteger() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isInteger();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isReal() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  // notice that we do not expose internal subtyping to the user
  return d_type->isReal() && !d_type->isInteger();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isString() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isString();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isRegExp() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isRegExp();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isRoundingMode() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isRoundingMode();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isBitVector() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isBitVector();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isFloatingPoint() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isFloatingPoint();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isDatatype() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isDatatype();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isParametricDatatype() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (!d_type->isDatatype()) return false;
  return d_type->isParametricDatatype();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isConstructor() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isConstructor();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isSelector() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isSelector();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isTester() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isTester();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isFunction() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isFunction();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isPredicate() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isPredicate();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isTuple() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isTuple();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isRecord() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isRecord();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isArray() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isArray();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isSet() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isSet();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isBag() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isBag();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isSequence() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isSequence();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isUninterpretedSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isSort();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isSortConstructor() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isSortConstructor();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isFirstClass() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isFirstClass();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isFunctionLike() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isFunctionLike();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isSubsortOf(const Sort& s) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_SOLVER("sort", s);
  //////// all checks before this line
  return d_type->isSubtypeOf(*s.d_type);
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isComparableTo(const Sort& s) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_SOLVER("sort", s);
  //////// all checks before this line
  return d_type->isComparableTo(*s.d_type);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Datatype Sort::getDatatype() const
{
  NodeManagerScope scope(d_solver->getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isDatatype()) << "Expected datatype sort.";
  //////// all checks before this line
  return Datatype(d_solver, d_type->getDType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Sort::instantiate(const std::vector<Sort>& params) const
{
  NodeManagerScope scope(d_solver->getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK_SORTS(params);
  CVC4_API_CHECK(isParametricDatatype() || isSortConstructor())
      << "Expected parametric datatype or sort constructor sort.";
  //////// all checks before this line
  std::vector<cvc5::TypeNode> tparams = sortVectorToTypeNodes(params);
  if (d_type->isDatatype())
  {
    return Sort(d_solver, d_type->instantiateParametricDatatype(tparams));
  }
  Assert(d_type->isSortConstructor());
  return Sort(d_solver, d_solver->getNodeManager()->mkSort(*d_type, tparams));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Sort::substitute(const Sort& sort, const Sort& replacement) const
{
  NodeManagerScope scope(d_solver->getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK_SORT(sort);
  CVC4_API_CHECK_SORT(replacement);
  //////// all checks before this line
  return Sort(
      d_solver,
      d_type->substitute(sort.getTypeNode(), replacement.getTypeNode()));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Sort::substitute(const std::vector<Sort>& sorts,
                      const std::vector<Sort>& replacements) const
{
  NodeManagerScope scope(d_solver->getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK_SORTS(sorts);
  CVC4_API_CHECK_SORTS(replacements);
  //////// all checks before this line

  std::vector<cvc5::TypeNode> tSorts = sortVectorToTypeNodes(sorts),
                              tReplacements =
                                  sortVectorToTypeNodes(replacements);
  return Sort(d_solver,
              d_type->substitute(tSorts.begin(),
                                 tSorts.end(),
                                 tReplacements.begin(),
                                 tReplacements.end()));
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::string Sort::toString() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (d_solver != nullptr)
  {
    NodeManagerScope scope(d_solver->getNodeManager());
    return d_type->toString();
  }
  return d_type->toString();
  ////////
  CVC4_API_TRY_CATCH_END;
}

const cvc5::TypeNode& Sort::getTypeNode(void) const { return *d_type; }

/* Constructor sort ------------------------------------------------------- */

size_t Sort::getConstructorArity() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isConstructor()) << "Not a constructor sort: " << (*this);
  //////// all checks before this line
  return d_type->getNumChildren() - 1;
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::vector<Sort> Sort::getConstructorDomainSorts() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isConstructor()) << "Not a constructor sort: " << (*this);
  //////// all checks before this line
  return typeNodeVectorToSorts(d_solver, d_type->getArgTypes());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Sort::getConstructorCodomainSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isConstructor()) << "Not a constructor sort: " << (*this);
  //////// all checks before this line
  return Sort(d_solver, d_type->getConstructorRangeType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Selector sort ------------------------------------------------------- */

Sort Sort::getSelectorDomainSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isSelector()) << "Not a selector sort: " << (*this);
  //////// all checks before this line
  return Sort(d_solver, d_type->getSelectorDomainType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Sort::getSelectorCodomainSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isSelector()) << "Not a selector sort: " << (*this);
  //////// all checks before this line
  return Sort(d_solver, d_type->getSelectorRangeType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Tester sort ------------------------------------------------------- */

Sort Sort::getTesterDomainSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isTester()) << "Not a tester sort: " << (*this);
  //////// all checks before this line
  return Sort(d_solver, d_type->getTesterDomainType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Sort::getTesterCodomainSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isTester()) << "Not a tester sort: " << (*this);
  //////// all checks before this line
  return d_solver->getBooleanSort();
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Function sort ------------------------------------------------------- */

size_t Sort::getFunctionArity() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isFunction()) << "Not a function sort: " << (*this);
  //////// all checks before this line
  return d_type->getNumChildren() - 1;
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::vector<Sort> Sort::getFunctionDomainSorts() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isFunction()) << "Not a function sort: " << (*this);
  //////// all checks before this line
  return typeNodeVectorToSorts(d_solver, d_type->getArgTypes());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Sort::getFunctionCodomainSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isFunction()) << "Not a function sort" << (*this);
  //////// all checks before this line
  return Sort(d_solver, d_type->getRangeType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Array sort ---------------------------------------------------------- */

Sort Sort::getArrayIndexSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isArray()) << "Not an array sort.";
  //////// all checks before this line
  return Sort(d_solver, d_type->getArrayIndexType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Sort::getArrayElementSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isArray()) << "Not an array sort.";
  //////// all checks before this line
  return Sort(d_solver, d_type->getArrayConstituentType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Set sort ------------------------------------------------------------ */

Sort Sort::getSetElementSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isSet()) << "Not a set sort.";
  //////// all checks before this line
  return Sort(d_solver, d_type->getSetElementType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Bag sort ------------------------------------------------------------ */

Sort Sort::getBagElementSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isBag()) << "Not a bag sort.";
  //////// all checks before this line
  return Sort(d_solver, d_type->getBagElementType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Sequence sort ------------------------------------------------------- */

Sort Sort::getSequenceElementSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isSequence()) << "Not a sequence sort.";
  //////// all checks before this line
  return Sort(d_solver, d_type->getSequenceElementType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Uninterpreted sort -------------------------------------------------- */

std::string Sort::getUninterpretedSortName() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isUninterpretedSort()) << "Not an uninterpreted sort.";
  //////// all checks before this line
  return d_type->getName();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Sort::isUninterpretedSortParameterized() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isUninterpretedSort()) << "Not an uninterpreted sort.";
  //////// all checks before this line

  /* This method is not implemented in the NodeManager, since whether a
   * uninterpreted sort is parameterized is irrelevant for solving. */
  return d_type->getNumChildren() > 0;
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::vector<Sort> Sort::getUninterpretedSortParamSorts() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isUninterpretedSort()) << "Not an uninterpreted sort.";
  //////// all checks before this line

  /* This method is not implemented in the NodeManager, since whether a
   * uninterpreted sort is parameterized is irrelevant for solving. */
  std::vector<TypeNode> params;
  for (size_t i = 0, nchildren = d_type->getNumChildren(); i < nchildren; i++)
  {
    params.push_back((*d_type)[i]);
  }
  return typeNodeVectorToSorts(d_solver, params);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Sort constructor sort ----------------------------------------------- */

std::string Sort::getSortConstructorName() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isSortConstructor()) << "Not a sort constructor sort.";
  //////// all checks before this line
  return d_type->getName();
  ////////
  CVC4_API_TRY_CATCH_END;
}

size_t Sort::getSortConstructorArity() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isSortConstructor()) << "Not a sort constructor sort.";
  //////// all checks before this line
  return d_type->getSortConstructorArity();
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Bit-vector sort ----------------------------------------------------- */

uint32_t Sort::getBVSize() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isBitVector()) << "Not a bit-vector sort.";
  //////// all checks before this line
  return d_type->getBitVectorSize();
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Floating-point sort ------------------------------------------------- */

uint32_t Sort::getFPExponentSize() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isFloatingPoint()) << "Not a floating-point sort.";
  //////// all checks before this line
  return d_type->getFloatingPointExponentSize();
  ////////
  CVC4_API_TRY_CATCH_END;
}

uint32_t Sort::getFPSignificandSize() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isFloatingPoint()) << "Not a floating-point sort.";
  //////// all checks before this line
  return d_type->getFloatingPointSignificandSize();
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Datatype sort ------------------------------------------------------- */

std::vector<Sort> Sort::getDatatypeParamSorts() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isParametricDatatype()) << "Not a parametric datatype sort.";
  //////// all checks before this line
  return typeNodeVectorToSorts(d_solver, d_type->getParamTypes());
  ////////
  CVC4_API_TRY_CATCH_END;
}

size_t Sort::getDatatypeArity() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isDatatype()) << "Not a datatype sort.";
  //////// all checks before this line
  return d_type->getNumChildren() - 1;
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Tuple sort ---------------------------------------------------------- */

size_t Sort::getTupleLength() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isTuple()) << "Not a tuple sort.";
  //////// all checks before this line
  return d_type->getTupleLength();
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::vector<Sort> Sort::getTupleSorts() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(isTuple()) << "Not a tuple sort.";
  //////// all checks before this line
  return typeNodeVectorToSorts(d_solver, d_type->getTupleTypes());
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* --------------------------------------------------------------------- */

std::ostream& operator<<(std::ostream& out, const Sort& s)
{
  out << s.toString();
  return out;
}

size_t SortHashFunction::operator()(const Sort& s) const
{
  return TypeNodeHashFunction()(*s.d_type);
}

/* Helpers                                                                    */
/* -------------------------------------------------------------------------- */

/* Split out to avoid nested API calls (problematic with API tracing).        */
/* .......................................................................... */

bool Sort::isNullHelper() const { return d_type->isNull(); }

/* -------------------------------------------------------------------------- */
/* Op                                                                     */
/* -------------------------------------------------------------------------- */

Op::Op() : d_solver(nullptr), d_kind(NULL_EXPR), d_node(new cvc5::Node()) {}

Op::Op(const Solver* slv, const Kind k)
    : d_solver(slv), d_kind(k), d_node(new cvc5::Node())
{
}

Op::Op(const Solver* slv, const Kind k, const cvc5::Node& n)
    : d_solver(slv), d_kind(k), d_node(new cvc5::Node(n))
{
}

Op::~Op()
{
  if (d_solver != nullptr)
  {
    // Ensure that the correct node manager is in scope when the type node is
    // destroyed.
    NodeManagerScope scope(d_solver->getNodeManager());
    d_node.reset();
  }
}

/* Public methods                                                             */
bool Op::operator==(const Op& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (d_node->isNull() && t.d_node->isNull())
  {
    return (d_kind == t.d_kind);
  }
  else if (d_node->isNull() || t.d_node->isNull())
  {
    return false;
  }
  return (d_kind == t.d_kind) && (*d_node == *t.d_node);
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Op::operator!=(const Op& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return !(*this == t);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Kind Op::getKind() const
{
  CVC4_API_CHECK(d_kind != NULL_EXPR) << "Expecting a non-null Kind";
  //////// all checks before this line
  return d_kind;
}

bool Op::isNull() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Op::isIndexed() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isIndexedHelper();
  ////////
  CVC4_API_TRY_CATCH_END;
}

template <>
std::string Op::getIndices() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(!d_node->isNull())
      << "Expecting a non-null internal expression. This Op is not indexed.";
  Kind k = intToExtKind(d_node->getKind());
  CVC4_API_CHECK(k == DIVISIBLE || k == RECORD_UPDATE)
      << "Can't get string index from"
      << " kind " << kindToString(k);
  //////// all checks before this line
  return k == DIVISIBLE ? d_node->getConst<Divisible>().k.toString()
                        : d_node->getConst<RecordUpdate>().getField();
  ////////
  CVC4_API_TRY_CATCH_END;
}

template <>
uint32_t Op::getIndices() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(!d_node->isNull())
      << "Expecting a non-null internal expression. This Op is not indexed.";
  //////// all checks before this line

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
      i = d_node->getConst<FloatingPointToUBV>().d_bv_size.d_size;
      break;
    case FLOATINGPOINT_TO_SBV:
      i = d_node->getConst<FloatingPointToSBV>().d_bv_size.d_size;
      break;
    case TUPLE_UPDATE: i = d_node->getConst<TupleUpdate>().getIndex(); break;
    case REGEXP_REPEAT:
      i = d_node->getConst<RegExpRepeat>().d_repeatAmount;
      break;
    default:
      CVC4_API_CHECK(false) << "Can't get uint32_t index from"
                            << " kind " << kindToString(k);
  }
  return i;
  ////////
  CVC4_API_TRY_CATCH_END;
}

template <>
std::pair<uint32_t, uint32_t> Op::getIndices() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(!d_node->isNull())
      << "Expecting a non-null internal expression. This Op is not indexed.";
  //////// all checks before this line

  std::pair<uint32_t, uint32_t> indices;
  Kind k = intToExtKind(d_node->getKind());

  // using if/else instead of case statement because want local variables
  if (k == BITVECTOR_EXTRACT)
  {
    cvc5::BitVectorExtract ext = d_node->getConst<BitVectorExtract>();
    indices = std::make_pair(ext.d_high, ext.d_low);
  }
  else if (k == FLOATINGPOINT_TO_FP_IEEE_BITVECTOR)
  {
    cvc5::FloatingPointToFPIEEEBitVector ext =
        d_node->getConst<FloatingPointToFPIEEEBitVector>();
    indices = std::make_pair(ext.getSize().exponentWidth(),
                             ext.getSize().significandWidth());
  }
  else if (k == FLOATINGPOINT_TO_FP_FLOATINGPOINT)
  {
    cvc5::FloatingPointToFPFloatingPoint ext =
        d_node->getConst<FloatingPointToFPFloatingPoint>();
    indices = std::make_pair(ext.getSize().exponentWidth(),
                             ext.getSize().significandWidth());
  }
  else if (k == FLOATINGPOINT_TO_FP_REAL)
  {
    cvc5::FloatingPointToFPReal ext = d_node->getConst<FloatingPointToFPReal>();
    indices = std::make_pair(ext.getSize().exponentWidth(),
                             ext.getSize().significandWidth());
  }
  else if (k == FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR)
  {
    cvc5::FloatingPointToFPSignedBitVector ext =
        d_node->getConst<FloatingPointToFPSignedBitVector>();
    indices = std::make_pair(ext.getSize().exponentWidth(),
                             ext.getSize().significandWidth());
  }
  else if (k == FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR)
  {
    cvc5::FloatingPointToFPUnsignedBitVector ext =
        d_node->getConst<FloatingPointToFPUnsignedBitVector>();
    indices = std::make_pair(ext.getSize().exponentWidth(),
                             ext.getSize().significandWidth());
  }
  else if (k == FLOATINGPOINT_TO_FP_GENERIC)
  {
    cvc5::FloatingPointToFPGeneric ext =
        d_node->getConst<FloatingPointToFPGeneric>();
    indices = std::make_pair(ext.getSize().exponentWidth(),
                             ext.getSize().significandWidth());
  }
  else if (k == REGEXP_LOOP)
  {
    cvc5::RegExpLoop ext = d_node->getConst<RegExpLoop>();
    indices = std::make_pair(ext.d_loopMinOcc, ext.d_loopMaxOcc);
  }
  else
  {
    CVC4_API_CHECK(false) << "Can't get pair<uint32_t, uint32_t> indices from"
                          << " kind " << kindToString(k);
  }
  return indices;
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::string Op::toString() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (d_node->isNull())
  {
    return kindToString(d_kind);
  }
  else
  {
    CVC4_API_CHECK(!d_node->isNull())
        << "Expecting a non-null internal expression";
    if (d_solver != nullptr)
    {
      NodeManagerScope scope(d_solver->getNodeManager());
      return d_node->toString();
    }
    return d_node->toString();
  }
  ////////
  CVC4_API_TRY_CATCH_END;
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
    return NodeHashFunction()(*t.d_node);
  }
  else
  {
    return KindHashFunction()(t.d_kind);
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

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

Term::Term() : d_solver(nullptr), d_node(new cvc5::Node()) {}

Term::Term(const Solver* slv, const cvc5::Node& n) : d_solver(slv)
{
  // Ensure that we create the node in the correct node manager.
  NodeManagerScope scope(d_solver->getNodeManager());
  d_node.reset(new cvc5::Node(n));
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

bool Term::operator==(const Term& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_node == *t.d_node;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Term::operator!=(const Term& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_node != *t.d_node;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Term::operator<(const Term& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_node < *t.d_node;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Term::operator>(const Term& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_node > *t.d_node;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Term::operator<=(const Term& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_node <= *t.d_node;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Term::operator>=(const Term& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_node >= *t.d_node;
  ////////
  CVC4_API_TRY_CATCH_END;
}

size_t Term::getNumChildren() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line

  // special case for apply kinds
  if (isApplyKind(d_node->getKind()))
  {
    return d_node->getNumChildren() + 1;
  }
  if(isCastedReal())
  {
    return 0;
  }
  return d_node->getNumChildren();
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Term::operator[](size_t index) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(index < getNumChildren()) << "index out of bound";
  CVC4_API_CHECK(!isApplyKind(d_node->getKind()) || d_node->hasOperator())
      << "Expected apply kind to have operator when accessing child of Term";
  //////// all checks before this line

  // special cases for apply kinds
  if (isApplyKind(d_node->getKind()))
  {
    if (index == 0)
    {
      // return the operator
      return Term(d_solver, d_node->getOperator());
    }
    else
    {
      index -= 1;
    }
  }
  // otherwise we are looking up child at (index-1)
  return Term(d_solver, (*d_node)[index]);
  ////////
  CVC4_API_TRY_CATCH_END;
}

uint64_t Term::getId() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getId();
  ////////
  CVC4_API_TRY_CATCH_END;
}

Kind Term::getKind() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getKindHelper();
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Term::getSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  NodeManagerScope scope(d_solver->getNodeManager());
  //////// all checks before this line
  return Sort(d_solver, d_node->getType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Term::substitute(const Term& term, const Term& replacement) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK_TERM(term);
  CVC4_API_CHECK_TERM(replacement);
  CVC4_API_CHECK(term.getSort().isComparableTo(replacement.getSort()))
      << "Expecting terms of comparable sort in substitute";
  //////// all checks before this line
  return Term(
      d_solver,
      d_node->substitute(TNode(*term.d_node), TNode(*replacement.d_node)));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Term::substitute(const std::vector<Term>& terms,
                      const std::vector<Term>& replacements) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(terms.size() == replacements.size())
      << "Expecting vectors of the same arity in substitute";
  CVC4_API_TERM_CHECK_TERMS_WITH_TERMS_COMPARABLE_TO(terms, replacements);
  //////// all checks before this line
  std::vector<Node> nodes = Term::termVectorToNodes(terms);
  std::vector<Node> nodeReplacements = Term::termVectorToNodes(replacements);
  return Term(d_solver,
              d_node->substitute(nodes.begin(),
                                 nodes.end(),
                                 nodeReplacements.begin(),
                                 nodeReplacements.end()));
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Term::hasOp() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->hasOperator();
  ////////
  CVC4_API_TRY_CATCH_END;
}

Op Term::getOp() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(d_node->hasOperator())
      << "Expecting Term to have an Op when calling getOp()";
  //////// all checks before this line

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
    cvc5::Node op = d_node->getOperator();
    return Op(d_solver, intToExtKind(d_node->getKind()), op);
  }
  // Notice this is the only case where getKindHelper is used, since the
  // cases above do not have special cases for intToExtKind.
  return Op(d_solver, getKindHelper());
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Term::isNull() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Term::getConstArrayBase() const
{
  NodeManagerScope scope(d_solver->getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  // CONST_ARRAY kind maps to STORE_ALL internal kind
  CVC4_API_CHECK(d_node->getKind() == cvc5::Kind::STORE_ALL)
      << "Expecting a CONST_ARRAY Term when calling getConstArrayBase()";
  //////// all checks before this line
  return Term(d_solver, d_node->getConst<ArrayStoreAll>().getValue());
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::vector<Term> Term::getConstSequenceElements() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(d_node->getKind() == cvc5::Kind::CONST_SEQUENCE)
      << "Expecting a CONST_SEQUENCE Term when calling "
         "getConstSequenceElements()";
  //////// all checks before this line
  const std::vector<Node>& elems = d_node->getConst<Sequence>().getVec();
  std::vector<Term> terms;
  for (const Node& t : elems)
  {
    terms.push_back(Term(d_solver, t));
  }
  return terms;
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Term::notTerm() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  Node res = d_node->notNode();
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Term::andTerm(const Term& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK_TERM(t);
  //////// all checks before this line
  Node res = d_node->andNode(*t.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Term::orTerm(const Term& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK_TERM(t);
  //////// all checks before this line
  Node res = d_node->orNode(*t.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Term::xorTerm(const Term& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK_TERM(t);
  //////// all checks before this line
  Node res = d_node->xorNode(*t.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Term::eqTerm(const Term& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK_TERM(t);
  //////// all checks before this line
  Node res = d_node->eqNode(*t.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Term::impTerm(const Term& t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK_TERM(t);
  //////// all checks before this line
  Node res = d_node->impNode(*t.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Term::iteTerm(const Term& then_t, const Term& else_t) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK_TERM(then_t);
  CVC4_API_CHECK_TERM(else_t);
  //////// all checks before this line
  Node res = d_node->iteNode(*then_t.d_node, *else_t.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::string Term::toString() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (d_solver != nullptr)
  {
    NodeManagerScope scope(d_solver->getNodeManager());
    return d_node->toString();
  }
  return d_node->toString();
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term::const_iterator::const_iterator()
    : d_solver(nullptr), d_origNode(nullptr), d_pos(0)
{
}

Term::const_iterator::const_iterator(const Solver* slv,
                                     const std::shared_ptr<cvc5::Node>& n,
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

const cvc5::Node& Term::getNode(void) const { return *d_node; }

namespace detail {
const Rational& getRational(const cvc5::Node& node)
{
  return node.getConst<Rational>();
}
Integer getInteger(const cvc5::Node& node)
{
  return node.getConst<Rational>().getNumerator();
}
template <typename T>
bool checkIntegerBounds(const Integer& i)
{
  return i >= std::numeric_limits<T>::min()
         && i <= std::numeric_limits<T>::max();
}
bool checkReal32Bounds(const Rational& r)
{
  return checkIntegerBounds<std::int32_t>(r.getNumerator())
         && checkIntegerBounds<std::uint32_t>(r.getDenominator());
}
bool checkReal64Bounds(const Rational& r)
{
  return checkIntegerBounds<std::int64_t>(r.getNumerator())
         && checkIntegerBounds<std::uint64_t>(r.getDenominator());
}

bool isInteger(const Node& node)
{
  return node.getKind() == cvc5::Kind::CONST_RATIONAL
         && node.getConst<Rational>().isIntegral();
}
bool isInt32(const Node& node)
{
  return isInteger(node)
         && checkIntegerBounds<std::int32_t>(getInteger(node));
}
bool isUInt32(const Node& node)
{
  return isInteger(node)
         && checkIntegerBounds<std::uint32_t>(getInteger(node));
}
bool isInt64(const Node& node)
{
  return isInteger(node)
         && checkIntegerBounds<std::int64_t>(getInteger(node));
}
bool isUInt64(const Node& node)
{
  return isInteger(node)
         && checkIntegerBounds<std::uint64_t>(getInteger(node));
}
}  // namespace detail

bool Term::isInt32() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return detail::isInt32(*d_node);
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::int32_t Term::getInt32() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(detail::isInt32(*d_node))
      << "Term should be a Int32 when calling getInt32()";
  //////// all checks before this line
  return detail::getInteger(*d_node).getSignedInt();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Term::isUInt32() const { return detail::isUInt32(*d_node); }
std::uint32_t Term::getUInt32() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(detail::isUInt32(*d_node))
      << "Term should be a UInt32 when calling getUInt32()";
  //////// all checks before this line
  return detail::getInteger(*d_node).getUnsignedInt();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Term::isInt64() const { return detail::isInt64(*d_node); }
std::int64_t Term::getInt64() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(detail::isInt64(*d_node))
      << "Term should be a Int64 when calling getInt64()";
  //////// all checks before this line
  return detail::getInteger(*d_node).getLong();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Term::isUInt64() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return detail::isUInt64(*d_node);
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::uint64_t Term::getUInt64() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(detail::isUInt64(*d_node))
      << "Term should be a UInt64 when calling getUInt64()";
  //////// all checks before this line
  return detail::getInteger(*d_node).getUnsignedLong();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Term::isInteger() const { return detail::isInteger(*d_node); }
std::string Term::getInteger() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(detail::isInteger(*d_node))
      << "Term should be an Int when calling getIntString()";
  //////// all checks before this line
  return detail::getInteger(*d_node).toString();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Term::isString() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == cvc5::Kind::CONST_STRING;
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::wstring Term::getString() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(d_node->getKind() == cvc5::Kind::CONST_STRING)
      << "Term should be a String when calling getString()";
  //////// all checks before this line
  return d_node->getConst<cvc5::String>().toWString();
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::vector<Node> Term::termVectorToNodes(const std::vector<Term>& terms)
{
  std::vector<Node> res;
  for (const Term& t : terms)
  {
    res.push_back(t.getNode());
  }
  return res;
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
  return NodeHashFunction()(*t.d_node);
}

/* Helpers                                                                    */
/* -------------------------------------------------------------------------- */

/* Split out to avoid nested API calls (problematic with API tracing).        */
/* .......................................................................... */

bool Term::isNullHelper() const
{
  /* Split out to avoid nested API calls (problematic with API tracing). */
  return d_node->isNull();
}

Kind Term::getKindHelper() const
{
  /* Sequence kinds do not exist internally, so we must convert their internal
   * (string) versions back to sequence. All operators where this is
   * necessary are such that their first child is of sequence type, which
   * we check here. */
  if (d_node->getNumChildren() > 0 && (*d_node)[0].getType().isSequence())
  {
    switch (d_node->getKind())
    {
      case cvc5::Kind::STRING_CONCAT: return SEQ_CONCAT;
      case cvc5::Kind::STRING_LENGTH: return SEQ_LENGTH;
      case cvc5::Kind::STRING_SUBSTR: return SEQ_EXTRACT;
      case cvc5::Kind::STRING_UPDATE: return SEQ_UPDATE;
      case cvc5::Kind::STRING_CHARAT: return SEQ_AT;
      case cvc5::Kind::STRING_STRCTN: return SEQ_CONTAINS;
      case cvc5::Kind::STRING_STRIDOF: return SEQ_INDEXOF;
      case cvc5::Kind::STRING_STRREPL: return SEQ_REPLACE;
      case cvc5::Kind::STRING_STRREPLALL: return SEQ_REPLACE_ALL;
      case cvc5::Kind::STRING_REV: return SEQ_REV;
      case cvc5::Kind::STRING_PREFIX: return SEQ_PREFIX;
      case cvc5::Kind::STRING_SUFFIX: return SEQ_SUFFIX;
      default:
        // fall through to conversion below
        break;
    }
  }
  // Notice that kinds like APPLY_TYPE_ASCRIPTION will be converted to
  // INTERNAL_KIND.
  if (isCastedReal())
  {
    return CONST_RATIONAL;
  }
  return intToExtKind(d_node->getKind());
}

bool Term::isCastedReal() const
{
  if (d_node->getKind() == kind::CAST_TO_REAL)
  {
    return (*d_node)[0].isConst() && (*d_node)[0].getType().isInteger();
  }
  return false;
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
    : d_solver(slv), d_ctor(new cvc5::DTypeConstructor(name))
{
}
DatatypeConstructorDecl::~DatatypeConstructorDecl()
{
  if (d_ctor != nullptr)
  {
    // ensure proper node manager is in scope
    NodeManagerScope scope(d_solver->getNodeManager());
    d_ctor.reset();
  }
}

void DatatypeConstructorDecl::addSelector(const std::string& name,
                                          const Sort& sort)
{
  NodeManagerScope scope(d_solver->getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK_SORT(sort);
  CVC4_API_ARG_CHECK_EXPECTED(!sort.isNull(), sort)
      << "non-null range sort for selector";
  //////// all checks before this line
  d_ctor->addArg(name, *sort.d_type);
  ////////
  CVC4_API_TRY_CATCH_END;
}

void DatatypeConstructorDecl::addSelectorSelf(const std::string& name)
{
  NodeManagerScope scope(d_solver->getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  d_ctor->addArgSelf(name);
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool DatatypeConstructorDecl::isNull() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::string DatatypeConstructorDecl::toString() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  std::stringstream ss;
  ss << *d_ctor;
  return ss.str();
  ////////
  CVC4_API_TRY_CATCH_END;
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

bool DatatypeConstructorDecl::isNullHelper() const { return d_ctor == nullptr; }

/* DatatypeDecl ------------------------------------------------------------- */

DatatypeDecl::DatatypeDecl() : d_solver(nullptr), d_dtype(nullptr) {}

DatatypeDecl::DatatypeDecl(const Solver* slv,
                           const std::string& name,
                           bool isCoDatatype)
    : d_solver(slv), d_dtype(new cvc5::DType(name, isCoDatatype))
{
}

DatatypeDecl::DatatypeDecl(const Solver* slv,
                           const std::string& name,
                           const Sort& param,
                           bool isCoDatatype)
    : d_solver(slv),
      d_dtype(new cvc5::DType(
          name, std::vector<TypeNode>{*param.d_type}, isCoDatatype))
{
}

DatatypeDecl::DatatypeDecl(const Solver* slv,
                           const std::string& name,
                           const std::vector<Sort>& params,
                           bool isCoDatatype)
    : d_solver(slv)
{
  std::vector<TypeNode> tparams = Sort::sortVectorToTypeNodes(params);
  d_dtype = std::shared_ptr<cvc5::DType>(
      new cvc5::DType(name, tparams, isCoDatatype));
}

bool DatatypeDecl::isNullHelper() const { return !d_dtype; }

DatatypeDecl::~DatatypeDecl()
{
  if (d_dtype != nullptr)
  {
    // ensure proper node manager is in scope
    NodeManagerScope scope(d_solver->getNodeManager());
    d_dtype.reset();
  }
}

void DatatypeDecl::addConstructor(const DatatypeConstructorDecl& ctor)
{
  NodeManagerScope scope(d_solver->getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_ARG_CHECK_NOT_NULL(ctor);
  CVC4_API_ARG_CHECK_SOLVER("datatype constructor declaration", ctor);
  //////// all checks before this line
  d_dtype->addConstructor(ctor.d_ctor);
  ////////
  CVC4_API_TRY_CATCH_END;
}

size_t DatatypeDecl::getNumConstructors() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->getNumConstructors();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool DatatypeDecl::isParametric() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isParametric();
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::string DatatypeDecl::toString() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  std::stringstream ss;
  ss << *d_dtype;
  return ss.str();
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::string DatatypeDecl::getName() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->getName();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool DatatypeDecl::isNull() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::ostream& operator<<(std::ostream& out, const DatatypeDecl& dtdecl)
{
  out << dtdecl.toString();
  return out;
}

cvc5::DType& DatatypeDecl::getDatatype(void) const { return *d_dtype; }

/* DatatypeSelector --------------------------------------------------------- */

DatatypeSelector::DatatypeSelector() : d_solver(nullptr), d_stor(nullptr) {}

DatatypeSelector::DatatypeSelector(const Solver* slv,
                                   const cvc5::DTypeSelector& stor)
    : d_solver(slv), d_stor(new cvc5::DTypeSelector(stor))
{
  CVC4_API_CHECK(d_stor->isResolved()) << "Expected resolved datatype selector";
}

DatatypeSelector::~DatatypeSelector()
{
  if (d_stor != nullptr)
  {
    // ensure proper node manager is in scope
    NodeManagerScope scope(d_solver->getNodeManager());
    d_stor.reset();
  }
}

std::string DatatypeSelector::getName() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_stor->getName();
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term DatatypeSelector::getSelectorTerm() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Term(d_solver, d_stor->getSelector());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort DatatypeSelector::getRangeSort() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Sort(d_solver, d_stor->getRangeType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool DatatypeSelector::isNull() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::string DatatypeSelector::toString() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  std::stringstream ss;
  ss << *d_stor;
  return ss.str();
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::ostream& operator<<(std::ostream& out, const DatatypeSelector& stor)
{
  out << stor.toString();
  return out;
}

bool DatatypeSelector::isNullHelper() const { return d_stor == nullptr; }

/* DatatypeConstructor ------------------------------------------------------ */

DatatypeConstructor::DatatypeConstructor() : d_solver(nullptr), d_ctor(nullptr)
{
}

DatatypeConstructor::DatatypeConstructor(const Solver* slv,
                                         const cvc5::DTypeConstructor& ctor)
    : d_solver(slv), d_ctor(new cvc5::DTypeConstructor(ctor))
{
  CVC4_API_CHECK(d_ctor->isResolved())
      << "Expected resolved datatype constructor";
}

DatatypeConstructor::~DatatypeConstructor()
{
  if (d_ctor != nullptr)
  {
    // ensure proper node manager is in scope
    NodeManagerScope scope(d_solver->getNodeManager());
    d_ctor.reset();
  }
}

std::string DatatypeConstructor::getName() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_ctor->getName();
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term DatatypeConstructor::getConstructorTerm() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Term(d_solver, d_ctor->getConstructor());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term DatatypeConstructor::getSpecializedConstructorTerm(
    const Sort& retSort) const
{
  NodeManagerScope scope(d_solver->getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(d_ctor->isResolved())
      << "Expected resolved datatype constructor";
  CVC4_API_CHECK(retSort.isDatatype())
      << "Cannot get specialized constructor type for non-datatype type "
      << retSort;
  //////// all checks before this line

  NodeManager* nm = d_solver->getNodeManager();
  Node ret =
      nm->mkNode(kind::APPLY_TYPE_ASCRIPTION,
                 nm->mkConst(AscriptionType(
                     d_ctor->getSpecializedConstructorType(*retSort.d_type))),
                 d_ctor->getConstructor());
  (void)ret.getType(true); /* kick off type checking */
  // apply type ascription to the operator
  Term sctor = api::Term(d_solver, ret);
  return sctor;
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term DatatypeConstructor::getTesterTerm() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Term(d_solver, d_ctor->getTester());
  ////////
  CVC4_API_TRY_CATCH_END;
}

size_t DatatypeConstructor::getNumSelectors() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_ctor->getNumArgs();
  ////////
  CVC4_API_TRY_CATCH_END;
}

DatatypeSelector DatatypeConstructor::operator[](size_t index) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return DatatypeSelector(d_solver, (*d_ctor)[index]);
  ////////
  CVC4_API_TRY_CATCH_END;
}

DatatypeSelector DatatypeConstructor::operator[](const std::string& name) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getSelectorForName(name);
  ////////
  CVC4_API_TRY_CATCH_END;
}

DatatypeSelector DatatypeConstructor::getSelector(const std::string& name) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getSelectorForName(name);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term DatatypeConstructor::getSelectorTerm(const std::string& name) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getSelector(name).getSelectorTerm();
  ////////
  CVC4_API_TRY_CATCH_END;
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
    const Solver* slv, const cvc5::DTypeConstructor& ctor, bool begin)
{
  d_solver = slv;
  d_int_stors = &ctor.getArgs();

  const std::vector<std::shared_ptr<cvc5::DTypeSelector>>& sels =
      ctor.getArgs();
  for (const std::shared_ptr<cvc5::DTypeSelector>& s : sels)
  {
    /* Can not use emplace_back here since constructor is private. */
    d_stors.push_back(DatatypeSelector(d_solver, *s.get()));
  }
  d_idx = begin ? 0 : sels.size();
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

bool DatatypeConstructor::isNull() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::string DatatypeConstructor::toString() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  std::stringstream ss;
  ss << *d_ctor;
  return ss.str();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool DatatypeConstructor::isNullHelper() const { return d_ctor == nullptr; }

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
  if (!foundSel)
  {
    std::stringstream snames;
    snames << "{ ";
    for (size_t i = 0, ncons = getNumSelectors(); i < ncons; i++)
    {
      snames << (*d_ctor)[i].getName() << " ";
    }
    snames << "} ";
    CVC4_API_CHECK(foundSel) << "No selector " << name << " for constructor "
                             << getName() << " exists among " << snames.str();
  }
  return DatatypeSelector(d_solver, (*d_ctor)[index]);
}

std::ostream& operator<<(std::ostream& out, const DatatypeConstructor& ctor)
{
  out << ctor.toString();
  return out;
}

/* Datatype ----------------------------------------------------------------- */

Datatype::Datatype(const Solver* slv, const cvc5::DType& dtype)
    : d_solver(slv), d_dtype(new cvc5::DType(dtype))
{
  CVC4_API_CHECK(d_dtype->isResolved()) << "Expected resolved datatype";
}

Datatype::Datatype() : d_solver(nullptr), d_dtype(nullptr) {}

Datatype::~Datatype()
{
  if (d_dtype != nullptr)
  {
    // ensure proper node manager is in scope
    NodeManagerScope scope(d_solver->getNodeManager());
    d_dtype.reset();
  }
}

DatatypeConstructor Datatype::operator[](size_t idx) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  CVC4_API_CHECK(idx < getNumConstructors()) << "Index out of bounds.";
  //////// all checks before this line
  return DatatypeConstructor(d_solver, (*d_dtype)[idx]);
  ////////
  CVC4_API_TRY_CATCH_END;
}

DatatypeConstructor Datatype::operator[](const std::string& name) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getConstructorForName(name);
  ////////
  CVC4_API_TRY_CATCH_END;
}

DatatypeConstructor Datatype::getConstructor(const std::string& name) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getConstructorForName(name);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Datatype::getConstructorTerm(const std::string& name) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getConstructor(name).getConstructorTerm();
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::string Datatype::getName() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->getName();
  ////////
  CVC4_API_TRY_CATCH_END;
}

size_t Datatype::getNumConstructors() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->getNumConstructors();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Datatype::isParametric() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isParametric();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Datatype::isCodatatype() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isCodatatype();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Datatype::isTuple() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isTuple();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Datatype::isRecord() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isRecord();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Datatype::isFinite() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isFinite();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Datatype::isWellFounded() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isWellFounded();
  ////////
  CVC4_API_TRY_CATCH_END;
}
bool Datatype::hasNestedRecursion() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->hasNestedRecursion();
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Datatype::isNull() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::string Datatype::toString() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->getName();
  ////////
  CVC4_API_TRY_CATCH_END;
}

Datatype::const_iterator Datatype::begin() const
{
  return Datatype::const_iterator(d_solver, *d_dtype, true);
}

Datatype::const_iterator Datatype::end() const
{
  return Datatype::const_iterator(d_solver, *d_dtype, false);
}

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
  if (!foundCons)
  {
    std::stringstream snames;
    snames << "{ ";
    for (size_t i = 0, ncons = getNumConstructors(); i < ncons; i++)
    {
      snames << (*d_dtype)[i].getName() << " ";
    }
    snames << "}";
    CVC4_API_CHECK(foundCons) << "No constructor " << name << " for datatype "
                              << getName() << " exists, among " << snames.str();
  }
  return DatatypeConstructor(d_solver, (*d_dtype)[index]);
}

Datatype::const_iterator::const_iterator(const Solver* slv,
                                         const cvc5::DType& dtype,
                                         bool begin)
    : d_solver(slv), d_int_ctors(&dtype.getConstructors())
{
  const std::vector<std::shared_ptr<DTypeConstructor>>& cons =
      dtype.getConstructors();
  for (const std::shared_ptr<DTypeConstructor>& c : cons)
  {
    /* Can not use emplace_back here since constructor is private. */
    d_ctors.push_back(DatatypeConstructor(d_solver, *c.get()));
  }
  d_idx = begin ? 0 : cons.size();
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

bool Datatype::isNullHelper() const { return d_dtype == nullptr; }

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

void Grammar::addRule(const Term& ntSymbol, const Term& rule)
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(!d_isResolved) << "Grammar cannot be modified after passing "
                                   "it as an argument to synthFun/synthInv";
  CVC4_API_CHECK_TERM(ntSymbol);
  CVC4_API_CHECK_TERM(rule);
  CVC4_API_ARG_CHECK_EXPECTED(
      d_ntsToTerms.find(ntSymbol) != d_ntsToTerms.cend(), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  CVC4_API_CHECK(ntSymbol.d_node->getType() == rule.d_node->getType())
      << "Expected ntSymbol and rule to have the same sort";
  CVC4_API_ARG_CHECK_EXPECTED(!containsFreeVariables(rule), rule)
      << "a term whose free variables are limited to synthFun/synthInv "
         "parameters and non-terminal symbols of the grammar";
  //////// all checks before this line
  d_ntsToTerms[ntSymbol].push_back(rule);
  ////////
  CVC4_API_TRY_CATCH_END;
}

void Grammar::addRules(const Term& ntSymbol, const std::vector<Term>& rules)
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(!d_isResolved) << "Grammar cannot be modified after passing "
                                   "it as an argument to synthFun/synthInv";
  CVC4_API_CHECK_TERM(ntSymbol);
  CVC4_API_CHECK_TERMS_WITH_SORT(rules, ntSymbol.getSort());
  CVC4_API_ARG_CHECK_EXPECTED(
      d_ntsToTerms.find(ntSymbol) != d_ntsToTerms.cend(), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  for (size_t i = 0, n = rules.size(); i < n; ++i)
  {
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !containsFreeVariables(rules[i]), rules[i], rules, i)
        << "a term whose free variables are limited to synthFun/synthInv "
           "parameters and non-terminal symbols of the grammar";
  }
  //////// all checks before this line
  d_ntsToTerms[ntSymbol].insert(
      d_ntsToTerms[ntSymbol].cend(), rules.cbegin(), rules.cend());
  ////////
  CVC4_API_TRY_CATCH_END;
}

void Grammar::addAnyConstant(const Term& ntSymbol)
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(!d_isResolved) << "Grammar cannot be modified after passing "
                                   "it as an argument to synthFun/synthInv";
  CVC4_API_CHECK_TERM(ntSymbol);
  CVC4_API_ARG_CHECK_EXPECTED(
      d_ntsToTerms.find(ntSymbol) != d_ntsToTerms.cend(), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  //////// all checks before this line
  d_allowConst.insert(ntSymbol);
  ////////
  CVC4_API_TRY_CATCH_END;
}

void Grammar::addAnyVariable(const Term& ntSymbol)
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(!d_isResolved) << "Grammar cannot be modified after passing "
                                   "it as an argument to synthFun/synthInv";
  CVC4_API_CHECK_TERM(ntSymbol);
  CVC4_API_ARG_CHECK_EXPECTED(
      d_ntsToTerms.find(ntSymbol) != d_ntsToTerms.cend(), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  //////// all checks before this line
  d_allowVars.insert(ntSymbol);
  ////////
  CVC4_API_TRY_CATCH_END;
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
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
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
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Grammar::resolve()
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line

  d_isResolved = true;

  Term bvl;

  if (!d_sygusVars.empty())
  {
    bvl = Term(
        d_solver,
        d_solver->getNodeManager()->mkNode(
            cvc5::kind::BOUND_VAR_LIST, Term::termVectorToNodes(d_sygusVars)));
  }

  std::unordered_map<Term, Sort, TermHashFunction> ntsToUnres(d_ntSyms.size());

  for (Term ntsymbol : d_ntSyms)
  {
    // make the unresolved type, used for referencing the final version of
    // the ntsymbol's datatype
    ntsToUnres[ntsymbol] =
        Sort(d_solver, d_solver->getNodeManager()->mkSort(ntsymbol.toString()));
  }

  std::vector<cvc5::DType> datatypes;
  std::set<TypeNode> unresTypes;

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
      addSygusConstructorVariables(dtDecl,
                                   Sort(d_solver, ntSym.d_node->getType()));
    }

    bool aci = d_allowConst.find(ntSym) != d_allowConst.end();
    TypeNode btt = ntSym.d_node->getType();
    dtDecl.d_dtype->setSygus(btt, *bvl.d_node, aci, false);

    // We can be in a case where the only rule specified was (Variable T)
    // and there are no variables of type T, in which case this is a bogus
    // grammar. This results in the error below.
    CVC4_API_CHECK(dtDecl.d_dtype->getNumConstructors() != 0)
        << "Grouped rule listing for " << *dtDecl.d_dtype
        << " produced an empty rule list";

    datatypes.push_back(*dtDecl.d_dtype);
    unresTypes.insert(*ntsToUnres[ntSym].d_type);
  }

  std::vector<TypeNode> datatypeTypes =
      d_solver->getNodeManager()->mkMutualDatatypeTypes(
          datatypes, unresTypes, NodeManager::DATATYPE_FLAG_PLACEHOLDER);

  // return is the first datatype
  return Sort(d_solver, datatypeTypes[0]);
  ////////
  CVC4_API_TRY_CATCH_END;
}

void Grammar::addSygusConstructorTerm(
    DatatypeDecl& dt,
    const Term& term,
    const std::unordered_map<Term, Sort, TermHashFunction>& ntsToUnres) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_DTDECL(dt);
  CVC4_API_CHECK_TERM(term);
  CVC4_API_CHECK_TERMS_MAP(ntsToUnres);
  //////// all checks before this line

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
    Term lbvl =
        Term(d_solver,
             d_solver->getNodeManager()->mkNode(cvc5::kind::BOUND_VAR_LIST,
                                                Term::termVectorToNodes(args)));
    // its operator is a lambda
    op = Term(d_solver,
              d_solver->getNodeManager()->mkNode(
                  cvc5::kind::LAMBDA, *lbvl.d_node, *op.d_node));
  }
  std::vector<TypeNode> cargst = Sort::sortVectorToTypeNodes(cargs);
  dt.d_dtype->addSygusConstructor(*op.d_node, ssCName.str(), cargst);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Grammar::purifySygusGTerm(
    const Term& term,
    std::vector<Term>& args,
    std::vector<Sort>& cargs,
    const std::unordered_map<Term, Sort, TermHashFunction>& ntsToUnres) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_TERM(term);
  CVC4_API_CHECK_TERMS(args);
  CVC4_API_CHECK_SORTS(cargs);
  CVC4_API_CHECK_TERMS_MAP(ntsToUnres);
  //////// all checks before this line

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
    childChanged = childChanged || *ptermc.d_node != (*term.d_node)[i];
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
    nb.append(Term::termVectorToNodes(pchildren));
    nret = nb.constructNode();
  }
  else
  {
    nret = d_solver->getNodeManager()->mkNode(
        term.d_node->getKind(), Term::termVectorToNodes(pchildren));
  }

  return Term(d_solver, nret);
  ////////
  CVC4_API_TRY_CATCH_END;
}

void Grammar::addSygusConstructorVariables(DatatypeDecl& dt,
                                           const Sort& sort) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK_DTDECL(dt);
  CVC4_API_CHECK_SORT(sort);
  //////// all checks before this line

  // each variable of appropriate type becomes a sygus constructor in dt.
  for (unsigned i = 0, size = d_sygusVars.size(); i < size; i++)
  {
    Term v = d_sygusVars[i];
    if (v.d_node->getType() == *sort.d_type)
    {
      std::stringstream ss;
      ss << v;
      std::vector<TypeNode> cargs;
      dt.d_dtype->addSygusConstructor(*v.d_node, ss.str(), cargs);
    }
  }
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Grammar::containsFreeVariables(const Term& rule) const
{
  std::unordered_set<TNode, TNodeHashFunction> scope;

  for (const Term& sygusVar : d_sygusVars)
  {
    scope.emplace(*sygusVar.d_node);
  }

  for (const Term& ntsymbol : d_ntSyms)
  {
    scope.emplace(*ntsymbol.d_node);
  }

  std::unordered_set<Node, NodeHashFunction> fvs;
  return expr::getFreeVariablesScope(*rule.d_node, fvs, scope, false);
}

std::ostream& operator<<(std::ostream& out, const Grammar& grammar)
{
  return out << grammar.toString();
}

/* -------------------------------------------------------------------------- */
/* Rounding Mode for Floating Points                                          */
/* -------------------------------------------------------------------------- */

const static std::
    unordered_map<RoundingMode, cvc5::RoundingMode, RoundingModeHashFunction>
        s_rmodes{
            {ROUND_NEAREST_TIES_TO_EVEN,
             cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN},
            {ROUND_TOWARD_POSITIVE, cvc5::RoundingMode::ROUND_TOWARD_POSITIVE},
            {ROUND_TOWARD_NEGATIVE, cvc5::RoundingMode::ROUND_TOWARD_NEGATIVE},
            {ROUND_TOWARD_ZERO, cvc5::RoundingMode::ROUND_TOWARD_ZERO},
            {ROUND_NEAREST_TIES_TO_AWAY,
             cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY},
        };

const static std::unordered_map<cvc5::RoundingMode,
                                RoundingMode,
                                cvc5::RoundingModeHashFunction>
    s_rmodes_internal{
        {cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN,
         ROUND_NEAREST_TIES_TO_EVEN},
        {cvc5::RoundingMode::ROUND_TOWARD_POSITIVE, ROUND_TOWARD_POSITIVE},
        {cvc5::RoundingMode::ROUND_TOWARD_POSITIVE, ROUND_TOWARD_NEGATIVE},
        {cvc5::RoundingMode::ROUND_TOWARD_ZERO, ROUND_TOWARD_ZERO},
        {cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY,
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
  d_nodeMgr.reset(new NodeManager());
  d_originalOptions.reset(new Options());
  if (opts != nullptr)
  {
    d_originalOptions->copyValues(*opts);
  }
  d_smtEngine.reset(new SmtEngine(d_nodeMgr.get(), d_originalOptions.get()));
  d_smtEngine->setSolver(this);
  d_rng.reset(new Random(d_smtEngine->getOptions()[options::seed]));
#if CVC4_STATISTICS_ON
  d_stats.reset(new Statistics());
  d_smtEngine->getStatisticsRegistry()->registerStat(&d_stats->d_consts);
  d_smtEngine->getStatisticsRegistry()->registerStat(&d_stats->d_vars);
  d_smtEngine->getStatisticsRegistry()->registerStat(&d_stats->d_terms);
#endif
}

Solver::~Solver() {}

/* Helpers and private functions                                              */
/* -------------------------------------------------------------------------- */

NodeManager* Solver::getNodeManager(void) const { return d_nodeMgr.get(); }

void Solver::increment_term_stats(Kind kind) const
{
#ifdef CVC4_STATISTICS_ON
  d_stats->d_terms << kind;
#endif
}

void Solver::increment_vars_consts_stats(const Sort& sort, bool is_var) const
{
#ifdef CVC4_STATISTICS_ON
  const TypeNode tn = sort.getTypeNode();
  TypeConstant tc = tn.getKind() == cvc5::kind::TYPE_CONSTANT
                        ? tn.getConst<TypeConstant>()
                        : LAST_TYPE;
  if (is_var)
  {
    d_stats->d_vars << tc;
  }
  else
  {
    d_stats->d_consts << tc;
  }
#endif
}

/* Split out to avoid nested API calls (problematic with API tracing).        */
/* .......................................................................... */

template <typename T>
Term Solver::mkValHelper(T t) const
{
  //////// all checks before this line
  Node res = getNodeManager()->mkConst(t);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
}

Term Solver::mkRealFromStrHelper(const std::string& s) const
{
  //////// all checks before this line
  try
  {
    cvc5::Rational r = s.find('/') != std::string::npos
                           ? cvc5::Rational(s)
                           : cvc5::Rational::fromDecimal(s);
    return mkValHelper<cvc5::Rational>(r);
  }
  catch (const std::invalid_argument& e)
  {
    /* Catch to throw with a more meaningful error message. To be caught in
     * enclosing CVC4_API_TRY_CATCH_* block to throw CVC4ApiException. */
    std::stringstream message;
    message << "Cannot construct Real or Int from string argument '" << s << "'"
            << std::endl;
    throw std::invalid_argument(message.str());
  }
}

Term Solver::mkBVFromIntHelper(uint32_t size, uint64_t val) const
{
  CVC4_API_ARG_CHECK_EXPECTED(size > 0, size) << "a bit-width > 0";
  //////// all checks before this line
  return mkValHelper<cvc5::BitVector>(cvc5::BitVector(size, val));
}

Term Solver::mkBVFromStrHelper(const std::string& s, uint32_t base) const
{
  CVC4_API_ARG_CHECK_EXPECTED(!s.empty(), s) << "a non-empty string";
  CVC4_API_ARG_CHECK_EXPECTED(base == 2 || base == 10 || base == 16, base)
      << "base 2, 10, or 16";
  //////// all checks before this line
  return mkValHelper<cvc5::BitVector>(cvc5::BitVector(s, base));
}

Term Solver::mkBVFromStrHelper(uint32_t size,
                               const std::string& s,
                               uint32_t base) const
{
  CVC4_API_ARG_CHECK_EXPECTED(!s.empty(), s) << "a non-empty string";
  CVC4_API_ARG_CHECK_EXPECTED(base == 2 || base == 10 || base == 16, base)
      << "base 2, 10, or 16";
  //////// all checks before this line

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

  return mkValHelper<cvc5::BitVector>(cvc5::BitVector(size, val));
}

Term Solver::mkCharFromStrHelper(const std::string& s) const
{
  CVC4_API_CHECK(s.find_first_not_of("0123456789abcdefABCDEF", 0)
                     == std::string::npos
                 && s.size() <= 5 && s.size() > 0)
      << "Unexpected string for hexadecimal character " << s;
  uint32_t val = static_cast<uint32_t>(std::stoul(s, 0, 16));
  CVC4_API_CHECK(val < String::num_codes())
      << "Not a valid code point for hexadecimal character " << s;
  //////// all checks before this line
  std::vector<unsigned> cpts;
  cpts.push_back(val);
  return mkValHelper<cvc5::String>(cvc5::String(cpts));
}

Term Solver::getValueHelper(const Term& term) const
{
  // Note: Term is checked in the caller to avoid double checks
  //////// all checks before this line
  Node value = d_smtEngine->getValue(*term.d_node);
  Term res = Term(this, value);
  // May need to wrap in real cast so that user know this is a real.
  TypeNode tn = (*term.d_node).getType();
  if (!tn.isInteger() && value.getType().isInteger())
  {
    return ensureRealSort(res);
  }
  return res;
}

Sort Solver::mkTupleSortHelper(const std::vector<Sort>& sorts) const
{
  // Note: Sorts are checked in the caller to avoid double checks
  //////// all checks before this line
  std::vector<TypeNode> typeNodes = Sort::sortVectorToTypeNodes(sorts);
  return Sort(this, getNodeManager()->mkTupleType(typeNodes));
}

Term Solver::mkTermFromKind(Kind kind) const
{
  CVC4_API_KIND_CHECK_EXPECTED(
      kind == PI || kind == REGEXP_EMPTY || kind == REGEXP_SIGMA, kind)
      << "PI or REGEXP_EMPTY or REGEXP_SIGMA";
  //////// all checks before this line
  Node res;
  if (kind == REGEXP_EMPTY || kind == REGEXP_SIGMA)
  {
    cvc5::Kind k = extToIntKind(kind);
    Assert(isDefinedIntKind(k));
    res = d_nodeMgr->mkNode(k, std::vector<Node>());
  }
  else
  {
    Assert(kind == PI);
    res = d_nodeMgr->mkNullaryOperator(d_nodeMgr->realType(), cvc5::kind::PI);
  }
  (void)res.getType(true); /* kick off type checking */
  increment_term_stats(kind);
  return Term(this, res);
}

Term Solver::mkTermHelper(Kind kind, const std::vector<Term>& children) const
{
  // Note: Kind and children are checked in the caller to avoid double checks
  //////// all checks before this line

  std::vector<Node> echildren = Term::termVectorToNodes(children);
  cvc5::Kind k = extToIntKind(kind);
  Node res;
  if (echildren.size() > 2)
  {
    if (kind == INTS_DIVISION || kind == XOR || kind == MINUS
        || kind == DIVISION || kind == HO_APPLY || kind == REGEXP_DIFF)
    {
      // left-associative, but CVC4 internally only supports 2 args
      res = d_nodeMgr->mkLeftAssociative(k, echildren);
    }
    else if (kind == IMPLIES)
    {
      // right-associative, but CVC4 internally only supports 2 args
      res = d_nodeMgr->mkRightAssociative(k, echildren);
    }
    else if (kind == EQUAL || kind == LT || kind == GT || kind == LEQ
             || kind == GEQ)
    {
      // "chainable", but CVC4 internally only supports 2 args
      res = d_nodeMgr->mkChain(k, echildren);
    }
    else if (kind::isAssociative(k))
    {
      // mkAssociative has special treatment for associative operators with lots
      // of children
      res = d_nodeMgr->mkAssociative(k, echildren);
    }
    else
    {
      // default case, must check kind
      checkMkTerm(kind, children.size());
      res = d_nodeMgr->mkNode(k, echildren);
    }
  }
  else if (kind::isAssociative(k))
  {
    // associative case, same as above
    res = d_nodeMgr->mkAssociative(k, echildren);
  }
  else
  {
    // default case, same as above
    checkMkTerm(kind, children.size());
    if (kind == api::SINGLETON)
    {
      // the type of the term is the same as the type of the internal node
      // see Term::getSort()
      TypeNode type = children[0].d_node->getType();
      // Internally NodeManager::mkSingleton needs a type argument
      // to construct a singleton, since there is no difference between
      // integers and reals (both are Rationals).
      // At the API, mkReal and mkInteger are different and therefore the
      // element type can be used safely here.
      res = getNodeManager()->mkSingleton(type, *children[0].d_node);
    }
    else if (kind == api::MK_BAG)
    {
      // the type of the term is the same as the type of the internal node
      // see Term::getSort()
      TypeNode type = children[0].d_node->getType();
      // Internally NodeManager::mkBag needs a type argument
      // to construct a bag, since there is no difference between
      // integers and reals (both are Rationals).
      // At the API, mkReal and mkInteger are different and therefore the
      // element type can be used safely here.
      res = getNodeManager()->mkBag(
          type, *children[0].d_node, *children[1].d_node);
    }
    else
    {
      res = d_nodeMgr->mkNode(k, echildren);
    }
  }

  (void)res.getType(true); /* kick off type checking */
  increment_term_stats(kind);
  return Term(this, res);
}

Term Solver::mkTermHelper(const Op& op, const std::vector<Term>& children) const
{
  // Note: Op and children are checked in the caller to avoid double checks
  checkMkTerm(op.d_kind, children.size());
  //////// all checks before this line

  if (!op.isIndexedHelper())
  {
    return mkTermHelper(op.d_kind, children);
  }

  const cvc5::Kind int_kind = extToIntKind(op.d_kind);
  std::vector<Node> echildren = Term::termVectorToNodes(children);

  NodeBuilder<> nb(int_kind);
  nb << *op.d_node;
  nb.append(echildren);
  Node res = nb.constructNode();

  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
}

std::vector<Sort> Solver::mkDatatypeSortsInternal(
    const std::vector<DatatypeDecl>& dtypedecls,
    const std::set<Sort>& unresolvedSorts) const
{
  // Note: dtypedecls and unresolvedSorts are checked in the caller to avoid
  //       double checks
  //////// all checks before this line

  std::vector<cvc5::DType> datatypes;
  for (size_t i = 0, ndts = dtypedecls.size(); i < ndts; ++i)
  {
    datatypes.push_back(dtypedecls[i].getDatatype());
  }

  std::set<TypeNode> utypes = Sort::sortSetToTypeNodes(unresolvedSorts);
  std::vector<cvc5::TypeNode> dtypes =
      getNodeManager()->mkMutualDatatypeTypes(datatypes, utypes);
  std::vector<Sort> retTypes = Sort::typeNodeVectorToSorts(this, dtypes);
  return retTypes;
}

Term Solver::synthFunHelper(const std::string& symbol,
                            const std::vector<Term>& boundVars,
                            const Sort& sort,
                            bool isInv,
                            Grammar* grammar) const
{
  // Note: boundVars, sort and grammar are checked in the caller to avoid
  //       double checks.
  std::vector<TypeNode> varTypes;
  for (const auto& bv : boundVars)
  {
    if (grammar)
    {
      CVC4_API_CHECK(grammar->d_ntSyms[0].d_node->getType() == *sort.d_type)
          << "Invalid Start symbol for grammar, Expected Start's sort to be "
          << *sort.d_type << " but found "
          << grammar->d_ntSyms[0].d_node->getType();
    }
    varTypes.push_back(bv.d_node->getType());
  }
  //////// all checks before this line

  TypeNode funType = varTypes.empty() ? *sort.d_type
                                      : getNodeManager()->mkFunctionType(
                                          varTypes, *sort.d_type);

  Node fun = getNodeManager()->mkBoundVar(symbol, funType);
  (void)fun.getType(true); /* kick off type checking */

  std::vector<Node> bvns = Term::termVectorToNodes(boundVars);

  d_smtEngine->declareSynthFun(
      fun,
      grammar == nullptr ? funType : *grammar->resolve().d_type,
      isInv,
      bvns);

  return Term(this, fun);
}

Term Solver::ensureTermSort(const Term& term, const Sort& sort) const
{
  // Note: Term and sort are checked in the caller to avoid double checks
  CVC4_API_CHECK(term.getSort() == sort
                 || (term.getSort().isInteger() && sort.isReal()))
      << "Expected conversion from Int to Real";
  //////// all checks before this line

  Sort t = term.getSort();
  if (term.getSort() == sort)
  {
    return term;
  }

  // Integers are reals, too
  Assert(t.d_type->isReal());
  Term res = term;
  if (t.isInteger())
  {
    // Must cast to Real to ensure correct type is passed to parametric type
    // constructors. We do this cast using division with 1. This has the
    // advantage wrt using TO_REAL since (constant) division is always included
    // in the theory.
    res = Term(this,
               d_nodeMgr->mkNode(extToIntKind(DIVISION),
                                 *res.d_node,
                                 d_nodeMgr->mkConst(cvc5::Rational(1))));
  }
  Assert(res.getSort() == sort);
  return res;
}

Term Solver::ensureRealSort(const Term& t) const
{
  Assert(this == t.d_solver);
  CVC4_API_ARG_CHECK_EXPECTED(
      t.getSort() == getIntegerSort() || t.getSort() == getRealSort(),
      " an integer or real term");
  // Note: Term is checked in the caller to avoid double checks
  //////// all checks before this line
  if (t.getSort() == getIntegerSort())
  {
    Node n = getNodeManager()->mkNode(kind::CAST_TO_REAL, *t.d_node);
    return Term(this, n);
  }
  return t;
}

bool Solver::isValidInteger(const std::string& s) const
{
  //////// all checks before this line
  if (s.length() == 0)
  {
    // string should not be empty
    return false;
  }

  size_t index = 0;
  if (s[index] == '-')
  {
    if (s.length() == 1)
    {
      // negative integers should contain at least one digit
      return false;
    }
    index = 1;
  }

  if (s[index] == '0' && s.length() > (index + 1))
  {
    // From SMT-Lib 2.6: A <numeral> is the digit 0 or a non-empty sequence of
    // digits not starting with 0. So integers like 001, 000 are not allowed
    return false;
  }

  // all remaining characters should be decimal digits
  for (; index < s.length(); ++index)
  {
    if (!std::isdigit(s[index]))
    {
      return false;
    }
  }

  return true;
}

/* Helpers for mkTerm checks.                                                 */
/* .......................................................................... */

void Solver::checkMkTerm(Kind kind, uint32_t nchildren) const
{
  CVC4_API_KIND_CHECK(kind);
  Assert(isDefinedIntKind(extToIntKind(kind)));
  const cvc5::kind::MetaKind mk = kind::metaKindOf(extToIntKind(kind));
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

/* Solver Configuration                                                       */
/* -------------------------------------------------------------------------- */

bool Solver::supportsFloatingPoint() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Configuration::isBuiltWithSymFPU();
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Sorts Handling                                                             */
/* -------------------------------------------------------------------------- */

Sort Solver::getNullSort(void) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, TypeNode());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::getBooleanSort(void) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->booleanType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::getIntegerSort(void) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->integerType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::getRealSort(void) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->realType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::getRegExpSort(void) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->regExpType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::getStringSort(void) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->stringType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::getRoundingModeSort(void) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";
  //////// all checks before this line
  return Sort(this, getNodeManager()->roundingModeType());
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Create sorts ------------------------------------------------------- */

Sort Solver::mkArraySort(const Sort& indexSort, const Sort& elemSort) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(indexSort);
  CVC4_API_SOLVER_CHECK_SORT(elemSort);
  //////// all checks before this line
  return Sort(
      this, getNodeManager()->mkArrayType(*indexSort.d_type, *elemSort.d_type));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkBitVectorSort(uint32_t size) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(size > 0, size) << "size > 0";
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkBitVectorType(size));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkFloatingPointSort(uint32_t exp, uint32_t sig) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";
  CVC4_API_ARG_CHECK_EXPECTED(exp > 0, exp) << "exponent size > 0";
  CVC4_API_ARG_CHECK_EXPECTED(sig > 0, sig) << "significand size > 0";
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkFloatingPointType(exp, sig));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkDatatypeSort(const DatatypeDecl& dtypedecl) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_DTDECL(dtypedecl);
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkDatatypeType(*dtypedecl.d_dtype));
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::vector<Sort> Solver::mkDatatypeSorts(
    const std::vector<DatatypeDecl>& dtypedecls) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_SOLVER_CHECK_DTDECLS(dtypedecls);
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkDatatypeSortsInternal(dtypedecls, {});
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::vector<Sort> Solver::mkDatatypeSorts(
    const std::vector<DatatypeDecl>& dtypedecls,
    const std::set<Sort>& unresolvedSorts) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_DTDECLS(dtypedecls);
  CVC4_API_SOLVER_CHECK_SORTS(unresolvedSorts);
  //////// all checks before this line
  return mkDatatypeSortsInternal(dtypedecls, unresolvedSorts);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkFunctionSort(const Sort& domain, const Sort& codomain) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_DOMAIN_SORT(domain);
  CVC4_API_SOLVER_CHECK_CODOMAIN_SORT(codomain);
  //////// all checks before this line
  return Sort(
      this, getNodeManager()->mkFunctionType(*domain.d_type, *codomain.d_type));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkFunctionSort(const std::vector<Sort>& sorts,
                            const Sort& codomain) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(sorts.size() >= 1, sorts)
      << "at least one parameter sort for function sort";
  CVC4_API_SOLVER_CHECK_DOMAIN_SORTS(sorts);
  CVC4_API_SOLVER_CHECK_CODOMAIN_SORT(codomain);
  //////// all checks before this line
  std::vector<TypeNode> argTypes = Sort::sortVectorToTypeNodes(sorts);
  return Sort(this,
              getNodeManager()->mkFunctionType(argTypes, *codomain.d_type));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkParamSort(const std::string& symbol) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(
      this,
      getNodeManager()->mkSort(symbol, NodeManager::SORT_FLAG_PLACEHOLDER));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkPredicateSort(const std::vector<Sort>& sorts) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(sorts.size() >= 1, sorts)
      << "at least one parameter sort for predicate sort";
  CVC4_API_SOLVER_CHECK_DOMAIN_SORTS(sorts);
  //////// all checks before this line
  return Sort(
      this,
      getNodeManager()->mkPredicateType(Sort::sortVectorToTypeNodes(sorts)));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkRecordSort(
    const std::vector<std::pair<std::string, Sort>>& fields) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  std::vector<std::pair<std::string, TypeNode>> f;
  for (size_t i = 0, size = fields.size(); i < size; ++i)
  {
    const auto& p = fields[i];
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(!p.second.isNull(), "sort", fields, i)
        << "non-null sort";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == p.second.d_solver, "sort", fields, i)
        << "sort associated with this solver object";
    f.emplace_back(p.first, *p.second.d_type);
  }
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkRecordType(f));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkSetSort(const Sort& elemSort) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(elemSort);
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkSetType(*elemSort.d_type));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkBagSort(const Sort& elemSort) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(elemSort);
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkBagType(*elemSort.d_type));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkSequenceSort(const Sort& elemSort) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(elemSort);
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkSequenceType(*elemSort.d_type));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkUninterpretedSort(const std::string& symbol) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkSort(symbol));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkSortConstructorSort(const std::string& symbol,
                                   size_t arity) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(arity > 0, arity) << "an arity > 0";
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkSortConstructor(symbol, arity));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Sort Solver::mkTupleSort(const std::vector<Sort>& sorts) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORTS_NOT_FUNCTION_LIKE(sorts);
  //////// all checks before this line
  return mkTupleSortHelper(sorts);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Create consts                                                              */
/* -------------------------------------------------------------------------- */

Term Solver::mkTrue(void) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Term(this, d_nodeMgr->mkConst<bool>(true));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkFalse(void) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Term(this, d_nodeMgr->mkConst<bool>(false));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkBoolean(bool val) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Term(this, d_nodeMgr->mkConst<bool>(val));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkPi() const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  Node res =
      d_nodeMgr->mkNullaryOperator(d_nodeMgr->realType(), cvc5::kind::PI);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkInteger(const std::string& s) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(isValidInteger(s), s) << " an integer ";
  Term integer = mkRealFromStrHelper(s);
  CVC4_API_ARG_CHECK_EXPECTED(integer.getSort() == getIntegerSort(), s)
      << " a string representing an integer";
  //////// all checks before this line
  return integer;
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkInteger(int64_t val) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  Term integer = mkValHelper<cvc5::Rational>(cvc5::Rational(val));
  Assert(integer.getSort() == getIntegerSort());
  return integer;
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkReal(const std::string& s) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  /* CLN and GMP handle this case differently, CLN interprets it as 0, GMP
   * throws an std::invalid_argument exception. For consistency, we treat it
   * as invalid. */
  CVC4_API_ARG_CHECK_EXPECTED(s != ".", s)
      << "a string representing a real or rational value.";
  //////// all checks before this line
  Term rational = mkRealFromStrHelper(s);
  return ensureRealSort(rational);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkReal(int64_t val) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  Term rational = mkValHelper<cvc5::Rational>(cvc5::Rational(val));
  return ensureRealSort(rational);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkReal(int64_t num, int64_t den) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  Term rational = mkValHelper<cvc5::Rational>(cvc5::Rational(num, den));
  return ensureRealSort(rational);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkRegexpEmpty() const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  Node res =
      d_nodeMgr->mkNode(cvc5::kind::REGEXP_EMPTY, std::vector<cvc5::Node>());
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkRegexpSigma() const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  Node res =
      d_nodeMgr->mkNode(cvc5::kind::REGEXP_SIGMA, std::vector<cvc5::Node>());
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkEmptySet(const Sort& sort) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(sort.isNull() || sort.isSet(), sort)
      << "null sort or set sort";
  CVC4_API_ARG_CHECK_EXPECTED(sort.isNull() || this == sort.d_solver, sort)
      << "set sort associated with this solver object";
  //////// all checks before this line
  return mkValHelper<cvc5::EmptySet>(cvc5::EmptySet(*sort.d_type));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkEmptyBag(const Sort& sort) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(sort.isNull() || sort.isBag(), sort)
      << "null sort or bag sort";
  CVC4_API_ARG_CHECK_EXPECTED(sort.isNull() || this == sort.d_solver, sort)
      << "bag sort associated with this solver object";
  //////// all checks before this line
  return mkValHelper<cvc5::EmptyBag>(cvc5::EmptyBag(*sort.d_type));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkSepNil(const Sort& sort) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  Node res =
      getNodeManager()->mkNullaryOperator(*sort.d_type, cvc5::kind::SEP_NIL);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkString(const std::string& s, bool useEscSequences) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper<cvc5::String>(cvc5::String(s, useEscSequences));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkString(const unsigned char c) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper<cvc5::String>(cvc5::String(std::string(1, c)));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkString(const std::vector<uint32_t>& s) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper<cvc5::String>(cvc5::String(s));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkChar(const std::string& s) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkCharFromStrHelper(s);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkEmptySequence(const Sort& sort) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  std::vector<Node> seq;
  Node res = d_nodeMgr->mkConst(Sequence(*sort.d_type, seq));
  return Term(this, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkUniverseSet(const Sort& sort) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line

  Node res = getNodeManager()->mkNullaryOperator(*sort.d_type,
                                                 cvc5::kind::UNIVERSE_SET);
  // TODO(#2771): Reenable?
  // (void)res->getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkBitVector(uint32_t size, uint64_t val) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkBVFromIntHelper(size, val);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkBitVector(const std::string& s, uint32_t base) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkBVFromStrHelper(s, base);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkBitVector(uint32_t size,
                         const std::string& s,
                         uint32_t base) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkBVFromStrHelper(size, s, base);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkConstArray(const Sort& sort, const Term& val) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(sort);
  CVC4_API_SOLVER_CHECK_TERM(val);
  CVC4_API_ARG_CHECK_EXPECTED(sort.isArray(), sort) << "an array sort";
  CVC4_API_CHECK(val.getSort().isSubsortOf(sort.getArrayElementSort()))
      << "Value does not match element sort";
  //////// all checks before this line

  // handle the special case of (CAST_TO_REAL n) where n is an integer
  Node n = *val.d_node;
  if (val.isCastedReal())
  {
    // this is safe because the constant array stores its type
    n = n[0];
  }
  Term res =
      mkValHelper<cvc5::ArrayStoreAll>(cvc5::ArrayStoreAll(*sort.d_type, n));
  return res;
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkPosInf(uint32_t exp, uint32_t sig) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";
  //////// all checks before this line
  return mkValHelper<cvc5::FloatingPoint>(
      FloatingPoint::makeInf(FloatingPointSize(exp, sig), false));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkNegInf(uint32_t exp, uint32_t sig) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";
  //////// all checks before this line
  return mkValHelper<cvc5::FloatingPoint>(
      FloatingPoint::makeInf(FloatingPointSize(exp, sig), true));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkNaN(uint32_t exp, uint32_t sig) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";
  //////// all checks before this line
  return mkValHelper<cvc5::FloatingPoint>(
      FloatingPoint::makeNaN(FloatingPointSize(exp, sig)));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkPosZero(uint32_t exp, uint32_t sig) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";
  //////// all checks before this line
  return mkValHelper<cvc5::FloatingPoint>(
      FloatingPoint::makeZero(FloatingPointSize(exp, sig), false));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkNegZero(uint32_t exp, uint32_t sig) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";
  //////// all checks before this line
  return mkValHelper<cvc5::FloatingPoint>(
      FloatingPoint::makeZero(FloatingPointSize(exp, sig), true));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkRoundingMode(RoundingMode rm) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";
  //////// all checks before this line
  return mkValHelper<cvc5::RoundingMode>(s_rmodes.at(rm));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkUninterpretedConst(const Sort& sort, int32_t index) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  return mkValHelper<cvc5::UninterpretedConstant>(
      cvc5::UninterpretedConstant(*sort.d_type, index));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkAbstractValue(const std::string& index) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(!index.empty(), index) << "a non-empty string";

  cvc5::Integer idx(index, 10);
  CVC4_API_ARG_CHECK_EXPECTED(idx > 0, index)
      << "a string representing an integer > 0";
  //////// all checks before this line
  return Term(this, getNodeManager()->mkConst(cvc5::AbstractValue(idx)));
  // do not call getType(), for abstract values, type can not be computed
  // until it is substituted away
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkAbstractValue(uint64_t index) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(index > 0, index) << "an integer > 0";
  //////// all checks before this line
  return Term(this,
              getNodeManager()->mkConst(cvc5::AbstractValue(Integer(index))));
  // do not call getType(), for abstract values, type can not be computed
  // until it is substituted away
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkFloatingPoint(uint32_t exp, uint32_t sig, Term val) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(Configuration::isBuiltWithSymFPU())
      << "Expected CVC4 to be compiled with SymFPU support";
  CVC4_API_SOLVER_CHECK_TERM(val);
  CVC4_API_ARG_CHECK_EXPECTED(exp > 0, exp) << "a value > 0";
  CVC4_API_ARG_CHECK_EXPECTED(sig > 0, sig) << "a value > 0";
  uint32_t bw = exp + sig;
  CVC4_API_ARG_CHECK_EXPECTED(bw == val.getSort().getBVSize(), val)
      << "a bit-vector constant with bit-width '" << bw << "'";
  CVC4_API_ARG_CHECK_EXPECTED(
      val.getSort().isBitVector() && val.d_node->isConst(), val)
      << "bit-vector constant";
  //////// all checks before this line
  return mkValHelper<cvc5::FloatingPoint>(
      cvc5::FloatingPoint(exp, sig, val.d_node->getConst<BitVector>()));
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Create constants                                                           */
/* -------------------------------------------------------------------------- */

Term Solver::mkConst(const Sort& sort, const std::string& symbol) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  Node res = d_nodeMgr->mkVar(symbol, *sort.d_type);
  (void)res.getType(true); /* kick off type checking */
  increment_vars_consts_stats(sort, false);
  return Term(this, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkConst(const Sort& sort) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  Node res = d_nodeMgr->mkVar(*sort.d_type);
  (void)res.getType(true); /* kick off type checking */
  increment_vars_consts_stats(sort, false);
  return Term(this, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Create variables                                                           */
/* -------------------------------------------------------------------------- */

Term Solver::mkVar(const Sort& sort, const std::string& symbol) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  Node res = symbol.empty() ? d_nodeMgr->mkBoundVar(*sort.d_type)
                            : d_nodeMgr->mkBoundVar(symbol, *sort.d_type);
  (void)res.getType(true); /* kick off type checking */
  increment_vars_consts_stats(sort, true);
  return Term(this, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Create datatype constructor declarations                                   */
/* -------------------------------------------------------------------------- */

DatatypeConstructorDecl Solver::mkDatatypeConstructorDecl(
    const std::string& name)
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return DatatypeConstructorDecl(this, name);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Create datatype declarations                                               */
/* -------------------------------------------------------------------------- */

DatatypeDecl Solver::mkDatatypeDecl(const std::string& name, bool isCoDatatype)
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return DatatypeDecl(this, name, isCoDatatype);
  ////////
  CVC4_API_TRY_CATCH_END;
}

DatatypeDecl Solver::mkDatatypeDecl(const std::string& name,
                                    Sort param,
                                    bool isCoDatatype)
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(param);
  //////// all checks before this line
  return DatatypeDecl(this, name, param, isCoDatatype);
  ////////
  CVC4_API_TRY_CATCH_END;
}

DatatypeDecl Solver::mkDatatypeDecl(const std::string& name,
                                    const std::vector<Sort>& params,
                                    bool isCoDatatype)
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORTS(params);
  //////// all checks before this line
  return DatatypeDecl(this, name, params, isCoDatatype);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Create terms                                                               */
/* -------------------------------------------------------------------------- */

Term Solver::mkTerm(Kind kind) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK(kind);
  //////// all checks before this line
  return mkTermFromKind(kind);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkTerm(Kind kind, const Term& child) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK(kind);
  CVC4_API_SOLVER_CHECK_TERM(child);
  //////// all checks before this line
  return mkTermHelper(kind, std::vector<Term>{child});
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK(kind);
  CVC4_API_SOLVER_CHECK_TERM(child1);
  CVC4_API_SOLVER_CHECK_TERM(child2);
  //////// all checks before this line
  return mkTermHelper(kind, std::vector<Term>{child1, child2});
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkTerm(Kind kind,
                    const Term& child1,
                    const Term& child2,
                    const Term& child3) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK(kind);
  CVC4_API_SOLVER_CHECK_TERM(child1);
  CVC4_API_SOLVER_CHECK_TERM(child2);
  CVC4_API_SOLVER_CHECK_TERM(child3);
  //////// all checks before this line
  // need to use internal term call to check e.g. associative construction
  return mkTermHelper(kind, std::vector<Term>{child1, child2, child3});
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkTerm(Kind kind, const std::vector<Term>& children) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK(kind);
  CVC4_API_SOLVER_CHECK_TERMS(children);
  //////// all checks before this line
  return mkTermHelper(kind, children);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkTerm(const Op& op) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_OP(op);
  checkMkTerm(op.d_kind, 0);
  //////// all checks before this line

  if (!op.isIndexedHelper())
  {
    return mkTermFromKind(op.d_kind);
  }

  const cvc5::Kind int_kind = extToIntKind(op.d_kind);
  Term res = Term(this, getNodeManager()->mkNode(int_kind, *op.d_node));

  (void)res.d_node->getType(true); /* kick off type checking */
  return res;
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkTerm(const Op& op, const Term& child) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_OP(op);
  CVC4_API_SOLVER_CHECK_TERM(child);
  //////// all checks before this line
  return mkTermHelper(op, std::vector<Term>{child});
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkTerm(const Op& op, const Term& child1, const Term& child2) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_OP(op);
  CVC4_API_SOLVER_CHECK_TERM(child1);
  CVC4_API_SOLVER_CHECK_TERM(child2);
  //////// all checks before this line
  return mkTermHelper(op, std::vector<Term>{child1, child2});
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkTerm(const Op& op,
                    const Term& child1,
                    const Term& child2,
                    const Term& child3) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_OP(op);
  CVC4_API_SOLVER_CHECK_TERM(child1);
  CVC4_API_SOLVER_CHECK_TERM(child2);
  CVC4_API_SOLVER_CHECK_TERM(child3);
  //////// all checks before this line
  return mkTermHelper(op, std::vector<Term>{child1, child2, child3});
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkTerm(const Op& op, const std::vector<Term>& children) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_OP(op);
  CVC4_API_SOLVER_CHECK_TERMS(children);
  //////// all checks before this line
  return mkTermHelper(op, children);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkTuple(const std::vector<Sort>& sorts,
                     const std::vector<Term>& terms) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(sorts.size() == terms.size())
      << "Expected the same number of sorts and elements";
  CVC4_API_SOLVER_CHECK_SORTS(sorts);
  CVC4_API_SOLVER_CHECK_TERMS(terms);
  //////// all checks before this line
  std::vector<cvc5::Node> args;
  for (size_t i = 0, size = sorts.size(); i < size; i++)
  {
    args.push_back(*(ensureTermSort(terms[i], sorts[i])).d_node);
  }

  Sort s = mkTupleSortHelper(sorts);
  Datatype dt = s.getDatatype();
  NodeBuilder<> nb(extToIntKind(APPLY_CONSTRUCTOR));
  nb << *dt[0].getConstructorTerm().d_node;
  nb.append(args);
  Node res = nb.constructNode();
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Create operators                                                           */
/* -------------------------------------------------------------------------- */

Op Solver::mkOp(Kind kind) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK(kind);
  CVC4_API_CHECK(s_indexed_kinds.find(kind) == s_indexed_kinds.end())
      << "Expected a kind for a non-indexed operator.";
  //////// all checks before this line
  return Op(this, kind);
  ////////
  CVC4_API_TRY_CATCH_END
}

Op Solver::mkOp(Kind kind, const std::string& arg) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK(kind);
  CVC4_API_KIND_CHECK_EXPECTED((kind == RECORD_UPDATE) || (kind == DIVISIBLE),
                               kind)
      << "RECORD_UPDATE or DIVISIBLE";
  //////// all checks before this line
  Op res;
  if (kind == RECORD_UPDATE)
  {
    res = Op(this,
             kind,
             *mkValHelper<cvc5::RecordUpdate>(cvc5::RecordUpdate(arg)).d_node);
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
             *mkValHelper<cvc5::Divisible>(cvc5::Divisible(cvc5::Integer(arg)))
                  .d_node);
  }
  return res;
  ////////
  CVC4_API_TRY_CATCH_END;
}

Op Solver::mkOp(Kind kind, uint32_t arg) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK(kind);
  //////// all checks before this line
  Op res;
  switch (kind)
  {
    case DIVISIBLE:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::Divisible>(cvc5::Divisible(arg)).d_node);
      break;
    case BITVECTOR_REPEAT:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::BitVectorRepeat>(cvc5::BitVectorRepeat(arg))
                    .d_node);
      break;
    case BITVECTOR_ZERO_EXTEND:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::BitVectorZeroExtend>(
                    cvc5::BitVectorZeroExtend(arg))
                    .d_node);
      break;
    case BITVECTOR_SIGN_EXTEND:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::BitVectorSignExtend>(
                    cvc5::BitVectorSignExtend(arg))
                    .d_node);
      break;
    case BITVECTOR_ROTATE_LEFT:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::BitVectorRotateLeft>(
                    cvc5::BitVectorRotateLeft(arg))
                    .d_node);
      break;
    case BITVECTOR_ROTATE_RIGHT:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::BitVectorRotateRight>(
                    cvc5::BitVectorRotateRight(arg))
                    .d_node);
      break;
    case INT_TO_BITVECTOR:
      res = Op(
          this,
          kind,
          *mkValHelper<cvc5::IntToBitVector>(cvc5::IntToBitVector(arg)).d_node);
      break;
    case IAND:
      res =
          Op(this, kind, *mkValHelper<cvc5::IntAnd>(cvc5::IntAnd(arg)).d_node);
      break;
    case FLOATINGPOINT_TO_UBV:
      res = Op(
          this,
          kind,
          *mkValHelper<cvc5::FloatingPointToUBV>(cvc5::FloatingPointToUBV(arg))
               .d_node);
      break;
    case FLOATINGPOINT_TO_SBV:
      res = Op(
          this,
          kind,
          *mkValHelper<cvc5::FloatingPointToSBV>(cvc5::FloatingPointToSBV(arg))
               .d_node);
      break;
    case TUPLE_UPDATE:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::TupleUpdate>(cvc5::TupleUpdate(arg)).d_node);
      break;
    case REGEXP_REPEAT:
      res =
          Op(this,
             kind,
             *mkValHelper<cvc5::RegExpRepeat>(cvc5::RegExpRepeat(arg)).d_node);
      break;
    default:
      CVC4_API_KIND_CHECK_EXPECTED(false, kind)
          << "operator kind with uint32_t argument";
  }
  Assert(!res.isNull());
  return res;
  ////////
  CVC4_API_TRY_CATCH_END;
}

Op Solver::mkOp(Kind kind, uint32_t arg1, uint32_t arg2) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK(kind);
  //////// all checks before this line

  Op res;
  switch (kind)
  {
    case BITVECTOR_EXTRACT:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::BitVectorExtract>(
                    cvc5::BitVectorExtract(arg1, arg2))
                    .d_node);
      break;
    case FLOATINGPOINT_TO_FP_IEEE_BITVECTOR:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::FloatingPointToFPIEEEBitVector>(
                    cvc5::FloatingPointToFPIEEEBitVector(arg1, arg2))
                    .d_node);
      break;
    case FLOATINGPOINT_TO_FP_FLOATINGPOINT:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::FloatingPointToFPFloatingPoint>(
                    cvc5::FloatingPointToFPFloatingPoint(arg1, arg2))
                    .d_node);
      break;
    case FLOATINGPOINT_TO_FP_REAL:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::FloatingPointToFPReal>(
                    cvc5::FloatingPointToFPReal(arg1, arg2))
                    .d_node);
      break;
    case FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::FloatingPointToFPSignedBitVector>(
                    cvc5::FloatingPointToFPSignedBitVector(arg1, arg2))
                    .d_node);
      break;
    case FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::FloatingPointToFPUnsignedBitVector>(
                    cvc5::FloatingPointToFPUnsignedBitVector(arg1, arg2))
                    .d_node);
      break;
    case FLOATINGPOINT_TO_FP_GENERIC:
      res = Op(this,
               kind,
               *mkValHelper<cvc5::FloatingPointToFPGeneric>(
                    cvc5::FloatingPointToFPGeneric(arg1, arg2))
                    .d_node);
      break;
    case REGEXP_LOOP:
      res = Op(
          this,
          kind,
          *mkValHelper<cvc5::RegExpLoop>(cvc5::RegExpLoop(arg1, arg2)).d_node);
      break;
    default:
      CVC4_API_KIND_CHECK_EXPECTED(false, kind)
          << "operator kind with two uint32_t arguments";
  }
  Assert(!res.isNull());
  return res;
  ////////
  CVC4_API_TRY_CATCH_END;
}

Op Solver::mkOp(Kind kind, const std::vector<uint32_t>& args) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_KIND_CHECK(kind);
  //////// all checks before this line

  Op res;
  switch (kind)
  {
    case TUPLE_PROJECT:
    {
      res = Op(this,
               kind,
               *mkValHelper<cvc5::TupleProjectOp>(cvc5::TupleProjectOp(args))
                    .d_node);
    }
    break;
    default:
    {
      std::string message = "operator kind with " + std::to_string(args.size())
                            + " uint32_t arguments";
      CVC4_API_KIND_CHECK_EXPECTED(false, kind) << message;
    }
  }
  Assert(!res.isNull());
  return res;
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* Non-SMT-LIB commands                                                       */
/* -------------------------------------------------------------------------- */

Term Solver::simplify(const Term& term)
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(term);
  //////// all checks before this line
  return Term(this, d_smtEngine->simplify(*term.d_node));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Result Solver::checkEntailed(const Term& term) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(!d_smtEngine->isQueryMade()
                 || d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  CVC4_API_SOLVER_CHECK_TERM(term);
  //////// all checks before this line
  cvc5::Result r = d_smtEngine->checkEntailed(*term.d_node);
  return Result(r);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Result Solver::checkEntailed(const std::vector<Term>& terms) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  NodeManagerScope scope(getNodeManager());
  CVC4_API_CHECK(!d_smtEngine->isQueryMade()
                 || d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  CVC4_API_SOLVER_CHECK_TERMS(terms);
  //////// all checks before this line
  return d_smtEngine->checkEntailed(Term::termVectorToNodes(terms));
  ////////
  CVC4_API_TRY_CATCH_END;
}

/* SMT-LIB commands                                                           */
/* -------------------------------------------------------------------------- */

/**
 *  ( assert <term> )
 */
void Solver::assertFormula(const Term& term) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(term);
  CVC4_API_SOLVER_CHECK_TERM_WITH_SORT(term, getBooleanSort());
  //////// all checks before this line
  d_smtEngine->assertFormula(*term.d_node);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( check-sat )
 */
Result Solver::checkSat(void) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  NodeManagerScope scope(getNodeManager());
  CVC4_API_CHECK(!d_smtEngine->isQueryMade()
                 || d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  //////// all checks before this line
  cvc5::Result r = d_smtEngine->checkSat();
  return Result(r);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( check-sat-assuming ( <prop_literal> ) )
 */
Result Solver::checkSatAssuming(const Term& assumption) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  NodeManagerScope scope(getNodeManager());
  CVC4_API_CHECK(!d_smtEngine->isQueryMade()
                 || d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  CVC4_API_SOLVER_CHECK_TERM_WITH_SORT(assumption, getBooleanSort());
  //////// all checks before this line
  cvc5::Result r = d_smtEngine->checkSat(*assumption.d_node);
  return Result(r);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( check-sat-assuming ( <prop_literal>* ) )
 */
Result Solver::checkSatAssuming(const std::vector<Term>& assumptions) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  NodeManagerScope scope(getNodeManager());
  CVC4_API_CHECK(!d_smtEngine->isQueryMade() || assumptions.size() == 0
                 || d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  CVC4_API_SOLVER_CHECK_TERMS_WITH_SORT(assumptions, getBooleanSort());
  //////// all checks before this line
  for (const Term& term : assumptions)
  {
    CVC4_API_SOLVER_CHECK_TERM(term);
  }
  std::vector<Node> eassumptions = Term::termVectorToNodes(assumptions);
  cvc5::Result r = d_smtEngine->checkSat(eassumptions);
  return Result(r);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( declare-datatype <symbol> <datatype_decl> )
 */
Sort Solver::declareDatatype(
    const std::string& symbol,
    const std::vector<DatatypeConstructorDecl>& ctors) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_CHECK_EXPECTED(ctors.size() > 0, ctors)
      << "a datatype declaration with at least one constructor";
  CVC4_API_SOLVER_CHECK_DTCTORDECLS(ctors);
  //////// all checks before this line
  DatatypeDecl dtdecl(this, symbol);
  for (size_t i = 0, size = ctors.size(); i < size; i++)
  {
    dtdecl.addConstructor(ctors[i]);
  }
  return Sort(this, getNodeManager()->mkDatatypeType(*dtdecl.d_dtype));
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( declare-fun <symbol> ( <sort>* ) <sort> )
 */
Term Solver::declareFun(const std::string& symbol,
                        const std::vector<Sort>& sorts,
                        const Sort& sort) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_DOMAIN_SORTS(sorts);
  CVC4_API_SOLVER_CHECK_CODOMAIN_SORT(sort);
  //////// all checks before this line

  TypeNode type = *sort.d_type;
  if (!sorts.empty())
  {
    std::vector<TypeNode> types = Sort::sortVectorToTypeNodes(sorts);
    type = getNodeManager()->mkFunctionType(types, type);
  }
  return Term(this, d_nodeMgr->mkVar(symbol, type));
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( declare-sort <symbol> <numeral> )
 */
Sort Solver::declareSort(const std::string& symbol, uint32_t arity) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (arity == 0)
  {
    return Sort(this, getNodeManager()->mkSort(symbol));
  }
  return Sort(this, getNodeManager()->mkSortConstructor(symbol, arity));
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( define-fun <function_def> )
 */
Term Solver::defineFun(const std::string& symbol,
                       const std::vector<Term>& bound_vars,
                       const Sort& sort,
                       const Term& term,
                       bool global) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_CODOMAIN_SORT(sort);
  CVC4_API_SOLVER_CHECK_TERM(term);
  CVC4_API_CHECK(sort == term.getSort())
      << "Invalid sort of function body '" << term << "', expected '" << sort
      << "'";

  std::vector<Sort> domain_sorts;
  for (const auto& bv : bound_vars)
  {
    domain_sorts.push_back(bv.getSort());
  }
  Sort fun_sort =
      domain_sorts.empty()
          ? sort
          : Sort(this,
                 getNodeManager()->mkFunctionType(
                     Sort::sortVectorToTypeNodes(domain_sorts), *sort.d_type));
  Term fun = mkConst(fun_sort, symbol);

  CVC4_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN(fun, bound_vars, domain_sorts);
  //////// all checks before this line

  d_smtEngine->defineFunction(
      *fun.d_node, Term::termVectorToNodes(bound_vars), *term.d_node, global);
  return fun;
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::defineFun(const Term& fun,
                       const std::vector<Term>& bound_vars,
                       const Term& term,
                       bool global) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(fun);
  CVC4_API_SOLVER_CHECK_TERM(term);
  if (fun.getSort().isFunction())
  {
    std::vector<Sort> domain_sorts = fun.getSort().getFunctionDomainSorts();
    CVC4_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN(fun, bound_vars, domain_sorts);
    Sort codomain = fun.getSort().getFunctionCodomainSort();
    CVC4_API_CHECK(codomain == term.getSort())
        << "Invalid sort of function body '" << term << "', expected '"
        << codomain << "'";
  }
  else
  {
    CVC4_API_SOLVER_CHECK_BOUND_VARS(bound_vars);
    CVC4_API_ARG_CHECK_EXPECTED(bound_vars.size() == 0, fun)
        << "function or nullary symbol";
  }
  //////// all checks before this line
  std::vector<Node> ebound_vars = Term::termVectorToNodes(bound_vars);
  d_smtEngine->defineFunction(*fun.d_node, ebound_vars, *term.d_node, global);
  return fun;
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( define-fun-rec <function_def> )
 */
Term Solver::defineFunRec(const std::string& symbol,
                          const std::vector<Term>& bound_vars,
                          const Sort& sort,
                          const Term& term,
                          bool global) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;

  CVC4_API_CHECK(d_smtEngine->getUserLogicInfo().isQuantified())
      << "recursive function definitions require a logic with quantifiers";
  CVC4_API_CHECK(
      d_smtEngine->getUserLogicInfo().isTheoryEnabled(theory::THEORY_UF))
      << "recursive function definitions require a logic with uninterpreted "
         "functions";

  CVC4_API_SOLVER_CHECK_TERM(term);
  CVC4_API_SOLVER_CHECK_CODOMAIN_SORT(sort);
  CVC4_API_CHECK(sort == term.getSort())
      << "Invalid sort of function body '" << term << "', expected '" << sort
      << "'";

  std::vector<Sort> domain_sorts;
  for (const auto& bv : bound_vars)
  {
    domain_sorts.push_back(bv.getSort());
  }
  Sort fun_sort =
      domain_sorts.empty()
          ? sort
          : Sort(this,
                 getNodeManager()->mkFunctionType(
                     Sort::sortVectorToTypeNodes(domain_sorts), *sort.d_type));
  Term fun = mkConst(fun_sort, symbol);

  CVC4_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN(fun, bound_vars, domain_sorts);
  //////// all checks before this line

  d_smtEngine->defineFunctionRec(
      *fun.d_node, Term::termVectorToNodes(bound_vars), *term.d_node, global);

  return fun;
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::defineFunRec(const Term& fun,
                          const std::vector<Term>& bound_vars,
                          const Term& term,
                          bool global) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;

  CVC4_API_CHECK(d_smtEngine->getUserLogicInfo().isQuantified())
      << "recursive function definitions require a logic with quantifiers";
  CVC4_API_CHECK(
      d_smtEngine->getUserLogicInfo().isTheoryEnabled(theory::THEORY_UF))
      << "recursive function definitions require a logic with uninterpreted "
         "functions";

  CVC4_API_SOLVER_CHECK_TERM(fun);
  CVC4_API_SOLVER_CHECK_TERM(term);
  if (fun.getSort().isFunction())
  {
    std::vector<Sort> domain_sorts = fun.getSort().getFunctionDomainSorts();
    CVC4_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN(fun, bound_vars, domain_sorts);
    Sort codomain = fun.getSort().getFunctionCodomainSort();
    CVC4_API_CHECK(codomain == term.getSort())
        << "Invalid sort of function body '" << term << "', expected '"
        << codomain << "'";
  }
  else
  {
    CVC4_API_SOLVER_CHECK_BOUND_VARS(bound_vars);
    CVC4_API_ARG_CHECK_EXPECTED(bound_vars.size() == 0, fun)
        << "function or nullary symbol";
  }
  //////// all checks before this line

  std::vector<Node> ebound_vars = Term::termVectorToNodes(bound_vars);
  d_smtEngine->defineFunctionRec(
      *fun.d_node, ebound_vars, *term.d_node, global);
  return fun;
  ////////
  CVC4_API_TRY_CATCH_END;
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
  CVC4_API_TRY_CATCH_BEGIN;

  CVC4_API_CHECK(d_smtEngine->getUserLogicInfo().isQuantified())
      << "recursive function definitions require a logic with quantifiers";
  CVC4_API_CHECK(
      d_smtEngine->getUserLogicInfo().isTheoryEnabled(theory::THEORY_UF))
      << "recursive function definitions require a logic with uninterpreted "
         "functions";
  CVC4_API_SOLVER_CHECK_TERMS(funs);
  CVC4_API_SOLVER_CHECK_TERMS(terms);

  size_t funs_size = funs.size();
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(funs_size == bound_vars.size(), bound_vars)
      << "'" << funs_size << "'";
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(funs_size == terms.size(), terms)
      << "'" << funs_size << "'";

  for (size_t j = 0; j < funs_size; ++j)
  {
    const Term& fun = funs[j];
    const std::vector<Term>& bvars = bound_vars[j];
    const Term& term = terms[j];

    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == fun.d_solver, "function", funs, j)
        << "function associated with this solver object";
    CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == term.d_solver, "term", terms, j)
        << "term associated with this solver object";

    if (fun.getSort().isFunction())
    {
      std::vector<Sort> domain_sorts = fun.getSort().getFunctionDomainSorts();
      CVC4_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN(fun, bvars, domain_sorts);
      Sort codomain = fun.getSort().getFunctionCodomainSort();
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
          codomain == term.getSort(), "sort of function body", terms, j)
          << "'" << codomain << "'";
    }
    else
    {
      CVC4_API_SOLVER_CHECK_BOUND_VARS(bvars);
      CVC4_API_ARG_CHECK_EXPECTED(bvars.size() == 0, fun)
          << "function or nullary symbol";
    }
  }
  //////// all checks before this line
  std::vector<Node> efuns = Term::termVectorToNodes(funs);
  std::vector<std::vector<Node>> ebound_vars;
  for (const auto& v : bound_vars)
  {
    ebound_vars.push_back(Term::termVectorToNodes(v));
  }
  std::vector<Node> nodes = Term::termVectorToNodes(terms);
  d_smtEngine->defineFunctionsRec(efuns, ebound_vars, nodes, global);
  ////////
  CVC4_API_TRY_CATCH_END;
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
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  std::vector<Node> assertions = d_smtEngine->getAssertions();
  /* Can not use
   *   return std::vector<Term>(assertions.begin(), assertions.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const Node& e : assertions)
  {
    res.push_back(Term(this, e));
  }
  return res;
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( get-info <info_flag> )
 */
std::string Solver::getInfo(const std::string& flag) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_RECOVERABLE_CHECK(d_smtEngine->isValidGetInfoFlag(flag))
      << "Unrecognized flag for getInfo.";
  //////// all checks before this line
  return d_smtEngine->getInfo(flag).toString();
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( get-option <keyword> )
 */
std::string Solver::getOption(const std::string& option) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  Node res = d_smtEngine->getOption(option);
  return res.toString();
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( get-unsat-assumptions )
 */
std::vector<Term> Solver::getUnsatAssumptions(void) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  NodeManagerScope scope(getNodeManager());
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot get unsat assumptions unless incremental solving is enabled "
         "(try --incremental)";
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::unsatAssumptions])
      << "Cannot get unsat assumptions unless explicitly enabled "
         "(try --produce-unsat-assumptions)";
  CVC4_API_CHECK(d_smtEngine->getSmtMode() == SmtMode::UNSAT)
      << "Cannot get unsat assumptions unless in unsat mode.";
  //////// all checks before this line

  std::vector<Node> uassumptions = d_smtEngine->getUnsatAssumptions();
  /* Can not use
   *   return std::vector<Term>(uassumptions.begin(), uassumptions.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const Node& n : uassumptions)
  {
    res.push_back(Term(this, n));
  }
  return res;
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( get-unsat-core )
 */
std::vector<Term> Solver::getUnsatCore(void) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  NodeManagerScope scope(getNodeManager());
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::unsatCores])
      << "Cannot get unsat core unless explicitly enabled "
         "(try --produce-unsat-cores)";
  CVC4_API_RECOVERABLE_CHECK(d_smtEngine->getSmtMode() == SmtMode::UNSAT)
      << "Cannot get unsat core unless in unsat mode.";
  //////// all checks before this line
  UnsatCore core = d_smtEngine->getUnsatCore();
  /* Can not use
   *   return std::vector<Term>(core.begin(), core.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const Node& e : core)
  {
    res.push_back(Term(this, e));
  }
  return res;
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( get-proof )
 */
std::string Solver::getProof(void) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  NodeManagerScope scope(getNodeManager());
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::produceProofs])
      << "Cannot get proof explicitly enabled (try --prooduce-proofs)";
  CVC4_API_RECOVERABLE_CHECK(d_smtEngine->getSmtMode() == SmtMode::UNSAT)
      << "Cannot get proof unless in unsat mode.";
  return d_smtEngine->getProof();
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( get-value ( <term> ) )
 */
Term Solver::getValue(const Term& term) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(term);
  //////// all checks before this line
  return getValueHelper(term);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( get-value ( <term>+ ) )
 */
std::vector<Term> Solver::getValue(const std::vector<Term>& terms) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  NodeManagerScope scope(getNodeManager());
  CVC4_API_RECOVERABLE_CHECK(d_smtEngine->getOptions()[options::produceModels])
      << "Cannot get value unless model generation is enabled "
         "(try --produce-models)";
  CVC4_API_RECOVERABLE_CHECK(d_smtEngine->isSmtModeSat())
      << "Cannot get value unless after a SAT or unknown response.";
  CVC4_API_SOLVER_CHECK_TERMS(terms);
  //////// all checks before this line

  std::vector<Term> res;
  for (size_t i = 0, n = terms.size(); i < n; ++i)
  {
    /* Can not use emplace_back here since constructor is private. */
    res.push_back(getValueHelper(terms[i]));
  }
  return res;
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::getQuantifierElimination(const Term& q) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(q);
  //////// all checks before this line
  return Term(this,
              d_smtEngine->getQuantifierElimination(q.getNode(), true, true));
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::getQuantifierEliminationDisjunct(const Term& q) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(q);
  //////// all checks before this line
  return Term(
      this, d_smtEngine->getQuantifierElimination(q.getNode(), false, true));
  ////////
  CVC4_API_TRY_CATCH_END;
}

void Solver::declareSeparationHeap(const Sort& locSort,
                                   const Sort& dataSort) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(locSort);
  CVC4_API_SOLVER_CHECK_SORT(dataSort);
  CVC4_API_CHECK(
      d_smtEngine->getLogicInfo().isTheoryEnabled(theory::THEORY_SEP))
      << "Cannot obtain separation logic expressions if not using the "
         "separation logic theory.";
  //////// all checks before this line
  d_smtEngine->declareSepHeap(locSort.getTypeNode(), dataSort.getTypeNode());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::getSeparationHeap() const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(
      d_smtEngine->getLogicInfo().isTheoryEnabled(theory::THEORY_SEP))
      << "Cannot obtain separation logic expressions if not using the "
         "separation logic theory.";
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::produceModels])
      << "Cannot get separation heap term unless model generation is enabled "
         "(try --produce-models)";
  CVC4_API_RECOVERABLE_CHECK(d_smtEngine->isSmtModeSat())
      << "Can only get separtion heap term after sat or unknown response.";
  //////// all checks before this line
  return Term(this, d_smtEngine->getSepHeapExpr());
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::getSeparationNilTerm() const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(
      d_smtEngine->getLogicInfo().isTheoryEnabled(theory::THEORY_SEP))
      << "Cannot obtain separation logic expressions if not using the "
         "separation logic theory.";
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::produceModels])
      << "Cannot get separation nil term unless model generation is enabled "
         "(try --produce-models)";
  CVC4_API_RECOVERABLE_CHECK(d_smtEngine->isSmtModeSat())
      << "Can only get separtion nil term after sat or unknown response.";
  //////// all checks before this line
  return Term(this, d_smtEngine->getSepNilExpr());
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( pop <numeral> )
 */
void Solver::pop(uint32_t nscopes) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot pop when not solving incrementally (use --incremental)";
  CVC4_API_CHECK(nscopes <= d_smtEngine->getNumUserLevels())
      << "Cannot pop beyond first pushed context";
  //////// all checks before this line
  for (uint32_t n = 0; n < nscopes; ++n)
  {
    d_smtEngine->pop();
  }
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Solver::getInterpolant(const Term& conj, Term& output) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(conj);
  //////// all checks before this line
  Node result;
  bool success = d_smtEngine->getInterpol(*conj.d_node, result);
  if (success)
  {
    output = Term(this, result);
  }
  return success;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Solver::getInterpolant(const Term& conj,
                            Grammar& grammar,
                            Term& output) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(conj);
  //////// all checks before this line
  Node result;
  bool success =
      d_smtEngine->getInterpol(*conj.d_node, *grammar.resolve().d_type, result);
  if (success)
  {
    output = Term(this, result);
  }
  return success;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Solver::getAbduct(const Term& conj, Term& output) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(conj);
  //////// all checks before this line
  Node result;
  bool success = d_smtEngine->getAbduct(*conj.d_node, result);
  if (success)
  {
    output = Term(this, result);
  }
  return success;
  ////////
  CVC4_API_TRY_CATCH_END;
}

bool Solver::getAbduct(const Term& conj, Grammar& grammar, Term& output) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(conj);
  //////// all checks before this line
  Node result;
  bool success =
      d_smtEngine->getAbduct(*conj.d_node, *grammar.resolve().d_type, result);
  if (success)
  {
    output = Term(this, result);
  }
  return success;
  ////////
  CVC4_API_TRY_CATCH_END;
}

void Solver::blockModel() const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::produceModels])
      << "Cannot get value unless model generation is enabled "
         "(try --produce-models)";
  CVC4_API_RECOVERABLE_CHECK(d_smtEngine->isSmtModeSat())
      << "Can only block model after sat or unknown response.";
  //////// all checks before this line
  d_smtEngine->blockModel();
  ////////
  CVC4_API_TRY_CATCH_END;
}

void Solver::blockModelValues(const std::vector<Term>& terms) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::produceModels])
      << "Cannot get value unless model generation is enabled "
         "(try --produce-models)";
  CVC4_API_RECOVERABLE_CHECK(d_smtEngine->isSmtModeSat())
      << "Can only block model values after sat or unknown response.";
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(!terms.empty(), terms)
      << "a non-empty set of terms";
  CVC4_API_SOLVER_CHECK_TERMS(terms);
  //////// all checks before this line
  d_smtEngine->blockModelValues(Term::termVectorToNodes(terms));
  ////////
  CVC4_API_TRY_CATCH_END;
}

void Solver::printInstantiations(std::ostream& out) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  d_smtEngine->printInstantiations(out);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( push <numeral> )
 */
void Solver::push(uint32_t nscopes) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(d_smtEngine->getOptions()[options::incrementalSolving])
      << "Cannot push when not solving incrementally (use --incremental)";
  //////// all checks before this line
  for (uint32_t n = 0; n < nscopes; ++n)
  {
    d_smtEngine->push();
  }
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( reset-assertions )
 */
void Solver::resetAssertions(void) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  d_smtEngine->resetAssertions();
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( set-info <attribute> )
 */
void Solver::setInfo(const std::string& keyword, const std::string& value) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_RECOVERABLE_ARG_CHECK_EXPECTED(
      keyword == "source" || keyword == "category" || keyword == "difficulty"
          || keyword == "filename" || keyword == "license" || keyword == "name"
          || keyword == "notes" || keyword == "smt-lib-version"
          || keyword == "status",
      keyword)
      << "'source', 'category', 'difficulty', 'filename', 'license', 'name', "
         "'notes', 'smt-lib-version' or 'status'";
  CVC4_API_RECOVERABLE_ARG_CHECK_EXPECTED(
      keyword != "smt-lib-version" || value == "2" || value == "2.0"
          || value == "2.5" || value == "2.6",
      value)
      << "'2.0', '2.5', '2.6'";
  CVC4_API_ARG_CHECK_EXPECTED(keyword != "status" || value == "sat"
                                  || value == "unsat" || value == "unknown",
                              value)
      << "'sat', 'unsat' or 'unknown'";
  //////// all checks before this line
  d_smtEngine->setInfo(keyword, value);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( set-logic <symbol> )
 */
void Solver::setLogic(const std::string& logic) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(!d_smtEngine->isFullyInited())
      << "Invalid call to 'setLogic', solver is already fully initialized";
  cvc5::LogicInfo logic_info(logic);
  //////// all checks before this line
  d_smtEngine->setLogic(logic_info);
  ////////
  CVC4_API_TRY_CATCH_END;
}

/**
 *  ( set-option <option> )
 */
void Solver::setOption(const std::string& option,
                       const std::string& value) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_CHECK(!d_smtEngine->isFullyInited())
      << "Invalid call to 'setOption', solver is already fully initialized";
  //////// all checks before this line
  d_smtEngine->setOption(option, value);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::mkSygusVar(const Sort& sort, const std::string& symbol) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  Node res = getNodeManager()->mkBoundVar(symbol, *sort.d_type);
  (void)res.getType(true); /* kick off type checking */

  d_smtEngine->declareSygusVar(res);

  return Term(this, res);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Grammar Solver::mkSygusGrammar(const std::vector<Term>& boundVars,
                               const std::vector<Term>& ntSymbols) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(!ntSymbols.empty(), ntSymbols)
      << "a non-empty vector";
  CVC4_API_SOLVER_CHECK_BOUND_VARS(boundVars);
  CVC4_API_SOLVER_CHECK_BOUND_VARS(ntSymbols);
  //////// all checks before this line
  return Grammar(this, boundVars, ntSymbols);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::synthFun(const std::string& symbol,
                      const std::vector<Term>& boundVars,
                      const Sort& sort) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_BOUND_VARS(boundVars);
  CVC4_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  return synthFunHelper(symbol, boundVars, sort);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::synthFun(const std::string& symbol,
                      const std::vector<Term>& boundVars,
                      Sort sort,
                      Grammar& grammar) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_BOUND_VARS(boundVars);
  CVC4_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  return synthFunHelper(symbol, boundVars, sort, false, &grammar);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::synthInv(const std::string& symbol,
                      const std::vector<Term>& boundVars) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_BOUND_VARS(boundVars);
  //////// all checks before this line
  return synthFunHelper(
      symbol, boundVars, Sort(this, getNodeManager()->booleanType()), true);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::synthInv(const std::string& symbol,
                      const std::vector<Term>& boundVars,
                      Grammar& grammar) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_BOUND_VARS(boundVars);
  //////// all checks before this line
  return synthFunHelper(symbol,
                        boundVars,
                        Sort(this, getNodeManager()->booleanType()),
                        true,
                        &grammar);
  ////////
  CVC4_API_TRY_CATCH_END;
}

void Solver::addSygusConstraint(const Term& term) const
{
  NodeManagerScope scope(getNodeManager());
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(term);
  CVC4_API_ARG_CHECK_EXPECTED(
      term.d_node->getType() == getNodeManager()->booleanType(), term)
      << "boolean term";
  //////// all checks before this line
  d_smtEngine->assertSygusConstraint(*term.d_node);
  ////////
  CVC4_API_TRY_CATCH_END;
}

void Solver::addSygusInvConstraint(Term inv,
                                   Term pre,
                                   Term trans,
                                   Term post) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(inv);
  CVC4_API_SOLVER_CHECK_TERM(pre);
  CVC4_API_SOLVER_CHECK_TERM(trans);
  CVC4_API_SOLVER_CHECK_TERM(post);

  CVC4_API_ARG_CHECK_EXPECTED(inv.d_node->getType().isFunction(), inv)
      << "a function";

  TypeNode invType = inv.d_node->getType();

  CVC4_API_ARG_CHECK_EXPECTED(invType.getRangeType().isBoolean(), inv)
      << "boolean range";

  CVC4_API_CHECK(pre.d_node->getType() == invType)
      << "Expected inv and pre to have the same sort";

  CVC4_API_CHECK(post.d_node->getType() == invType)
      << "Expected inv and post to have the same sort";
  //////// all checks before this line

  const std::vector<TypeNode>& invArgTypes = invType.getArgTypes();

  std::vector<TypeNode> expectedTypes;
  expectedTypes.reserve(2 * invArgTypes.size() + 1);

  for (size_t i = 0, n = invArgTypes.size(); i < 2 * n; i += 2)
  {
    expectedTypes.push_back(invArgTypes[i % n]);
    expectedTypes.push_back(invArgTypes[(i + 1) % n]);
  }

  expectedTypes.push_back(invType.getRangeType());
  TypeNode expectedTransType = getNodeManager()->mkFunctionType(expectedTypes);

  CVC4_API_CHECK(trans.d_node->getType() == expectedTransType)
      << "Expected trans's sort to be " << invType;

  d_smtEngine->assertSygusInvConstraint(
      *inv.d_node, *pre.d_node, *trans.d_node, *post.d_node);
  ////////
  CVC4_API_TRY_CATCH_END;
}

Result Solver::checkSynth() const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_smtEngine->checkSynth();
  ////////
  CVC4_API_TRY_CATCH_END;
}

Term Solver::getSynthSolution(Term term) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_SOLVER_CHECK_TERM(term);

  std::map<cvc5::Node, cvc5::Node> map;
  CVC4_API_CHECK(d_smtEngine->getSynthSolutions(map))
      << "The solver is not in a state immediately preceded by a "
         "successful call to checkSynth";

  std::map<cvc5::Node, cvc5::Node>::const_iterator it = map.find(*term.d_node);

  CVC4_API_CHECK(it != map.cend()) << "Synth solution not found for given term";
  //////// all checks before this line
  return Term(this, it->second);
  ////////
  CVC4_API_TRY_CATCH_END;
}

std::vector<Term> Solver::getSynthSolutions(
    const std::vector<Term>& terms) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  CVC4_API_ARG_SIZE_CHECK_EXPECTED(!terms.empty(), terms) << "non-empty vector";
  CVC4_API_SOLVER_CHECK_TERMS(terms);

  std::map<cvc5::Node, cvc5::Node> map;
  CVC4_API_CHECK(d_smtEngine->getSynthSolutions(map))
      << "The solver is not in a state immediately preceded by a "
         "successful call to checkSynth";
  //////// all checks before this line

  std::vector<Term> synthSolution;
  synthSolution.reserve(terms.size());

  for (size_t i = 0, n = terms.size(); i < n; ++i)
  {
    std::map<cvc5::Node, cvc5::Node>::const_iterator it =
        map.find(*terms[i].d_node);

    CVC4_API_CHECK(it != map.cend())
        << "Synth solution not found for term at index " << i;

    synthSolution.push_back(Term(this, it->second));
  }

  return synthSolution;
  ////////
  CVC4_API_TRY_CATCH_END;
}

void Solver::printSynthSolution(std::ostream& out) const
{
  CVC4_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  d_smtEngine->printSynthSolution(out);
  ////////
  CVC4_API_TRY_CATCH_END;
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

}  // namespace api

}  // namespace cvc5

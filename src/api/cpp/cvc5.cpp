/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 C++ API.
 *
 * A brief note on how to guard API functions:
 *
 * In general, we think of API guards as a fence -- they are supposed to make
 * sure that no invalid arguments get passed into internal realms of cvc5.
 * Thus we always want to catch such cases on the API level (and can then
 * assert internally that no invalid argument is passed in).
 *
 * The only special case is when we use 3rd party back-ends we have no control
 * over, and which throw (invalid_argument) exceptions anyways. In this case,
 * we do not replicate argument checks but delegate them to the back-end,
 * catch thrown exceptions, and raise a CVC5ApiException.
 *
 * Our Integer implementation, e.g., is such a special case since we support
 * two different back end implementations (GMP, CLN). Be aware that they do
 * not fully agree on what is (in)valid input, which requires extra checks for
 * consistent behavior (see Solver::mkRealOrIntegerFromStrHelper for example).
 */

#include "api/cpp/cvc5.h"

#include <cstring>
#include <sstream>

#include "api/cpp/cvc5_checks.h"
#include "base/check.h"
#include "base/configuration.h"
#include "base/modal_exception.h"
#include "expr/array_store_all.h"
#include "expr/ascription_type.h"
#include "expr/cardinality_constraint.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/dtype_selector.h"
#include "expr/emptybag.h"
#include "expr/emptyset.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node_manager_attributes.h"
#include "expr/sequence.h"
#include "expr/type_node.h"
#include "options/base_options.h"
#include "options/expr_options.h"
#include "options/main_options.h"
#include "options/option_exception.h"
#include "options/options.h"
#include "options/options_public.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "proof/unsat_core.h"
#include "smt/env.h"
#include "smt/model.h"
#include "smt/smt_mode.h"
#include "smt/solver_engine.h"
#include "theory/bags/table_project_op.h"
#include "theory/datatypes/tuple_project_op.h"
#include "theory/logic_info.h"
#include "theory/theory_model.h"
#include "util/bitvector.h"
#include "util/divisible.h"
#include "util/floatingpoint.h"
#include "util/iand.h"
#include "util/random.h"
#include "util/regexp.h"
#include "util/result.h"
#include "util/roundingmode.h"
#include "util/statistics_registry.h"
#include "util/statistics_stats.h"
#include "util/statistics_value.h"
#include "util/string.h"
#include "util/synth_result.h"
#include "util/uninterpreted_sort_value.h"
#include "util/utility.h"

namespace cvc5 {

/* -------------------------------------------------------------------------- */
/* APIStatistics                                                              */
/* -------------------------------------------------------------------------- */

struct APIStatistics
{
  internal::HistogramStat<internal::TypeConstant> d_consts;
  internal::HistogramStat<internal::TypeConstant> d_vars;
  internal::HistogramStat<Kind> d_terms;
};

/* -------------------------------------------------------------------------- */
/* Kind                                                                       */
/* -------------------------------------------------------------------------- */

#define KIND_ENUM(external_name, internal_name)                  \
  {                                                              \
    external_name, std::make_pair(internal_name, #external_name) \
  }

/* Mapping from external (API) kind to internal kind. */
const static std::unordered_map<Kind, std::pair<internal::Kind, std::string>>
    s_kinds{
        KIND_ENUM(INTERNAL_KIND, internal::Kind::UNDEFINED_KIND),
        KIND_ENUM(UNDEFINED_KIND, internal::Kind::UNDEFINED_KIND),
        KIND_ENUM(NULL_TERM, internal::Kind::NULL_EXPR),
        /* Builtin ---------------------------------------------------------- */
        KIND_ENUM(UNINTERPRETED_SORT_VALUE,
                  internal::Kind::UNINTERPRETED_SORT_VALUE),
        KIND_ENUM(EQUAL, internal::Kind::EQUAL),
        KIND_ENUM(DISTINCT, internal::Kind::DISTINCT),
        KIND_ENUM(CONSTANT, internal::Kind::VARIABLE),
        KIND_ENUM(VARIABLE, internal::Kind::BOUND_VARIABLE),
        KIND_ENUM(SEXPR, internal::Kind::SEXPR),
        KIND_ENUM(LAMBDA, internal::Kind::LAMBDA),
        KIND_ENUM(WITNESS, internal::Kind::WITNESS),
        /* Boolean ---------------------------------------------------------- */
        KIND_ENUM(CONST_BOOLEAN, internal::Kind::CONST_BOOLEAN),
        KIND_ENUM(NOT, internal::Kind::NOT),
        KIND_ENUM(AND, internal::Kind::AND),
        KIND_ENUM(IMPLIES, internal::Kind::IMPLIES),
        KIND_ENUM(OR, internal::Kind::OR),
        KIND_ENUM(XOR, internal::Kind::XOR),
        KIND_ENUM(ITE, internal::Kind::ITE),
        /* UF --------------------------------------------------------------- */
        KIND_ENUM(APPLY_UF, internal::Kind::APPLY_UF),
        KIND_ENUM(CARDINALITY_CONSTRAINT,
                  internal::Kind::CARDINALITY_CONSTRAINT),
        KIND_ENUM(HO_APPLY, internal::Kind::HO_APPLY),
        /* Arithmetic ------------------------------------------------------- */
        KIND_ENUM(ADD, internal::Kind::ADD),
        KIND_ENUM(MULT, internal::Kind::MULT),
        KIND_ENUM(IAND, internal::Kind::IAND),
        KIND_ENUM(POW2, internal::Kind::POW2),
        KIND_ENUM(SUB, internal::Kind::SUB),
        KIND_ENUM(NEG, internal::Kind::NEG),
        KIND_ENUM(DIVISION, internal::Kind::DIVISION),
        KIND_ENUM(INTS_DIVISION, internal::Kind::INTS_DIVISION),
        KIND_ENUM(INTS_MODULUS, internal::Kind::INTS_MODULUS),
        KIND_ENUM(ABS, internal::Kind::ABS),
        KIND_ENUM(DIVISIBLE, internal::Kind::DIVISIBLE),
        KIND_ENUM(POW, internal::Kind::POW),
        KIND_ENUM(EXPONENTIAL, internal::Kind::EXPONENTIAL),
        KIND_ENUM(SINE, internal::Kind::SINE),
        KIND_ENUM(COSINE, internal::Kind::COSINE),
        KIND_ENUM(TANGENT, internal::Kind::TANGENT),
        KIND_ENUM(COSECANT, internal::Kind::COSECANT),
        KIND_ENUM(SECANT, internal::Kind::SECANT),
        KIND_ENUM(COTANGENT, internal::Kind::COTANGENT),
        KIND_ENUM(ARCSINE, internal::Kind::ARCSINE),
        KIND_ENUM(ARCCOSINE, internal::Kind::ARCCOSINE),
        KIND_ENUM(ARCTANGENT, internal::Kind::ARCTANGENT),
        KIND_ENUM(ARCCOSECANT, internal::Kind::ARCCOSECANT),
        KIND_ENUM(ARCSECANT, internal::Kind::ARCSECANT),
        KIND_ENUM(ARCCOTANGENT, internal::Kind::ARCCOTANGENT),
        KIND_ENUM(SQRT, internal::Kind::SQRT),
        KIND_ENUM(CONST_RATIONAL, internal::Kind::CONST_RATIONAL),
        KIND_ENUM(CONST_INTEGER, internal::Kind::CONST_INTEGER),
        KIND_ENUM(LT, internal::Kind::LT),
        KIND_ENUM(LEQ, internal::Kind::LEQ),
        KIND_ENUM(GT, internal::Kind::GT),
        KIND_ENUM(GEQ, internal::Kind::GEQ),
        KIND_ENUM(IS_INTEGER, internal::Kind::IS_INTEGER),
        KIND_ENUM(TO_INTEGER, internal::Kind::TO_INTEGER),
        KIND_ENUM(TO_REAL, internal::Kind::TO_REAL),
        KIND_ENUM(PI, internal::Kind::PI),
        /* BV --------------------------------------------------------------- */
        KIND_ENUM(CONST_BITVECTOR, internal::Kind::CONST_BITVECTOR),
        KIND_ENUM(BITVECTOR_CONCAT, internal::Kind::BITVECTOR_CONCAT),
        KIND_ENUM(BITVECTOR_AND, internal::Kind::BITVECTOR_AND),
        KIND_ENUM(BITVECTOR_OR, internal::Kind::BITVECTOR_OR),
        KIND_ENUM(BITVECTOR_XOR, internal::Kind::BITVECTOR_XOR),
        KIND_ENUM(BITVECTOR_NOT, internal::Kind::BITVECTOR_NOT),
        KIND_ENUM(BITVECTOR_NAND, internal::Kind::BITVECTOR_NAND),
        KIND_ENUM(BITVECTOR_NOR, internal::Kind::BITVECTOR_NOR),
        KIND_ENUM(BITVECTOR_XNOR, internal::Kind::BITVECTOR_XNOR),
        KIND_ENUM(BITVECTOR_COMP, internal::Kind::BITVECTOR_COMP),
        KIND_ENUM(BITVECTOR_MULT, internal::Kind::BITVECTOR_MULT),
        KIND_ENUM(BITVECTOR_ADD, internal::Kind::BITVECTOR_ADD),
        KIND_ENUM(BITVECTOR_SUB, internal::Kind::BITVECTOR_SUB),
        KIND_ENUM(BITVECTOR_NEG, internal::Kind::BITVECTOR_NEG),
        KIND_ENUM(BITVECTOR_UDIV, internal::Kind::BITVECTOR_UDIV),
        KIND_ENUM(BITVECTOR_UREM, internal::Kind::BITVECTOR_UREM),
        KIND_ENUM(BITVECTOR_SDIV, internal::Kind::BITVECTOR_SDIV),
        KIND_ENUM(BITVECTOR_SREM, internal::Kind::BITVECTOR_SREM),
        KIND_ENUM(BITVECTOR_SMOD, internal::Kind::BITVECTOR_SMOD),
        KIND_ENUM(BITVECTOR_SHL, internal::Kind::BITVECTOR_SHL),
        KIND_ENUM(BITVECTOR_LSHR, internal::Kind::BITVECTOR_LSHR),
        KIND_ENUM(BITVECTOR_ASHR, internal::Kind::BITVECTOR_ASHR),
        KIND_ENUM(BITVECTOR_ULT, internal::Kind::BITVECTOR_ULT),
        KIND_ENUM(BITVECTOR_ULE, internal::Kind::BITVECTOR_ULE),
        KIND_ENUM(BITVECTOR_UGT, internal::Kind::BITVECTOR_UGT),
        KIND_ENUM(BITVECTOR_UGE, internal::Kind::BITVECTOR_UGE),
        KIND_ENUM(BITVECTOR_SLT, internal::Kind::BITVECTOR_SLT),
        KIND_ENUM(BITVECTOR_SLE, internal::Kind::BITVECTOR_SLE),
        KIND_ENUM(BITVECTOR_SGT, internal::Kind::BITVECTOR_SGT),
        KIND_ENUM(BITVECTOR_SGE, internal::Kind::BITVECTOR_SGE),
        KIND_ENUM(BITVECTOR_ULTBV, internal::Kind::BITVECTOR_ULTBV),
        KIND_ENUM(BITVECTOR_SLTBV, internal::Kind::BITVECTOR_SLTBV),
        KIND_ENUM(BITVECTOR_ITE, internal::Kind::BITVECTOR_ITE),
        KIND_ENUM(BITVECTOR_REDOR, internal::Kind::BITVECTOR_REDOR),
        KIND_ENUM(BITVECTOR_REDAND, internal::Kind::BITVECTOR_REDAND),
        KIND_ENUM(BITVECTOR_EXTRACT, internal::Kind::BITVECTOR_EXTRACT),
        KIND_ENUM(BITVECTOR_REPEAT, internal::Kind::BITVECTOR_REPEAT),
        KIND_ENUM(BITVECTOR_ZERO_EXTEND, internal::Kind::BITVECTOR_ZERO_EXTEND),
        KIND_ENUM(BITVECTOR_SIGN_EXTEND, internal::Kind::BITVECTOR_SIGN_EXTEND),
        KIND_ENUM(BITVECTOR_ROTATE_LEFT, internal::Kind::BITVECTOR_ROTATE_LEFT),
        KIND_ENUM(BITVECTOR_ROTATE_RIGHT,
                  internal::Kind::BITVECTOR_ROTATE_RIGHT),
        KIND_ENUM(INT_TO_BITVECTOR, internal::Kind::INT_TO_BITVECTOR),
        KIND_ENUM(BITVECTOR_TO_NAT, internal::Kind::BITVECTOR_TO_NAT),
        /* FP --------------------------------------------------------------- */
        KIND_ENUM(CONST_FLOATINGPOINT, internal::Kind::CONST_FLOATINGPOINT),
        KIND_ENUM(CONST_ROUNDINGMODE, internal::Kind::CONST_ROUNDINGMODE),
        KIND_ENUM(FLOATINGPOINT_FP, internal::Kind::FLOATINGPOINT_FP),
        KIND_ENUM(FLOATINGPOINT_EQ, internal::Kind::FLOATINGPOINT_EQ),
        KIND_ENUM(FLOATINGPOINT_ABS, internal::Kind::FLOATINGPOINT_ABS),
        KIND_ENUM(FLOATINGPOINT_NEG, internal::Kind::FLOATINGPOINT_NEG),
        KIND_ENUM(FLOATINGPOINT_ADD, internal::Kind::FLOATINGPOINT_ADD),
        KIND_ENUM(FLOATINGPOINT_SUB, internal::Kind::FLOATINGPOINT_SUB),
        KIND_ENUM(FLOATINGPOINT_MULT, internal::Kind::FLOATINGPOINT_MULT),
        KIND_ENUM(FLOATINGPOINT_DIV, internal::Kind::FLOATINGPOINT_DIV),
        KIND_ENUM(FLOATINGPOINT_FMA, internal::Kind::FLOATINGPOINT_FMA),
        KIND_ENUM(FLOATINGPOINT_SQRT, internal::Kind::FLOATINGPOINT_SQRT),
        KIND_ENUM(FLOATINGPOINT_REM, internal::Kind::FLOATINGPOINT_REM),
        KIND_ENUM(FLOATINGPOINT_RTI, internal::Kind::FLOATINGPOINT_RTI),
        KIND_ENUM(FLOATINGPOINT_MIN, internal::Kind::FLOATINGPOINT_MIN),
        KIND_ENUM(FLOATINGPOINT_MAX, internal::Kind::FLOATINGPOINT_MAX),
        KIND_ENUM(FLOATINGPOINT_LEQ, internal::Kind::FLOATINGPOINT_LEQ),
        KIND_ENUM(FLOATINGPOINT_LT, internal::Kind::FLOATINGPOINT_LT),
        KIND_ENUM(FLOATINGPOINT_GEQ, internal::Kind::FLOATINGPOINT_GEQ),
        KIND_ENUM(FLOATINGPOINT_GT, internal::Kind::FLOATINGPOINT_GT),
        KIND_ENUM(FLOATINGPOINT_IS_NORMAL,
                  internal::Kind::FLOATINGPOINT_IS_NORMAL),
        KIND_ENUM(FLOATINGPOINT_IS_SUBNORMAL,
                  internal::Kind::FLOATINGPOINT_IS_SUBNORMAL),
        KIND_ENUM(FLOATINGPOINT_IS_ZERO, internal::Kind::FLOATINGPOINT_IS_ZERO),
        KIND_ENUM(FLOATINGPOINT_IS_INF, internal::Kind::FLOATINGPOINT_IS_INF),
        KIND_ENUM(FLOATINGPOINT_IS_NAN, internal::Kind::FLOATINGPOINT_IS_NAN),
        KIND_ENUM(FLOATINGPOINT_IS_NEG, internal::Kind::FLOATINGPOINT_IS_NEG),
        KIND_ENUM(FLOATINGPOINT_IS_POS, internal::Kind::FLOATINGPOINT_IS_POS),
        KIND_ENUM(FLOATINGPOINT_TO_FP_FROM_FP,
                  internal::Kind::FLOATINGPOINT_TO_FP_FROM_FP),
        KIND_ENUM(FLOATINGPOINT_TO_FP_FROM_IEEE_BV,
                  internal::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV),
        KIND_ENUM(FLOATINGPOINT_TO_FP_FROM_REAL,
                  internal::Kind::FLOATINGPOINT_TO_FP_FROM_REAL),
        KIND_ENUM(FLOATINGPOINT_TO_FP_FROM_SBV,
                  internal::Kind::FLOATINGPOINT_TO_FP_FROM_SBV),
        KIND_ENUM(FLOATINGPOINT_TO_FP_FROM_UBV,
                  internal::Kind::FLOATINGPOINT_TO_FP_FROM_UBV),
        KIND_ENUM(FLOATINGPOINT_TO_UBV, internal::Kind::FLOATINGPOINT_TO_UBV),
        KIND_ENUM(FLOATINGPOINT_TO_SBV, internal::Kind::FLOATINGPOINT_TO_SBV),
        KIND_ENUM(FLOATINGPOINT_TO_REAL, internal::Kind::FLOATINGPOINT_TO_REAL),
        /* Arrays ----------------------------------------------------------- */
        KIND_ENUM(SELECT, internal::Kind::SELECT),
        KIND_ENUM(STORE, internal::Kind::STORE),
        KIND_ENUM(CONST_ARRAY, internal::Kind::STORE_ALL),
        KIND_ENUM(EQ_RANGE, internal::Kind::EQ_RANGE),
        /* Datatypes -------------------------------------------------------- */
        KIND_ENUM(APPLY_SELECTOR, internal::Kind::APPLY_SELECTOR),
        KIND_ENUM(APPLY_CONSTRUCTOR, internal::Kind::APPLY_CONSTRUCTOR),
        KIND_ENUM(APPLY_TESTER, internal::Kind::APPLY_TESTER),
        KIND_ENUM(APPLY_UPDATER, internal::Kind::APPLY_UPDATER),
        KIND_ENUM(MATCH, internal::Kind::MATCH),
        KIND_ENUM(MATCH_CASE, internal::Kind::MATCH_CASE),
        KIND_ENUM(MATCH_BIND_CASE, internal::Kind::MATCH_BIND_CASE),
        KIND_ENUM(TUPLE_PROJECT, internal::Kind::TUPLE_PROJECT),
        /* Separation Logic ------------------------------------------------- */
        KIND_ENUM(SEP_NIL, internal::Kind::SEP_NIL),
        KIND_ENUM(SEP_EMP, internal::Kind::SEP_EMP),
        KIND_ENUM(SEP_PTO, internal::Kind::SEP_PTO),
        KIND_ENUM(SEP_STAR, internal::Kind::SEP_STAR),
        KIND_ENUM(SEP_WAND, internal::Kind::SEP_WAND),
        /* Sets ------------------------------------------------------------- */
        KIND_ENUM(SET_EMPTY, internal::Kind::SET_EMPTY),
        KIND_ENUM(SET_UNION, internal::Kind::SET_UNION),
        KIND_ENUM(SET_INTER, internal::Kind::SET_INTER),
        KIND_ENUM(SET_MINUS, internal::Kind::SET_MINUS),
        KIND_ENUM(SET_SUBSET, internal::Kind::SET_SUBSET),
        KIND_ENUM(SET_MEMBER, internal::Kind::SET_MEMBER),
        KIND_ENUM(SET_SINGLETON, internal::Kind::SET_SINGLETON),
        KIND_ENUM(SET_INSERT, internal::Kind::SET_INSERT),
        KIND_ENUM(SET_CARD, internal::Kind::SET_CARD),
        KIND_ENUM(SET_COMPLEMENT, internal::Kind::SET_COMPLEMENT),
        KIND_ENUM(SET_UNIVERSE, internal::Kind::SET_UNIVERSE),
        KIND_ENUM(SET_COMPREHENSION, internal::Kind::SET_COMPREHENSION),
        KIND_ENUM(SET_CHOOSE, internal::Kind::SET_CHOOSE),
        KIND_ENUM(SET_IS_SINGLETON, internal::Kind::SET_IS_SINGLETON),
        KIND_ENUM(SET_MAP, internal::Kind::SET_MAP),
        KIND_ENUM(SET_FILTER, internal::Kind::SET_FILTER),
        /* Relations -------------------------------------------------------- */
        KIND_ENUM(RELATION_JOIN, internal::Kind::RELATION_JOIN),
        KIND_ENUM(RELATION_PRODUCT, internal::Kind::RELATION_PRODUCT),
        KIND_ENUM(RELATION_TRANSPOSE, internal::Kind::RELATION_TRANSPOSE),
        KIND_ENUM(RELATION_TCLOSURE, internal::Kind::RELATION_TCLOSURE),
        KIND_ENUM(RELATION_JOIN_IMAGE, internal::Kind::RELATION_JOIN_IMAGE),
        KIND_ENUM(RELATION_IDEN, internal::Kind::RELATION_IDEN),
        /* Bags ------------------------------------------------------------- */
        KIND_ENUM(BAG_UNION_MAX, internal::Kind::BAG_UNION_MAX),
        KIND_ENUM(BAG_UNION_DISJOINT, internal::Kind::BAG_UNION_DISJOINT),
        KIND_ENUM(BAG_INTER_MIN, internal::Kind::BAG_INTER_MIN),
        KIND_ENUM(BAG_DIFFERENCE_SUBTRACT,
                  internal::Kind::BAG_DIFFERENCE_SUBTRACT),
        KIND_ENUM(BAG_DIFFERENCE_REMOVE, internal::Kind::BAG_DIFFERENCE_REMOVE),
        KIND_ENUM(BAG_SUBBAG, internal::Kind::BAG_SUBBAG),
        KIND_ENUM(BAG_COUNT, internal::Kind::BAG_COUNT),
        KIND_ENUM(BAG_MEMBER, internal::Kind::BAG_MEMBER),
        KIND_ENUM(BAG_DUPLICATE_REMOVAL, internal::Kind::BAG_DUPLICATE_REMOVAL),
        KIND_ENUM(BAG_MAKE, internal::Kind::BAG_MAKE),
        KIND_ENUM(BAG_EMPTY, internal::Kind::BAG_EMPTY),
        KIND_ENUM(BAG_CARD, internal::Kind::BAG_CARD),
        KIND_ENUM(BAG_CHOOSE, internal::Kind::BAG_CHOOSE),
        KIND_ENUM(BAG_IS_SINGLETON, internal::Kind::BAG_IS_SINGLETON),
        KIND_ENUM(BAG_FROM_SET, internal::Kind::BAG_FROM_SET),
        KIND_ENUM(BAG_TO_SET, internal::Kind::BAG_TO_SET),
        KIND_ENUM(BAG_MAP, internal::Kind::BAG_MAP),
        KIND_ENUM(BAG_FILTER, internal::Kind::BAG_FILTER),
        KIND_ENUM(BAG_FOLD, internal::Kind::BAG_FOLD),
        KIND_ENUM(BAG_PARTITION, internal::Kind::BAG_PARTITION),
        KIND_ENUM(TABLE_PRODUCT, internal::Kind::TABLE_PRODUCT),
        KIND_ENUM(TABLE_PROJECT, internal::Kind::TABLE_PROJECT),
        KIND_ENUM(TABLE_AGGREGATE, internal::Kind::TABLE_AGGREGATE),
        KIND_ENUM(TABLE_JOIN, internal::Kind::TABLE_JOIN),
        KIND_ENUM(TABLE_GROUP, internal::Kind::TABLE_GROUP),
        /* Strings ---------------------------------------------------------- */
        KIND_ENUM(STRING_CONCAT, internal::Kind::STRING_CONCAT),
        KIND_ENUM(STRING_IN_REGEXP, internal::Kind::STRING_IN_REGEXP),
        KIND_ENUM(STRING_LENGTH, internal::Kind::STRING_LENGTH),
        KIND_ENUM(STRING_SUBSTR, internal::Kind::STRING_SUBSTR),
        KIND_ENUM(STRING_UPDATE, internal::Kind::STRING_UPDATE),
        KIND_ENUM(STRING_CHARAT, internal::Kind::STRING_CHARAT),
        KIND_ENUM(STRING_CONTAINS, internal::Kind::STRING_CONTAINS),
        KIND_ENUM(STRING_INDEXOF, internal::Kind::STRING_INDEXOF),
        KIND_ENUM(STRING_INDEXOF_RE, internal::Kind::STRING_INDEXOF_RE),
        KIND_ENUM(STRING_REPLACE, internal::Kind::STRING_REPLACE),
        KIND_ENUM(STRING_REPLACE_ALL, internal::Kind::STRING_REPLACE_ALL),
        KIND_ENUM(STRING_REPLACE_RE, internal::Kind::STRING_REPLACE_RE),
        KIND_ENUM(STRING_REPLACE_RE_ALL, internal::Kind::STRING_REPLACE_RE_ALL),
        KIND_ENUM(STRING_TO_LOWER, internal::Kind::STRING_TO_LOWER),
        KIND_ENUM(STRING_TO_UPPER, internal::Kind::STRING_TO_UPPER),
        KIND_ENUM(STRING_REV, internal::Kind::STRING_REV),
        KIND_ENUM(STRING_FROM_CODE, internal::Kind::STRING_FROM_CODE),
        KIND_ENUM(STRING_TO_CODE, internal::Kind::STRING_TO_CODE),
        KIND_ENUM(STRING_LT, internal::Kind::STRING_LT),
        KIND_ENUM(STRING_LEQ, internal::Kind::STRING_LEQ),
        KIND_ENUM(STRING_PREFIX, internal::Kind::STRING_PREFIX),
        KIND_ENUM(STRING_SUFFIX, internal::Kind::STRING_SUFFIX),
        KIND_ENUM(STRING_IS_DIGIT, internal::Kind::STRING_IS_DIGIT),
        KIND_ENUM(STRING_FROM_INT, internal::Kind::STRING_ITOS),
        KIND_ENUM(STRING_TO_INT, internal::Kind::STRING_STOI),
        KIND_ENUM(CONST_STRING, internal::Kind::CONST_STRING),
        KIND_ENUM(STRING_TO_REGEXP, internal::Kind::STRING_TO_REGEXP),
        KIND_ENUM(REGEXP_CONCAT, internal::Kind::REGEXP_CONCAT),
        KIND_ENUM(REGEXP_UNION, internal::Kind::REGEXP_UNION),
        KIND_ENUM(REGEXP_INTER, internal::Kind::REGEXP_INTER),
        KIND_ENUM(REGEXP_DIFF, internal::Kind::REGEXP_DIFF),
        KIND_ENUM(REGEXP_STAR, internal::Kind::REGEXP_STAR),
        KIND_ENUM(REGEXP_PLUS, internal::Kind::REGEXP_PLUS),
        KIND_ENUM(REGEXP_OPT, internal::Kind::REGEXP_OPT),
        KIND_ENUM(REGEXP_RANGE, internal::Kind::REGEXP_RANGE),
        KIND_ENUM(REGEXP_REPEAT, internal::Kind::REGEXP_REPEAT),
        KIND_ENUM(REGEXP_LOOP, internal::Kind::REGEXP_LOOP),
        KIND_ENUM(REGEXP_NONE, internal::Kind::REGEXP_NONE),
        KIND_ENUM(REGEXP_ALL, internal::Kind::REGEXP_ALL),
        KIND_ENUM(REGEXP_ALLCHAR, internal::Kind::REGEXP_ALLCHAR),
        KIND_ENUM(REGEXP_COMPLEMENT, internal::Kind::REGEXP_COMPLEMENT),
        // maps to the same kind as the string versions
        KIND_ENUM(SEQ_CONCAT, internal::Kind::STRING_CONCAT),
        KIND_ENUM(SEQ_LENGTH, internal::Kind::STRING_LENGTH),
        KIND_ENUM(SEQ_EXTRACT, internal::Kind::STRING_SUBSTR),
        KIND_ENUM(SEQ_UPDATE, internal::Kind::STRING_UPDATE),
        KIND_ENUM(SEQ_AT, internal::Kind::STRING_CHARAT),
        KIND_ENUM(SEQ_CONTAINS, internal::Kind::STRING_CONTAINS),
        KIND_ENUM(SEQ_INDEXOF, internal::Kind::STRING_INDEXOF),
        KIND_ENUM(SEQ_REPLACE, internal::Kind::STRING_REPLACE),
        KIND_ENUM(SEQ_REPLACE_ALL, internal::Kind::STRING_REPLACE_ALL),
        KIND_ENUM(SEQ_REV, internal::Kind::STRING_REV),
        KIND_ENUM(SEQ_PREFIX, internal::Kind::STRING_PREFIX),
        KIND_ENUM(SEQ_SUFFIX, internal::Kind::STRING_SUFFIX),
        KIND_ENUM(CONST_SEQUENCE, internal::Kind::CONST_SEQUENCE),
        KIND_ENUM(SEQ_UNIT, internal::Kind::SEQ_UNIT),
        KIND_ENUM(SEQ_NTH, internal::Kind::SEQ_NTH),
        /* Quantifiers ------------------------------------------------------ */
        KIND_ENUM(FORALL, internal::Kind::FORALL),
        KIND_ENUM(EXISTS, internal::Kind::EXISTS),
        KIND_ENUM(VARIABLE_LIST, internal::Kind::BOUND_VAR_LIST),
        KIND_ENUM(INST_PATTERN, internal::Kind::INST_PATTERN),
        KIND_ENUM(INST_NO_PATTERN, internal::Kind::INST_NO_PATTERN),
        KIND_ENUM(INST_POOL, internal::Kind::INST_POOL),
        KIND_ENUM(INST_ADD_TO_POOL, internal::Kind::INST_ADD_TO_POOL),
        KIND_ENUM(SKOLEM_ADD_TO_POOL, internal::Kind::SKOLEM_ADD_TO_POOL),
        KIND_ENUM(INST_ATTRIBUTE, internal::Kind::INST_ATTRIBUTE),
        KIND_ENUM(INST_PATTERN_LIST, internal::Kind::INST_PATTERN_LIST),
        KIND_ENUM(LAST_KIND, internal::Kind::LAST_KIND),
    };

/* Mapping from internal kind to external (API) kind. */
const static std::unordered_map<internal::Kind,
                                Kind,
                                internal::kind::KindHashFunction>
    s_kinds_internal{
        {internal::Kind::UNDEFINED_KIND, UNDEFINED_KIND},
        {internal::Kind::NULL_EXPR, NULL_TERM},
        /* Builtin --------------------------------------------------------- */
        {internal::Kind::UNINTERPRETED_SORT_VALUE, UNINTERPRETED_SORT_VALUE},
        {internal::Kind::EQUAL, EQUAL},
        {internal::Kind::DISTINCT, DISTINCT},
        {internal::Kind::VARIABLE, CONSTANT},
        {internal::Kind::BOUND_VARIABLE, VARIABLE},
        {internal::Kind::SEXPR, SEXPR},
        {internal::Kind::LAMBDA, LAMBDA},
        {internal::Kind::WITNESS, WITNESS},
        /* Boolean --------------------------------------------------------- */
        {internal::Kind::CONST_BOOLEAN, CONST_BOOLEAN},
        {internal::Kind::NOT, NOT},
        {internal::Kind::AND, AND},
        {internal::Kind::IMPLIES, IMPLIES},
        {internal::Kind::OR, OR},
        {internal::Kind::XOR, XOR},
        {internal::Kind::ITE, ITE},
        /* UF -------------------------------------------------------------- */
        {internal::Kind::APPLY_UF, APPLY_UF},
        {internal::Kind::CARDINALITY_CONSTRAINT, CARDINALITY_CONSTRAINT},
        {internal::Kind::HO_APPLY, HO_APPLY},
        /* Arithmetic ------------------------------------------------------ */
        {internal::Kind::ADD, ADD},
        {internal::Kind::MULT, MULT},
        {internal::Kind::IAND, IAND},
        {internal::Kind::POW2, POW2},
        {internal::Kind::SUB, SUB},
        {internal::Kind::NEG, NEG},
        {internal::Kind::DIVISION, DIVISION},
        {internal::Kind::DIVISION_TOTAL, INTERNAL_KIND},
        {internal::Kind::INTS_DIVISION, INTS_DIVISION},
        {internal::Kind::INTS_DIVISION_TOTAL, INTERNAL_KIND},
        {internal::Kind::INTS_MODULUS, INTS_MODULUS},
        {internal::Kind::INTS_MODULUS_TOTAL, INTERNAL_KIND},
        {internal::Kind::ABS, ABS},
        {internal::Kind::DIVISIBLE, DIVISIBLE},
        {internal::Kind::POW, POW},
        {internal::Kind::EXPONENTIAL, EXPONENTIAL},
        {internal::Kind::SINE, SINE},
        {internal::Kind::COSINE, COSINE},
        {internal::Kind::TANGENT, TANGENT},
        {internal::Kind::COSECANT, COSECANT},
        {internal::Kind::SECANT, SECANT},
        {internal::Kind::COTANGENT, COTANGENT},
        {internal::Kind::ARCSINE, ARCSINE},
        {internal::Kind::ARCCOSINE, ARCCOSINE},
        {internal::Kind::ARCTANGENT, ARCTANGENT},
        {internal::Kind::ARCCOSECANT, ARCCOSECANT},
        {internal::Kind::ARCSECANT, ARCSECANT},
        {internal::Kind::ARCCOTANGENT, ARCCOTANGENT},
        {internal::Kind::SQRT, SQRT},
        {internal::Kind::DIVISIBLE_OP, DIVISIBLE},
        {internal::Kind::CONST_RATIONAL, CONST_RATIONAL},
        {internal::Kind::CONST_INTEGER, CONST_INTEGER},
        {internal::Kind::LT, LT},
        {internal::Kind::LEQ, LEQ},
        {internal::Kind::GT, GT},
        {internal::Kind::GEQ, GEQ},
        {internal::Kind::IS_INTEGER, IS_INTEGER},
        {internal::Kind::TO_INTEGER, TO_INTEGER},
        {internal::Kind::TO_REAL, TO_REAL},
        {internal::Kind::PI, PI},
        {internal::Kind::IAND_OP, IAND},
        /* BV -------------------------------------------------------------- */
        {internal::Kind::CONST_BITVECTOR, CONST_BITVECTOR},
        {internal::Kind::BITVECTOR_CONCAT, BITVECTOR_CONCAT},
        {internal::Kind::BITVECTOR_AND, BITVECTOR_AND},
        {internal::Kind::BITVECTOR_OR, BITVECTOR_OR},
        {internal::Kind::BITVECTOR_XOR, BITVECTOR_XOR},
        {internal::Kind::BITVECTOR_NOT, BITVECTOR_NOT},
        {internal::Kind::BITVECTOR_NAND, BITVECTOR_NAND},
        {internal::Kind::BITVECTOR_NOR, BITVECTOR_NOR},
        {internal::Kind::BITVECTOR_XNOR, BITVECTOR_XNOR},
        {internal::Kind::BITVECTOR_COMP, BITVECTOR_COMP},
        {internal::Kind::BITVECTOR_MULT, BITVECTOR_MULT},
        {internal::Kind::BITVECTOR_ADD, BITVECTOR_ADD},
        {internal::Kind::BITVECTOR_SUB, BITVECTOR_SUB},
        {internal::Kind::BITVECTOR_NEG, BITVECTOR_NEG},
        {internal::Kind::BITVECTOR_UDIV, BITVECTOR_UDIV},
        {internal::Kind::BITVECTOR_UREM, BITVECTOR_UREM},
        {internal::Kind::BITVECTOR_SDIV, BITVECTOR_SDIV},
        {internal::Kind::BITVECTOR_SREM, BITVECTOR_SREM},
        {internal::Kind::BITVECTOR_SMOD, BITVECTOR_SMOD},
        {internal::Kind::BITVECTOR_SHL, BITVECTOR_SHL},
        {internal::Kind::BITVECTOR_LSHR, BITVECTOR_LSHR},
        {internal::Kind::BITVECTOR_ASHR, BITVECTOR_ASHR},
        {internal::Kind::BITVECTOR_ULT, BITVECTOR_ULT},
        {internal::Kind::BITVECTOR_ULE, BITVECTOR_ULE},
        {internal::Kind::BITVECTOR_UGT, BITVECTOR_UGT},
        {internal::Kind::BITVECTOR_UGE, BITVECTOR_UGE},
        {internal::Kind::BITVECTOR_SLT, BITVECTOR_SLT},
        {internal::Kind::BITVECTOR_SLE, BITVECTOR_SLE},
        {internal::Kind::BITVECTOR_SGT, BITVECTOR_SGT},
        {internal::Kind::BITVECTOR_SGE, BITVECTOR_SGE},
        {internal::Kind::BITVECTOR_ULTBV, BITVECTOR_ULTBV},
        {internal::Kind::BITVECTOR_SLTBV, BITVECTOR_SLTBV},
        {internal::Kind::BITVECTOR_ITE, BITVECTOR_ITE},
        {internal::Kind::BITVECTOR_REDOR, BITVECTOR_REDOR},
        {internal::Kind::BITVECTOR_REDAND, BITVECTOR_REDAND},
        {internal::Kind::BITVECTOR_EXTRACT_OP, BITVECTOR_EXTRACT},
        {internal::Kind::BITVECTOR_REPEAT_OP, BITVECTOR_REPEAT},
        {internal::Kind::BITVECTOR_ZERO_EXTEND_OP, BITVECTOR_ZERO_EXTEND},
        {internal::Kind::BITVECTOR_SIGN_EXTEND_OP, BITVECTOR_SIGN_EXTEND},
        {internal::Kind::BITVECTOR_ROTATE_LEFT_OP, BITVECTOR_ROTATE_LEFT},
        {internal::Kind::BITVECTOR_ROTATE_RIGHT_OP, BITVECTOR_ROTATE_RIGHT},
        {internal::Kind::BITVECTOR_EXTRACT, BITVECTOR_EXTRACT},
        {internal::Kind::BITVECTOR_REPEAT, BITVECTOR_REPEAT},
        {internal::Kind::BITVECTOR_ZERO_EXTEND, BITVECTOR_ZERO_EXTEND},
        {internal::Kind::BITVECTOR_SIGN_EXTEND, BITVECTOR_SIGN_EXTEND},
        {internal::Kind::BITVECTOR_ROTATE_LEFT, BITVECTOR_ROTATE_LEFT},
        {internal::Kind::BITVECTOR_ROTATE_RIGHT, BITVECTOR_ROTATE_RIGHT},
        {internal::Kind::INT_TO_BITVECTOR_OP, INT_TO_BITVECTOR},
        {internal::Kind::INT_TO_BITVECTOR, INT_TO_BITVECTOR},
        {internal::Kind::BITVECTOR_TO_NAT, BITVECTOR_TO_NAT},
        /* FP -------------------------------------------------------------- */
        {internal::Kind::CONST_FLOATINGPOINT, CONST_FLOATINGPOINT},
        {internal::Kind::CONST_ROUNDINGMODE, CONST_ROUNDINGMODE},
        {internal::Kind::FLOATINGPOINT_FP, FLOATINGPOINT_FP},
        {internal::Kind::FLOATINGPOINT_EQ, FLOATINGPOINT_EQ},
        {internal::Kind::FLOATINGPOINT_ABS, FLOATINGPOINT_ABS},
        {internal::Kind::FLOATINGPOINT_NEG, FLOATINGPOINT_NEG},
        {internal::Kind::FLOATINGPOINT_ADD, FLOATINGPOINT_ADD},
        {internal::Kind::FLOATINGPOINT_SUB, FLOATINGPOINT_SUB},
        {internal::Kind::FLOATINGPOINT_MULT, FLOATINGPOINT_MULT},
        {internal::Kind::FLOATINGPOINT_DIV, FLOATINGPOINT_DIV},
        {internal::Kind::FLOATINGPOINT_FMA, FLOATINGPOINT_FMA},
        {internal::Kind::FLOATINGPOINT_SQRT, FLOATINGPOINT_SQRT},
        {internal::Kind::FLOATINGPOINT_REM, FLOATINGPOINT_REM},
        {internal::Kind::FLOATINGPOINT_RTI, FLOATINGPOINT_RTI},
        {internal::Kind::FLOATINGPOINT_MIN, FLOATINGPOINT_MIN},
        {internal::Kind::FLOATINGPOINT_MAX, FLOATINGPOINT_MAX},
        {internal::Kind::FLOATINGPOINT_LEQ, FLOATINGPOINT_LEQ},
        {internal::Kind::FLOATINGPOINT_LT, FLOATINGPOINT_LT},
        {internal::Kind::FLOATINGPOINT_GEQ, FLOATINGPOINT_GEQ},
        {internal::Kind::FLOATINGPOINT_GT, FLOATINGPOINT_GT},
        {internal::Kind::FLOATINGPOINT_IS_NORMAL, FLOATINGPOINT_IS_NORMAL},
        {internal::Kind::FLOATINGPOINT_IS_SUBNORMAL,
         FLOATINGPOINT_IS_SUBNORMAL},
        {internal::Kind::FLOATINGPOINT_IS_ZERO, FLOATINGPOINT_IS_ZERO},
        {internal::Kind::FLOATINGPOINT_IS_INF, FLOATINGPOINT_IS_INF},
        {internal::Kind::FLOATINGPOINT_IS_NAN, FLOATINGPOINT_IS_NAN},
        {internal::Kind::FLOATINGPOINT_IS_NEG, FLOATINGPOINT_IS_NEG},
        {internal::Kind::FLOATINGPOINT_IS_POS, FLOATINGPOINT_IS_POS},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV_OP,
         FLOATINGPOINT_TO_FP_FROM_IEEE_BV},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV,
         FLOATINGPOINT_TO_FP_FROM_IEEE_BV},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_FP_OP,
         FLOATINGPOINT_TO_FP_FROM_FP},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_FP,
         FLOATINGPOINT_TO_FP_FROM_FP},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_REAL_OP,
         FLOATINGPOINT_TO_FP_FROM_REAL},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_REAL,
         FLOATINGPOINT_TO_FP_FROM_REAL},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_SBV_OP,
         FLOATINGPOINT_TO_FP_FROM_SBV},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_SBV,
         FLOATINGPOINT_TO_FP_FROM_SBV},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_UBV_OP,
         FLOATINGPOINT_TO_FP_FROM_UBV},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_UBV,
         FLOATINGPOINT_TO_FP_FROM_UBV},
        {internal::Kind::FLOATINGPOINT_TO_UBV_OP, FLOATINGPOINT_TO_UBV},
        {internal::Kind::FLOATINGPOINT_TO_UBV, FLOATINGPOINT_TO_UBV},
        {internal::Kind::FLOATINGPOINT_TO_UBV_TOTAL_OP, INTERNAL_KIND},
        {internal::Kind::FLOATINGPOINT_TO_UBV_TOTAL, INTERNAL_KIND},
        {internal::Kind::FLOATINGPOINT_TO_SBV_OP, FLOATINGPOINT_TO_SBV},
        {internal::Kind::FLOATINGPOINT_TO_SBV, FLOATINGPOINT_TO_SBV},
        {internal::Kind::FLOATINGPOINT_TO_SBV_TOTAL_OP, INTERNAL_KIND},
        {internal::Kind::FLOATINGPOINT_TO_SBV_TOTAL, INTERNAL_KIND},
        {internal::Kind::FLOATINGPOINT_TO_REAL, FLOATINGPOINT_TO_REAL},
        {internal::Kind::FLOATINGPOINT_TO_REAL_TOTAL, INTERNAL_KIND},
        /* Arrays ---------------------------------------------------------- */
        {internal::Kind::SELECT, SELECT},
        {internal::Kind::STORE, STORE},
        {internal::Kind::STORE_ALL, CONST_ARRAY},
        /* Datatypes ------------------------------------------------------- */
        {internal::Kind::APPLY_SELECTOR, APPLY_SELECTOR},
        {internal::Kind::APPLY_CONSTRUCTOR, APPLY_CONSTRUCTOR},
        {internal::Kind::APPLY_TESTER, APPLY_TESTER},
        {internal::Kind::APPLY_UPDATER, APPLY_UPDATER},
        {internal::Kind::MATCH, MATCH},
        {internal::Kind::MATCH_CASE, MATCH_CASE},
        {internal::Kind::MATCH_BIND_CASE, MATCH_BIND_CASE},
        {internal::Kind::TUPLE_PROJECT, TUPLE_PROJECT},
        {internal::Kind::TUPLE_PROJECT_OP, TUPLE_PROJECT},
        /* Separation Logic ------------------------------------------------ */
        {internal::Kind::SEP_NIL, SEP_NIL},
        {internal::Kind::SEP_EMP, SEP_EMP},
        {internal::Kind::SEP_PTO, SEP_PTO},
        {internal::Kind::SEP_STAR, SEP_STAR},
        {internal::Kind::SEP_WAND, SEP_WAND},
        /* Sets ------------------------------------------------------------ */
        {internal::Kind::SET_EMPTY, SET_EMPTY},
        {internal::Kind::SET_UNION, SET_UNION},
        {internal::Kind::SET_INTER, SET_INTER},
        {internal::Kind::SET_MINUS, SET_MINUS},
        {internal::Kind::SET_SUBSET, SET_SUBSET},
        {internal::Kind::SET_MEMBER, SET_MEMBER},
        {internal::Kind::SET_SINGLETON, SET_SINGLETON},
        {internal::Kind::SET_INSERT, SET_INSERT},
        {internal::Kind::SET_CARD, SET_CARD},
        {internal::Kind::SET_COMPLEMENT, SET_COMPLEMENT},
        {internal::Kind::SET_UNIVERSE, SET_UNIVERSE},
        {internal::Kind::SET_COMPREHENSION, SET_COMPREHENSION},
        {internal::Kind::SET_CHOOSE, SET_CHOOSE},
        {internal::Kind::SET_IS_SINGLETON, SET_IS_SINGLETON},
        {internal::Kind::SET_MAP, SET_MAP},
        {internal::Kind::SET_FILTER, SET_FILTER},
        /* Relations ------------------------------------------------------- */
        {internal::Kind::RELATION_JOIN, RELATION_JOIN},
        {internal::Kind::RELATION_PRODUCT, RELATION_PRODUCT},
        {internal::Kind::RELATION_TRANSPOSE, RELATION_TRANSPOSE},
        {internal::Kind::RELATION_TCLOSURE, RELATION_TCLOSURE},
        {internal::Kind::RELATION_JOIN_IMAGE, RELATION_JOIN_IMAGE},
        {internal::Kind::RELATION_IDEN, RELATION_IDEN},
        /* Bags ------------------------------------------------------------ */
        {internal::Kind::BAG_UNION_MAX, BAG_UNION_MAX},
        {internal::Kind::BAG_UNION_DISJOINT, BAG_UNION_DISJOINT},
        {internal::Kind::BAG_INTER_MIN, BAG_INTER_MIN},
        {internal::Kind::BAG_DIFFERENCE_SUBTRACT, BAG_DIFFERENCE_SUBTRACT},
        {internal::Kind::BAG_DIFFERENCE_REMOVE, BAG_DIFFERENCE_REMOVE},
        {internal::Kind::BAG_SUBBAG, BAG_SUBBAG},
        {internal::Kind::BAG_COUNT, BAG_COUNT},
        {internal::Kind::BAG_MEMBER, BAG_MEMBER},
        {internal::Kind::BAG_DUPLICATE_REMOVAL, BAG_DUPLICATE_REMOVAL},
        {internal::Kind::BAG_MAKE, BAG_MAKE},
        {internal::Kind::BAG_EMPTY, BAG_EMPTY},
        {internal::Kind::BAG_CARD, BAG_CARD},
        {internal::Kind::BAG_CHOOSE, BAG_CHOOSE},
        {internal::Kind::BAG_IS_SINGLETON, BAG_IS_SINGLETON},
        {internal::Kind::BAG_FROM_SET, BAG_FROM_SET},
        {internal::Kind::BAG_TO_SET, BAG_TO_SET},
        {internal::Kind::BAG_MAP, BAG_MAP},
        {internal::Kind::BAG_FILTER, BAG_FILTER},
        {internal::Kind::BAG_FOLD, BAG_FOLD},
        {internal::Kind::BAG_PARTITION, BAG_PARTITION},
        {internal::Kind::TABLE_PRODUCT, TABLE_PRODUCT},
        {internal::Kind::TABLE_PROJECT, TABLE_PROJECT},
        {internal::Kind::TABLE_PROJECT_OP, TABLE_PROJECT},
        {internal::Kind::TABLE_AGGREGATE_OP, TABLE_AGGREGATE},
        {internal::Kind::TABLE_AGGREGATE, TABLE_AGGREGATE},
        {internal::Kind::TABLE_JOIN_OP, TABLE_JOIN},
        {internal::Kind::TABLE_JOIN, TABLE_JOIN},
        {internal::Kind::TABLE_GROUP_OP, TABLE_GROUP},
        {internal::Kind::TABLE_GROUP, TABLE_GROUP},
        /* Strings --------------------------------------------------------- */
        {internal::Kind::STRING_CONCAT, STRING_CONCAT},
        {internal::Kind::STRING_IN_REGEXP, STRING_IN_REGEXP},
        {internal::Kind::STRING_LENGTH, STRING_LENGTH},
        {internal::Kind::STRING_SUBSTR, STRING_SUBSTR},
        {internal::Kind::STRING_UPDATE, STRING_UPDATE},
        {internal::Kind::STRING_CHARAT, STRING_CHARAT},
        {internal::Kind::STRING_CONTAINS, STRING_CONTAINS},
        {internal::Kind::STRING_INDEXOF, STRING_INDEXOF},
        {internal::Kind::STRING_INDEXOF_RE, STRING_INDEXOF_RE},
        {internal::Kind::STRING_REPLACE, STRING_REPLACE},
        {internal::Kind::STRING_REPLACE_ALL, STRING_REPLACE_ALL},
        {internal::Kind::STRING_REPLACE_RE, STRING_REPLACE_RE},
        {internal::Kind::STRING_REPLACE_RE_ALL, STRING_REPLACE_RE_ALL},
        {internal::Kind::STRING_TO_LOWER, STRING_TO_LOWER},
        {internal::Kind::STRING_TO_UPPER, STRING_TO_UPPER},
        {internal::Kind::STRING_REV, STRING_REV},
        {internal::Kind::STRING_FROM_CODE, STRING_FROM_CODE},
        {internal::Kind::STRING_TO_CODE, STRING_TO_CODE},
        {internal::Kind::STRING_LT, STRING_LT},
        {internal::Kind::STRING_LEQ, STRING_LEQ},
        {internal::Kind::STRING_PREFIX, STRING_PREFIX},
        {internal::Kind::STRING_SUFFIX, STRING_SUFFIX},
        {internal::Kind::STRING_IS_DIGIT, STRING_IS_DIGIT},
        {internal::Kind::STRING_ITOS, STRING_FROM_INT},
        {internal::Kind::STRING_STOI, STRING_TO_INT},
        {internal::Kind::CONST_STRING, CONST_STRING},
        {internal::Kind::STRING_TO_REGEXP, STRING_TO_REGEXP},
        {internal::Kind::REGEXP_CONCAT, REGEXP_CONCAT},
        {internal::Kind::REGEXP_UNION, REGEXP_UNION},
        {internal::Kind::REGEXP_INTER, REGEXP_INTER},
        {internal::Kind::REGEXP_DIFF, REGEXP_DIFF},
        {internal::Kind::REGEXP_STAR, REGEXP_STAR},
        {internal::Kind::REGEXP_PLUS, REGEXP_PLUS},
        {internal::Kind::REGEXP_OPT, REGEXP_OPT},
        {internal::Kind::REGEXP_RANGE, REGEXP_RANGE},
        {internal::Kind::REGEXP_REPEAT, REGEXP_REPEAT},
        {internal::Kind::REGEXP_REPEAT_OP, REGEXP_REPEAT},
        {internal::Kind::REGEXP_LOOP, REGEXP_LOOP},
        {internal::Kind::REGEXP_LOOP_OP, REGEXP_LOOP},
        {internal::Kind::REGEXP_NONE, REGEXP_NONE},
        {internal::Kind::REGEXP_ALL, REGEXP_ALL},
        {internal::Kind::REGEXP_ALLCHAR, REGEXP_ALLCHAR},
        {internal::Kind::REGEXP_COMPLEMENT, REGEXP_COMPLEMENT},
        {internal::Kind::CONST_SEQUENCE, CONST_SEQUENCE},
        {internal::Kind::SEQ_UNIT, SEQ_UNIT},
        {internal::Kind::SEQ_NTH, SEQ_NTH},
        /* Quantifiers ----------------------------------------------------- */
        {internal::Kind::FORALL, FORALL},
        {internal::Kind::EXISTS, EXISTS},
        {internal::Kind::BOUND_VAR_LIST, VARIABLE_LIST},
        {internal::Kind::INST_PATTERN, INST_PATTERN},
        {internal::Kind::INST_NO_PATTERN, INST_NO_PATTERN},
        {internal::Kind::INST_POOL, INST_POOL},
        {internal::Kind::INST_ADD_TO_POOL, INST_ADD_TO_POOL},
        {internal::Kind::SKOLEM_ADD_TO_POOL, SKOLEM_ADD_TO_POOL},
        {internal::Kind::INST_ATTRIBUTE, INST_ATTRIBUTE},
        {internal::Kind::INST_PATTERN_LIST, INST_PATTERN_LIST},
        /* ----------------------------------------------------------------- */
        {internal::Kind::LAST_KIND, LAST_KIND},
    };

/* Set of kinds for indexed operators */
const static std::unordered_set<Kind> s_indexed_kinds(
    {DIVISIBLE,
     IAND,
     BITVECTOR_REPEAT,
     BITVECTOR_ZERO_EXTEND,
     BITVECTOR_SIGN_EXTEND,
     BITVECTOR_ROTATE_LEFT,
     BITVECTOR_ROTATE_RIGHT,
     INT_TO_BITVECTOR,
     FLOATINGPOINT_TO_UBV,
     FLOATINGPOINT_TO_SBV,
     BITVECTOR_EXTRACT,
     FLOATINGPOINT_TO_FP_FROM_IEEE_BV,
     FLOATINGPOINT_TO_FP_FROM_FP,
     FLOATINGPOINT_TO_FP_FROM_REAL,
     FLOATINGPOINT_TO_FP_FROM_SBV,
     FLOATINGPOINT_TO_FP_FROM_UBV});

/* -------------------------------------------------------------------------- */
/* Rounding Mode for Floating Points                                          */
/* -------------------------------------------------------------------------- */

const static std::unordered_map<RoundingMode, cvc5::internal::RoundingMode>
    s_rmodes{
        {ROUND_NEAREST_TIES_TO_EVEN,
         cvc5::internal::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN},
        {ROUND_TOWARD_POSITIVE,
         cvc5::internal::RoundingMode::ROUND_TOWARD_POSITIVE},
        {ROUND_TOWARD_NEGATIVE,
         cvc5::internal::RoundingMode::ROUND_TOWARD_NEGATIVE},
        {ROUND_TOWARD_ZERO, cvc5::internal::RoundingMode::ROUND_TOWARD_ZERO},
        {ROUND_NEAREST_TIES_TO_AWAY,
         cvc5::internal::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY},
    };

const static std::unordered_map<cvc5::internal::RoundingMode, RoundingMode>
    s_rmodes_internal{
        {cvc5::internal::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN,
         ROUND_NEAREST_TIES_TO_EVEN},
        {cvc5::internal::RoundingMode::ROUND_TOWARD_POSITIVE,
         ROUND_TOWARD_POSITIVE},
        {cvc5::internal::RoundingMode::ROUND_TOWARD_NEGATIVE,
         ROUND_TOWARD_NEGATIVE},
        {cvc5::internal::RoundingMode::ROUND_TOWARD_ZERO, ROUND_TOWARD_ZERO},
        {cvc5::internal::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY,
         ROUND_NEAREST_TIES_TO_AWAY},
    };

namespace {

/** Convert a internal::Kind (internal) to a cvc5::Kind (external).
 */
cvc5::Kind intToExtKind(internal::Kind k)
{
  auto it = s_kinds_internal.find(k);
  if (it == s_kinds_internal.end())
  {
    return INTERNAL_KIND;
  }
  return it->second;
}

/** Convert a cvc5::Kind (external) to a internal::Kind (internal).
 */
internal::Kind extToIntKind(cvc5::Kind k)
{
  auto it = s_kinds.find(k);
  if (it == s_kinds.end())
  {
    return internal::Kind::UNDEFINED_KIND;
  }
  return it->second.first;
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
bool isApplyKind(internal::Kind k)
{
  return (k == internal::Kind::APPLY_UF
          || k == internal::Kind::APPLY_CONSTRUCTOR
          || k == internal::Kind::APPLY_SELECTOR
          || k == internal::Kind::APPLY_TESTER
          || k == internal::Kind::APPLY_UPDATER);
}

#ifdef CVC5_ASSERTIONS
/** Return true if given kind is a defined internal kind. */
bool isDefinedIntKind(internal::Kind k)
{
  return k != internal::Kind::UNDEFINED_KIND && k != internal::Kind::LAST_KIND;
}
#endif

/** Return the minimum arity of given kind. */
uint32_t minArity(Kind k)
{
  Assert(isDefinedKind(k));
  Assert(isDefinedIntKind(extToIntKind(k)));
  uint32_t min = internal::kind::metakind::getMinArityForKind(extToIntKind(k));

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
  uint32_t max = internal::kind::metakind::getMaxArityForKind(extToIntKind(k));

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
  auto it = s_kinds.find(k);
  if (it == s_kinds.end())
  {
    return "UNDEFINED_KIND";
  }
  return it->second.second;
}

std::ostream& operator<<(std::ostream& out, Kind k)
{
  return out << kindToString(k);
}

/* -------------------------------------------------------------------------- */
/* API guard helpers                                                          */
/* -------------------------------------------------------------------------- */

namespace {

class CVC5ApiExceptionStream
{
 public:
  CVC5ApiExceptionStream() {}
  /* Note: This needs to be explicitly set to 'noexcept(false)' since it is
   * a destructor that throws an exception and in C++11 all destructors
   * default to noexcept(true) (else this triggers a call to std::terminate). */
  ~CVC5ApiExceptionStream() noexcept(false)
  {
    if (std::uncaught_exceptions() == 0)
    {
      throw CVC5ApiException(d_stream.str());
    }
  }

  std::ostream& ostream() { return d_stream; }

 private:
  std::stringstream d_stream;
};

class CVC5ApiRecoverableExceptionStream
{
 public:
  CVC5ApiRecoverableExceptionStream() {}
  /* Note: This needs to be explicitly set to 'noexcept(false)' since it is
   * a destructor that throws an exception and in C++11 all destructors
   * default to noexcept(true) (else this triggers a call to std::terminate). */
  ~CVC5ApiRecoverableExceptionStream() noexcept(false)
  {
    if (std::uncaught_exceptions() == 0)
    {
      throw CVC5ApiRecoverableException(d_stream.str());
    }
  }

  std::ostream& ostream() { return d_stream; }

 private:
  std::stringstream d_stream;
};

class CVC5ApiUnsupportedExceptionStream
{
 public:
  CVC5ApiUnsupportedExceptionStream() {}
  /* Note: This needs to be explicitly set to 'noexcept(false)' since it is
   * a destructor that throws an exception and in C++11 all destructors
   * default to noexcept(true) (else this triggers a call to std::terminate). */
  ~CVC5ApiUnsupportedExceptionStream() noexcept(false)
  {
    if (std::uncaught_exceptions() == 0)
    {
      throw CVC5ApiUnsupportedException(d_stream.str());
    }
  }

  std::ostream& ostream() { return d_stream; }

 private:
  std::stringstream d_stream;
};

#define CVC5_API_TRY_CATCH_BEGIN \
  try                            \
  {
#define CVC5_API_TRY_CATCH_END                         \
  }                                                    \
  catch (const internal::OptionException& e)           \
  {                                                    \
    throw CVC5ApiOptionException(e.getMessage());      \
  }                                                    \
  catch (const internal::RecoverableModalException& e) \
  {                                                    \
    throw CVC5ApiRecoverableException(e.getMessage()); \
  }                                                    \
  catch (const internal::Exception& e)                 \
  {                                                    \
    throw CVC5ApiException(e.getMessage());            \
  }                                                    \
  catch (const std::invalid_argument& e) { throw CVC5ApiException(e.what()); }

}  // namespace

/* -------------------------------------------------------------------------- */
/* Result                                                                     */
/* -------------------------------------------------------------------------- */

Result::Result(const internal::Result& r) : d_result(new internal::Result(r)) {}

Result::Result() : d_result(new internal::Result()) {}

bool Result::isNull() const
{
  return d_result->getStatus() == internal::Result::NONE;
}

bool Result::isSat(void) const
{
  return d_result->getStatus() == internal::Result::SAT;
}

bool Result::isUnsat(void) const
{
  return d_result->getStatus() == internal::Result::UNSAT;
}

bool Result::isUnknown(void) const
{
  return d_result->getStatus() == internal::Result::UNKNOWN;
}

bool Result::operator==(const Result& r) const
{
  return *d_result == *r.d_result;
}

bool Result::operator!=(const Result& r) const
{
  return *d_result != *r.d_result;
}

UnknownExplanation Result::getUnknownExplanation(void) const
{
  return d_result->getUnknownExplanation();
}

std::string Result::toString(void) const { return d_result->toString(); }

std::ostream& operator<<(std::ostream& out, const Result& r)
{
  out << r.toString();
  return out;
}

/* -------------------------------------------------------------------------- */
/* SynthResult */
/* -------------------------------------------------------------------------- */

SynthResult::SynthResult(const internal::SynthResult& r)
    : d_result(new internal::SynthResult(r))
{
}

SynthResult::SynthResult() : d_result(new internal::SynthResult()) {}

bool SynthResult::isNull() const
{
  return d_result->getStatus() == internal::SynthResult::NONE;
}

bool SynthResult::hasSolution(void) const
{
  return d_result->getStatus() == internal::SynthResult::SOLUTION;
}

bool SynthResult::hasNoSolution() const
{
  return d_result->getStatus() == internal::SynthResult::NO_SOLUTION;
}

bool SynthResult::isUnknown() const
{
  return d_result->getStatus() == internal::SynthResult::UNKNOWN;
}

std::string SynthResult::toString(void) const { return d_result->toString(); }

std::ostream& operator<<(std::ostream& out, const SynthResult& sr)
{
  out << sr.toString();
  return out;
}

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

Sort::Sort(const Solver* slv, const internal::TypeNode& t)
    : d_solver(slv), d_type(new internal::TypeNode(t))
{
}

Sort::Sort() : d_solver(nullptr), d_type(new internal::TypeNode()) {}

Sort::~Sort()
{
  if (d_solver != nullptr)
  {
    d_type.reset();
  }
}

std::vector<internal::TypeNode> Sort::sortVectorToTypeNodes(
    const std::vector<Sort>& sorts)
{
  std::vector<internal::TypeNode> typeNodes;
  for (const Sort& sort : sorts)
  {
    typeNodes.push_back(sort.getTypeNode());
  }
  return typeNodes;
}

std::vector<Sort> Sort::typeNodeVectorToSorts(
    const Solver* slv, const std::vector<internal::TypeNode>& types)
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
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_type == *s.d_type;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::operator!=(const Sort& s) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_type != *s.d_type;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::operator<(const Sort& s) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_type < *s.d_type;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::operator>(const Sort& s) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_type > *s.d_type;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::operator<=(const Sort& s) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_type <= *s.d_type;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::operator>=(const Sort& s) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_type >= *s.d_type;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::hasSymbol() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_type->hasAttribute(internal::expr::VarNameAttr());
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Sort::getSymbol() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->hasAttribute(internal::expr::VarNameAttr()))
      << "Invalid call to '" << __PRETTY_FUNCTION__
      << "', expected the sort to have a symbol.";
  //////// all checks before this line
  return d_type->getAttribute(internal::expr::VarNameAttr());
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isNull() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isBoolean() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isBoolean();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isInteger() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isInteger();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isReal() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  // notice that we do not expose internal subtyping to the user
  return d_type->isReal() && !d_type->isInteger();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isString() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isString();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isRegExp() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isRegExp();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isRoundingMode() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isRoundingMode();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isBitVector() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isBitVector();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isFloatingPoint() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isFloatingPoint();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isDatatype() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isDatatype();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isDatatypeConstructor() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isDatatypeConstructor();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isDatatypeSelector() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isDatatypeSelector();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isDatatypeTester() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isDatatypeTester();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isDatatypeUpdater() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isDatatypeUpdater();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isFunction() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isFunction();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isPredicate() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isPredicate();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isTuple() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isTuple();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isRecord() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isRecord();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isArray() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isArray();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isSet() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isSet();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isBag() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isBag();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isSequence() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isSequence();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isUninterpretedSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isUninterpretedSort();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isUninterpretedSortConstructor() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isUninterpretedSortConstructor();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::getUninterpretedSortConstructor() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isInstantiatedUninterpretedSort())
      << "Expected instantiated uninterpreted sort.";
  //////// all checks before this line
  return Sort(d_solver, d_type->getUninterpretedSortConstructor());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Datatype Sort::getDatatype() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatype()) << "Expected datatype sort.";
  //////// all checks before this line
  return Datatype(d_solver, d_type->getDType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::isInstantiated() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_type->isInstantiated();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::instantiate(const std::vector<Sort>& params) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK_DOMAIN_SORTS(params);
  CVC5_API_CHECK(d_type->isParametricDatatype()
                 || d_type->isUninterpretedSortConstructor())
      << "Expected parametric datatype or sort constructor sort.";
  CVC5_API_CHECK(!d_type->isParametricDatatype()
                 || d_type->getNumChildren() == params.size() + 1)
      << "Arity mismatch for instantiated parametric datatype";
  CVC5_API_CHECK(!d_type->isUninterpretedSortConstructor()
                 || d_type->getUninterpretedSortConstructorArity()
                        == params.size())
      << "Arity mismatch for instantiated sort constructor";
  //////// all checks before this line
  std::vector<internal::TypeNode> tparams = sortVectorToTypeNodes(params);
  return Sort(d_solver, d_type->instantiate(tparams));
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Sort> Sort::getInstantiatedParameters() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isInstantiated())
      << "Expected instantiated parametric sort";
  //////// all checks before this line
  return typeNodeVectorToSorts(d_solver, d_type->getInstantiatedParamTypes());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::substitute(const Sort& sort, const Sort& replacement) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK_SORT(sort);
  CVC5_API_CHECK_SORT(replacement);
  //////// all checks before this line
  return Sort(
      d_solver,
      d_type->substitute(sort.getTypeNode(), replacement.getTypeNode()));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::substitute(const std::vector<Sort>& sorts,
                      const std::vector<Sort>& replacements) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK_SORTS(sorts);
  CVC5_API_CHECK_SORTS(replacements);
  //////// all checks before this line

  std::vector<internal::TypeNode> tSorts = sortVectorToTypeNodes(sorts),
                                  tReplacements =
                                      sortVectorToTypeNodes(replacements);
  return Sort(d_solver,
              d_type->substitute(tSorts.begin(),
                                 tSorts.end(),
                                 tReplacements.begin(),
                                 tReplacements.end()));
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Sort::toString() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->toString();
  ////////
  CVC5_API_TRY_CATCH_END;
}

const internal::TypeNode& Sort::getTypeNode(void) const { return *d_type; }

/* Constructor sort ------------------------------------------------------- */

size_t Sort::getDatatypeConstructorArity() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatypeConstructor())
      << "Not a constructor sort: " << (*this);
  //////// all checks before this line
  return d_type->getNumChildren() - 1;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Sort> Sort::getDatatypeConstructorDomainSorts() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatypeConstructor())
      << "Not a constructor sort: " << (*this);
  //////// all checks before this line
  return typeNodeVectorToSorts(d_solver, d_type->getArgTypes());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::getDatatypeConstructorCodomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatypeConstructor())
      << "Not a constructor sort: " << (*this);
  //////// all checks before this line
  return Sort(d_solver, d_type->getDatatypeConstructorRangeType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Selector sort ------------------------------------------------------- */

Sort Sort::getDatatypeSelectorDomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatypeSelector())
      << "Not a selector sort: " << (*this);
  //////// all checks before this line
  return Sort(d_solver, d_type->getDatatypeSelectorDomainType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::getDatatypeSelectorCodomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatypeSelector())
      << "Not a selector sort: " << (*this);
  //////// all checks before this line
  return Sort(d_solver, d_type->getDatatypeSelectorRangeType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Tester sort ------------------------------------------------------- */

Sort Sort::getDatatypeTesterDomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatypeTester())
      << "Not a tester sort: " << (*this);
  //////// all checks before this line
  return Sort(d_solver, d_type->getDatatypeTesterDomainType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::getDatatypeTesterCodomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatypeTester())
      << "Not a tester sort: " << (*this);
  //////// all checks before this line
  return d_solver->getBooleanSort();
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Function sort ------------------------------------------------------- */

size_t Sort::getFunctionArity() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isFunction()) << "Not a function sort: " << (*this);
  //////// all checks before this line
  return d_type->getNumChildren() - 1;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Sort> Sort::getFunctionDomainSorts() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isFunction()) << "Not a function sort: " << (*this);
  //////// all checks before this line
  return typeNodeVectorToSorts(d_solver, d_type->getArgTypes());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::getFunctionCodomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isFunction()) << "Not a function sort" << (*this);
  //////// all checks before this line
  return Sort(d_solver, d_type->getRangeType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Array sort ---------------------------------------------------------- */

Sort Sort::getArrayIndexSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isArray()) << "Not an array sort.";
  //////// all checks before this line
  return Sort(d_solver, d_type->getArrayIndexType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::getArrayElementSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isArray()) << "Not an array sort.";
  //////// all checks before this line
  return Sort(d_solver, d_type->getArrayConstituentType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Set sort ------------------------------------------------------------ */

Sort Sort::getSetElementSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isSet()) << "Not a set sort.";
  //////// all checks before this line
  return Sort(d_solver, d_type->getSetElementType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Bag sort ------------------------------------------------------------ */

Sort Sort::getBagElementSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isBag()) << "Not a bag sort.";
  //////// all checks before this line
  return Sort(d_solver, d_type->getBagElementType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Sequence sort ------------------------------------------------------- */

Sort Sort::getSequenceElementSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isSequence()) << "Not a sequence sort.";
  //////// all checks before this line
  return Sort(d_solver, d_type->getSequenceElementType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Sort constructor sort ----------------------------------------------- */

size_t Sort::getUninterpretedSortConstructorArity() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isUninterpretedSortConstructor())
      << "Not a sort constructor sort.";
  //////// all checks before this line
  return d_type->getUninterpretedSortConstructorArity();
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Bit-vector sort ----------------------------------------------------- */

uint32_t Sort::getBitVectorSize() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isBitVector()) << "Not a bit-vector sort.";
  //////// all checks before this line
  return d_type->getBitVectorSize();
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Floating-point sort ------------------------------------------------- */

uint32_t Sort::getFloatingPointExponentSize() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isFloatingPoint()) << "Not a floating-point sort.";
  //////// all checks before this line
  return d_type->getFloatingPointExponentSize();
  ////////
  CVC5_API_TRY_CATCH_END;
}

uint32_t Sort::getFloatingPointSignificandSize() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isFloatingPoint()) << "Not a floating-point sort.";
  //////// all checks before this line
  return d_type->getFloatingPointSignificandSize();
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Datatype sort ------------------------------------------------------- */

size_t Sort::getDatatypeArity() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatype()) << "Not a datatype sort.";
  //////// all checks before this line
  return d_type->isParametricDatatype() ? d_type->getNumChildren() - 1 : 0;
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Tuple sort ---------------------------------------------------------- */

size_t Sort::getTupleLength() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isTuple()) << "Not a tuple sort.";
  //////// all checks before this line
  return d_type->getTupleLength();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Sort> Sort::getTupleSorts() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isTuple()) << "Not a tuple sort.";
  //////// all checks before this line
  return typeNodeVectorToSorts(d_solver, d_type->getTupleTypes());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* --------------------------------------------------------------------- */

std::ostream& operator<<(std::ostream& out, const Sort& s)
{
  out << s.toString();
  return out;
}

/* Helpers                                                                    */
/* -------------------------------------------------------------------------- */

/* Split out to avoid nested API calls (problematic with API tracing).        */
/* .......................................................................... */

bool Sort::isNullHelper() const { return d_type->isNull(); }

/* -------------------------------------------------------------------------- */
/* Op                                                                     */
/* -------------------------------------------------------------------------- */

Op::Op() : d_solver(nullptr), d_kind(NULL_TERM), d_node(new internal::Node()) {}

Op::Op(const Solver* slv, const Kind k)
    : d_solver(slv), d_kind(k), d_node(new internal::Node())
{
}

Op::Op(const Solver* slv, const Kind k, const internal::Node& n)
    : d_solver(slv), d_kind(k), d_node(new internal::Node(n))
{
}

Op::~Op()
{
  if (d_solver != nullptr)
  {
    // Ensure that the correct node manager is in scope when the type node is
    // destroyed.
    d_node.reset();
  }
}

/* Public methods                                                             */
bool Op::operator==(const Op& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
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
  CVC5_API_TRY_CATCH_END;
}

bool Op::operator!=(const Op& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return !(*this == t);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Kind Op::getKind() const
{
  CVC5_API_CHECK(d_kind != NULL_TERM) << "Expecting a non-null Kind";
  //////// all checks before this line
  return d_kind;
}

bool Op::isNull() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Op::isIndexed() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isIndexedHelper();
  ////////
  CVC5_API_TRY_CATCH_END;
}

size_t Op::getNumIndices() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getNumIndicesHelper();
  ////////
  CVC5_API_TRY_CATCH_END;
}

size_t Op::getNumIndicesHelper() const
{
  if (!isIndexedHelper())
  {
    return 0;
  }

  Kind k = intToExtKind(d_node->getKind());
  size_t size = 0;
  switch (k)
  {
    case DIVISIBLE: size = 1; break;
    case BITVECTOR_REPEAT: size = 1; break;
    case BITVECTOR_ZERO_EXTEND: size = 1; break;
    case BITVECTOR_SIGN_EXTEND: size = 1; break;
    case BITVECTOR_ROTATE_LEFT: size = 1; break;
    case BITVECTOR_ROTATE_RIGHT: size = 1; break;
    case INT_TO_BITVECTOR: size = 1; break;
    case IAND: size = 1; break;
    case FLOATINGPOINT_TO_UBV: size = 1; break;
    case FLOATINGPOINT_TO_SBV: size = 1; break;
    case REGEXP_REPEAT: size = 1; break;
    case BITVECTOR_EXTRACT: size = 2; break;
    case FLOATINGPOINT_TO_FP_FROM_IEEE_BV: size = 2; break;
    case FLOATINGPOINT_TO_FP_FROM_FP: size = 2; break;
    case FLOATINGPOINT_TO_FP_FROM_REAL: size = 2; break;
    case FLOATINGPOINT_TO_FP_FROM_SBV: size = 2; break;
    case FLOATINGPOINT_TO_FP_FROM_UBV: size = 2; break;
    case REGEXP_LOOP: size = 2; break;
    case TUPLE_PROJECT:
      size = d_node->getConst<internal::TupleProjectOp>().getIndices().size();
      break;
    case TABLE_PROJECT:
      size = d_node->getConst<internal::TableProjectOp>().getIndices().size();
      break;
    default: CVC5_API_CHECK(false) << "Unhandled kind " << kindToString(k);
  }
  return size;
}

Term Op::operator[](size_t index) const
{
  return getIndexHelper(index);
}

Term Op::getIndexHelper(size_t index) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(!d_node->isNull())
      << "Expecting a non-null internal expression. This Op is not indexed.";
  CVC5_API_CHECK(index < getNumIndicesHelper()) << "index out of bound";
  Kind k = intToExtKind(d_node->getKind());
  Term t;
  switch (k)
  {
    case DIVISIBLE:
    {
      t = d_solver->mkRationalValHelper(
          internal::Rational(d_node->getConst<internal::Divisible>().k));
      break;
    }
    case BITVECTOR_REPEAT:
    {
      t = d_solver->mkRationalValHelper(
          d_node->getConst<internal::BitVectorRepeat>().d_repeatAmount);
      break;
    }
    case BITVECTOR_ZERO_EXTEND:
    {
      t = d_solver->mkRationalValHelper(
          d_node->getConst<internal::BitVectorZeroExtend>().d_zeroExtendAmount);
      break;
    }
    case BITVECTOR_SIGN_EXTEND:
    {
      t = d_solver->mkRationalValHelper(
          d_node->getConst<internal::BitVectorSignExtend>().d_signExtendAmount);
      break;
    }
    case BITVECTOR_ROTATE_LEFT:
    {
      t = d_solver->mkRationalValHelper(
          d_node->getConst<internal::BitVectorRotateLeft>().d_rotateLeftAmount);
      break;
    }
    case BITVECTOR_ROTATE_RIGHT:
    {
      t = d_solver->mkRationalValHelper(
          d_node->getConst<internal::BitVectorRotateRight>()
              .d_rotateRightAmount);
      break;
    }
    case INT_TO_BITVECTOR:
    {
      t = d_solver->mkRationalValHelper(
          d_node->getConst<internal::IntToBitVector>().d_size);
      break;
    }
    case IAND:
    {
      t = d_solver->mkRationalValHelper(
          d_node->getConst<internal::IntAnd>().d_size);
      break;
    }
    case FLOATINGPOINT_TO_UBV:
    {
      t = d_solver->mkRationalValHelper(
          d_node->getConst<internal::FloatingPointToUBV>().d_bv_size.d_size);
      break;
    }
    case FLOATINGPOINT_TO_SBV:
    {
      t = d_solver->mkRationalValHelper(
          d_node->getConst<internal::FloatingPointToSBV>().d_bv_size.d_size);
      break;
    }
    case REGEXP_REPEAT:
    {
      t = d_solver->mkRationalValHelper(
          d_node->getConst<internal::RegExpRepeat>().d_repeatAmount);
      break;
    }
    case BITVECTOR_EXTRACT:
    {
      internal::BitVectorExtract ext =
          d_node->getConst<internal::BitVectorExtract>();
      t = index == 0 ? d_solver->mkRationalValHelper(ext.d_high)
                     : d_solver->mkRationalValHelper(ext.d_low);
      break;
    }
    case FLOATINGPOINT_TO_FP_FROM_IEEE_BV:
    {
      internal::FloatingPointToFPIEEEBitVector ext =
          d_node->getConst<internal::FloatingPointToFPIEEEBitVector>();

      t = index == 0
              ? d_solver->mkRationalValHelper(ext.getSize().exponentWidth())
              : d_solver->mkRationalValHelper(ext.getSize().significandWidth());
      break;
    }
    case FLOATINGPOINT_TO_FP_FROM_FP:
    {
      internal::FloatingPointToFPFloatingPoint ext =
          d_node->getConst<internal::FloatingPointToFPFloatingPoint>();
      t = index == 0
              ? d_solver->mkRationalValHelper(ext.getSize().exponentWidth())
              : d_solver->mkRationalValHelper(ext.getSize().significandWidth());
      break;
    }
    case FLOATINGPOINT_TO_FP_FROM_REAL:
    {
      internal::FloatingPointToFPReal ext =
          d_node->getConst<internal::FloatingPointToFPReal>();

      t = index == 0
              ? d_solver->mkRationalValHelper(ext.getSize().exponentWidth())
              : d_solver->mkRationalValHelper(ext.getSize().significandWidth());
      break;
    }
    case FLOATINGPOINT_TO_FP_FROM_SBV:
    {
      internal::FloatingPointToFPSignedBitVector ext =
          d_node->getConst<internal::FloatingPointToFPSignedBitVector>();
      t = index == 0
              ? d_solver->mkRationalValHelper(ext.getSize().exponentWidth())
              : d_solver->mkRationalValHelper(ext.getSize().significandWidth());
      break;
    }
    case FLOATINGPOINT_TO_FP_FROM_UBV:
    {
      internal::FloatingPointToFPUnsignedBitVector ext =
          d_node->getConst<internal::FloatingPointToFPUnsignedBitVector>();
      t = index == 0
              ? d_solver->mkRationalValHelper(ext.getSize().exponentWidth())
              : d_solver->mkRationalValHelper(ext.getSize().significandWidth());
      break;
    }
    case REGEXP_LOOP:
    {
      internal::RegExpLoop ext = d_node->getConst<internal::RegExpLoop>();
      t = index == 0 ? d_solver->mkRationalValHelper(ext.d_loopMinOcc)
                     : d_solver->mkRationalValHelper(ext.d_loopMaxOcc);

      break;
    }

    case TUPLE_PROJECT:
    {
      const std::vector<uint32_t>& projectionIndices =
          d_node->getConst<internal::TupleProjectOp>().getIndices();
      t = d_solver->mkRationalValHelper(projectionIndices[index]);
      break;
    }
    default:
    {
      CVC5_API_CHECK(false) << "Unhandled kind " << kindToString(k);
      break;
    }
  }

  //////// all checks before this line
  return t;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Op::toString() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (d_node->isNull())
  {
    return kindToString(d_kind);
  }
  else
  {
    CVC5_API_CHECK(!d_node->isNull())
        << "Expecting a non-null internal expression";
    if (d_solver != nullptr)
    {
      return d_node->toString();
    }
    return d_node->toString();
  }
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::ostream& operator<<(std::ostream& out, const Op& t)
{
  out << t.toString();
  return out;
}

/* Helpers                                                                    */
/* -------------------------------------------------------------------------- */

/* Split out to avoid nested API calls (problematic with API tracing).        */
/* .......................................................................... */

bool Op::isNullHelper() const
{
  return (d_node->isNull() && (d_kind == NULL_TERM));
}

bool Op::isIndexedHelper() const { return !d_node->isNull(); }

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

Term::Term() : d_solver(nullptr), d_node(new internal::Node()) {}

Term::Term(const Solver* slv, const internal::Node& n) : d_solver(slv)
{
  d_node.reset(new internal::Node(n));
}

Term::~Term()
{
  if (d_solver != nullptr)
  {
    d_node.reset();
  }
}

bool Term::operator==(const Term& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_node == *t.d_node;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::operator!=(const Term& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_node != *t.d_node;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::operator<(const Term& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_node < *t.d_node;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::operator>(const Term& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_node > *t.d_node;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::operator<=(const Term& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_node <= *t.d_node;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::operator>=(const Term& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return *d_node >= *t.d_node;
  ////////
  CVC5_API_TRY_CATCH_END;
}

size_t Term::getNumChildren() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line

  // special case for apply kinds
  if (isApplyKind(d_node->getKind()))
  {
    return d_node->getNumChildren() + 1;
  }
  return d_node->getNumChildren();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::operator[](size_t index) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(index < getNumChildren()) << "index out of bound";
  CVC5_API_CHECK(!isApplyKind(d_node->getKind()) || d_node->hasOperator())
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
  CVC5_API_TRY_CATCH_END;
}

uint64_t Term::getId() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getId();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Kind Term::getKind() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getKindHelper();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Term::getSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Sort(d_solver, d_node->getType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::substitute(const Term& term, const Term& replacement) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK_TERM(term);
  CVC5_API_CHECK_TERM(replacement);
  CVC5_API_CHECK(term.getSort() == replacement.getSort())
      << "Expecting terms of the same sort in substitute";
  //////// all checks before this line
  return Term(d_solver,
              d_node->substitute(internal::TNode(*term.d_node),
                                 internal::TNode(*replacement.d_node)));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::substitute(const std::vector<Term>& terms,
                      const std::vector<Term>& replacements) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(terms.size() == replacements.size())
      << "Expecting vectors of the same arity in substitute";
  CVC5_API_TERM_CHECK_TERMS_WITH_TERMS_SORT_EQUAL_TO(terms, replacements);
  //////// all checks before this line
  std::vector<internal::Node> nodes = Term::termVectorToNodes(terms);
  std::vector<internal::Node> nodeReplacements =
      Term::termVectorToNodes(replacements);
  return Term(d_solver,
              d_node->substitute(nodes.begin(),
                                 nodes.end(),
                                 nodeReplacements.begin(),
                                 nodeReplacements.end()));
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::hasOp() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->hasOperator();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Op Term::getOp() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_node->hasOperator())
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
  else if (d_node->getMetaKind() == internal::kind::metakind::PARAMETERIZED)
  {
    // it's an indexed operator
    // so we should return the indexed op
    internal::Node op = d_node->getOperator();
    return Op(d_solver, intToExtKind(d_node->getKind()), op);
  }
  // Notice this is the only case where getKindHelper is used, since the
  // cases above do not have special cases for intToExtKind.
  return Op(d_solver, getKindHelper());
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::hasSymbol() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->hasAttribute(internal::expr::VarNameAttr());
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Term::getSymbol() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_node->hasAttribute(internal::expr::VarNameAttr()))
      << "Invalid call to '" << __PRETTY_FUNCTION__
      << "', expected the term to have a symbol.";
  //////// all checks before this line
  return d_node->getAttribute(internal::expr::VarNameAttr());
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isNull() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::notTerm() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  internal::Node res = d_node->notNode();
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::andTerm(const Term& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK_TERM(t);
  //////// all checks before this line
  internal::Node res = d_node->andNode(*t.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::orTerm(const Term& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK_TERM(t);
  //////// all checks before this line
  internal::Node res = d_node->orNode(*t.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::xorTerm(const Term& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK_TERM(t);
  //////// all checks before this line
  internal::Node res = d_node->xorNode(*t.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::eqTerm(const Term& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK_TERM(t);
  //////// all checks before this line
  internal::Node res = d_node->eqNode(*t.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::impTerm(const Term& t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK_TERM(t);
  //////// all checks before this line
  internal::Node res = d_node->impNode(*t.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::iteTerm(const Term& then_t, const Term& else_t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK_TERM(then_t);
  CVC5_API_CHECK_TERM(else_t);
  //////// all checks before this line
  internal::Node res = d_node->iteNode(*then_t.d_node, *else_t.d_node);
  (void)res.getType(true); /* kick off type checking */
  return Term(d_solver, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Term::toString() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_node->toString();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term::const_iterator::const_iterator()
    : d_solver(nullptr), d_origNode(nullptr), d_pos(0)
{
}

Term::const_iterator::const_iterator(const Solver* slv,
                                     const std::shared_ptr<internal::Node>& n,
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

const internal::Node& Term::getNode(void) const { return *d_node; }

namespace detail {
const internal::Rational& getRational(const internal::Node& node)
{
  switch (node.getKind())
  {
    case internal::Kind::CONST_INTEGER:
    case internal::Kind::CONST_RATIONAL:
      return node.getConst<internal::Rational>();
    default:
      CVC5_API_CHECK(false) << "Node is not a rational.";
      return node.getConst<internal::Rational>();
  }
}
internal::Integer getInteger(const internal::Node& node)
{
  return node.getConst<internal::Rational>().getNumerator();
}
template <typename T>
bool checkIntegerBounds(const internal::Integer& i)
{
  return i >= std::numeric_limits<T>::min()
         && i <= std::numeric_limits<T>::max();
}
bool checkReal32Bounds(const internal::Rational& r)
{
  return checkIntegerBounds<std::int32_t>(r.getNumerator())
         && checkIntegerBounds<std::uint32_t>(r.getDenominator());
}
bool checkReal64Bounds(const internal::Rational& r)
{
  return checkIntegerBounds<std::int64_t>(r.getNumerator())
         && checkIntegerBounds<std::uint64_t>(r.getDenominator());
}

bool isReal(const internal::Node& node)
{
  return node.getKind() == internal::Kind::CONST_RATIONAL
         || node.getKind() == internal::Kind::CONST_INTEGER;
}
bool isReal32(const internal::Node& node)
{
  return isReal(node) && checkReal32Bounds(getRational(node));
}
bool isReal64(const internal::Node& node)
{
  return isReal(node) && checkReal64Bounds(getRational(node));
}

bool isInteger(const internal::Node& node)
{
  return (node.getKind() == internal::Kind::CONST_RATIONAL
          || node.getKind() == internal::Kind::CONST_INTEGER)
         && node.getConst<internal::Rational>().isIntegral();
}
bool isInt32(const internal::Node& node)
{
  return isInteger(node) && checkIntegerBounds<std::int32_t>(getInteger(node));
}
bool isUInt32(const internal::Node& node)
{
  return isInteger(node) && checkIntegerBounds<std::uint32_t>(getInteger(node));
}
bool isInt64(const internal::Node& node)
{
  return isInteger(node) && checkIntegerBounds<std::int64_t>(getInteger(node));
}
bool isUInt64(const internal::Node& node)
{
  return isInteger(node) && checkIntegerBounds<std::uint64_t>(getInteger(node));
}
}  // namespace detail

int32_t Term::getRealOrIntegerValueSign() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  const internal::Rational& r = detail::getRational(*d_node);
  return static_cast<int32_t>(r.sgn());
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isInt32Value() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return detail::isInt32(*d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::int32_t Term::getInt32Value() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(detail::isInt32(*d_node), *d_node)
      << "Term to be a 32-bit integer value when calling getInt32Value()";
  //////// all checks before this line
  return detail::getInteger(*d_node).getSignedInt();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isUInt32Value() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return detail::isUInt32(*d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::uint32_t Term::getUInt32Value() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(detail::isUInt32(*d_node), *d_node)
      << "Term to be a unsigned 32-bit integer value when calling "
         "getUInt32Value()";
  //////// all checks before this line
  return detail::getInteger(*d_node).getUnsignedInt();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isInt64Value() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return detail::isInt64(*d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::int64_t Term::getInt64Value() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(detail::isInt64(*d_node), *d_node)
      << "Term to be a 64-bit integer value when calling getInt64Value()";
  //////// all checks before this line
  return detail::getInteger(*d_node).getSigned64();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isUInt64Value() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return detail::isUInt64(*d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::uint64_t Term::getUInt64Value() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(detail::isUInt64(*d_node), *d_node)
      << "Term to be a unsigned 64-bit integer value when calling "
         "getUInt64Value()";
  //////// all checks before this line
  return detail::getInteger(*d_node).getUnsigned64();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isIntegerValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return detail::isInteger(*d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::string Term::getIntegerValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(detail::isInteger(*d_node), *d_node)
      << "Term to be an integer value when calling getIntegerValue()";
  //////// all checks before this line
  return detail::getInteger(*d_node).toString();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isStringValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::CONST_STRING;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::wstring Term::getStringValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(d_node->getKind() == internal::Kind::CONST_STRING,
                              *d_node)
      << "Term to be a string value when calling getStringValue()";
  //////// all checks before this line
  return d_node->getConst<internal::String>().toWString();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<internal::Node> Term::termVectorToNodes(
    const std::vector<Term>& terms)
{
  std::vector<internal::Node> res;
  for (const Term& t : terms)
  {
    res.push_back(t.getNode());
  }
  return res;
}

std::vector<Term> Term::nodeVectorToTerms(
    const Solver* slv, const std::vector<internal::Node>& nodes)
{
  std::vector<Term> res;
  for (const internal::Node& n : nodes)
  {
    res.push_back(Term(slv, n));
  }
  return res;
}

bool Term::isReal32Value() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return detail::isReal32(*d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::pair<std::int32_t, std::uint32_t> Term::getReal32Value() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(detail::isReal32(*d_node), *d_node)
      << "Term to be a 32-bit rational value when calling getReal32Value()";
  //////// all checks before this line
  const internal::Rational& r = detail::getRational(*d_node);
  return std::make_pair(r.getNumerator().getSignedInt(),
                        r.getDenominator().getUnsignedInt());
  ////////
  CVC5_API_TRY_CATCH_END;
}
bool Term::isReal64Value() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return detail::isReal64(*d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::pair<std::int64_t, std::uint64_t> Term::getReal64Value() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(detail::isReal64(*d_node), *d_node)
      << "Term to be a 64-bit rational value when calling getReal64Value()";
  //////// all checks before this line
  const internal::Rational& r = detail::getRational(*d_node);
  return std::make_pair(r.getNumerator().getSigned64(),
                        r.getDenominator().getUnsigned64());
  ////////
  CVC5_API_TRY_CATCH_END;
}
bool Term::isRealValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return detail::isReal(*d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::string Term::getRealValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(detail::isReal(*d_node), *d_node)
      << "Term to be a rational value when calling getRealValue()";
  //////// all checks before this line
  const internal::Rational& rat = detail::getRational(*d_node);
  std::string res = rat.toString();
  if (rat.isIntegral())
  {
    return res + "/1";
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isConstArray() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::STORE_ALL;
  ////////
  CVC5_API_TRY_CATCH_END;
}
Term Term::getConstArrayBase() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(d_node->getKind() == internal::Kind::STORE_ALL,
                              *d_node)
      << "Term to be a constant array when calling getConstArrayBase()";
  //////// all checks before this line
  const auto& ar = d_node->getConst<internal::ArrayStoreAll>();
  return Term(d_solver, ar.getValue());
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isBooleanValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::CONST_BOOLEAN;
  ////////
  CVC5_API_TRY_CATCH_END;
}
bool Term::getBooleanValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(
      d_node->getKind() == internal::Kind::CONST_BOOLEAN, *d_node)
      << "Term to be a Boolean value when calling getBooleanValue()";
  //////// all checks before this line
  return d_node->getConst<bool>();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isBitVectorValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::CONST_BITVECTOR;
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::string Term::getBitVectorValue(std::uint32_t base) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(
      d_node->getKind() == internal::Kind::CONST_BITVECTOR, *d_node)
      << "Term to be a bit-vector value when calling getBitVectorValue()";
  //////// all checks before this line
  return d_node->getConst<internal::BitVector>().toString(base);
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isUninterpretedSortValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::UNINTERPRETED_SORT_VALUE;
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::string Term::getUninterpretedSortValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(
      d_node->getKind() == internal::Kind::UNINTERPRETED_SORT_VALUE, *d_node)
      << "Term to be an abstract value when calling "
         "getUninterpretedSortValue()";
  //////// all checks before this line
  std::stringstream ss;
  ss << d_node->getConst<internal::UninterpretedSortValue>();
  return ss.str();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isTupleValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::APPLY_CONSTRUCTOR
         && d_node->isConst() && d_node->getType().getDType().isTuple();
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::vector<Term> Term::getTupleValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(
      d_node->getKind() == internal::Kind::APPLY_CONSTRUCTOR
          && d_node->isConst() && d_node->getType().getDType().isTuple(),
      *d_node)
      << "Term to be a tuple value when calling getTupleValue()";
  //////// all checks before this line
  std::vector<Term> res;
  for (size_t i = 0, n = d_node->getNumChildren(); i < n; ++i)
  {
    res.emplace_back(Term(d_solver, (*d_node)[i]));
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isRoundingModeValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::CONST_ROUNDINGMODE;
  ////////
  CVC5_API_TRY_CATCH_END;
}
RoundingMode Term::getRoundingModeValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(
      d_node->getKind() == internal::Kind::CONST_ROUNDINGMODE, *d_node)
      << "Term to be a floating-point rounding mode value when calling "
         "getRoundingModeValue()";
  //////// all checks before this line
  return s_rmodes_internal.at(d_node->getConst<cvc5::internal::RoundingMode>());
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isFloatingPointPosZero() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  if (d_node->getKind() == internal::Kind::CONST_FLOATINGPOINT)
  {
    const auto& fp = d_node->getConst<internal::FloatingPoint>();
    return fp.isZero() && fp.isPositive();
  }
  return false;
  ////////
  CVC5_API_TRY_CATCH_END;
}
bool Term::isFloatingPointNegZero() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  if (d_node->getKind() == internal::Kind::CONST_FLOATINGPOINT)
  {
    const auto& fp = d_node->getConst<internal::FloatingPoint>();
    return fp.isZero() && fp.isNegative();
  }
  return false;
  ////////
  CVC5_API_TRY_CATCH_END;
}
bool Term::isFloatingPointPosInf() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  if (d_node->getKind() == internal::Kind::CONST_FLOATINGPOINT)
  {
    const auto& fp = d_node->getConst<internal::FloatingPoint>();
    return fp.isInfinite() && fp.isPositive();
  }
  return false;
  ////////
  CVC5_API_TRY_CATCH_END;
}
bool Term::isFloatingPointNegInf() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  if (d_node->getKind() == internal::Kind::CONST_FLOATINGPOINT)
  {
    const auto& fp = d_node->getConst<internal::FloatingPoint>();
    return fp.isInfinite() && fp.isNegative();
  }
  return false;
  ////////
  CVC5_API_TRY_CATCH_END;
}
bool Term::isFloatingPointNaN() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::CONST_FLOATINGPOINT
         && d_node->getConst<internal::FloatingPoint>().isNaN();
  ////////
  CVC5_API_TRY_CATCH_END;
}
bool Term::isFloatingPointValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::CONST_FLOATINGPOINT;
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::tuple<std::uint32_t, std::uint32_t, Term> Term::getFloatingPointValue()
    const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(
      d_node->getKind() == internal::Kind::CONST_FLOATINGPOINT, *d_node)
      << "Term to be a floating-point value when calling "
         "getFloatingPointValue()";
  //////// all checks before this line
  const auto& fp = d_node->getConst<internal::FloatingPoint>();
  return std::make_tuple(fp.getSize().exponentWidth(),
                         fp.getSize().significandWidth(),
                         d_solver->mkValHelper(fp.pack()));
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isSetValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getType().isSet() && d_node->isConst();
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Term::collectSet(std::set<Term>& set,
                      const internal::Node& node,
                      const Solver* slv)
{
  // We asserted that node has a set type, and node.isConst()
  // Thus, node only contains of SET_EMPTY, SET_UNION and SET_SINGLETON.
  switch (node.getKind())
  {
    case internal::Kind::SET_EMPTY: break;
    case internal::Kind::SET_SINGLETON: set.emplace(Term(slv, node[0])); break;
    case internal::Kind::SET_UNION:
    {
      for (const auto& sub : node)
      {
        collectSet(set, sub, slv);
      }
      break;
    }
    default:
      CVC5_API_ARG_CHECK_EXPECTED(false, node)
          << "Term to be a set value when calling getSetValue()";
      break;
  }
}

std::set<Term> Term::getSetValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(d_node->getType().isSet() && d_node->isConst(),
                              *d_node)
      << "Term to be a set value when calling getSetValue()";
  //////// all checks before this line
  std::set<Term> res;
  Term::collectSet(res, *d_node, d_solver);
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isSequenceValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::CONST_SEQUENCE;
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::vector<Term> Term::getSequenceValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(
      d_node->getKind() == internal::Kind::CONST_SEQUENCE, *d_node)
      << "Term to be a sequence value when calling getSequenceValue()";
  //////// all checks before this line
  std::vector<Term> res;
  const internal::Sequence& seq = d_node->getConst<internal::Sequence>();
  for (const auto& node: seq.getVec())
  {
    res.emplace_back(Term(d_solver, node));
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isCardinalityConstraint() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::CARDINALITY_CONSTRAINT;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::pair<Sort, uint32_t> Term::getCardinalityConstraint() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(
      d_node->getKind() == internal::Kind::CARDINALITY_CONSTRAINT, *d_node)
      << "Term to be a cardinality constraint when calling "
         "getCardinalityConstraint()";
  // this should never happen since we restrict what the user can create
  CVC5_API_ARG_CHECK_EXPECTED(
      detail::checkIntegerBounds<std::uint32_t>(
          d_node->getOperator()
              .getConst<internal::CardinalityConstraint>()
              .getUpperBound()),
      *d_node)
      << "Upper bound for cardinality constraint does not fit uint32_t";
  //////// all checks before this line
  const internal::CardinalityConstraint& cc =
      d_node->getOperator().getConst<internal::CardinalityConstraint>();
  return std::make_pair(Sort(d_solver, cc.getType()),
                        cc.getUpperBound().getUnsignedInt());
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::ostream& operator<<(std::ostream& out, const Term& t)
{
  out << t.toString();
  return out;
}

std::ostream& operator<<(std::ostream& out, const std::vector<Term>& vector)
{
  internal::container_to_stream(out, vector);
  return out;
}

std::ostream& operator<<(std::ostream& out, const std::set<Term>& set)
{
  internal::container_to_stream(out, set);
  return out;
}

std::ostream& operator<<(std::ostream& out,
                         const std::unordered_set<Term>& unordered_set)
{
  internal::container_to_stream(out, unordered_set);
  return out;
}

template <typename V>
std::ostream& operator<<(std::ostream& out, const std::map<Term, V>& map)
{
  internal::container_to_stream(out, map);
  return out;
}

template <typename V>
std::ostream& operator<<(std::ostream& out,
                         const std::unordered_map<Term, V>& unordered_map)
{
  internal::container_to_stream(out, unordered_map);
  return out;
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
      case internal::Kind::STRING_CONCAT: return SEQ_CONCAT;
      case internal::Kind::STRING_LENGTH: return SEQ_LENGTH;
      case internal::Kind::STRING_SUBSTR: return SEQ_EXTRACT;
      case internal::Kind::STRING_UPDATE: return SEQ_UPDATE;
      case internal::Kind::STRING_CHARAT: return SEQ_AT;
      case internal::Kind::STRING_CONTAINS: return SEQ_CONTAINS;
      case internal::Kind::STRING_INDEXOF: return SEQ_INDEXOF;
      case internal::Kind::STRING_REPLACE: return SEQ_REPLACE;
      case internal::Kind::STRING_REPLACE_ALL: return SEQ_REPLACE_ALL;
      case internal::Kind::STRING_REV: return SEQ_REV;
      case internal::Kind::STRING_PREFIX: return SEQ_PREFIX;
      case internal::Kind::STRING_SUFFIX: return SEQ_SUFFIX;
      default:
        // fall through to conversion below
        break;
    }
  }
  // Notice that kinds like APPLY_TYPE_ASCRIPTION will be converted to
  // INTERNAL_KIND.
  return intToExtKind(d_node->getKind());
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
    : d_solver(slv), d_ctor(new internal::DTypeConstructor(name))
{
}
DatatypeConstructorDecl::~DatatypeConstructorDecl()
{
  if (d_ctor != nullptr)
  {
    d_ctor.reset();
  }
}

void DatatypeConstructorDecl::addSelector(const std::string& name,
                                          const Sort& sort)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK_SORT(sort);
  CVC5_API_ARG_CHECK_EXPECTED(!sort.isNull(), sort)
      << "non-null codomain sort for selector";
  //////// all checks before this line
  d_ctor->addArg(name, *sort.d_type);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void DatatypeConstructorDecl::addSelectorSelf(const std::string& name)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  d_ctor->addArgSelf(name);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void DatatypeConstructorDecl::addSelectorUnresolved(
    const std::string& name, const std::string& unresDataypeName)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  // make the unresolved sort with the given name
  internal::TypeNode usort =
      d_solver->getNodeManager()->mkUnresolvedDatatypeSort(unresDataypeName);
  d_ctor->addArg(name, usort);
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool DatatypeConstructorDecl::isNull() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string DatatypeConstructorDecl::toString() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  std::stringstream ss;
  ss << *d_ctor;
  return ss.str();
  ////////
  CVC5_API_TRY_CATCH_END;
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
  internal::container_to_stream(out, vector);
  return out;
}

bool DatatypeConstructorDecl::isNullHelper() const { return d_ctor == nullptr; }

bool DatatypeConstructorDecl::isResolved() const
{
  return d_ctor == nullptr || d_ctor->isResolved();
}

/* DatatypeDecl ------------------------------------------------------------- */

DatatypeDecl::DatatypeDecl() : d_solver(nullptr), d_dtype(nullptr) {}

DatatypeDecl::DatatypeDecl(const Solver* slv,
                           const std::string& name,
                           bool isCoDatatype)
    : d_solver(slv), d_dtype(new internal::DType(name, isCoDatatype))
{
}

DatatypeDecl::DatatypeDecl(const Solver* slv,
                           const std::string& name,
                           const std::vector<Sort>& params,
                           bool isCoDatatype)
    : d_solver(slv)
{
  std::vector<internal::TypeNode> tparams = Sort::sortVectorToTypeNodes(params);
  d_dtype = std::shared_ptr<internal::DType>(
      new internal::DType(name, tparams, isCoDatatype));
}

bool DatatypeDecl::isNullHelper() const { return !d_dtype; }

DatatypeDecl::~DatatypeDecl()
{
  if (d_dtype != nullptr)
  {
    d_dtype.reset();
  }
}

void DatatypeDecl::addConstructor(const DatatypeConstructorDecl& ctor)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_NOT_NULL(ctor);
  CVC5_API_ARG_CHECK_SOLVER("datatype constructor declaration", ctor);
  //////// all checks before this line
  d_dtype->addConstructor(ctor.d_ctor);
  ////////
  CVC5_API_TRY_CATCH_END;
}

size_t DatatypeDecl::getNumConstructors() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->getNumConstructors();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool DatatypeDecl::isParametric() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isParametric();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string DatatypeDecl::toString() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  std::stringstream ss;
  ss << *d_dtype;
  return ss.str();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string DatatypeDecl::getName() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->getName();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool DatatypeDecl::isNull() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::ostream& operator<<(std::ostream& out, const DatatypeDecl& dtdecl)
{
  out << dtdecl.toString();
  return out;
}

internal::DType& DatatypeDecl::getDatatype(void) const { return *d_dtype; }

/* DatatypeSelector --------------------------------------------------------- */

DatatypeSelector::DatatypeSelector() : d_solver(nullptr), d_stor(nullptr) {}

DatatypeSelector::DatatypeSelector(const Solver* slv,
                                   const internal::DTypeSelector& stor)
    : d_solver(slv), d_stor(new internal::DTypeSelector(stor))
{
  CVC5_API_CHECK(d_stor->isResolved()) << "Expected resolved datatype selector";
}

DatatypeSelector::~DatatypeSelector()
{
  if (d_stor != nullptr)
  {
    d_stor.reset();
  }
}

std::string DatatypeSelector::getName() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_stor->getName();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term DatatypeSelector::getTerm() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Term(d_solver, d_stor->getSelector());
  ////////
  CVC5_API_TRY_CATCH_END;
}
Term DatatypeSelector::getUpdaterTerm() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Term(d_solver, d_stor->getUpdater());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort DatatypeSelector::getCodomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Sort(d_solver, d_stor->getRangeType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool DatatypeSelector::isNull() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string DatatypeSelector::toString() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  std::stringstream ss;
  ss << *d_stor;
  return ss.str();
  ////////
  CVC5_API_TRY_CATCH_END;
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
                                         const internal::DTypeConstructor& ctor)
    : d_solver(slv), d_ctor(new internal::DTypeConstructor(ctor))
{
  CVC5_API_CHECK(d_ctor->isResolved())
      << "Expected resolved datatype constructor";
}

DatatypeConstructor::~DatatypeConstructor()
{
  if (d_ctor != nullptr)
  {
    d_ctor.reset();
  }
}

std::string DatatypeConstructor::getName() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_ctor->getName();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term DatatypeConstructor::getTerm() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Term(d_solver, d_ctor->getConstructor());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term DatatypeConstructor::getInstantiatedTerm(const Sort& retSort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_ctor->isResolved())
      << "Expected resolved datatype constructor";
  CVC5_API_CHECK(retSort.isDatatype())
      << "Cannot get specialized constructor type for non-datatype type "
      << retSort;
  //////// all checks before this line
  internal::Node ret = d_ctor->getInstantiatedConstructor(*retSort.d_type);
  (void)ret.getType(true); /* kick off type checking */
  // apply type ascription to the operator
  Term sctor = Term(d_solver, ret);
  return sctor;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term DatatypeConstructor::getTesterTerm() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Term(d_solver, d_ctor->getTester());
  ////////
  CVC5_API_TRY_CATCH_END;
}

size_t DatatypeConstructor::getNumSelectors() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_ctor->getNumArgs();
  ////////
  CVC5_API_TRY_CATCH_END;
}

DatatypeSelector DatatypeConstructor::operator[](size_t index) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return DatatypeSelector(d_solver, (*d_ctor)[index]);
  ////////
  CVC5_API_TRY_CATCH_END;
}

DatatypeSelector DatatypeConstructor::operator[](const std::string& name) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getSelectorForName(name);
  ////////
  CVC5_API_TRY_CATCH_END;
}

DatatypeSelector DatatypeConstructor::getSelector(const std::string& name) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getSelectorForName(name);
  ////////
  CVC5_API_TRY_CATCH_END;
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
    const Solver* slv, const internal::DTypeConstructor& ctor, bool begin)
{
  d_solver = slv;
  d_int_stors = &ctor.getArgs();

  const std::vector<std::shared_ptr<internal::DTypeSelector>>& sels =
      ctor.getArgs();
  for (const std::shared_ptr<internal::DTypeSelector>& s : sels)
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
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string DatatypeConstructor::toString() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  std::stringstream ss;
  ss << *d_ctor;
  return ss.str();
  ////////
  CVC5_API_TRY_CATCH_END;
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
    CVC5_API_CHECK(foundSel) << "No selector " << name << " for constructor "
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

Datatype::Datatype(const Solver* slv, const internal::DType& dtype)
    : d_solver(slv), d_dtype(new internal::DType(dtype))
{
  CVC5_API_CHECK(d_dtype->isResolved()) << "Expected resolved datatype";
}

Datatype::Datatype() : d_solver(nullptr), d_dtype(nullptr) {}

Datatype::~Datatype()
{
  if (d_dtype != nullptr)
  {
    d_dtype.reset();
  }
}

DatatypeConstructor Datatype::operator[](size_t idx) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(idx < getNumConstructors()) << "Index out of bounds.";
  //////// all checks before this line
  return DatatypeConstructor(d_solver, (*d_dtype)[idx]);
  ////////
  CVC5_API_TRY_CATCH_END;
}

DatatypeConstructor Datatype::operator[](const std::string& name) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getConstructorForName(name);
  ////////
  CVC5_API_TRY_CATCH_END;
}

DatatypeConstructor Datatype::getConstructor(const std::string& name) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getConstructorForName(name);
  ////////
  CVC5_API_TRY_CATCH_END;
}

DatatypeSelector Datatype::getSelector(const std::string& name) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return getSelectorForName(name);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Datatype::getName() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->getName();
  ////////
  CVC5_API_TRY_CATCH_END;
}

size_t Datatype::getNumConstructors() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->getNumConstructors();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Sort> Datatype::getParameters() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isParametric()) << "Expected parametric datatype";
  //////// all checks before this line
  std::vector<internal::TypeNode> params = d_dtype->getParameters();
  return Sort::typeNodeVectorToSorts(d_solver, params);
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Datatype::isParametric() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isParametric();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Datatype::isCodatatype() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isCodatatype();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Datatype::isTuple() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isTuple();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Datatype::isRecord() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isRecord();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Datatype::isFinite() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(!d_dtype->isParametric())
      << "Invalid call to 'isFinite()', expected non-parametric Datatype";
  //////// all checks before this line
  // we assume that finite model finding is disabled by passing false as the
  // second argument
  return isCardinalityClassFinite(d_dtype->getCardinalityClass(), false);
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Datatype::isWellFounded() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->isWellFounded();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Datatype::isNull() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return isNullHelper();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Datatype::toString() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype->getName();
  ////////
  CVC5_API_TRY_CATCH_END;
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
    CVC5_API_CHECK(foundCons) << "No constructor " << name << " for datatype "
                              << getName() << " exists, among " << snames.str();
  }
  return DatatypeConstructor(d_solver, (*d_dtype)[index]);
}

DatatypeSelector Datatype::getSelectorForName(const std::string& name) const
{
  bool foundSel = false;
  size_t index = 0;
  size_t sindex = 0;
  for (size_t i = 0, ncons = getNumConstructors(); i < ncons; i++)
  {
    int si = (*d_dtype)[i].getSelectorIndexForName(name);
    if (si >= 0)
    {
      sindex = static_cast<size_t>(si);
      index = i;
      foundSel = true;
      break;
    }
  }
  if (!foundSel)
  {
    CVC5_API_CHECK(foundSel)
        << "No select " << name << " for datatype " << getName() << " exists";
  }
  return DatatypeSelector(d_solver, (*d_dtype)[index][sindex]);
}

Datatype::const_iterator::const_iterator(const Solver* slv,
                                         const internal::DType& dtype,
                                         bool begin)
    : d_solver(slv), d_int_ctors(&dtype.getConstructors())
{
  const std::vector<std::shared_ptr<internal::DTypeConstructor>>& cons =
      dtype.getConstructors();
  for (const std::shared_ptr<internal::DTypeConstructor>& c : cons)
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

std::ostream& operator<<(std::ostream& out, const Datatype& dtype)
{
  return out << dtype.toString();
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

void Grammar::addRule(const Term& ntSymbol, const Term& rule)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_isResolved) << "Grammar cannot be modified after passing "
                                   "it as an argument to synthFun/synthInv";
  CVC5_API_CHECK_TERM(ntSymbol);
  CVC5_API_CHECK_TERM(rule);
  CVC5_API_ARG_CHECK_EXPECTED(
      d_ntsToTerms.find(ntSymbol) != d_ntsToTerms.cend(), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  CVC5_API_CHECK(ntSymbol.d_node->getType() == rule.d_node->getType())
      << "Expected ntSymbol and rule to have the same sort";
  CVC5_API_ARG_CHECK_EXPECTED(!containsFreeVariables(rule), rule)
      << "a term whose free variables are limited to synthFun/synthInv "
         "parameters and non-terminal symbols of the grammar";
  //////// all checks before this line
  d_ntsToTerms[ntSymbol].push_back(rule);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Grammar::addRules(const Term& ntSymbol, const std::vector<Term>& rules)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_isResolved) << "Grammar cannot be modified after passing "
                                   "it as an argument to synthFun/synthInv";
  CVC5_API_CHECK_TERM(ntSymbol);
  CVC5_API_CHECK_TERMS_WITH_SORT(rules, ntSymbol.getSort());
  CVC5_API_ARG_CHECK_EXPECTED(
      d_ntsToTerms.find(ntSymbol) != d_ntsToTerms.cend(), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  for (size_t i = 0, n = rules.size(); i < n; ++i)
  {
    CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(
        !containsFreeVariables(rules[i]), rules[i], rules, i)
        << "a term whose free variables are limited to synthFun/synthInv "
           "parameters and non-terminal symbols of the grammar";
  }
  //////// all checks before this line
  d_ntsToTerms[ntSymbol].insert(
      d_ntsToTerms[ntSymbol].cend(), rules.cbegin(), rules.cend());
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Grammar::addAnyConstant(const Term& ntSymbol)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_isResolved) << "Grammar cannot be modified after passing "
                                   "it as an argument to synthFun/synthInv";
  CVC5_API_CHECK_TERM(ntSymbol);
  CVC5_API_ARG_CHECK_EXPECTED(
      d_ntsToTerms.find(ntSymbol) != d_ntsToTerms.cend(), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  //////// all checks before this line
  d_allowConst.insert(ntSymbol);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Grammar::addAnyVariable(const Term& ntSymbol)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_isResolved) << "Grammar cannot be modified after passing "
                                   "it as an argument to synthFun/synthInv";
  CVC5_API_CHECK_TERM(ntSymbol);
  CVC5_API_ARG_CHECK_EXPECTED(
      d_ntsToTerms.find(ntSymbol) != d_ntsToTerms.cend(), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  //////// all checks before this line
  d_allowVars.insert(ntSymbol);
  ////////
  CVC5_API_TRY_CATCH_END;
}

/**
 * This function concatenates the outputs of calling f on each element between
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
  CVC5_API_TRY_CATCH_BEGIN;
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
  CVC5_API_TRY_CATCH_END;
}

Sort Grammar::resolve()
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line

  d_isResolved = true;

  Term bvl;

  if (!d_sygusVars.empty())
  {
    bvl = Term(d_solver,
               d_solver->getNodeManager()->mkNode(
                   internal::kind::BOUND_VAR_LIST,
                   Term::termVectorToNodes(d_sygusVars)));
  }

  std::unordered_map<Term, Sort> ntsToUnres(d_ntSyms.size());

  for (Term ntsymbol : d_ntSyms)
  {
    // make the unresolved type, used for referencing the final version of
    // the ntsymbol's datatype
    ntsToUnres[ntsymbol] =
        Sort(d_solver,
             d_solver->getNodeManager()->mkUnresolvedDatatypeSort(
                 ntsymbol.toString()));
  }

  std::vector<internal::DType> datatypes;

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
    internal::TypeNode btt = ntSym.d_node->getType();
    dtDecl.d_dtype->setSygus(btt, *bvl.d_node, aci, false);

    // We can be in a case where the only rule specified was (Variable T)
    // and there are no variables of type T, in which case this is a bogus
    // grammar. This results in the error below.
    CVC5_API_CHECK(dtDecl.d_dtype->getNumConstructors() != 0)
        << "Grouped rule listing for " << *dtDecl.d_dtype
        << " produced an empty rule list";

    datatypes.push_back(*dtDecl.d_dtype);
  }

  std::vector<internal::TypeNode> datatypeTypes =
      d_solver->getNodeManager()->mkMutualDatatypeTypes(datatypes);

  // return is the first datatype
  return Sort(d_solver, datatypeTypes[0]);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Grammar::addSygusConstructorTerm(
    DatatypeDecl& dt,
    const Term& term,
    const std::unordered_map<Term, Sort>& ntsToUnres) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_DTDECL(dt);
  CVC5_API_CHECK_TERM(term);
  CVC5_API_CHECK_TERMS_MAP(ntsToUnres);
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
             d_solver->getNodeManager()->mkNode(internal::kind::BOUND_VAR_LIST,
                                                Term::termVectorToNodes(args)));
    // its operator is a lambda
    op = Term(d_solver,
              d_solver->getNodeManager()->mkNode(
                  internal::kind::LAMBDA, *lbvl.d_node, *op.d_node));
  }
  std::vector<internal::TypeNode> cargst = Sort::sortVectorToTypeNodes(cargs);
  dt.d_dtype->addSygusConstructor(*op.d_node, ssCName.str(), cargst);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Grammar::purifySygusGTerm(
    const Term& term,
    std::vector<Term>& args,
    std::vector<Sort>& cargs,
    const std::unordered_map<Term, Sort>& ntsToUnres) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_TERM(term);
  CVC5_API_CHECK_TERMS(args);
  CVC5_API_CHECK_SORTS(cargs);
  CVC5_API_CHECK_TERMS_MAP(ntsToUnres);
  //////// all checks before this line

  std::unordered_map<Term, Sort>::const_iterator itn = ntsToUnres.find(term);
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

  internal::Node nret;

  if (term.d_node->getMetaKind() == internal::kind::metakind::PARAMETERIZED)
  {
    // it's an indexed operator so we should provide the op
    internal::NodeBuilder nb(term.d_node->getKind());
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
  CVC5_API_TRY_CATCH_END;
}

void Grammar::addSygusConstructorVariables(DatatypeDecl& dt,
                                           const Sort& sort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_DTDECL(dt);
  CVC5_API_CHECK_SORT(sort);
  //////// all checks before this line

  // each variable of appropriate type becomes a sygus constructor in dt.
  for (unsigned i = 0, size = d_sygusVars.size(); i < size; i++)
  {
    Term v = d_sygusVars[i];
    if (v.d_node->getType() == *sort.d_type)
    {
      std::stringstream ss;
      ss << v;
      std::vector<internal::TypeNode> cargs;
      dt.d_dtype->addSygusConstructor(*v.d_node, ss.str(), cargs);
    }
  }
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Grammar::containsFreeVariables(const Term& rule) const
{
  // we allow the argument list and non-terminal symbols to be in scope
  std::unordered_set<internal::TNode> scope;

  for (const Term& sygusVar : d_sygusVars)
  {
    scope.emplace(*sygusVar.d_node);
  }

  for (const Term& ntsymbol : d_ntSyms)
  {
    scope.emplace(*ntsymbol.d_node);
  }

  return internal::expr::hasFreeVariablesScope(*rule.d_node, scope);
}

std::ostream& operator<<(std::ostream& out, const Grammar& grammar)
{
  return out << grammar.toString();
}

/* -------------------------------------------------------------------------- */
/* Options                                                                    */
/* -------------------------------------------------------------------------- */

DriverOptions::DriverOptions(const Solver& solver) : d_solver(solver) {}

std::istream& DriverOptions::in() const
{
  return *d_solver.d_slv->getOptions().base.in;
}
std::ostream& DriverOptions::err() const
{
  return *d_solver.d_slv->getOptions().base.err;
}
std::ostream& DriverOptions::out() const
{
  return *d_solver.d_slv->getOptions().base.out;
}

/* -------------------------------------------------------------------------- */
/* Statistics                                                                 */
/* -------------------------------------------------------------------------- */

struct Stat::StatData
{
  internal::StatExportData data;
  template <typename T>
  StatData(T&& t) : data(std::forward<T>(t))
  {
  }
  StatData() : data() {}
};

Stat::Stat() {}
Stat::~Stat() {}
Stat::Stat(const Stat& s)
    : d_internal(s.d_internal),
      d_default(s.d_default)
{
  if (s.d_data)
  {
    d_data = std::make_unique<StatData>(s.d_data->data);
  }
}
Stat& Stat::operator=(const Stat& s)
{
  d_internal = s.d_internal;
  d_default = s.d_default;
  if (s.d_data)
  {
    d_data = std::make_unique<StatData>(s.d_data->data);
  }
  return *this;
}

bool Stat::isInternal() const { return d_internal; }
bool Stat::isDefault() const { return d_default; }

bool Stat::isInt() const
{
  if (!d_data) return false;
  return std::holds_alternative<int64_t>(d_data->data);
}
int64_t Stat::getInt() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(static_cast<bool>(d_data)) << "Stat holds no value";
  CVC5_API_RECOVERABLE_CHECK(isInt()) << "Expected Stat of type int64_t.";
  return std::get<int64_t>(d_data->data);
  CVC5_API_TRY_CATCH_END;
}
bool Stat::isDouble() const
{
  if (!d_data) return false;
  return std::holds_alternative<double>(d_data->data);
}
double Stat::getDouble() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(static_cast<bool>(d_data)) << "Stat holds no value";
  CVC5_API_RECOVERABLE_CHECK(isDouble()) << "Expected Stat of type double.";
  return std::get<double>(d_data->data);
  CVC5_API_TRY_CATCH_END;
}
bool Stat::isString() const
{
  if (!d_data) return false;
  return std::holds_alternative<std::string>(d_data->data);
}
const std::string& Stat::getString() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(static_cast<bool>(d_data)) << "Stat holds no value";
  CVC5_API_RECOVERABLE_CHECK(isString())
      << "Expected Stat of type std::string.";
  return std::get<std::string>(d_data->data);
  CVC5_API_TRY_CATCH_END;
}
bool Stat::isHistogram() const
{
  if (!d_data) return false;
  return std::holds_alternative<HistogramData>(d_data->data);
}
const Stat::HistogramData& Stat::getHistogram() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(static_cast<bool>(d_data)) << "Stat holds no value";
  CVC5_API_RECOVERABLE_CHECK(isHistogram())
      << "Expected Stat of type histogram.";
  return std::get<HistogramData>(d_data->data);
  CVC5_API_TRY_CATCH_END;
}

Stat::Stat(bool internal, bool defaulted, StatData&& sd)
    : d_internal(internal),
      d_default(defaulted),
      d_data(std::make_unique<StatData>(std::move(sd)))
{
}

std::ostream& operator<<(std::ostream& os, const Stat& sv)
{
  return internal::detail::print(os, sv.d_data->data);
}

Statistics::BaseType::const_reference Statistics::iterator::operator*() const
{
  return d_it.operator*();
}
Statistics::BaseType::const_pointer Statistics::iterator::operator->() const
{
  return d_it.operator->();
}
Statistics::iterator& Statistics::iterator::operator++()
{
  do
  {
    ++d_it;
  } while (!isVisible());
  return *this;
}
Statistics::iterator Statistics::iterator::operator++(int)
{
  iterator tmp = *this;
  do
  {
    ++d_it;
  } while (!isVisible());
  return tmp;
}
Statistics::iterator& Statistics::iterator::operator--()
{
  do
  {
    --d_it;
  } while (!isVisible());
  return *this;
}
Statistics::iterator Statistics::iterator::operator--(int)
{
  iterator tmp = *this;
  do
  {
    --d_it;
  } while (!isVisible());
  return tmp;
}
bool Statistics::iterator::operator==(const Statistics::iterator& rhs) const
{
  return d_it == rhs.d_it;
}
bool Statistics::iterator::operator!=(const Statistics::iterator& rhs) const
{
  return d_it != rhs.d_it;
}
Statistics::iterator::iterator(Statistics::BaseType::const_iterator it,
                               const Statistics::BaseType& base,
                               bool internal,
                               bool defaulted)
    : d_it(it), d_base(&base), d_showInternal(internal), d_showDefault(defaulted)
{
  while (!isVisible())
  {
    ++d_it;
  }
}
bool Statistics::iterator::isVisible() const
{
  if (d_it == d_base->end()) return true;
  if (!d_showInternal && d_it->second.isInternal()) return false;
  if (!d_showDefault && d_it->second.isDefault()) return false;
  return true;
}

const Stat& Statistics::get(const std::string& name)
{
  CVC5_API_TRY_CATCH_BEGIN;
  auto it = d_stats.find(name);
  CVC5_API_RECOVERABLE_CHECK(it != d_stats.end())
      << "No stat with name \"" << name << "\" exists.";
  return it->second;
  CVC5_API_TRY_CATCH_END;
}

Statistics::iterator Statistics::begin(bool internal, bool defaulted) const
{
  return iterator(d_stats.begin(), d_stats, internal, defaulted);
}
Statistics::iterator Statistics::end() const
{
  return iterator(d_stats.end(), d_stats, false, false);
}

Statistics::Statistics(const internal::StatisticsRegistry& reg)
{
  for (const auto& svp : reg)
  {
    d_stats.emplace(svp.first,
                    Stat(svp.second->d_internal,
                         svp.second->isDefault(),
                         svp.second->getViewer()));
  }
}

std::ostream& operator<<(std::ostream& out, const Statistics& stats)
{
  for (const auto& stat : stats)
  {
    out << stat.first << " = " << stat.second << std::endl;
  }
  return out;
}

/* -------------------------------------------------------------------------- */
/* Solver                                                                     */
/* -------------------------------------------------------------------------- */

Solver::Solver(std::unique_ptr<internal::Options>&& original)
{
  d_nodeMgr = internal::NodeManager::currentNM();
  d_nodeMgr->init();
  d_originalOptions = std::move(original);
  d_slv.reset(new internal::SolverEngine(d_nodeMgr, d_originalOptions.get()));
  d_slv->setSolver(this);
  d_rng.reset(new internal::Random(d_slv->getOptions().driver.seed));
  resetStatistics();
}

Solver::Solver() : Solver(std::make_unique<internal::Options>()) {}

Solver::~Solver() {}

/* Helpers and private functions                                              */
/* -------------------------------------------------------------------------- */

internal::NodeManager* Solver::getNodeManager(void) const { return d_nodeMgr; }

void Solver::increment_term_stats(Kind kind) const
{
  if constexpr (internal::configuration::isStatisticsBuild())
  {
    d_stats->d_terms << kind;
  }
}

void Solver::increment_vars_consts_stats(const Sort& sort, bool is_var) const
{
  if constexpr (internal::configuration::isStatisticsBuild())
  {
    const internal::TypeNode tn = sort.getTypeNode();
    internal::TypeConstant tc = tn.getKind() == internal::kind::TYPE_CONSTANT
                                    ? tn.getConst<internal::TypeConstant>()
                                    : internal::LAST_TYPE;
    if (is_var)
    {
      d_stats->d_vars << tc;
    }
    else
    {
      d_stats->d_consts << tc;
    }
  }
}

/* Split out to avoid nested API calls (problematic with API tracing).        */
/* .......................................................................... */

template <typename T>
Op Solver::mkOpHelper(Kind kind, const T& t) const
{
  //////// all checks before this line
  internal::Node res = getNodeManager()->mkConst(t);
  static_cast<void>(res.getType(true)); /* kick off type checking */
  return Op(this, kind, res);
}

template <typename T>
Term Solver::mkValHelper(const T& t) const
{
  //////// all checks before this line
  internal::Node res = getNodeManager()->mkConst(t);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
}

Term Solver::mkRationalValHelper(const internal::Rational& r, bool isInt) const
{
  //////// all checks before this line
  internal::NodeManager* nm = getNodeManager();
  internal::Node res = isInt ? nm->mkConstInt(r) : nm->mkConstReal(r);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
}

Term Solver::mkRealOrIntegerFromStrHelper(const std::string& s,
                                          bool isInt) const
{
  //////// all checks before this line
  try
  {
    internal::Rational r = s.find('/') != std::string::npos
                               ? internal::Rational(s)
                               : internal::Rational::fromDecimal(s);
    return mkRationalValHelper(r, isInt);
  }
  catch (const std::invalid_argument& e)
  {
    /* Catch to throw with a more meaningful error message. To be caught in
     * enclosing CVC5_API_TRY_CATCH_* block to throw CVC5ApiException. */
    std::stringstream message;
    message << "Cannot construct Real or Int from string argument '" << s << "'"
            << std::endl;
    throw std::invalid_argument(message.str());
  }
}

Term Solver::mkBVFromIntHelper(uint32_t size, uint64_t val) const
{
  CVC5_API_ARG_CHECK_EXPECTED(size > 0, size) << "a bit-width > 0";
  //////// all checks before this line
  return mkValHelper(internal::BitVector(size, val));
}

Term Solver::mkBVFromStrHelper(uint32_t size,
                               const std::string& s,
                               uint32_t base) const
{
  CVC5_API_ARG_CHECK_EXPECTED(size > 0, size) << "a bit-width > 0";
  CVC5_API_ARG_CHECK_EXPECTED(!s.empty(), s) << "a non-empty string";
  CVC5_API_ARG_CHECK_EXPECTED(base == 2 || base == 10 || base == 16, base)
      << "base 2, 10, or 16";
  //////// all checks before this line

  internal::Integer val(s, base);

  if (val.strictlyNegative())
  {
    CVC5_API_CHECK(val >= -internal::Integer(2).pow(size - 1))
        << "Overflow in bitvector construction (specified bitvector size "
        << size << " too small to hold value " << s << ")";
  }
  else
  {
    CVC5_API_CHECK(val.modByPow2(size) == val)
        << "Overflow in bitvector construction (specified bitvector size "
        << size << " too small to hold value " << s << ")";
  }
  return mkValHelper(internal::BitVector(size, val));
}

Term Solver::getValueHelper(const Term& term) const
{
  // Note: Term is checked in the caller to avoid double checks
  bool wasShadow = false;
  bool freeOrShadowedVar =
      internal::expr::hasFreeOrShadowedVar(term.getNode(), wasShadow);
  CVC5_API_RECOVERABLE_CHECK(!freeOrShadowedVar)
      << "Cannot get value of term containing "
      << (wasShadow ? "shadowed" : "free") << " variables";
  //////// all checks before this line
  internal::Node value = d_slv->getValue(*term.d_node);
  Term res = Term(this, value);
  Assert(res.getSort() == term.getSort());
  return res;
}

Sort Solver::mkTupleSortHelper(const std::vector<Sort>& sorts) const
{
  // Note: Sorts are checked in the caller to avoid double checks
  //////// all checks before this line
  std::vector<internal::TypeNode> typeNodes =
      Sort::sortVectorToTypeNodes(sorts);
  return Sort(this, getNodeManager()->mkTupleType(typeNodes));
}

Term Solver::mkTermFromKind(Kind kind) const
{
  CVC5_API_KIND_CHECK_EXPECTED(kind == PI || kind == REGEXP_NONE
                                   || kind == REGEXP_ALL
                                   || kind == REGEXP_ALLCHAR || kind == SEP_EMP,
                               kind)
      << "PI, REGEXP_NONE, REGEXP_ALL, REGEXP_ALLCHAR or SEP_EMP";
  //////// all checks before this line
  internal::Node res;
  internal::Kind k = extToIntKind(kind);
  if (kind == REGEXP_NONE || kind == REGEXP_ALL || kind == REGEXP_ALLCHAR)
  {
    Assert(isDefinedIntKind(k));
    res = d_nodeMgr->mkNode(k, std::vector<internal::Node>());
  }
  else if (kind == SEP_EMP)
  {
    res = d_nodeMgr->mkNullaryOperator(d_nodeMgr->booleanType(), k);
  }
  else
  {
    Assert(kind == PI);
    res = d_nodeMgr->mkNullaryOperator(d_nodeMgr->realType(), k);
  }
  (void)res.getType(true); /* kick off type checking */
  increment_term_stats(kind);
  return Term(this, res);
}

Term Solver::mkTermHelper(Kind kind, const std::vector<Term>& children) const
{
  // Note: Kind and children are checked in the caller to avoid double checks
  //////// all checks before this line
  if (children.size() == 0)
  {
    return mkTermFromKind(kind);
  }
  std::vector<internal::Node> echildren = Term::termVectorToNodes(children);
  internal::Kind k = extToIntKind(kind);
  internal::Node res;
  if (echildren.size() > 2)
  {
    if (kind == INTS_DIVISION || kind == XOR || kind == SUB || kind == DIVISION
        || kind == HO_APPLY || kind == REGEXP_DIFF || kind == SET_UNION
        || kind == SET_INTER || kind == SET_MINUS || kind == BAG_INTER_MIN
        || kind == BAG_UNION_MAX || kind == BAG_UNION_DISJOINT
        || kind == BAG_DIFFERENCE_REMOVE || kind == BAG_DIFFERENCE_SUBTRACT)
    {
      // left-associative, but cvc5 internally only supports 2 args
      res = d_nodeMgr->mkLeftAssociative(k, echildren);
    }
    else if (kind == IMPLIES)
    {
      // right-associative, but cvc5 internally only supports 2 args
      res = d_nodeMgr->mkRightAssociative(k, echildren);
    }
    else if (kind == EQUAL || kind == LT || kind == GT || kind == LEQ
             || kind == GEQ)
    {
      // "chainable", but cvc5 internally only supports 2 args
      res = d_nodeMgr->mkChain(k, echildren);
    }
    else if (internal::kind::isAssociative(k))
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
  else if (internal::kind::isAssociative(k))
  {
    // associative case, same as above
    checkMkTerm(kind, children.size());
    res = d_nodeMgr->mkAssociative(k, echildren);
  }
  else
  {
    // default case, same as above
    checkMkTerm(kind, children.size());
    // make the term
    res = d_nodeMgr->mkNode(k, echildren);
  }

  (void)res.getType(true); /* kick off type checking */
  increment_term_stats(kind);
  return Term(this, res);
}

Term Solver::mkTermHelper(const Op& op, const std::vector<Term>& children) const
{
  if (!op.isIndexedHelper())
  {
    return mkTermHelper(op.d_kind, children);
  }

  // Note: Op and children are checked in the caller to avoid double checks
  checkMkTerm(op.d_kind, children.size());
  //////// all checks before this line

  const internal::Kind int_kind = extToIntKind(op.d_kind);
  std::vector<internal::Node> echildren = Term::termVectorToNodes(children);

  internal::NodeBuilder nb(int_kind);
  nb << *op.d_node;
  nb.append(echildren);
  internal::Node res = nb.constructNode();

  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
}

Term Solver::synthFunHelper(const std::string& symbol,
                            const std::vector<Term>& boundVars,
                            const Sort& sort,
                            bool isInv,
                            Grammar* grammar) const
{
  // Note: boundVars, sort and grammar are checked in the caller to avoid
  //       double checks.
  std::vector<internal::TypeNode> varTypes;
  for (const auto& bv : boundVars)
  {
    if (grammar)
    {
      CVC5_API_CHECK(grammar->d_ntSyms[0].d_node->getType() == *sort.d_type)
          << "Invalid Start symbol for grammar, Expected Start's sort to be "
          << *sort.d_type << " but found "
          << grammar->d_ntSyms[0].d_node->getType();
    }
    varTypes.push_back(bv.d_node->getType());
  }
  //////// all checks before this line

  internal::TypeNode funType =
      varTypes.empty()
          ? *sort.d_type
          : getNodeManager()->mkFunctionType(varTypes, *sort.d_type);

  internal::Node fun = getNodeManager()->mkBoundVar(symbol, funType);
  (void)fun.getType(true); /* kick off type checking */

  std::vector<internal::Node> bvns = Term::termVectorToNodes(boundVars);

  d_slv->declareSynthFun(
      fun,
      grammar == nullptr ? funType : *grammar->resolve().d_type,
      isInv,
      bvns);

  return Term(this, fun);
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

void Solver::ensureWellFormedTerm(const Term& t) const
{
  // only check if option is set
  if (d_slv->getOptions().expr.wellFormedChecking)
  {
    bool wasShadow = false;
    if (internal::expr::hasFreeOrShadowedVar(*t.d_node, wasShadow))
    {
      std::stringstream se;
      se << "Cannot process term with " << (wasShadow ? "shadowed" : "free")
         << " variable";
      throw CVC5ApiException(se.str().c_str());
    }
  }
}

void Solver::ensureWellFormedTerms(const std::vector<Term>& ts) const
{
  // only check if option is set
  if (d_slv->getOptions().expr.wellFormedChecking)
  {
    for (const Term& t : ts)
    {
      ensureWellFormedTerm(t);
    }
  }
}

void Solver::resetStatistics()
{
  if constexpr (internal::configuration::isStatisticsBuild())
  {
    d_stats.reset(new APIStatistics{
        d_slv->getStatisticsRegistry()
            .registerHistogram<internal::TypeConstant>("cvc5::CONSTANT"),
        d_slv->getStatisticsRegistry()
            .registerHistogram<internal::TypeConstant>("cvc5::VARIABLE"),
        d_slv->getStatisticsRegistry().registerHistogram<Kind>("cvc5::TERM"),
    });
  }
}

void Solver::printStatisticsSafe(int fd) const
{
  d_slv->printStatisticsSafe(fd);
}

/* Helpers for mkTerm checks.                                                 */
/* .......................................................................... */

void Solver::checkMkTerm(Kind kind, uint32_t nchildren) const
{
  CVC5_API_KIND_CHECK(kind);
  Assert(isDefinedIntKind(extToIntKind(kind)));
  const internal::kind::MetaKind mk =
      internal::kind::metaKindOf(extToIntKind(kind));
  CVC5_API_KIND_CHECK_EXPECTED(mk == internal::kind::metakind::PARAMETERIZED
                                   || mk == internal::kind::metakind::OPERATOR,
                               kind)
      << "Only operator-style terms are created with mkTerm(), "
         "to create variables, constants and values see mkVar(), mkConst() "
         "and the respective theory-specific functions to create values, "
         "e.g., mkBitVector().";
  CVC5_API_KIND_CHECK_EXPECTED(
      nchildren >= minArity(kind) && nchildren <= maxArity(kind), kind)
      << "Terms with kind " << kindToString(kind) << " must have at least "
      << minArity(kind) << " children and at most " << maxArity(kind)
      << " children (the one under construction has " << nchildren << ")";
}

/* Sorts Handling                                                             */
/* -------------------------------------------------------------------------- */

Sort Solver::getNullSort(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, internal::TypeNode());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::getBooleanSort(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->booleanType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::getIntegerSort(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->integerType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::getRealSort(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->realType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::getRegExpSort(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->regExpType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::getStringSort(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->stringType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::getRoundingModeSort(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->roundingModeType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Create sorts ------------------------------------------------------- */

Sort Solver::mkArraySort(const Sort& indexSort, const Sort& elemSort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(indexSort);
  CVC5_API_SOLVER_CHECK_SORT(elemSort);
  //////// all checks before this line
  return Sort(
      this, getNodeManager()->mkArrayType(*indexSort.d_type, *elemSort.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkBitVectorSort(uint32_t size) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(size > 0, size) << "size > 0";
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkBitVectorType(size));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkFloatingPointSort(uint32_t exp, uint32_t sig) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(exp > 0, exp) << "exponent size > 0";
  CVC5_API_ARG_CHECK_EXPECTED(sig > 0, sig) << "significand size > 0";
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkFloatingPointType(exp, sig));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkDatatypeSort(const DatatypeDecl& dtypedecl) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_DTDECL(dtypedecl);
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkDatatypeType(*dtypedecl.d_dtype));
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Sort> Solver::mkDatatypeSorts(
    const std::vector<DatatypeDecl>& dtypedecls) const
{
  CVC5_API_SOLVER_CHECK_DTDECLS(dtypedecls);
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  std::vector<internal::DType> datatypes;
  for (size_t i = 0, ndts = dtypedecls.size(); i < ndts; ++i)
  {
    datatypes.push_back(dtypedecls[i].getDatatype());
  }
  std::vector<internal::TypeNode> dtypes =
      getNodeManager()->mkMutualDatatypeTypes(datatypes);
  std::vector<Sort> retTypes = Sort::typeNodeVectorToSorts(this, dtypes);
  return retTypes;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkFunctionSort(const std::vector<Sort>& sorts,
                            const Sort& codomain) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_SIZE_CHECK_EXPECTED(sorts.size() >= 1, sorts)
      << "at least one parameter sort for function sort";
  CVC5_API_SOLVER_CHECK_DOMAIN_SORTS(sorts);
  CVC5_API_SOLVER_CHECK_CODOMAIN_SORT(codomain);
  //////// all checks before this line
  std::vector<internal::TypeNode> argTypes = Sort::sortVectorToTypeNodes(sorts);
  return Sort(this,
              getNodeManager()->mkFunctionType(argTypes, *codomain.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkParamSort(const std::optional<std::string>& symbol) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::TypeNode tn =
      symbol ? getNodeManager()->mkSort(*symbol) : getNodeManager()->mkSort();
  return Sort(this, tn);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkPredicateSort(const std::vector<Sort>& sorts) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_SIZE_CHECK_EXPECTED(sorts.size() >= 1, sorts)
      << "at least one parameter sort for predicate sort";
  CVC5_API_SOLVER_CHECK_DOMAIN_SORTS(sorts);
  //////// all checks before this line
  return Sort(
      this,
      getNodeManager()->mkPredicateType(Sort::sortVectorToTypeNodes(sorts)));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkRecordSort(
    const std::vector<std::pair<std::string, Sort>>& fields) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  std::vector<std::pair<std::string, internal::TypeNode>> f;
  for (size_t i = 0, size = fields.size(); i < size; ++i)
  {
    const auto& p = fields[i];
    CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(!p.second.isNull(), "sort", fields, i)
        << "non-null sort";
    CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == p.second.d_solver, "sort", fields, i)
        << "sort associated with this solver object";
    f.emplace_back(p.first, *p.second.d_type);
  }
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkRecordType(f));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkSetSort(const Sort& elemSort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(elemSort);
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkSetType(*elemSort.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkBagSort(const Sort& elemSort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(elemSort);
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkBagType(*elemSort.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkSequenceSort(const Sort& elemSort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(elemSort);
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkSequenceType(*elemSort.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkUninterpretedSort(const std::optional<std::string>& symbol) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::TypeNode tn =
      symbol ? getNodeManager()->mkSort(*symbol) : getNodeManager()->mkSort();
  return Sort(this, tn);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkUnresolvedDatatypeSort(const std::string& symbol,
                                      size_t arity) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, getNodeManager()->mkUnresolvedDatatypeSort(symbol, arity));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkUninterpretedSortConstructorSort(
    size_t arity, const std::optional<std::string>& symbol) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(arity > 0, arity) << "an arity > 0";
  //////// all checks before this line
  if (symbol)
  {
    return Sort(this, getNodeManager()->mkSortConstructor(*symbol, arity));
  }
  return Sort(this, getNodeManager()->mkSortConstructor("", arity));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::mkTupleSort(const std::vector<Sort>& sorts) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_DOMAIN_SORTS(sorts);
  //////// all checks before this line
  return mkTupleSortHelper(sorts);
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Create consts                                                              */
/* -------------------------------------------------------------------------- */

Term Solver::mkTrue(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Term(this, d_nodeMgr->mkConst<bool>(true));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkFalse(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Term(this, d_nodeMgr->mkConst<bool>(false));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkBoolean(bool val) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Term(this, d_nodeMgr->mkConst<bool>(val));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkPi() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::Node res =
      d_nodeMgr->mkNullaryOperator(d_nodeMgr->realType(), internal::kind::PI);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkInteger(const std::string& s) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(isValidInteger(s), s) << " an integer ";
  Term integer = mkRealOrIntegerFromStrHelper(s);
  CVC5_API_ARG_CHECK_EXPECTED(integer.getSort() == getIntegerSort(), s)
      << " a string representing an integer";
  //////// all checks before this line
  return integer;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkInteger(int64_t val) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  Term integer = mkRationalValHelper(internal::Rational(val));
  Assert(integer.getSort() == getIntegerSort());
  return integer;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkReal(const std::string& s) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  /* CLN and GMP handle this case differently, CLN interprets it as 0, GMP
   * throws an std::invalid_argument exception. For consistency, we treat it
   * as invalid. */
  CVC5_API_ARG_CHECK_EXPECTED(s != ".", s)
      << "a string representing a real or rational value.";
  //////// all checks before this line
  return mkRealOrIntegerFromStrHelper(s, false);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkReal(int64_t val) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkRationalValHelper(internal::Rational(val), false);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkReal(int64_t num, int64_t den) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkRationalValHelper(internal::Rational(num, den), false);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkRegexpAll() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::Node res = d_nodeMgr->mkNode(internal::kind::REGEXP_ALL,
                                         std::vector<internal::Node>());
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkRegexpNone() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::Node res = d_nodeMgr->mkNode(internal::kind::REGEXP_NONE,
                                         std::vector<internal::Node>());
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkRegexpAllchar() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::Node res = d_nodeMgr->mkNode(internal::kind::REGEXP_ALLCHAR,
                                         std::vector<internal::Node>());
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkEmptySet(const Sort& sort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(sort.isNull() || sort.isSet(), sort)
      << "null sort or set sort";
  CVC5_API_ARG_CHECK_EXPECTED(sort.isNull() || this == sort.d_solver, sort)
      << "set sort associated with this solver object";
  //////// all checks before this line
  return mkValHelper(internal::EmptySet(*sort.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkEmptyBag(const Sort& sort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(sort.isNull() || sort.isBag(), sort)
      << "null sort or bag sort";
  CVC5_API_ARG_CHECK_EXPECTED(sort.isNull() || this == sort.d_solver, sort)
      << "bag sort associated with this solver object";
  //////// all checks before this line
  return mkValHelper(internal::EmptyBag(*sort.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkSepEmp() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::Node res = getNodeManager()->mkNullaryOperator(
      d_nodeMgr->booleanType(), internal::Kind::SEP_EMP);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkSepNil(const Sort& sort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  internal::Node res = getNodeManager()->mkNullaryOperator(
      *sort.d_type, internal::kind::SEP_NIL);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkString(const std::string& s, bool useEscSequences) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper(internal::String(s, useEscSequences));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkString(const std::wstring& s) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper(internal::String(s));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkEmptySequence(const Sort& sort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  std::vector<internal::Node> seq;
  internal::Node res =
      d_nodeMgr->mkConst(internal::Sequence(*sort.d_type, seq));
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkUniverseSet(const Sort& sort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line

  internal::Node res = getNodeManager()->mkNullaryOperator(
      *sort.d_type, internal::kind::SET_UNIVERSE);
  // TODO(#2771): Reenable?
  // (void)res->getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkBitVector(uint32_t size, uint64_t val) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkBVFromIntHelper(size, val);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkBitVector(uint32_t size,
                         const std::string& s,
                         uint32_t base) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkBVFromStrHelper(size, s, base);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkConstArray(const Sort& sort, const Term& val) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(sort);
  CVC5_API_SOLVER_CHECK_TERM(val);
  CVC5_API_ARG_CHECK_EXPECTED(sort.isArray(), sort) << "an array sort";
  CVC5_API_CHECK(val.getSort() == sort.getArrayElementSort())
      << "Value does not match element sort";
  //////// all checks before this line
  internal::Node n = *val.d_node;
  Term res = mkValHelper(internal::ArrayStoreAll(*sort.d_type, n));
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkFloatingPointPosInf(uint32_t exp, uint32_t sig) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper(internal::FloatingPoint::makeInf(
      internal::FloatingPointSize(exp, sig), false));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkFloatingPointNegInf(uint32_t exp, uint32_t sig) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper(internal::FloatingPoint::makeInf(
      internal::FloatingPointSize(exp, sig), true));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkFloatingPointNaN(uint32_t exp, uint32_t sig) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper(
      internal::FloatingPoint::makeNaN(internal::FloatingPointSize(exp, sig)));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkFloatingPointPosZero(uint32_t exp, uint32_t sig) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper(internal::FloatingPoint::makeZero(
      internal::FloatingPointSize(exp, sig), false));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkFloatingPointNegZero(uint32_t exp, uint32_t sig) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper(internal::FloatingPoint::makeZero(
      internal::FloatingPointSize(exp, sig), true));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkRoundingMode(RoundingMode rm) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper(s_rmodes.at(rm));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkFloatingPoint(uint32_t exp, uint32_t sig, Term val) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(val);
  CVC5_API_ARG_CHECK_EXPECTED(exp > 0, exp) << "a value > 0";
  CVC5_API_ARG_CHECK_EXPECTED(sig > 0, sig) << "a value > 0";
  uint32_t bw = exp + sig;
  CVC5_API_ARG_CHECK_EXPECTED(bw == val.d_node->getType().getBitVectorSize(),
                              val)
      << "a bit-vector constant with bit-width '" << bw << "'";
  CVC5_API_ARG_CHECK_EXPECTED(
      val.d_node->getType().isBitVector() && val.d_node->isConst(), val)
      << "bit-vector constant";
  //////// all checks before this line
  return mkValHelper(internal::FloatingPoint(
      exp, sig, val.d_node->getConst<internal::BitVector>()));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkCardinalityConstraint(const Sort& sort, uint32_t upperBound) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(sort);
  CVC5_API_ARG_CHECK_EXPECTED(sort.isUninterpretedSort(), sort)
      << "an uninterpreted sort";
  CVC5_API_ARG_CHECK_EXPECTED(upperBound > 0, upperBound) << "a value > 0";
  //////// all checks before this line
  internal::Node cco = d_nodeMgr->mkConst(
      internal::CardinalityConstraint(*sort.d_type, upperBound));
  internal::Node cc =
      d_nodeMgr->mkNode(internal::Kind::CARDINALITY_CONSTRAINT, cco);
  return Term(this, cc);
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Create constants                                                           */
/* -------------------------------------------------------------------------- */

Term Solver::mkConst(const Sort& sort,
                     const std::optional<std::string>& symbol) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  internal::Node res = symbol ? d_nodeMgr->mkVar(*symbol, *sort.d_type)
                              : d_nodeMgr->mkVar(*sort.d_type);
  (void)res.getType(true); /* kick off type checking */
  increment_vars_consts_stats(sort, false);
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Create variables                                                           */
/* -------------------------------------------------------------------------- */

Term Solver::mkVar(const Sort& sort,
                   const std::optional<std::string>& symbol) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(sort);
  //////// all checks before this line
  internal::Node res = symbol ? d_nodeMgr->mkBoundVar(*symbol, *sort.d_type)
                              : d_nodeMgr->mkBoundVar(*sort.d_type);
  (void)res.getType(true); /* kick off type checking */
  increment_vars_consts_stats(sort, true);
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Create datatype constructor declarations                                   */
/* -------------------------------------------------------------------------- */

DatatypeConstructorDecl Solver::mkDatatypeConstructorDecl(
    const std::string& name)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return DatatypeConstructorDecl(this, name);
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Create datatype declarations                                               */
/* -------------------------------------------------------------------------- */

DatatypeDecl Solver::mkDatatypeDecl(const std::string& name, bool isCoDatatype)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return DatatypeDecl(this, name, isCoDatatype);
  ////////
  CVC5_API_TRY_CATCH_END;
}

DatatypeDecl Solver::mkDatatypeDecl(const std::string& name,
                                    const std::vector<Sort>& params,
                                    bool isCoDatatype)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORTS(params);
  //////// all checks before this line
  return DatatypeDecl(this, name, params, isCoDatatype);
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Create terms                                                               */
/* -------------------------------------------------------------------------- */

Term Solver::mkTerm(Kind kind, const std::vector<Term>& children) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_KIND_CHECK(kind);
  CVC5_API_SOLVER_CHECK_TERMS(children);
  //////// all checks before this line
  return mkTermHelper(kind, children);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkTerm(const Op& op, const std::vector<Term>& children) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_OP(op);
  CVC5_API_SOLVER_CHECK_TERMS(children);
  //////// all checks before this line
  return mkTermHelper(op, children);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::mkTuple(const std::vector<Sort>& sorts,
                     const std::vector<Term>& terms) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(sorts.size() == terms.size())
      << "Expected the same number of sorts and elements";
  CVC5_API_SOLVER_CHECK_SORTS(sorts);
  CVC5_API_SOLVER_CHECK_TERMS(terms);
  for (size_t i = 0, size = sorts.size(); i < size; i++)
  {
    CVC5_API_CHECK(terms[i].getSort() == sorts[i])
        << "Type mismatch in mkTuple";
  }
  //////// all checks before this line
  std::vector<internal::Node> args;
  for (size_t i = 0, size = sorts.size(); i < size; i++)
  {
    args.push_back(*terms[i].d_node);
  }

  Sort s = mkTupleSortHelper(sorts);
  Datatype dt = s.getDatatype();
  internal::NodeBuilder nb(extToIntKind(APPLY_CONSTRUCTOR));
  nb << *dt[0].getTerm().d_node;
  nb.append(args);
  internal::Node res = nb.constructNode();
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Create operators                                                           */
/* -------------------------------------------------------------------------- */

Op Solver::mkOp(Kind kind, const std::vector<uint32_t>& args) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_KIND_CHECK(kind);
  //////// all checks before this line
  size_t nargs = args.size();

  Op res;
  switch (kind)
  {
    case BITVECTOR_EXTRACT:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      res = mkOpHelper(kind, internal::BitVectorExtract(args[0], args[1]));
      break;
    case BITVECTOR_REPEAT:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::BitVectorRepeat(args[0]));
      break;
    case BITVECTOR_ROTATE_LEFT:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::BitVectorRotateLeft(args[0]));
      break;
    case BITVECTOR_ROTATE_RIGHT:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::BitVectorRotateRight(args[0]));
      break;
    case BITVECTOR_SIGN_EXTEND:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::BitVectorSignExtend(args[0]));
      break;
    case BITVECTOR_ZERO_EXTEND:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::BitVectorZeroExtend(args[0]));
      break;
    case DIVISIBLE:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::Divisible(args[0]));
      break;
    case FLOATINGPOINT_TO_SBV:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::FloatingPointToSBV(args[0]));
      break;
    case FLOATINGPOINT_TO_UBV:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::FloatingPointToUBV(args[0]));
      break;
    case FLOATINGPOINT_TO_FP_FROM_IEEE_BV:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      res = mkOpHelper(
          kind, internal::FloatingPointToFPIEEEBitVector(args[0], args[1]));
      break;
    case FLOATINGPOINT_TO_FP_FROM_FP:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      res = mkOpHelper(
          kind, internal::FloatingPointToFPFloatingPoint(args[0], args[1]));
      break;
    case FLOATINGPOINT_TO_FP_FROM_REAL:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      res = mkOpHelper(kind, internal::FloatingPointToFPReal(args[0], args[1]));
      break;
    case FLOATINGPOINT_TO_FP_FROM_SBV:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      res = mkOpHelper(
          kind, internal::FloatingPointToFPSignedBitVector(args[0], args[1]));
      break;
    case FLOATINGPOINT_TO_FP_FROM_UBV:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      res = mkOpHelper(
          kind, internal::FloatingPointToFPUnsignedBitVector(args[0], args[1]));
      break;
    case IAND:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::IntAnd(args[0]));
      break;
    case INT_TO_BITVECTOR:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::IntToBitVector(args[0]));
      break;
    case REGEXP_REPEAT:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::RegExpRepeat(args[0]));
      break;
    case REGEXP_LOOP:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      res = mkOpHelper(kind, internal::RegExpLoop(args[0], args[1]));
      break;
    case TUPLE_PROJECT:
      res = mkOpHelper(kind, internal::TupleProjectOp(args));
      break;
    case TABLE_PROJECT:
      res = mkOpHelper(kind, internal::TableProjectOp(args));
      break;
    case TABLE_AGGREGATE:
      res = mkOpHelper(kind, internal::TableAggregateOp(args));
      break;
    case TABLE_JOIN:
      res = mkOpHelper(kind, internal::TableJoinOp(args));
      break;
    case TABLE_GROUP:
      res = mkOpHelper(kind, internal::TableGroupOp(args));
      break;
    default:
      if (nargs == 0)
      {
        CVC5_API_CHECK(s_indexed_kinds.find(kind) == s_indexed_kinds.end())
            << "Expected a kind for a non-indexed operator.";
        return Op(this, kind);
      }
      else
      {
        CVC5_API_KIND_CHECK_EXPECTED(false, kind)
            << "operator kind with " << nargs << " uint32_t arguments";
      }
  }
  Assert(!res.isNull());
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Op Solver::mkOp(Kind kind, const std::initializer_list<uint32_t>& args) const
{
  return mkOp(kind, std::vector<uint32_t>(args));
}

Op Solver::mkOp(Kind kind, const std::string& arg) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_KIND_CHECK(kind);
  CVC5_API_KIND_CHECK_EXPECTED((kind == DIVISIBLE), kind) << "DIVISIBLE";
  //////// all checks before this line
  Op res;
  /* CLN and GMP handle this case differently, CLN interprets it as 0, GMP
   * throws an std::invalid_argument exception. For consistency, we treat it
   * as invalid. */
  CVC5_API_ARG_CHECK_EXPECTED(arg != ".", arg)
      << "a string representing an integer, real or rational value.";
  res = mkOpHelper(kind, internal::Divisible(internal::Integer(arg)));
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Non-SMT-LIB commands                                                       */
/* -------------------------------------------------------------------------- */

Term Solver::simplify(const Term& term)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(term);
  //////// all checks before this line
  Term res = Term(this, d_slv->simplify(*term.d_node));
  Assert(*res.getSort().d_type == *term.getSort().d_type);
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* SMT-LIB commands                                                           */
/* -------------------------------------------------------------------------- */

void Solver::assertFormula(const Term& term) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(term);
  CVC5_API_SOLVER_CHECK_TERM_WITH_SORT(term, getBooleanSort());
  ensureWellFormedTerm(term);
  //////// all checks before this line
  d_slv->assertFormula(*term.d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Result Solver::checkSat(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_slv->isQueryMade()
                 || d_slv->getOptions().base.incrementalSolving)
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  //////// all checks before this line
  return d_slv->checkSat();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Result Solver::checkSatAssuming(const Term& assumption) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_slv->isQueryMade()
                 || d_slv->getOptions().base.incrementalSolving)
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  CVC5_API_SOLVER_CHECK_TERM_WITH_SORT(assumption, getBooleanSort());
  ensureWellFormedTerm(assumption);
  //////// all checks before this line
  return d_slv->checkSat(*assumption.d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Result Solver::checkSatAssuming(const std::vector<Term>& assumptions) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_slv->isQueryMade() || assumptions.size() == 0
                 || d_slv->getOptions().base.incrementalSolving)
      << "Cannot make multiple queries unless incremental solving is enabled "
         "(try --incremental)";
  CVC5_API_SOLVER_CHECK_TERMS_WITH_SORT(assumptions, getBooleanSort());
  ensureWellFormedTerms(assumptions);
  //////// all checks before this line
  for (const Term& term : assumptions)
  {
    CVC5_API_SOLVER_CHECK_TERM(term);
  }
  std::vector<internal::Node> eassumptions =
      Term::termVectorToNodes(assumptions);
  return d_slv->checkSat(eassumptions);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::declareDatatype(
    const std::string& symbol,
    const std::vector<DatatypeConstructorDecl>& ctors) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(ctors.size() > 0, ctors)
      << "a datatype declaration with at least one constructor";
  CVC5_API_SOLVER_CHECK_DTCTORDECLS(ctors);
  for (size_t i = 0, size = ctors.size(); i < size; i++)
  {
    CVC5_API_CHECK(!ctors[i].isResolved())
        << "cannot use a constructor for multiple datatypes";
  }
  //////// all checks before this line
  DatatypeDecl dtdecl(this, symbol);
  for (size_t i = 0, size = ctors.size(); i < size; i++)
  {
    dtdecl.addConstructor(ctors[i]);
  }
  return Sort(this, getNodeManager()->mkDatatypeType(*dtdecl.d_dtype));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::declareFun(const std::string& symbol,
                        const std::vector<Sort>& sorts,
                        const Sort& sort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_DOMAIN_SORTS(sorts);
  CVC5_API_SOLVER_CHECK_CODOMAIN_SORT(sort);
  //////// all checks before this line

  internal::TypeNode type = *sort.d_type;
  if (!sorts.empty())
  {
    std::vector<internal::TypeNode> types = Sort::sortVectorToTypeNodes(sorts);
    type = getNodeManager()->mkFunctionType(types, type);
  }
  return Term(this, d_nodeMgr->mkVar(symbol, type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::declareSort(const std::string& symbol, uint32_t arity) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (arity == 0)
  {
    return Sort(this, getNodeManager()->mkSort(symbol));
  }
  return Sort(this, getNodeManager()->mkSortConstructor(symbol, arity));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::defineFun(const std::string& symbol,
                       const std::vector<Term>& bound_vars,
                       const Sort& sort,
                       const Term& term,
                       bool global) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_CODOMAIN_SORT(sort);
  CVC5_API_SOLVER_CHECK_TERM(term);
  // the sort of the body must match the return sort
  CVC5_API_CHECK(term.d_node->getType() == *sort.d_type)
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

  CVC5_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN(fun, bound_vars, domain_sorts);
  //////// all checks before this line

  d_slv->defineFunction(
      *fun.d_node, Term::termVectorToNodes(bound_vars), *term.d_node, global);
  return fun;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::defineFunRec(const std::string& symbol,
                          const std::vector<Term>& bound_vars,
                          const Sort& sort,
                          const Term& term,
                          bool global) const
{
  CVC5_API_TRY_CATCH_BEGIN;

  CVC5_API_CHECK(d_slv->getUserLogicInfo().isQuantified())
      << "recursive function definitions require a logic with quantifiers";
  CVC5_API_CHECK(
      d_slv->getUserLogicInfo().isTheoryEnabled(internal::theory::THEORY_UF))
      << "recursive function definitions require a logic with uninterpreted "
         "functions";

  CVC5_API_SOLVER_CHECK_TERM(term);
  CVC5_API_SOLVER_CHECK_CODOMAIN_SORT(sort);
  CVC5_API_CHECK(term.d_node->getType() == *sort.d_type)
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

  CVC5_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN(fun, bound_vars, domain_sorts);
  //////// all checks before this line

  d_slv->defineFunctionRec(
      *fun.d_node, Term::termVectorToNodes(bound_vars), *term.d_node, global);

  return fun;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::defineFunRec(const Term& fun,
                          const std::vector<Term>& bound_vars,
                          const Term& term,
                          bool global) const
{
  CVC5_API_TRY_CATCH_BEGIN;

  CVC5_API_CHECK(d_slv->getUserLogicInfo().isQuantified())
      << "recursive function definitions require a logic with quantifiers";
  CVC5_API_CHECK(
      d_slv->getUserLogicInfo().isTheoryEnabled(internal::theory::THEORY_UF))
      << "recursive function definitions require a logic with uninterpreted "
         "functions";

  CVC5_API_SOLVER_CHECK_TERM(fun);
  CVC5_API_SOLVER_CHECK_TERM(term);
  if (fun.getSort().isFunction())
  {
    std::vector<Sort> domain_sorts = fun.getSort().getFunctionDomainSorts();
    CVC5_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN(fun, bound_vars, domain_sorts);
    Sort codomain = fun.getSort().getFunctionCodomainSort();
    CVC5_API_CHECK(*codomain.d_type == term.d_node->getType())
        << "Invalid sort of function body '" << term << "', expected '"
        << codomain << "'";
  }
  else
  {
    CVC5_API_SOLVER_CHECK_BOUND_VARS(bound_vars);
    CVC5_API_ARG_CHECK_EXPECTED(bound_vars.size() == 0, fun)
        << "function or nullary symbol";
  }
  //////// all checks before this line

  std::vector<internal::Node> ebound_vars = Term::termVectorToNodes(bound_vars);
  d_slv->defineFunctionRec(*fun.d_node, ebound_vars, *term.d_node, global);
  return fun;
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::defineFunsRec(const std::vector<Term>& funs,
                           const std::vector<std::vector<Term>>& bound_vars,
                           const std::vector<Term>& terms,
                           bool global) const
{
  CVC5_API_TRY_CATCH_BEGIN;

  CVC5_API_CHECK(d_slv->getUserLogicInfo().isQuantified())
      << "recursive function definitions require a logic with quantifiers";
  CVC5_API_CHECK(
      d_slv->getUserLogicInfo().isTheoryEnabled(internal::theory::THEORY_UF))
      << "recursive function definitions require a logic with uninterpreted "
         "functions";
  CVC5_API_SOLVER_CHECK_TERMS(funs);
  CVC5_API_SOLVER_CHECK_TERMS(terms);

  size_t funs_size = funs.size();
  CVC5_API_ARG_SIZE_CHECK_EXPECTED(funs_size == bound_vars.size(), bound_vars)
      << "'" << funs_size << "'";
  CVC5_API_ARG_SIZE_CHECK_EXPECTED(funs_size == terms.size(), terms)
      << "'" << funs_size << "'";

  for (size_t j = 0; j < funs_size; ++j)
  {
    const Term& fun = funs[j];
    const std::vector<Term>& bvars = bound_vars[j];
    const Term& term = terms[j];

    CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == fun.d_solver, "function", funs, j)
        << "function associated with this solver object";
    CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(
        this == term.d_solver, "term", terms, j)
        << "term associated with this solver object";

    if (fun.getSort().isFunction())
    {
      std::vector<Sort> domain_sorts = fun.getSort().getFunctionDomainSorts();
      CVC5_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN(fun, bvars, domain_sorts);
      Sort codomain = fun.getSort().getFunctionCodomainSort();
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(
          codomain == term.getSort(), "sort of function body", terms, j)
          << "'" << codomain << "'";
    }
    else
    {
      CVC5_API_SOLVER_CHECK_BOUND_VARS(bvars);
      CVC5_API_ARG_CHECK_EXPECTED(bvars.size() == 0, fun)
          << "function or nullary symbol";
    }
  }
  //////// all checks before this line
  std::vector<internal::Node> efuns = Term::termVectorToNodes(funs);
  std::vector<std::vector<internal::Node>> ebound_vars;
  for (const auto& v : bound_vars)
  {
    ebound_vars.push_back(Term::termVectorToNodes(v));
  }
  std::vector<internal::Node> nodes = Term::termVectorToNodes(terms);
  d_slv->defineFunctionsRec(efuns, ebound_vars, nodes, global);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Term> Solver::getAssertions(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  std::vector<internal::Node> assertions = d_slv->getAssertions();
  /* Can not use
   *   return std::vector<Term>(assertions.begin(), assertions.end());
   * here since constructor is private */
  return Term::nodeVectorToTerms(this, assertions);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Solver::getInfo(const std::string& flag) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_UNSUPPORTED_CHECK(d_slv->isValidGetInfoFlag(flag))
      << "Unrecognized flag: " << flag << ".";
  //////// all checks before this line
  return d_slv->getInfo(flag);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Solver::getOption(const std::string& option) const
{
  try
  {
    return d_slv->getOption(option);
  }
  catch (internal::OptionException& e)
  {
    throw CVC5ApiUnsupportedException(e.getMessage());
  }
}

// Supports a visitor from a list of lambdas
// Taken from https://en.cppreference.com/w/cpp/utility/variant/visit
template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

bool OptionInfo::boolValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(std::holds_alternative<ValueInfo<bool>>(valueInfo))
      << name << " is not a bool option";
  //////// all checks before this line
  return std::get<ValueInfo<bool>>(valueInfo).currentValue;
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::string OptionInfo::stringValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(
      std::holds_alternative<ValueInfo<std::string>>(valueInfo))
      << name << " is not a string option";
  //////// all checks before this line
  return std::get<ValueInfo<std::string>>(valueInfo).currentValue;
  ////////
  CVC5_API_TRY_CATCH_END;
}
int64_t OptionInfo::intValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(
      std::holds_alternative<NumberInfo<int64_t>>(valueInfo))
      << name << " is not an int option";
  //////// all checks before this line
  return std::get<NumberInfo<int64_t>>(valueInfo).currentValue;
  ////////
  CVC5_API_TRY_CATCH_END;
}
uint64_t OptionInfo::uintValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(
      std::holds_alternative<NumberInfo<uint64_t>>(valueInfo))
      << name << " is not a uint option";
  //////// all checks before this line
  return std::get<NumberInfo<uint64_t>>(valueInfo).currentValue;
  ////////
  CVC5_API_TRY_CATCH_END;
}
double OptionInfo::doubleValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(
      std::holds_alternative<NumberInfo<double>>(valueInfo))
      << name << " is not a double option";
  //////// all checks before this line
  return std::get<NumberInfo<double>>(valueInfo).currentValue;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::ostream& operator<<(std::ostream& os, const OptionInfo& oi)
{
  os << "OptionInfo{ " << oi.name;
  if (oi.setByUser)
  {
    os << " | set by user";
  }
  if (!oi.aliases.empty())
  {
    internal::container_to_stream(os, oi.aliases, ", ", "", ", ");
  }
  auto printNum = [&os](const std::string& type, const auto& vi) {
    os << " | " << type << " | " << vi.currentValue << " | default "
       << vi.defaultValue;
    if (vi.minimum || vi.maximum)
    {
      os << " |";
      if (vi.minimum)
      {
        os << " " << *vi.minimum << " <=";
      }
      os << " x";
      if (vi.maximum)
      {
        os << " <= " << *vi.maximum;
      }
    }
  };
  std::visit(overloaded{
                 [&os](const OptionInfo::VoidInfo& vi) { os << " | void"; },
                 [&os](const OptionInfo::ValueInfo<bool>& vi) {
                   os << std::boolalpha << " | bool | " << vi.currentValue
                      << " | default " << vi.defaultValue << std::noboolalpha;
                 },
                 [&os](const OptionInfo::ValueInfo<std::string>& vi) {
                   os << " | string | \"" << vi.currentValue
                      << "\" | default \"" << vi.defaultValue << "\"";
                 },
                 [&printNum](const OptionInfo::NumberInfo<int64_t>& vi) {
                   printNum("int64_t", vi);
                 },
                 [&printNum](const OptionInfo::NumberInfo<uint64_t>& vi) {
                   printNum("uint64_t", vi);
                 },
                 [&printNum](const OptionInfo::NumberInfo<double>& vi) {
                   printNum("double", vi);
                 },
                 [&os](const OptionInfo::ModeInfo& vi) {
                   os << " | mode | " << vi.currentValue << " | default "
                      << vi.defaultValue << " | modes: ";
                   internal::container_to_stream(os, vi.modes, "", "", ", ");
                 },
             },
             oi.valueInfo);
  os << " }";
  return os;
}

std::vector<std::string> Solver::getOptionNames() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return internal::options::getNames();
  ////////
  CVC5_API_TRY_CATCH_END;
}

OptionInfo Solver::getOptionInfo(const std::string& option) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  auto info = internal::options::getInfo(d_slv->getOptions(), option);
  CVC5_API_CHECK(info.name != "")
      << "Querying invalid or unknown option " << option;
  return std::visit(
      overloaded{
          [&info](const internal::options::OptionInfo::VoidInfo& vi) {
            return OptionInfo{info.name,
                              info.aliases,
                              info.setByUser,
                              OptionInfo::VoidInfo{}};
          },
          [&info](const internal::options::OptionInfo::ValueInfo<bool>& vi) {
            return OptionInfo{
                info.name,
                info.aliases,
                info.setByUser,
                OptionInfo::ValueInfo<bool>{vi.defaultValue, vi.currentValue}};
          },
          [&info](
              const internal::options::OptionInfo::ValueInfo<std::string>& vi) {
            return OptionInfo{info.name,
                              info.aliases,
                              info.setByUser,
                              OptionInfo::ValueInfo<std::string>{
                                  vi.defaultValue, vi.currentValue}};
          },
          [&info](
              const internal::options::OptionInfo::NumberInfo<int64_t>& vi) {
            return OptionInfo{
                info.name,
                info.aliases,
                info.setByUser,
                OptionInfo::NumberInfo<int64_t>{
                    vi.defaultValue, vi.currentValue, vi.minimum, vi.maximum}};
          },
          [&info](
              const internal::options::OptionInfo::NumberInfo<uint64_t>& vi) {
            return OptionInfo{
                info.name,
                info.aliases,
                info.setByUser,
                OptionInfo::NumberInfo<uint64_t>{
                    vi.defaultValue, vi.currentValue, vi.minimum, vi.maximum}};
          },
          [&info](const internal::options::OptionInfo::NumberInfo<double>& vi) {
            return OptionInfo{
                info.name,
                info.aliases,
                info.setByUser,
                OptionInfo::NumberInfo<double>{
                    vi.defaultValue, vi.currentValue, vi.minimum, vi.maximum}};
          },
          [&info](const internal::options::OptionInfo::ModeInfo& vi) {
            return OptionInfo{info.name,
                              info.aliases,
                              info.setByUser,
                              OptionInfo::ModeInfo{
                                  vi.defaultValue, vi.currentValue, vi.modes}};
          },
      },
      info.valueInfo);
  ////////
  CVC5_API_TRY_CATCH_END;
}

DriverOptions Solver::getDriverOptions() const { return DriverOptions(*this); }

std::vector<Term> Solver::getUnsatAssumptions(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().base.incrementalSolving)
      << "Cannot get unsat assumptions unless incremental solving is enabled "
         "(try --incremental)";
  CVC5_API_CHECK(d_slv->getOptions().smt.unsatAssumptions)
      << "Cannot get unsat assumptions unless explicitly enabled "
         "(try --produce-unsat-assumptions)";
  CVC5_API_CHECK(d_slv->getSmtMode() == internal::SmtMode::UNSAT)
      << "Cannot get unsat assumptions unless in unsat mode.";
  //////// all checks before this line

  std::vector<internal::Node> uassumptions = d_slv->getUnsatAssumptions();
  /* Can not use
   *   return std::vector<Term>(uassumptions.begin(), uassumptions.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const internal::Node& n : uassumptions)
  {
    res.push_back(Term(this, n));
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Term> Solver::getUnsatCore(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceUnsatCores)
      << "Cannot get unsat core unless explicitly enabled "
         "(try --produce-unsat-cores)";
  CVC5_API_RECOVERABLE_CHECK(d_slv->getSmtMode() == internal::SmtMode::UNSAT)
      << "Cannot get unsat core unless in unsat mode.";
  //////// all checks before this line
  internal::UnsatCore core = d_slv->getUnsatCore();
  /* Can not use
   *   return std::vector<Term>(core.begin(), core.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const internal::Node& e : core)
  {
    res.push_back(Term(this, e));
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::map<Term, Term> Solver::getDifficulty() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(d_slv->getSmtMode() == internal::SmtMode::UNSAT
                             || d_slv->getSmtMode() == internal::SmtMode::SAT
                             || d_slv->getSmtMode()
                                    == internal::SmtMode::SAT_UNKNOWN)
      << "Cannot get difficulty unless after a UNSAT, SAT or UNKNOWN response.";
  //////// all checks before this line
  std::map<Term, Term> res;
  std::map<internal::Node, internal::Node> dmap;
  d_slv->getDifficultyMap(dmap);
  for (const std::pair<const internal::Node, internal::Node>& d : dmap)
  {
    res[Term(this, d.first)] = Term(this, d.second);
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Solver::getProof(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceProofs)
      << "Cannot get proof unless proofs are enabled (try --produce-proofs)";
  CVC5_API_RECOVERABLE_CHECK(d_slv->getSmtMode() == internal::SmtMode::UNSAT)
      << "Cannot get proof unless in unsat mode.";
  return d_slv->getProof();
  CVC5_API_TRY_CATCH_END;
}

std::vector<Term> Solver::getLearnedLiterals(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceLearnedLiterals)
      << "Cannot get learned literals unless enabled (try "
         "--produce-learned-literals)";
  CVC5_API_RECOVERABLE_CHECK(d_slv->getSmtMode() == internal::SmtMode::UNSAT
                             || d_slv->getSmtMode() == internal::SmtMode::SAT
                             || d_slv->getSmtMode()
                                    == internal::SmtMode::SAT_UNKNOWN)
      << "Cannot get learned literals unless after a UNSAT, SAT or UNKNOWN "
         "response.";
  //////// all checks before this line
  std::vector<internal::Node> lits = d_slv->getLearnedLiterals();
  return Term::nodeVectorToTerms(this, lits);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getValue(const Term& term) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(d_slv->getOptions().smt.produceModels)
      << "Cannot get value unless model generation is enabled "
         "(try --produce-models)";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "Cannot get value unless after a SAT or UNKNOWN response.";
  CVC5_API_SOLVER_CHECK_TERM(term);
  CVC5_API_RECOVERABLE_CHECK(term.getSort().getTypeNode().isFirstClass())
      << "Cannot get value of a term that is not first class.";
  CVC5_API_RECOVERABLE_CHECK(!term.getSort().isDatatype()
                             || term.getSort().getDatatype().isWellFounded())
      << "Cannot get value of a term of non-well-founded datatype sort.";
  ensureWellFormedTerm(term);
  //////// all checks before this line
  return getValueHelper(term);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Term> Solver::getValue(const std::vector<Term>& terms) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(d_slv->getOptions().smt.produceModels)
      << "Cannot get value unless model generation is enabled "
         "(try --produce-models)";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "Cannot get value unless after a SAT or UNKNOWN response.";
  for (const Term& t : terms)
  {
    CVC5_API_RECOVERABLE_CHECK(t.getSort().getTypeNode().isFirstClass())
        << "Cannot get value of a term that is not first class.";
    CVC5_API_RECOVERABLE_CHECK(!t.getSort().isDatatype()
                               || t.getSort().getDatatype().isWellFounded())
        << "Cannot get value of a term of non-well-founded datatype sort.";
  }
  CVC5_API_SOLVER_CHECK_TERMS(terms);
  ensureWellFormedTerms(terms);
  //////// all checks before this line

  std::vector<Term> res;
  for (size_t i = 0, n = terms.size(); i < n; ++i)
  {
    /* Can not use emplace_back here since constructor is private. */
    res.push_back(getValueHelper(terms[i]));
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Term> Solver::getModelDomainElements(const Sort& s) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(d_slv->getOptions().smt.produceModels)
      << "Cannot get domain elements unless model generation is enabled "
         "(try --produce-models)";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "Cannot get domain elements unless after a SAT or UNKNOWN response.";
  CVC5_API_SOLVER_CHECK_SORT(s);
  CVC5_API_RECOVERABLE_CHECK(s.isUninterpretedSort())
      << "Expecting an uninterpreted sort as argument to "
         "getModelDomainElements.";
  //////// all checks before this line
  std::vector<Term> res;
  std::vector<internal::Node> elements =
      d_slv->getModelDomainElements(s.getTypeNode());
  for (const internal::Node& n : elements)
  {
    res.push_back(Term(this, n));
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Solver::isModelCoreSymbol(const Term& v) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(d_slv->getOptions().smt.produceModels)
      << "Cannot check if model core symbol unless model generation is enabled "
         "(try --produce-models)";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "Cannot check if model core symbol unless after a SAT or UNKNOWN "
         "response.";
  CVC5_API_SOLVER_CHECK_TERM(v);
  CVC5_API_RECOVERABLE_CHECK(v.getKind() == CONSTANT)
      << "Expecting a free constant as argument to isModelCoreSymbol.";
  //////// all checks before this line
  return d_slv->isModelCoreSymbol(v.getNode());
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Solver::getModel(const std::vector<Sort>& sorts,
                             const std::vector<Term>& vars) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(d_slv->getOptions().smt.produceModels)
      << "Cannot get model unless model generation is enabled "
         "(try --produce-models)";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "Cannot get model unless after a SAT or UNKNOWN response.";
  CVC5_API_SOLVER_CHECK_SORTS(sorts);
  for (const Sort& s : sorts)
  {
    CVC5_API_RECOVERABLE_CHECK(s.isUninterpretedSort())
        << "Expecting an uninterpreted sort as argument to "
           "getModel.";
  }
  CVC5_API_SOLVER_CHECK_TERMS(vars);
  for (const Term& v : vars)
  {
    CVC5_API_RECOVERABLE_CHECK(v.getKind() == CONSTANT)
        << "Expecting a free constant as argument to getModel.";
  }
  //////// all checks before this line
  return d_slv->getModel(Sort::sortVectorToTypeNodes(sorts),
                         Term::termVectorToNodes(vars));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getQuantifierElimination(const Term& q) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(q);
  //////// all checks before this line
  return Term(this, d_slv->getQuantifierElimination(q.getNode(), true));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getQuantifierEliminationDisjunct(const Term& q) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(q);
  //////// all checks before this line
  return Term(this, d_slv->getQuantifierElimination(q.getNode(), false));
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::declareSepHeap(const Sort& locSort, const Sort& dataSort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(locSort);
  CVC5_API_SOLVER_CHECK_SORT(dataSort);
  CVC5_API_CHECK(
      d_slv->getLogicInfo().isTheoryEnabled(internal::theory::THEORY_SEP))
      << "Cannot obtain separation logic expressions if not using the "
         "separation logic theory.";
  //////// all checks before this line
  d_slv->declareSepHeap(locSort.getTypeNode(), dataSort.getTypeNode());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getValueSepHeap() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(
      d_slv->getLogicInfo().isTheoryEnabled(internal::theory::THEORY_SEP))
      << "Cannot obtain separation logic expressions if not using the "
         "separation logic theory.";
  CVC5_API_CHECK(d_slv->getOptions().smt.produceModels)
      << "Cannot get separation heap term unless model generation is enabled "
         "(try --produce-models)";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "Can only get separtion heap term after SAT or UNKNOWN response.";
  //////// all checks before this line
  return Term(this, d_slv->getSepHeapExpr());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getValueSepNil() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(
      d_slv->getLogicInfo().isTheoryEnabled(internal::theory::THEORY_SEP))
      << "Cannot obtain separation logic expressions if not using the "
         "separation logic theory.";
  CVC5_API_CHECK(d_slv->getOptions().smt.produceModels)
      << "Cannot get separation nil term unless model generation is enabled "
         "(try --produce-models)";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "Can only get separtion nil term after SAT or UNKNOWN response.";
  //////// all checks before this line
  return Term(this, d_slv->getSepNilExpr());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::declarePool(const std::string& symbol,
                         const Sort& sort,
                         const std::vector<Term>& initValue) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(sort);
  CVC5_API_SOLVER_CHECK_TERMS(initValue);
  //////// all checks before this line
  internal::TypeNode setType = getNodeManager()->mkSetType(*sort.d_type);
  internal::Node pool = getNodeManager()->mkBoundVar(symbol, setType);
  std::vector<internal::Node> initv = Term::termVectorToNodes(initValue);
  d_slv->declarePool(pool, initv);
  return Term(this, pool);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::declareOracleFun(
    const std::string& symbol,
    const std::vector<Sort>& sorts,
    const Sort& sort,
    std::function<Term(const std::vector<Term>&)> fn) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_DOMAIN_SORTS(sorts);
  CVC5_API_SOLVER_CHECK_CODOMAIN_SORT(sort);
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.oracles)
      << "Cannot call declareOracleFun unless oracles is enabled (use "
         "--oracles)";
  //////// all checks before this line
  internal::TypeNode type = *sort.d_type;
  if (!sorts.empty())
  {
    std::vector<internal::TypeNode> types = Sort::sortVectorToTypeNodes(sorts);
    type = d_nodeMgr->mkFunctionType(types, type);
  }
  internal::Node fun = d_nodeMgr->mkVar(symbol, type);
  // Wrap the terms-to-term function so that it is nodes-to-nodes. Note we
  // make the method return a vector of size one to conform to the interface
  // at the SolverEngine level.
  d_slv->declareOracleFun(
      fun, [&, fn](const std::vector<internal::Node> nodes) {
        std::vector<Term> terms = Term::nodeVectorToTerms(this, nodes);
        Term output = fn(terms);
        return Term::termVectorToNodes({output});
      });
  return Term(this, fun);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::pop(uint32_t nscopes) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().base.incrementalSolving)
      << "Cannot pop when not solving incrementally (use --incremental)";
  CVC5_API_CHECK(nscopes <= d_slv->getNumUserLevels())
      << "Cannot pop beyond first pushed context";
  //////// all checks before this line
  for (uint32_t n = 0; n < nscopes; ++n)
  {
    d_slv->pop();
  }
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getInterpolant(const Term& conj) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(conj);
  CVC5_API_CHECK(d_slv->getOptions().smt.interpolants)
      << "Cannot get interpolant unless interpolants are enabled (try "
         "--produce-interpolants)";
  //////// all checks before this line
  internal::TypeNode nullType;
  internal::Node result = d_slv->getInterpolant(*conj.d_node, nullType);
  return Term(this, result);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getInterpolant(const Term& conj, Grammar& grammar) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(conj);
  CVC5_API_CHECK(d_slv->getOptions().smt.interpolants)
      << "Cannot get interpolant unless interpolants are enabled (try "
         "--produce-interpolants)";
  //////// all checks before this line
  internal::Node result =
      d_slv->getInterpolant(*conj.d_node, *grammar.resolve().d_type);
  return Term(this, result);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getInterpolantNext() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.interpolants)
      << "Cannot get interpolant unless interpolants are enabled (try "
         "--produce-interpolants)";
  CVC5_API_CHECK(d_slv->getOptions().base.incrementalSolving)
      << "Cannot get next interpolant when not solving incrementally (try "
         "--incremental)";
  //////// all checks before this line
  internal::Node result = d_slv->getInterpolantNext();
  return Term(this, result);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getAbduct(const Term& conj) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(conj);
  CVC5_API_CHECK(d_slv->getOptions().smt.produceAbducts)
      << "Cannot get abduct unless abducts are enabled (try --produce-abducts)";
  //////// all checks before this line
  internal::TypeNode nullType;
  internal::Node result = d_slv->getAbduct(*conj.d_node, nullType);
  return Term(this, result);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getAbduct(const Term& conj, Grammar& grammar) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(conj);
  CVC5_API_CHECK(d_slv->getOptions().smt.produceAbducts)
      << "Cannot get abduct unless abducts are enabled (try --produce-abducts)";
  //////// all checks before this line
  internal::Node result =
      d_slv->getAbduct(*conj.d_node, *grammar.resolve().d_type);
  return Term(this, result);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getAbductNext() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceAbducts)
      << "Cannot get next abduct unless abducts are enabled (try "
         "--produce-abducts)";
  CVC5_API_CHECK(d_slv->getOptions().base.incrementalSolving)
      << "Cannot get next abduct when not solving incrementally (try "
         "--incremental)";
  //////// all checks before this line
  internal::Node result = d_slv->getAbductNext();
  return Term(this, result);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::blockModel(modes::BlockModelsMode mode) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceModels)
      << "Cannot get value unless model generation is enabled "
         "(try --produce-models)";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "Can only block model after SAT or UNKNOWN response.";
  //////// all checks before this line
  d_slv->blockModel(mode);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::blockModelValues(const std::vector<Term>& terms) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceModels)
      << "Cannot get value unless model generation is enabled "
         "(try --produce-models)";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "Can only block model values after SAT or UNKNOWN response.";
  CVC5_API_ARG_SIZE_CHECK_EXPECTED(!terms.empty(), terms)
      << "a non-empty set of terms";
  CVC5_API_SOLVER_CHECK_TERMS(terms);
  ensureWellFormedTerms(terms);
  //////// all checks before this line
  d_slv->blockModelValues(Term::termVectorToNodes(terms));
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Solver::getInstantiations() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(d_slv->getSmtMode() == internal::SmtMode::UNSAT
                             || d_slv->getSmtMode() == internal::SmtMode::SAT
                             || d_slv->getSmtMode()
                                    == internal::SmtMode::SAT_UNKNOWN)
      << "Cannot get instantiations unless after a UNSAT, SAT or UNKNOWN "
         "response.";
  //////// all checks before this line
  std::stringstream ss;
  d_slv->printInstantiations(ss);
  return ss.str();
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::push(uint32_t nscopes) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().base.incrementalSolving)
      << "Cannot push when not solving incrementally (use --incremental)";
  //////// all checks before this line
  for (uint32_t n = 0; n < nscopes; ++n)
  {
    d_slv->push();
  }
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::resetAssertions(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  d_slv->resetAssertions();
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::setInfo(const std::string& keyword, const std::string& value) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_UNSUPPORTED_CHECK(
      keyword == "source" || keyword == "category" || keyword == "difficulty"
      || keyword == "filename" || keyword == "license" || keyword == "name"
      || keyword == "notes" || keyword == "smt-lib-version"
      || keyword == "status")
      << "Unrecognized keyword: " << keyword
      << ", expected 'source', 'category', 'difficulty', "
         "'filename', 'license', 'name', "
         "'notes', 'smt-lib-version' or 'status'";
  CVC5_API_RECOVERABLE_ARG_CHECK_EXPECTED(
      keyword != "smt-lib-version" || value == "2" || value == "2.0"
          || value == "2.5" || value == "2.6",
      value)
      << "'2.0', '2.5', '2.6'";
  CVC5_API_ARG_CHECK_EXPECTED(keyword != "status" || value == "sat"
                                  || value == "unsat" || value == "unknown",
                              value)
      << "'sat', 'unsat' or 'unknown'";
  //////// all checks before this line
  if (keyword == "filename")
  {
    // only the Solver object has non-const access to the original options
    d_originalOptions->writeDriver().filename = value;
  }
  d_slv->setInfo(keyword, value);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::setLogic(const std::string& logic) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_slv->isFullyInited())
      << "Invalid call to 'setLogic', solver is already fully initialized";
  internal::LogicInfo logic_info(logic);
  //////// all checks before this line
  d_slv->setLogic(logic_info);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::setOption(const std::string& option,
                       const std::string& value) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  std::vector<std::string> options = internal::options::getNames();
  CVC5_API_UNSUPPORTED_CHECK(
      option.find("command-verbosity") != std::string::npos
      || std::find(options.cbegin(), options.cend(), option) != options.cend())
      << "Unrecognized option: " << option << '.';
  static constexpr auto mutableOpts = {"diagnostic-output-channel",
                                       "print-success",
                                       "regular-output-channel",
                                       "reproducible-resource-limit",
                                       "verbosity"};
  if (std::find(mutableOpts.begin(), mutableOpts.end(), option)
      == mutableOpts.end())
  {
    CVC5_API_CHECK(!d_slv->isFullyInited())
        << "Invalid call to 'setOption' for option '" << option
        << "', solver is already fully initialized";
  }
  //////// all checks before this line
  d_slv->setOption(option, value);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::declareSygusVar(const std::string& symbol, const Sort& sort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(sort);
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "Cannot call declareSygusVar unless sygus is enabled (use --sygus)";
  //////// all checks before this line
  internal::Node res = getNodeManager()->mkBoundVar(symbol, *sort.d_type);
  (void)res.getType(true); /* kick off type checking */

  d_slv->declareSygusVar(res);

  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Grammar Solver::mkGrammar(const std::vector<Term>& boundVars,
                          const std::vector<Term>& ntSymbols) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_SIZE_CHECK_EXPECTED(!ntSymbols.empty(), ntSymbols)
      << "a non-empty vector";
  CVC5_API_SOLVER_CHECK_BOUND_VARS(boundVars);
  CVC5_API_SOLVER_CHECK_BOUND_VARS(ntSymbols);
  //////// all checks before this line
  return Grammar(this, boundVars, ntSymbols);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::synthFun(const std::string& symbol,
                      const std::vector<Term>& boundVars,
                      const Sort& sort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_BOUND_VARS(boundVars);
  CVC5_API_SOLVER_CHECK_SORT(sort);
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "Cannot call synthFun unless sygus is enabled (use --sygus)";
  //////// all checks before this line
  return synthFunHelper(symbol, boundVars, sort);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::synthFun(const std::string& symbol,
                      const std::vector<Term>& boundVars,
                      Sort sort,
                      Grammar& grammar) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_BOUND_VARS(boundVars);
  CVC5_API_SOLVER_CHECK_SORT(sort);
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "Cannot call synthFun unless sygus is enabled (use --sygus)";
  //////// all checks before this line
  return synthFunHelper(symbol, boundVars, sort, false, &grammar);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::synthInv(const std::string& symbol,
                      const std::vector<Term>& boundVars) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_BOUND_VARS(boundVars);
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "Cannot call synthInv unless sygus is enabled (use --sygus)";
  //////// all checks before this line
  return synthFunHelper(
      symbol, boundVars, Sort(this, getNodeManager()->booleanType()), true);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::synthInv(const std::string& symbol,
                      const std::vector<Term>& boundVars,
                      Grammar& grammar) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_BOUND_VARS(boundVars);
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "Cannot call synthInv unless sygus is enabled (use --sygus)";
  //////// all checks before this line
  return synthFunHelper(symbol,
                        boundVars,
                        Sort(this, getNodeManager()->booleanType()),
                        true,
                        &grammar);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::addSygusConstraint(const Term& term) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(term);
  CVC5_API_ARG_CHECK_EXPECTED(
      term.d_node->getType() == getNodeManager()->booleanType(), term)
      << "boolean term";
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "Cannot addSygusConstraint unless sygus is enabled (use --sygus)";
  //////// all checks before this line
  d_slv->assertSygusConstraint(*term.d_node, false);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::addSygusAssume(const Term& term) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(term);
  CVC5_API_ARG_CHECK_EXPECTED(
      term.d_node->getType() == getNodeManager()->booleanType(), term)
      << "boolean term";
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "Cannot addSygusAssume unless sygus is enabled (use --sygus)";
  //////// all checks before this line
  d_slv->assertSygusConstraint(*term.d_node, true);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::addSygusInvConstraint(Term inv,
                                   Term pre,
                                   Term trans,
                                   Term post) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(inv);
  CVC5_API_SOLVER_CHECK_TERM(pre);
  CVC5_API_SOLVER_CHECK_TERM(trans);
  CVC5_API_SOLVER_CHECK_TERM(post);

  CVC5_API_ARG_CHECK_EXPECTED(inv.d_node->getType().isFunction(), inv)
      << "a function";

  internal::TypeNode invType = inv.d_node->getType();

  CVC5_API_ARG_CHECK_EXPECTED(invType.getRangeType().isBoolean(), inv)
      << "boolean range";

  CVC5_API_CHECK(pre.d_node->getType() == invType)
      << "Expected inv and pre to have the same sort";

  CVC5_API_CHECK(post.d_node->getType() == invType)
      << "Expected inv and post to have the same sort";
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "Cannot addSygusInvConstraint unless sygus is enabled (use --sygus)";
  //////// all checks before this line

  const std::vector<internal::TypeNode>& invArgTypes = invType.getArgTypes();

  std::vector<internal::TypeNode> expectedTypes;
  expectedTypes.reserve(2 * invArgTypes.size() + 1);

  for (size_t i = 0, n = invArgTypes.size(); i < 2 * n; i += 2)
  {
    expectedTypes.push_back(invArgTypes[i % n]);
    expectedTypes.push_back(invArgTypes[(i + 1) % n]);
  }

  expectedTypes.push_back(invType.getRangeType());
  internal::TypeNode expectedTransType =
      getNodeManager()->mkFunctionType(expectedTypes);

  CVC5_API_CHECK(trans.d_node->getType() == expectedTransType)
      << "Expected trans's sort to be " << invType;

  d_slv->assertSygusInvConstraint(
      *inv.d_node, *pre.d_node, *trans.d_node, *post.d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}

SynthResult Solver::checkSynth() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "Cannot checkSynth unless sygus is enabled (use --sygus)";
  //////// all checks before this line
  return d_slv->checkSynth();
  ////////
  CVC5_API_TRY_CATCH_END;
}

SynthResult Solver::checkSynthNext() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "Cannot checkSynthNext unless sygus is enabled (use --sygus)";
  CVC5_API_CHECK(d_slv->getOptions().base.incrementalSolving)
      << "Cannot checkSynthNext when not solving incrementally (use "
         "--incremental)";
  //////// all checks before this line
  return d_slv->checkSynth(true);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getSynthSolution(Term term) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(term);

  std::map<internal::Node, internal::Node> map;
  CVC5_API_CHECK(d_slv->getSynthSolutions(map))
      << "The solver is not in a state immediately preceded by a "
         "successful call to checkSynth";

  std::map<internal::Node, internal::Node>::const_iterator it =
      map.find(*term.d_node);

  CVC5_API_CHECK(it != map.cend()) << "Synth solution not found for given term";
  //////// all checks before this line
  return Term(this, it->second);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Term> Solver::getSynthSolutions(
    const std::vector<Term>& terms) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_SIZE_CHECK_EXPECTED(!terms.empty(), terms) << "non-empty vector";
  CVC5_API_SOLVER_CHECK_TERMS(terms);

  std::map<internal::Node, internal::Node> map;
  CVC5_API_CHECK(d_slv->getSynthSolutions(map))
      << "The solver is not in a state immediately preceded by a "
         "successful call to checkSynth";
  //////// all checks before this line

  std::vector<Term> synthSolution;
  synthSolution.reserve(terms.size());

  for (size_t i = 0, n = terms.size(); i < n; ++i)
  {
    std::map<internal::Node, internal::Node>::const_iterator it =
        map.find(*terms[i].d_node);

    CVC5_API_CHECK(it != map.cend())
        << "Synth solution not found for term at index " << i;

    synthSolution.push_back(Term(this, it->second));
  }

  return synthSolution;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Statistics Solver::getStatistics() const
{
  return Statistics(d_slv->getStatisticsRegistry());
}

bool Solver::isOutputOn(const std::string& tag) const
{
  // `isOutputOn(tag)` may raise an `OptionException`, which we do not want to
  // forward as such. We thus do not use the standard exception handling macros
  // here but roll our own.
  try
  {
    return d_slv->getEnv().isOutputOn(tag);
  }
  catch (const internal::Exception& e)
  {
    throw CVC5ApiException("Invalid output tag " + tag);
  }
}

std::ostream& Solver::getOutput(const std::string& tag) const
{
  // `output(tag)` may raise an `OptionException`, which we do not want to
  // forward as such. We thus do not use the standard exception handling macros
  // here but roll our own.
  try
  {
    return d_slv->getEnv().output(tag);
  }
  catch (const internal::Exception& e)
  {
    throw CVC5ApiException("Invalid output tag " + tag);
  }
}

}  // namespace cvc5

namespace std {

size_t hash<cvc5::Kind>::operator()(cvc5::Kind k) const
{
  return static_cast<size_t>(k);
}

size_t hash<cvc5::Op>::operator()(const cvc5::Op& t) const
{
  if (t.isIndexedHelper())
  {
    return std::hash<cvc5::internal::Node>()(*t.d_node);
  }
  else
  {
    return std::hash<cvc5::Kind>()(t.d_kind);
  }
}

size_t std::hash<cvc5::Sort>::operator()(const cvc5::Sort& s) const
{
  return std::hash<cvc5::internal::TypeNode>()(*s.d_type);
}

size_t std::hash<cvc5::Term>::operator()(const cvc5::Term& t) const
{
  return std::hash<cvc5::internal::Node>()(*t.d_node);
}

}  // namespace std

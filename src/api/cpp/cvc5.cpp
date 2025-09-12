/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

#include <cvc5/cvc5.h>

#include <cstring>
#include <sstream>

#include "api/cpp/cvc5_checks.h"
#include "base/check.h"
#include "base/configuration.h"
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
#include "expr/plugin.h"
#include "expr/sequence.h"
#include "expr/skolem_manager.h"
#include "expr/sygus_grammar.h"
#include "expr/type_node.h"
#include "options/base_options.h"
#include "options/expr_options.h"
#include "options/main_options.h"
#include "options/options.h"
#include "options/options_public.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "proof/proof_node.h"
#include "proof/unsat_core.h"
#include "smt/env.h"
#include "smt/model.h"
#include "smt/smt_mode.h"
#include "smt/solver_engine.h"
#include "theory/arith/nl/poly_conversion.h"
#include "theory/datatypes/project_op.h"
#include "theory/logic_info.h"
#include "theory/theory_model.h"
#include "util/bitvector.h"
#include "util/divisible.h"
#include "util/finite_field_value.h"
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

#define KIND_ENUM(external_name, internal_name)                              \
  {                                                                          \
    external_name,                                                           \
        std::make_pair(internal_name, std::string(#external_name).substr(6)) \
  }

/* Mapping from external (API) kind to internal kind. */
const static std::unordered_map<Kind, std::pair<internal::Kind, std::string>>
    s_kinds{
        KIND_ENUM(Kind::INTERNAL_KIND, internal::Kind::UNDEFINED_KIND),
        KIND_ENUM(Kind::UNDEFINED_KIND, internal::Kind::UNDEFINED_KIND),
        KIND_ENUM(Kind::NULL_TERM, internal::Kind::NULL_EXPR),
        /* Builtin ---------------------------------------------------------- */
        KIND_ENUM(Kind::UNINTERPRETED_SORT_VALUE,
                  internal::Kind::UNINTERPRETED_SORT_VALUE),
        KIND_ENUM(Kind::EQUAL, internal::Kind::EQUAL),
        KIND_ENUM(Kind::DISTINCT, internal::Kind::DISTINCT),
        KIND_ENUM(Kind::CONSTANT, internal::Kind::VARIABLE),
        KIND_ENUM(Kind::VARIABLE, internal::Kind::BOUND_VARIABLE),
        KIND_ENUM(Kind::SKOLEM, internal::Kind::SKOLEM),
        KIND_ENUM(Kind::SEXPR, internal::Kind::SEXPR),
        KIND_ENUM(Kind::LAMBDA, internal::Kind::LAMBDA),
        KIND_ENUM(Kind::WITNESS, internal::Kind::WITNESS),
        /* Boolean ---------------------------------------------------------- */
        KIND_ENUM(Kind::CONST_BOOLEAN, internal::Kind::CONST_BOOLEAN),
        KIND_ENUM(Kind::NOT, internal::Kind::NOT),
        KIND_ENUM(Kind::AND, internal::Kind::AND),
        KIND_ENUM(Kind::IMPLIES, internal::Kind::IMPLIES),
        KIND_ENUM(Kind::OR, internal::Kind::OR),
        KIND_ENUM(Kind::XOR, internal::Kind::XOR),
        KIND_ENUM(Kind::ITE, internal::Kind::ITE),
        /* UF --------------------------------------------------------------- */
        KIND_ENUM(Kind::APPLY_UF, internal::Kind::APPLY_UF),
        KIND_ENUM(Kind::CARDINALITY_CONSTRAINT,
                  internal::Kind::CARDINALITY_CONSTRAINT),
        KIND_ENUM(Kind::HO_APPLY, internal::Kind::HO_APPLY),
        /* Arithmetic ------------------------------------------------------- */
        KIND_ENUM(Kind::ADD, internal::Kind::ADD),
        KIND_ENUM(Kind::MULT, internal::Kind::MULT),
        KIND_ENUM(Kind::IAND, internal::Kind::IAND),
        KIND_ENUM(Kind::POW2, internal::Kind::POW2),
        KIND_ENUM(Kind::SUB, internal::Kind::SUB),
        KIND_ENUM(Kind::NEG, internal::Kind::NEG),
        KIND_ENUM(Kind::DIVISION, internal::Kind::DIVISION),
        KIND_ENUM(Kind::DIVISION_TOTAL, internal::Kind::DIVISION_TOTAL),
        KIND_ENUM(Kind::INTS_DIVISION, internal::Kind::INTS_DIVISION),
        KIND_ENUM(Kind::INTS_DIVISION_TOTAL,
                  internal::Kind::INTS_DIVISION_TOTAL),
        KIND_ENUM(Kind::INTS_MODULUS, internal::Kind::INTS_MODULUS),
        KIND_ENUM(Kind::INTS_MODULUS_TOTAL, internal::Kind::INTS_MODULUS_TOTAL),
        KIND_ENUM(Kind::ABS, internal::Kind::ABS),
        KIND_ENUM(Kind::DIVISIBLE, internal::Kind::DIVISIBLE),
        KIND_ENUM(Kind::POW, internal::Kind::POW),
        KIND_ENUM(Kind::EXPONENTIAL, internal::Kind::EXPONENTIAL),
        KIND_ENUM(Kind::SINE, internal::Kind::SINE),
        KIND_ENUM(Kind::COSINE, internal::Kind::COSINE),
        KIND_ENUM(Kind::TANGENT, internal::Kind::TANGENT),
        KIND_ENUM(Kind::COSECANT, internal::Kind::COSECANT),
        KIND_ENUM(Kind::SECANT, internal::Kind::SECANT),
        KIND_ENUM(Kind::COTANGENT, internal::Kind::COTANGENT),
        KIND_ENUM(Kind::ARCSINE, internal::Kind::ARCSINE),
        KIND_ENUM(Kind::ARCCOSINE, internal::Kind::ARCCOSINE),
        KIND_ENUM(Kind::ARCTANGENT, internal::Kind::ARCTANGENT),
        KIND_ENUM(Kind::ARCCOSECANT, internal::Kind::ARCCOSECANT),
        KIND_ENUM(Kind::ARCSECANT, internal::Kind::ARCSECANT),
        KIND_ENUM(Kind::ARCCOTANGENT, internal::Kind::ARCCOTANGENT),
        KIND_ENUM(Kind::SQRT, internal::Kind::SQRT),
        KIND_ENUM(Kind::CONST_RATIONAL, internal::Kind::CONST_RATIONAL),
        KIND_ENUM(Kind::CONST_INTEGER, internal::Kind::CONST_INTEGER),
        KIND_ENUM(Kind::LT, internal::Kind::LT),
        KIND_ENUM(Kind::LEQ, internal::Kind::LEQ),
        KIND_ENUM(Kind::GT, internal::Kind::GT),
        KIND_ENUM(Kind::GEQ, internal::Kind::GEQ),
        KIND_ENUM(Kind::IS_INTEGER, internal::Kind::IS_INTEGER),
        KIND_ENUM(Kind::TO_INTEGER, internal::Kind::TO_INTEGER),
        KIND_ENUM(Kind::TO_REAL, internal::Kind::TO_REAL),
        KIND_ENUM(Kind::PI, internal::Kind::PI),
        /* BV --------------------------------------------------------------- */
        KIND_ENUM(Kind::CONST_BITVECTOR, internal::Kind::CONST_BITVECTOR),
        KIND_ENUM(Kind::BITVECTOR_CONCAT, internal::Kind::BITVECTOR_CONCAT),
        KIND_ENUM(Kind::BITVECTOR_AND, internal::Kind::BITVECTOR_AND),
        KIND_ENUM(Kind::BITVECTOR_OR, internal::Kind::BITVECTOR_OR),
        KIND_ENUM(Kind::BITVECTOR_XOR, internal::Kind::BITVECTOR_XOR),
        KIND_ENUM(Kind::BITVECTOR_NOT, internal::Kind::BITVECTOR_NOT),
        KIND_ENUM(Kind::BITVECTOR_NAND, internal::Kind::BITVECTOR_NAND),
        KIND_ENUM(Kind::BITVECTOR_NOR, internal::Kind::BITVECTOR_NOR),
        KIND_ENUM(Kind::BITVECTOR_XNOR, internal::Kind::BITVECTOR_XNOR),
        KIND_ENUM(Kind::BITVECTOR_COMP, internal::Kind::BITVECTOR_COMP),
        KIND_ENUM(Kind::BITVECTOR_MULT, internal::Kind::BITVECTOR_MULT),
        KIND_ENUM(Kind::BITVECTOR_ADD, internal::Kind::BITVECTOR_ADD),
        KIND_ENUM(Kind::BITVECTOR_SUB, internal::Kind::BITVECTOR_SUB),
        KIND_ENUM(Kind::BITVECTOR_NEG, internal::Kind::BITVECTOR_NEG),
        KIND_ENUM(Kind::BITVECTOR_UDIV, internal::Kind::BITVECTOR_UDIV),
        KIND_ENUM(Kind::BITVECTOR_UREM, internal::Kind::BITVECTOR_UREM),
        KIND_ENUM(Kind::BITVECTOR_SDIV, internal::Kind::BITVECTOR_SDIV),
        KIND_ENUM(Kind::BITVECTOR_SREM, internal::Kind::BITVECTOR_SREM),
        KIND_ENUM(Kind::BITVECTOR_SMOD, internal::Kind::BITVECTOR_SMOD),
        KIND_ENUM(Kind::BITVECTOR_SHL, internal::Kind::BITVECTOR_SHL),
        KIND_ENUM(Kind::BITVECTOR_LSHR, internal::Kind::BITVECTOR_LSHR),
        KIND_ENUM(Kind::BITVECTOR_ASHR, internal::Kind::BITVECTOR_ASHR),
        KIND_ENUM(Kind::BITVECTOR_ULT, internal::Kind::BITVECTOR_ULT),
        KIND_ENUM(Kind::BITVECTOR_ULE, internal::Kind::BITVECTOR_ULE),
        KIND_ENUM(Kind::BITVECTOR_UGT, internal::Kind::BITVECTOR_UGT),
        KIND_ENUM(Kind::BITVECTOR_UGE, internal::Kind::BITVECTOR_UGE),
        KIND_ENUM(Kind::BITVECTOR_SLT, internal::Kind::BITVECTOR_SLT),
        KIND_ENUM(Kind::BITVECTOR_SLE, internal::Kind::BITVECTOR_SLE),
        KIND_ENUM(Kind::BITVECTOR_SGT, internal::Kind::BITVECTOR_SGT),
        KIND_ENUM(Kind::BITVECTOR_SGE, internal::Kind::BITVECTOR_SGE),
        KIND_ENUM(Kind::BITVECTOR_ULTBV, internal::Kind::BITVECTOR_ULTBV),
        KIND_ENUM(Kind::BITVECTOR_SLTBV, internal::Kind::BITVECTOR_SLTBV),
        KIND_ENUM(Kind::BITVECTOR_NEGO, internal::Kind::BITVECTOR_NEGO),
        KIND_ENUM(Kind::BITVECTOR_UADDO, internal::Kind::BITVECTOR_UADDO),
        KIND_ENUM(Kind::BITVECTOR_SADDO, internal::Kind::BITVECTOR_SADDO),
        KIND_ENUM(Kind::BITVECTOR_UMULO, internal::Kind::BITVECTOR_UMULO),
        KIND_ENUM(Kind::BITVECTOR_SMULO, internal::Kind::BITVECTOR_SMULO),
        KIND_ENUM(Kind::BITVECTOR_USUBO, internal::Kind::BITVECTOR_USUBO),
        KIND_ENUM(Kind::BITVECTOR_SSUBO, internal::Kind::BITVECTOR_SSUBO),
        KIND_ENUM(Kind::BITVECTOR_SDIVO, internal::Kind::BITVECTOR_SDIVO),
        KIND_ENUM(Kind::BITVECTOR_ITE, internal::Kind::BITVECTOR_ITE),
        KIND_ENUM(Kind::BITVECTOR_REDOR, internal::Kind::BITVECTOR_REDOR),
        KIND_ENUM(Kind::BITVECTOR_REDAND, internal::Kind::BITVECTOR_REDAND),
        KIND_ENUM(Kind::BITVECTOR_EXTRACT, internal::Kind::BITVECTOR_EXTRACT),
        KIND_ENUM(Kind::BITVECTOR_REPEAT, internal::Kind::BITVECTOR_REPEAT),
        KIND_ENUM(Kind::BITVECTOR_ZERO_EXTEND,
                  internal::Kind::BITVECTOR_ZERO_EXTEND),
        KIND_ENUM(Kind::BITVECTOR_SIGN_EXTEND,
                  internal::Kind::BITVECTOR_SIGN_EXTEND),
        KIND_ENUM(Kind::BITVECTOR_ROTATE_LEFT,
                  internal::Kind::BITVECTOR_ROTATE_LEFT),
        KIND_ENUM(Kind::BITVECTOR_ROTATE_RIGHT,
                  internal::Kind::BITVECTOR_ROTATE_RIGHT),
        KIND_ENUM(Kind::INT_TO_BITVECTOR, internal::Kind::INT_TO_BITVECTOR),
        KIND_ENUM(Kind::BITVECTOR_UBV_TO_INT,
                  internal::Kind::BITVECTOR_UBV_TO_INT),
        KIND_ENUM(Kind::BITVECTOR_SBV_TO_INT,
                  internal::Kind::BITVECTOR_SBV_TO_INT),
        // note we silently change BITVECTOR_TO_NAT to BITVECTOR_UBV_TO_INT
        KIND_ENUM(Kind::BITVECTOR_TO_NAT, internal::Kind::BITVECTOR_UBV_TO_INT),
        KIND_ENUM(Kind::BITVECTOR_FROM_BOOLS,
                  internal::Kind::BITVECTOR_FROM_BOOLS),
        KIND_ENUM(Kind::BITVECTOR_BIT, internal::Kind::BITVECTOR_BIT),
        /* Finite Fields --------------------------------------------------- */
        KIND_ENUM(Kind::CONST_FINITE_FIELD, internal::Kind::CONST_FINITE_FIELD),
        KIND_ENUM(Kind::FINITE_FIELD_BITSUM,
                  internal::Kind::FINITE_FIELD_BITSUM),
        KIND_ENUM(Kind::FINITE_FIELD_MULT, internal::Kind::FINITE_FIELD_MULT),
        KIND_ENUM(Kind::FINITE_FIELD_ADD, internal::Kind::FINITE_FIELD_ADD),
        KIND_ENUM(Kind::FINITE_FIELD_NEG, internal::Kind::FINITE_FIELD_NEG),
        /* FP --------------------------------------------------------------- */
        KIND_ENUM(Kind::CONST_FLOATINGPOINT,
                  internal::Kind::CONST_FLOATINGPOINT),
        KIND_ENUM(Kind::CONST_ROUNDINGMODE, internal::Kind::CONST_ROUNDINGMODE),
        KIND_ENUM(Kind::FLOATINGPOINT_FP, internal::Kind::FLOATINGPOINT_FP),
        KIND_ENUM(Kind::FLOATINGPOINT_EQ, internal::Kind::FLOATINGPOINT_EQ),
        KIND_ENUM(Kind::FLOATINGPOINT_ABS, internal::Kind::FLOATINGPOINT_ABS),
        KIND_ENUM(Kind::FLOATINGPOINT_NEG, internal::Kind::FLOATINGPOINT_NEG),
        KIND_ENUM(Kind::FLOATINGPOINT_ADD, internal::Kind::FLOATINGPOINT_ADD),
        KIND_ENUM(Kind::FLOATINGPOINT_SUB, internal::Kind::FLOATINGPOINT_SUB),
        KIND_ENUM(Kind::FLOATINGPOINT_MULT, internal::Kind::FLOATINGPOINT_MULT),
        KIND_ENUM(Kind::FLOATINGPOINT_DIV, internal::Kind::FLOATINGPOINT_DIV),
        KIND_ENUM(Kind::FLOATINGPOINT_FMA, internal::Kind::FLOATINGPOINT_FMA),
        KIND_ENUM(Kind::FLOATINGPOINT_SQRT, internal::Kind::FLOATINGPOINT_SQRT),
        KIND_ENUM(Kind::FLOATINGPOINT_REM, internal::Kind::FLOATINGPOINT_REM),
        KIND_ENUM(Kind::FLOATINGPOINT_RTI, internal::Kind::FLOATINGPOINT_RTI),
        KIND_ENUM(Kind::FLOATINGPOINT_MIN, internal::Kind::FLOATINGPOINT_MIN),
        KIND_ENUM(Kind::FLOATINGPOINT_MAX, internal::Kind::FLOATINGPOINT_MAX),
        KIND_ENUM(Kind::FLOATINGPOINT_LEQ, internal::Kind::FLOATINGPOINT_LEQ),
        KIND_ENUM(Kind::FLOATINGPOINT_LT, internal::Kind::FLOATINGPOINT_LT),
        KIND_ENUM(Kind::FLOATINGPOINT_GEQ, internal::Kind::FLOATINGPOINT_GEQ),
        KIND_ENUM(Kind::FLOATINGPOINT_GT, internal::Kind::FLOATINGPOINT_GT),
        KIND_ENUM(Kind::FLOATINGPOINT_IS_NORMAL,
                  internal::Kind::FLOATINGPOINT_IS_NORMAL),
        KIND_ENUM(Kind::FLOATINGPOINT_IS_SUBNORMAL,
                  internal::Kind::FLOATINGPOINT_IS_SUBNORMAL),
        KIND_ENUM(Kind::FLOATINGPOINT_IS_ZERO,
                  internal::Kind::FLOATINGPOINT_IS_ZERO),
        KIND_ENUM(Kind::FLOATINGPOINT_IS_INF,
                  internal::Kind::FLOATINGPOINT_IS_INF),
        KIND_ENUM(Kind::FLOATINGPOINT_IS_NAN,
                  internal::Kind::FLOATINGPOINT_IS_NAN),
        KIND_ENUM(Kind::FLOATINGPOINT_IS_NEG,
                  internal::Kind::FLOATINGPOINT_IS_NEG),
        KIND_ENUM(Kind::FLOATINGPOINT_IS_POS,
                  internal::Kind::FLOATINGPOINT_IS_POS),
        KIND_ENUM(Kind::FLOATINGPOINT_TO_FP_FROM_FP,
                  internal::Kind::FLOATINGPOINT_TO_FP_FROM_FP),
        KIND_ENUM(Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV,
                  internal::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV),
        KIND_ENUM(Kind::FLOATINGPOINT_TO_FP_FROM_REAL,
                  internal::Kind::FLOATINGPOINT_TO_FP_FROM_REAL),
        KIND_ENUM(Kind::FLOATINGPOINT_TO_FP_FROM_SBV,
                  internal::Kind::FLOATINGPOINT_TO_FP_FROM_SBV),
        KIND_ENUM(Kind::FLOATINGPOINT_TO_FP_FROM_UBV,
                  internal::Kind::FLOATINGPOINT_TO_FP_FROM_UBV),
        KIND_ENUM(Kind::FLOATINGPOINT_TO_UBV,
                  internal::Kind::FLOATINGPOINT_TO_UBV),
        KIND_ENUM(Kind::FLOATINGPOINT_TO_SBV,
                  internal::Kind::FLOATINGPOINT_TO_SBV),
        KIND_ENUM(Kind::FLOATINGPOINT_TO_REAL,
                  internal::Kind::FLOATINGPOINT_TO_REAL),
        /* Arrays ----------------------------------------------------------- */
        KIND_ENUM(Kind::SELECT, internal::Kind::SELECT),
        KIND_ENUM(Kind::STORE, internal::Kind::STORE),
        KIND_ENUM(Kind::CONST_ARRAY, internal::Kind::STORE_ALL),
        KIND_ENUM(Kind::EQ_RANGE, internal::Kind::EQ_RANGE),
        /* Datatypes -------------------------------------------------------- */
        KIND_ENUM(Kind::APPLY_SELECTOR, internal::Kind::APPLY_SELECTOR),
        KIND_ENUM(Kind::APPLY_CONSTRUCTOR, internal::Kind::APPLY_CONSTRUCTOR),
        KIND_ENUM(Kind::APPLY_TESTER, internal::Kind::APPLY_TESTER),
        KIND_ENUM(Kind::APPLY_UPDATER, internal::Kind::APPLY_UPDATER),
        KIND_ENUM(Kind::MATCH, internal::Kind::MATCH),
        KIND_ENUM(Kind::MATCH_CASE, internal::Kind::MATCH_CASE),
        KIND_ENUM(Kind::MATCH_BIND_CASE, internal::Kind::MATCH_BIND_CASE),
        KIND_ENUM(Kind::TUPLE_PROJECT, internal::Kind::TUPLE_PROJECT),
        KIND_ENUM(Kind::NULLABLE_LIFT, internal::Kind::NULLABLE_LIFT),
        /* Separation Logic ------------------------------------------------- */
        KIND_ENUM(Kind::SEP_NIL, internal::Kind::SEP_NIL),
        KIND_ENUM(Kind::SEP_EMP, internal::Kind::SEP_EMP),
        KIND_ENUM(Kind::SEP_PTO, internal::Kind::SEP_PTO),
        KIND_ENUM(Kind::SEP_STAR, internal::Kind::SEP_STAR),
        KIND_ENUM(Kind::SEP_WAND, internal::Kind::SEP_WAND),
        /* Sets ------------------------------------------------------------- */
        KIND_ENUM(Kind::SET_EMPTY, internal::Kind::SET_EMPTY),
        KIND_ENUM(Kind::SET_UNION, internal::Kind::SET_UNION),
        KIND_ENUM(Kind::SET_INTER, internal::Kind::SET_INTER),
        KIND_ENUM(Kind::SET_MINUS, internal::Kind::SET_MINUS),
        KIND_ENUM(Kind::SET_SUBSET, internal::Kind::SET_SUBSET),
        KIND_ENUM(Kind::SET_MEMBER, internal::Kind::SET_MEMBER),
        KIND_ENUM(Kind::SET_SINGLETON, internal::Kind::SET_SINGLETON),
        KIND_ENUM(Kind::SET_INSERT, internal::Kind::SET_INSERT),
        KIND_ENUM(Kind::SET_CARD, internal::Kind::SET_CARD),
        KIND_ENUM(Kind::SET_COMPLEMENT, internal::Kind::SET_COMPLEMENT),
        KIND_ENUM(Kind::SET_UNIVERSE, internal::Kind::SET_UNIVERSE),
        KIND_ENUM(Kind::SET_COMPREHENSION, internal::Kind::SET_COMPREHENSION),
        KIND_ENUM(Kind::SET_CHOOSE, internal::Kind::SET_CHOOSE),
        KIND_ENUM(Kind::SET_IS_EMPTY, internal::Kind::SET_IS_EMPTY),
        KIND_ENUM(Kind::SET_IS_SINGLETON, internal::Kind::SET_IS_SINGLETON),
        KIND_ENUM(Kind::SET_MAP, internal::Kind::SET_MAP),
        KIND_ENUM(Kind::SET_FILTER, internal::Kind::SET_FILTER),
        KIND_ENUM(Kind::SET_ALL, internal::Kind::SET_ALL),
        KIND_ENUM(Kind::SET_SOME, internal::Kind::SET_SOME),
        KIND_ENUM(Kind::SET_FOLD, internal::Kind::SET_FOLD),
        /* Relations -------------------------------------------------------- */
        KIND_ENUM(Kind::RELATION_JOIN, internal::Kind::RELATION_JOIN),
        KIND_ENUM(Kind::RELATION_TABLE_JOIN,
                  internal::Kind::RELATION_TABLE_JOIN),
        KIND_ENUM(Kind::RELATION_PRODUCT, internal::Kind::RELATION_PRODUCT),
        KIND_ENUM(Kind::RELATION_TRANSPOSE, internal::Kind::RELATION_TRANSPOSE),
        KIND_ENUM(Kind::RELATION_TCLOSURE, internal::Kind::RELATION_TCLOSURE),
        KIND_ENUM(Kind::RELATION_JOIN_IMAGE,
                  internal::Kind::RELATION_JOIN_IMAGE),
        KIND_ENUM(Kind::RELATION_IDEN, internal::Kind::RELATION_IDEN),
        KIND_ENUM(Kind::RELATION_GROUP, internal::Kind::RELATION_GROUP),
        KIND_ENUM(Kind::RELATION_AGGREGATE, internal::Kind::RELATION_AGGREGATE),
        KIND_ENUM(Kind::RELATION_PROJECT, internal::Kind::RELATION_PROJECT),
        /* Bags ------------------------------------------------------------- */
        KIND_ENUM(Kind::BAG_UNION_MAX, internal::Kind::BAG_UNION_MAX),
        KIND_ENUM(Kind::BAG_UNION_DISJOINT, internal::Kind::BAG_UNION_DISJOINT),
        KIND_ENUM(Kind::BAG_INTER_MIN, internal::Kind::BAG_INTER_MIN),
        KIND_ENUM(Kind::BAG_DIFFERENCE_SUBTRACT,
                  internal::Kind::BAG_DIFFERENCE_SUBTRACT),
        KIND_ENUM(Kind::BAG_DIFFERENCE_REMOVE,
                  internal::Kind::BAG_DIFFERENCE_REMOVE),
        KIND_ENUM(Kind::BAG_SUBBAG, internal::Kind::BAG_SUBBAG),
        KIND_ENUM(Kind::BAG_COUNT, internal::Kind::BAG_COUNT),
        KIND_ENUM(Kind::BAG_MEMBER, internal::Kind::BAG_MEMBER),
        KIND_ENUM(Kind::BAG_SETOF, internal::Kind::BAG_SETOF),
        KIND_ENUM(Kind::BAG_MAKE, internal::Kind::BAG_MAKE),
        KIND_ENUM(Kind::BAG_EMPTY, internal::Kind::BAG_EMPTY),
        KIND_ENUM(Kind::BAG_CARD, internal::Kind::BAG_CARD),
        KIND_ENUM(Kind::BAG_CHOOSE, internal::Kind::BAG_CHOOSE),
        KIND_ENUM(Kind::BAG_MAP, internal::Kind::BAG_MAP),
        KIND_ENUM(Kind::BAG_FILTER, internal::Kind::BAG_FILTER),
        KIND_ENUM(Kind::BAG_ALL, internal::Kind::BAG_ALL),
        KIND_ENUM(Kind::BAG_SOME, internal::Kind::BAG_SOME),
        KIND_ENUM(Kind::BAG_FOLD, internal::Kind::BAG_FOLD),
        KIND_ENUM(Kind::BAG_PARTITION, internal::Kind::BAG_PARTITION),
        KIND_ENUM(Kind::TABLE_PRODUCT, internal::Kind::TABLE_PRODUCT),
        KIND_ENUM(Kind::TABLE_PROJECT, internal::Kind::TABLE_PROJECT),
        KIND_ENUM(Kind::TABLE_AGGREGATE, internal::Kind::TABLE_AGGREGATE),
        KIND_ENUM(Kind::TABLE_JOIN, internal::Kind::TABLE_JOIN),
        KIND_ENUM(Kind::TABLE_GROUP, internal::Kind::TABLE_GROUP),
        /* Strings ---------------------------------------------------------- */
        KIND_ENUM(Kind::STRING_CONCAT, internal::Kind::STRING_CONCAT),
        KIND_ENUM(Kind::STRING_IN_REGEXP, internal::Kind::STRING_IN_REGEXP),
        KIND_ENUM(Kind::STRING_LENGTH, internal::Kind::STRING_LENGTH),
        KIND_ENUM(Kind::STRING_SUBSTR, internal::Kind::STRING_SUBSTR),
        KIND_ENUM(Kind::STRING_UPDATE, internal::Kind::STRING_UPDATE),
        KIND_ENUM(Kind::STRING_CHARAT, internal::Kind::STRING_CHARAT),
        KIND_ENUM(Kind::STRING_CONTAINS, internal::Kind::STRING_CONTAINS),
        KIND_ENUM(Kind::STRING_INDEXOF, internal::Kind::STRING_INDEXOF),
        KIND_ENUM(Kind::STRING_INDEXOF_RE, internal::Kind::STRING_INDEXOF_RE),
        KIND_ENUM(Kind::STRING_REPLACE, internal::Kind::STRING_REPLACE),
        KIND_ENUM(Kind::STRING_REPLACE_ALL, internal::Kind::STRING_REPLACE_ALL),
        KIND_ENUM(Kind::STRING_REPLACE_RE, internal::Kind::STRING_REPLACE_RE),
        KIND_ENUM(Kind::STRING_REPLACE_RE_ALL,
                  internal::Kind::STRING_REPLACE_RE_ALL),
        KIND_ENUM(Kind::STRING_TO_LOWER, internal::Kind::STRING_TO_LOWER),
        KIND_ENUM(Kind::STRING_TO_UPPER, internal::Kind::STRING_TO_UPPER),
        KIND_ENUM(Kind::STRING_REV, internal::Kind::STRING_REV),
        KIND_ENUM(Kind::STRING_FROM_CODE, internal::Kind::STRING_FROM_CODE),
        KIND_ENUM(Kind::STRING_TO_CODE, internal::Kind::STRING_TO_CODE),
        KIND_ENUM(Kind::STRING_LT, internal::Kind::STRING_LT),
        KIND_ENUM(Kind::STRING_LEQ, internal::Kind::STRING_LEQ),
        KIND_ENUM(Kind::STRING_PREFIX, internal::Kind::STRING_PREFIX),
        KIND_ENUM(Kind::STRING_SUFFIX, internal::Kind::STRING_SUFFIX),
        KIND_ENUM(Kind::STRING_IS_DIGIT, internal::Kind::STRING_IS_DIGIT),
        KIND_ENUM(Kind::STRING_FROM_INT, internal::Kind::STRING_ITOS),
        KIND_ENUM(Kind::STRING_TO_INT, internal::Kind::STRING_STOI),
        KIND_ENUM(Kind::CONST_STRING, internal::Kind::CONST_STRING),
        KIND_ENUM(Kind::STRING_TO_REGEXP, internal::Kind::STRING_TO_REGEXP),
        KIND_ENUM(Kind::REGEXP_CONCAT, internal::Kind::REGEXP_CONCAT),
        KIND_ENUM(Kind::REGEXP_UNION, internal::Kind::REGEXP_UNION),
        KIND_ENUM(Kind::REGEXP_INTER, internal::Kind::REGEXP_INTER),
        KIND_ENUM(Kind::REGEXP_DIFF, internal::Kind::REGEXP_DIFF),
        KIND_ENUM(Kind::REGEXP_STAR, internal::Kind::REGEXP_STAR),
        KIND_ENUM(Kind::REGEXP_PLUS, internal::Kind::REGEXP_PLUS),
        KIND_ENUM(Kind::REGEXP_OPT, internal::Kind::REGEXP_OPT),
        KIND_ENUM(Kind::REGEXP_RANGE, internal::Kind::REGEXP_RANGE),
        KIND_ENUM(Kind::REGEXP_REPEAT, internal::Kind::REGEXP_REPEAT),
        KIND_ENUM(Kind::REGEXP_LOOP, internal::Kind::REGEXP_LOOP),
        KIND_ENUM(Kind::REGEXP_NONE, internal::Kind::REGEXP_NONE),
        KIND_ENUM(Kind::REGEXP_ALL, internal::Kind::REGEXP_ALL),
        KIND_ENUM(Kind::REGEXP_ALLCHAR, internal::Kind::REGEXP_ALLCHAR),
        KIND_ENUM(Kind::REGEXP_COMPLEMENT, internal::Kind::REGEXP_COMPLEMENT),
        // maps to the same kind as the string versions
        KIND_ENUM(Kind::SEQ_CONCAT, internal::Kind::STRING_CONCAT),
        KIND_ENUM(Kind::SEQ_LENGTH, internal::Kind::STRING_LENGTH),
        KIND_ENUM(Kind::SEQ_EXTRACT, internal::Kind::STRING_SUBSTR),
        KIND_ENUM(Kind::SEQ_UPDATE, internal::Kind::STRING_UPDATE),
        KIND_ENUM(Kind::SEQ_AT, internal::Kind::STRING_CHARAT),
        KIND_ENUM(Kind::SEQ_CONTAINS, internal::Kind::STRING_CONTAINS),
        KIND_ENUM(Kind::SEQ_INDEXOF, internal::Kind::STRING_INDEXOF),
        KIND_ENUM(Kind::SEQ_REPLACE, internal::Kind::STRING_REPLACE),
        KIND_ENUM(Kind::SEQ_REPLACE_ALL, internal::Kind::STRING_REPLACE_ALL),
        KIND_ENUM(Kind::SEQ_REV, internal::Kind::STRING_REV),
        KIND_ENUM(Kind::SEQ_PREFIX, internal::Kind::STRING_PREFIX),
        KIND_ENUM(Kind::SEQ_SUFFIX, internal::Kind::STRING_SUFFIX),
        KIND_ENUM(Kind::CONST_SEQUENCE, internal::Kind::CONST_SEQUENCE),
        KIND_ENUM(Kind::SEQ_UNIT, internal::Kind::SEQ_UNIT),
        KIND_ENUM(Kind::SEQ_NTH, internal::Kind::SEQ_NTH),
        /* Quantifiers ------------------------------------------------------ */
        KIND_ENUM(Kind::FORALL, internal::Kind::FORALL),
        KIND_ENUM(Kind::EXISTS, internal::Kind::EXISTS),
        KIND_ENUM(Kind::VARIABLE_LIST, internal::Kind::BOUND_VAR_LIST),
        KIND_ENUM(Kind::INST_PATTERN, internal::Kind::INST_PATTERN),
        KIND_ENUM(Kind::INST_NO_PATTERN, internal::Kind::INST_NO_PATTERN),
        KIND_ENUM(Kind::INST_POOL, internal::Kind::INST_POOL),
        KIND_ENUM(Kind::INST_ADD_TO_POOL, internal::Kind::INST_ADD_TO_POOL),
        KIND_ENUM(Kind::SKOLEM_ADD_TO_POOL, internal::Kind::SKOLEM_ADD_TO_POOL),
        KIND_ENUM(Kind::INST_ATTRIBUTE, internal::Kind::INST_ATTRIBUTE),
        KIND_ENUM(Kind::INST_PATTERN_LIST, internal::Kind::INST_PATTERN_LIST),
        KIND_ENUM(Kind::LAST_KIND, internal::Kind::LAST_KIND),
    };

/* -------------------------------------------------------------------------- */
/* SortKind                                                                   */
/* -------------------------------------------------------------------------- */

#define SORT_KIND_ENUM(external_name, internal_name)                          \
  {                                                                           \
    external_name,                                                            \
        std::make_pair(internal_name, std::string(#external_name).substr(10)) \
  }

/* Mapping from external (API) kind to internal kind. */
const static std::unordered_map<SortKind,
                                std::pair<internal::Kind, std::string>>
    s_sort_kinds{
        SORT_KIND_ENUM(SortKind::INTERNAL_SORT_KIND,
                       internal::Kind::UNDEFINED_KIND),
        SORT_KIND_ENUM(SortKind::UNDEFINED_SORT_KIND,
                       internal::Kind::UNDEFINED_KIND),
        SORT_KIND_ENUM(SortKind::NULL_SORT, internal::Kind::NULL_EXPR),
        /* Sorts ------------------------------------------------------------ */
        // Note that many entries in this map (e.g. for type constants) are
        // given only for completeness and are not used since we don't
        // construct sorts based on SortKind.
        SORT_KIND_ENUM(SortKind::ABSTRACT_SORT, internal::Kind::ABSTRACT_TYPE),
        SORT_KIND_ENUM(SortKind::ARRAY_SORT, internal::Kind::ARRAY_TYPE),
        SORT_KIND_ENUM(SortKind::BAG_SORT, internal::Kind::BAG_TYPE),
        SORT_KIND_ENUM(SortKind::BITVECTOR_SORT,
                       internal::Kind::BITVECTOR_TYPE),
        SORT_KIND_ENUM(SortKind::BOOLEAN_SORT, internal::Kind::TYPE_CONSTANT),
        SORT_KIND_ENUM(SortKind::DATATYPE_SORT, internal::Kind::DATATYPE_TYPE),
        SORT_KIND_ENUM(SortKind::FINITE_FIELD_SORT,
                       internal::Kind::FINITE_FIELD_TYPE),
        SORT_KIND_ENUM(SortKind::FLOATINGPOINT_SORT,
                       internal::Kind::FLOATINGPOINT_TYPE),
        SORT_KIND_ENUM(SortKind::FUNCTION_SORT, internal::Kind::FUNCTION_TYPE),
        SORT_KIND_ENUM(SortKind::INTEGER_SORT, internal::Kind::TYPE_CONSTANT),
        SORT_KIND_ENUM(SortKind::REAL_SORT, internal::Kind::TYPE_CONSTANT),
        SORT_KIND_ENUM(SortKind::REGLAN_SORT, internal::Kind::TYPE_CONSTANT),
        SORT_KIND_ENUM(SortKind::ROUNDINGMODE_SORT,
                       internal::Kind::TYPE_CONSTANT),
        SORT_KIND_ENUM(SortKind::SEQUENCE_SORT, internal::Kind::SEQUENCE_TYPE),
        SORT_KIND_ENUM(SortKind::SET_SORT, internal::Kind::SET_TYPE),
        SORT_KIND_ENUM(SortKind::STRING_SORT, internal::Kind::TYPE_CONSTANT),
        SORT_KIND_ENUM(SortKind::TUPLE_SORT, internal::Kind::TUPLE_TYPE),
        SORT_KIND_ENUM(SortKind::NULLABLE_SORT, internal::Kind::NULLABLE_TYPE),
        SORT_KIND_ENUM(SortKind::UNINTERPRETED_SORT, internal::Kind::SORT_TYPE),
        SORT_KIND_ENUM(SortKind::LAST_SORT_KIND, internal::Kind::LAST_KIND),
    };

/* Mapping from internal kind to external (API) kind. */
const static std::unordered_map<internal::Kind,
                                Kind,
                                internal::kind::KindHashFunction>
    s_kinds_internal{
        {internal::Kind::UNDEFINED_KIND, Kind::UNDEFINED_KIND},
        {internal::Kind::NULL_EXPR, Kind::NULL_TERM},
        /* Builtin --------------------------------------------------------- */
        {internal::Kind::UNINTERPRETED_SORT_VALUE,
         Kind::UNINTERPRETED_SORT_VALUE},
        {internal::Kind::EQUAL, Kind::EQUAL},
        {internal::Kind::DISTINCT, Kind::DISTINCT},
        {internal::Kind::VARIABLE, Kind::CONSTANT},
        {internal::Kind::SKOLEM, Kind::SKOLEM},
        {internal::Kind::BOUND_VARIABLE, Kind::VARIABLE},
        {internal::Kind::SEXPR, Kind::SEXPR},
        {internal::Kind::LAMBDA, Kind::LAMBDA},
        {internal::Kind::WITNESS, Kind::WITNESS},
        /* Boolean --------------------------------------------------------- */
        {internal::Kind::CONST_BOOLEAN, Kind::CONST_BOOLEAN},
        {internal::Kind::NOT, Kind::NOT},
        {internal::Kind::AND, Kind::AND},
        {internal::Kind::IMPLIES, Kind::IMPLIES},
        {internal::Kind::OR, Kind::OR},
        {internal::Kind::XOR, Kind::XOR},
        {internal::Kind::ITE, Kind::ITE},
        /* UF -------------------------------------------------------------- */
        {internal::Kind::APPLY_UF, Kind::APPLY_UF},
        {internal::Kind::CARDINALITY_CONSTRAINT, Kind::CARDINALITY_CONSTRAINT},
        {internal::Kind::HO_APPLY, Kind::HO_APPLY},
        /* Arithmetic ------------------------------------------------------ */
        {internal::Kind::ADD, Kind::ADD},
        {internal::Kind::MULT, Kind::MULT},
        {internal::Kind::NONLINEAR_MULT, Kind::MULT},
        {internal::Kind::IAND, Kind::IAND},
        {internal::Kind::POW2, Kind::POW2},
        {internal::Kind::SUB, Kind::SUB},
        {internal::Kind::NEG, Kind::NEG},
        {internal::Kind::DIVISION, Kind::DIVISION},
        {internal::Kind::DIVISION_TOTAL, Kind::DIVISION_TOTAL},
        {internal::Kind::INTS_DIVISION, Kind::INTS_DIVISION},
        {internal::Kind::INTS_DIVISION_TOTAL, Kind::INTS_DIVISION_TOTAL},
        {internal::Kind::INTS_MODULUS, Kind::INTS_MODULUS},
        {internal::Kind::INTS_MODULUS_TOTAL, Kind::INTS_MODULUS_TOTAL},
        {internal::Kind::ABS, Kind::ABS},
        {internal::Kind::DIVISIBLE, Kind::DIVISIBLE},
        {internal::Kind::POW, Kind::POW},
        {internal::Kind::EXPONENTIAL, Kind::EXPONENTIAL},
        {internal::Kind::SINE, Kind::SINE},
        {internal::Kind::COSINE, Kind::COSINE},
        {internal::Kind::TANGENT, Kind::TANGENT},
        {internal::Kind::COSECANT, Kind::COSECANT},
        {internal::Kind::SECANT, Kind::SECANT},
        {internal::Kind::COTANGENT, Kind::COTANGENT},
        {internal::Kind::ARCSINE, Kind::ARCSINE},
        {internal::Kind::ARCCOSINE, Kind::ARCCOSINE},
        {internal::Kind::ARCTANGENT, Kind::ARCTANGENT},
        {internal::Kind::ARCCOSECANT, Kind::ARCCOSECANT},
        {internal::Kind::ARCSECANT, Kind::ARCSECANT},
        {internal::Kind::ARCCOTANGENT, Kind::ARCCOTANGENT},
        {internal::Kind::SQRT, Kind::SQRT},
        {internal::Kind::DIVISIBLE_OP, Kind::DIVISIBLE},
        {internal::Kind::CONST_RATIONAL, Kind::CONST_RATIONAL},
        {internal::Kind::CONST_INTEGER, Kind::CONST_INTEGER},
        {internal::Kind::LT, Kind::LT},
        {internal::Kind::LEQ, Kind::LEQ},
        {internal::Kind::GT, Kind::GT},
        {internal::Kind::GEQ, Kind::GEQ},
        {internal::Kind::IS_INTEGER, Kind::IS_INTEGER},
        {internal::Kind::TO_INTEGER, Kind::TO_INTEGER},
        {internal::Kind::TO_REAL, Kind::TO_REAL},
        {internal::Kind::PI, Kind::PI},
        {internal::Kind::IAND_OP, Kind::IAND},
        /* BV -------------------------------------------------------------- */
        {internal::Kind::CONST_BITVECTOR, Kind::CONST_BITVECTOR},
        {internal::Kind::BITVECTOR_CONCAT, Kind::BITVECTOR_CONCAT},
        {internal::Kind::BITVECTOR_AND, Kind::BITVECTOR_AND},
        {internal::Kind::BITVECTOR_OR, Kind::BITVECTOR_OR},
        {internal::Kind::BITVECTOR_XOR, Kind::BITVECTOR_XOR},
        {internal::Kind::BITVECTOR_NOT, Kind::BITVECTOR_NOT},
        {internal::Kind::BITVECTOR_NAND, Kind::BITVECTOR_NAND},
        {internal::Kind::BITVECTOR_NOR, Kind::BITVECTOR_NOR},
        {internal::Kind::BITVECTOR_XNOR, Kind::BITVECTOR_XNOR},
        {internal::Kind::BITVECTOR_COMP, Kind::BITVECTOR_COMP},
        {internal::Kind::BITVECTOR_MULT, Kind::BITVECTOR_MULT},
        {internal::Kind::BITVECTOR_ADD, Kind::BITVECTOR_ADD},
        {internal::Kind::BITVECTOR_SUB, Kind::BITVECTOR_SUB},
        {internal::Kind::BITVECTOR_NEG, Kind::BITVECTOR_NEG},
        {internal::Kind::BITVECTOR_UDIV, Kind::BITVECTOR_UDIV},
        {internal::Kind::BITVECTOR_UREM, Kind::BITVECTOR_UREM},
        {internal::Kind::BITVECTOR_SDIV, Kind::BITVECTOR_SDIV},
        {internal::Kind::BITVECTOR_SREM, Kind::BITVECTOR_SREM},
        {internal::Kind::BITVECTOR_SMOD, Kind::BITVECTOR_SMOD},
        {internal::Kind::BITVECTOR_SHL, Kind::BITVECTOR_SHL},
        {internal::Kind::BITVECTOR_LSHR, Kind::BITVECTOR_LSHR},
        {internal::Kind::BITVECTOR_ASHR, Kind::BITVECTOR_ASHR},
        {internal::Kind::BITVECTOR_ULT, Kind::BITVECTOR_ULT},
        {internal::Kind::BITVECTOR_ULE, Kind::BITVECTOR_ULE},
        {internal::Kind::BITVECTOR_UGT, Kind::BITVECTOR_UGT},
        {internal::Kind::BITVECTOR_UGE, Kind::BITVECTOR_UGE},
        {internal::Kind::BITVECTOR_SLT, Kind::BITVECTOR_SLT},
        {internal::Kind::BITVECTOR_SLE, Kind::BITVECTOR_SLE},
        {internal::Kind::BITVECTOR_SGT, Kind::BITVECTOR_SGT},
        {internal::Kind::BITVECTOR_SGE, Kind::BITVECTOR_SGE},
        {internal::Kind::BITVECTOR_ULTBV, Kind::BITVECTOR_ULTBV},
        {internal::Kind::BITVECTOR_SLTBV, Kind::BITVECTOR_SLTBV},
        {internal::Kind::BITVECTOR_NEGO, Kind::BITVECTOR_NEGO},
        {internal::Kind::BITVECTOR_UADDO, Kind::BITVECTOR_UADDO},
        {internal::Kind::BITVECTOR_SADDO, Kind::BITVECTOR_SADDO},
        {internal::Kind::BITVECTOR_UMULO, Kind::BITVECTOR_UMULO},
        {internal::Kind::BITVECTOR_SMULO, Kind::BITVECTOR_SMULO},
        {internal::Kind::BITVECTOR_USUBO, Kind::BITVECTOR_USUBO},
        {internal::Kind::BITVECTOR_SSUBO, Kind::BITVECTOR_SSUBO},
        {internal::Kind::BITVECTOR_SDIVO, Kind::BITVECTOR_SDIVO},
        {internal::Kind::BITVECTOR_ITE, Kind::BITVECTOR_ITE},
        {internal::Kind::BITVECTOR_REDOR, Kind::BITVECTOR_REDOR},
        {internal::Kind::BITVECTOR_REDAND, Kind::BITVECTOR_REDAND},
        {internal::Kind::BITVECTOR_BIT_OP, Kind::BITVECTOR_BIT},
        {internal::Kind::BITVECTOR_EXTRACT_OP, Kind::BITVECTOR_EXTRACT},
        {internal::Kind::BITVECTOR_REPEAT_OP, Kind::BITVECTOR_REPEAT},
        {internal::Kind::BITVECTOR_ZERO_EXTEND_OP, Kind::BITVECTOR_ZERO_EXTEND},
        {internal::Kind::BITVECTOR_SIGN_EXTEND_OP, Kind::BITVECTOR_SIGN_EXTEND},
        {internal::Kind::BITVECTOR_ROTATE_LEFT_OP, Kind::BITVECTOR_ROTATE_LEFT},
        {internal::Kind::BITVECTOR_ROTATE_RIGHT_OP,
         Kind::BITVECTOR_ROTATE_RIGHT},
        {internal::Kind::BITVECTOR_EXTRACT, Kind::BITVECTOR_EXTRACT},
        {internal::Kind::BITVECTOR_REPEAT, Kind::BITVECTOR_REPEAT},
        {internal::Kind::BITVECTOR_ZERO_EXTEND, Kind::BITVECTOR_ZERO_EXTEND},
        {internal::Kind::BITVECTOR_SIGN_EXTEND, Kind::BITVECTOR_SIGN_EXTEND},
        {internal::Kind::BITVECTOR_ROTATE_LEFT, Kind::BITVECTOR_ROTATE_LEFT},
        {internal::Kind::BITVECTOR_ROTATE_RIGHT, Kind::BITVECTOR_ROTATE_RIGHT},
        {internal::Kind::INT_TO_BITVECTOR_OP, Kind::INT_TO_BITVECTOR},
        {internal::Kind::INT_TO_BITVECTOR, Kind::INT_TO_BITVECTOR},
        // note that BITVECTOR_TO_NAT does not exist internally, only the
        // case for BITVECTOR_UBV_TO_INT is given
        {internal::Kind::BITVECTOR_UBV_TO_INT, Kind::BITVECTOR_UBV_TO_INT},
        {internal::Kind::BITVECTOR_SBV_TO_INT, Kind::BITVECTOR_SBV_TO_INT},
        {internal::Kind::BITVECTOR_FROM_BOOLS, Kind::BITVECTOR_FROM_BOOLS},
        {internal::Kind::BITVECTOR_BIT_OP, Kind::BITVECTOR_BIT},
        {internal::Kind::BITVECTOR_BIT, Kind::BITVECTOR_BIT},
        /* Finite Fields --------------------------------------------------- */
        {internal::Kind::CONST_FINITE_FIELD, Kind::CONST_FINITE_FIELD},
        {internal::Kind::FINITE_FIELD_BITSUM, Kind::FINITE_FIELD_BITSUM},
        {internal::Kind::FINITE_FIELD_MULT, Kind::FINITE_FIELD_MULT},
        {internal::Kind::FINITE_FIELD_ADD, Kind::FINITE_FIELD_ADD},
        {internal::Kind::FINITE_FIELD_NEG, Kind::FINITE_FIELD_NEG},
        /* FP -------------------------------------------------------------- */
        {internal::Kind::CONST_FLOATINGPOINT, Kind::CONST_FLOATINGPOINT},
        {internal::Kind::CONST_ROUNDINGMODE, Kind::CONST_ROUNDINGMODE},
        {internal::Kind::FLOATINGPOINT_FP, Kind::FLOATINGPOINT_FP},
        {internal::Kind::FLOATINGPOINT_EQ, Kind::FLOATINGPOINT_EQ},
        {internal::Kind::FLOATINGPOINT_ABS, Kind::FLOATINGPOINT_ABS},
        {internal::Kind::FLOATINGPOINT_NEG, Kind::FLOATINGPOINT_NEG},
        {internal::Kind::FLOATINGPOINT_ADD, Kind::FLOATINGPOINT_ADD},
        {internal::Kind::FLOATINGPOINT_SUB, Kind::FLOATINGPOINT_SUB},
        {internal::Kind::FLOATINGPOINT_MULT, Kind::FLOATINGPOINT_MULT},
        {internal::Kind::FLOATINGPOINT_DIV, Kind::FLOATINGPOINT_DIV},
        {internal::Kind::FLOATINGPOINT_FMA, Kind::FLOATINGPOINT_FMA},
        {internal::Kind::FLOATINGPOINT_SQRT, Kind::FLOATINGPOINT_SQRT},
        {internal::Kind::FLOATINGPOINT_REM, Kind::FLOATINGPOINT_REM},
        {internal::Kind::FLOATINGPOINT_RTI, Kind::FLOATINGPOINT_RTI},
        {internal::Kind::FLOATINGPOINT_MIN, Kind::FLOATINGPOINT_MIN},
        {internal::Kind::FLOATINGPOINT_MAX, Kind::FLOATINGPOINT_MAX},
        {internal::Kind::FLOATINGPOINT_LEQ, Kind::FLOATINGPOINT_LEQ},
        {internal::Kind::FLOATINGPOINT_LT, Kind::FLOATINGPOINT_LT},
        {internal::Kind::FLOATINGPOINT_GEQ, Kind::FLOATINGPOINT_GEQ},
        {internal::Kind::FLOATINGPOINT_GT, Kind::FLOATINGPOINT_GT},
        {internal::Kind::FLOATINGPOINT_IS_NORMAL,
         Kind::FLOATINGPOINT_IS_NORMAL},
        {internal::Kind::FLOATINGPOINT_IS_SUBNORMAL,
         Kind::FLOATINGPOINT_IS_SUBNORMAL},
        {internal::Kind::FLOATINGPOINT_IS_ZERO, Kind::FLOATINGPOINT_IS_ZERO},
        {internal::Kind::FLOATINGPOINT_IS_INF, Kind::FLOATINGPOINT_IS_INF},
        {internal::Kind::FLOATINGPOINT_IS_NAN, Kind::FLOATINGPOINT_IS_NAN},
        {internal::Kind::FLOATINGPOINT_IS_NEG, Kind::FLOATINGPOINT_IS_NEG},
        {internal::Kind::FLOATINGPOINT_IS_POS, Kind::FLOATINGPOINT_IS_POS},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV_OP,
         Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV,
         Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_FP_OP,
         Kind::FLOATINGPOINT_TO_FP_FROM_FP},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_FP,
         Kind::FLOATINGPOINT_TO_FP_FROM_FP},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_REAL_OP,
         Kind::FLOATINGPOINT_TO_FP_FROM_REAL},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_REAL,
         Kind::FLOATINGPOINT_TO_FP_FROM_REAL},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_SBV_OP,
         Kind::FLOATINGPOINT_TO_FP_FROM_SBV},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_SBV,
         Kind::FLOATINGPOINT_TO_FP_FROM_SBV},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_UBV_OP,
         Kind::FLOATINGPOINT_TO_FP_FROM_UBV},
        {internal::Kind::FLOATINGPOINT_TO_FP_FROM_UBV,
         Kind::FLOATINGPOINT_TO_FP_FROM_UBV},
        {internal::Kind::FLOATINGPOINT_TO_UBV_OP, Kind::FLOATINGPOINT_TO_UBV},
        {internal::Kind::FLOATINGPOINT_TO_UBV, Kind::FLOATINGPOINT_TO_UBV},
        {internal::Kind::FLOATINGPOINT_TO_UBV_TOTAL_OP, Kind::INTERNAL_KIND},
        {internal::Kind::FLOATINGPOINT_TO_UBV_TOTAL, Kind::INTERNAL_KIND},
        {internal::Kind::FLOATINGPOINT_TO_SBV_OP, Kind::FLOATINGPOINT_TO_SBV},
        {internal::Kind::FLOATINGPOINT_TO_SBV, Kind::FLOATINGPOINT_TO_SBV},
        {internal::Kind::FLOATINGPOINT_TO_SBV_TOTAL_OP, Kind::INTERNAL_KIND},
        {internal::Kind::FLOATINGPOINT_TO_SBV_TOTAL, Kind::INTERNAL_KIND},
        {internal::Kind::FLOATINGPOINT_TO_REAL, Kind::FLOATINGPOINT_TO_REAL},
        {internal::Kind::FLOATINGPOINT_TO_REAL_TOTAL, Kind::INTERNAL_KIND},
        /* Arrays ---------------------------------------------------------- */
        {internal::Kind::SELECT, Kind::SELECT},
        {internal::Kind::STORE, Kind::STORE},
        {internal::Kind::STORE_ALL, Kind::CONST_ARRAY},
        /* Datatypes ------------------------------------------------------- */
        {internal::Kind::APPLY_SELECTOR, Kind::APPLY_SELECTOR},
        {internal::Kind::APPLY_CONSTRUCTOR, Kind::APPLY_CONSTRUCTOR},
        {internal::Kind::APPLY_TESTER, Kind::APPLY_TESTER},
        {internal::Kind::APPLY_UPDATER, Kind::APPLY_UPDATER},
        {internal::Kind::MATCH, Kind::MATCH},
        {internal::Kind::MATCH_CASE, Kind::MATCH_CASE},
        {internal::Kind::MATCH_BIND_CASE, Kind::MATCH_BIND_CASE},
        {internal::Kind::TUPLE_PROJECT, Kind::TUPLE_PROJECT},
        {internal::Kind::TUPLE_PROJECT_OP, Kind::TUPLE_PROJECT},
        {internal::Kind::NULLABLE_LIFT, Kind::NULLABLE_LIFT},
        /* Separation Logic ------------------------------------------------ */
        {internal::Kind::SEP_NIL, Kind::SEP_NIL},
        {internal::Kind::SEP_EMP, Kind::SEP_EMP},
        {internal::Kind::SEP_PTO, Kind::SEP_PTO},
        {internal::Kind::SEP_STAR, Kind::SEP_STAR},
        {internal::Kind::SEP_WAND, Kind::SEP_WAND},
        /* Sets ------------------------------------------------------------ */
        {internal::Kind::SET_EMPTY, Kind::SET_EMPTY},
        {internal::Kind::SET_UNION, Kind::SET_UNION},
        {internal::Kind::SET_INTER, Kind::SET_INTER},
        {internal::Kind::SET_MINUS, Kind::SET_MINUS},
        {internal::Kind::SET_SUBSET, Kind::SET_SUBSET},
        {internal::Kind::SET_MEMBER, Kind::SET_MEMBER},
        {internal::Kind::SET_SINGLETON, Kind::SET_SINGLETON},
        {internal::Kind::SET_INSERT, Kind::SET_INSERT},
        {internal::Kind::SET_CARD, Kind::SET_CARD},
        {internal::Kind::SET_COMPLEMENT, Kind::SET_COMPLEMENT},
        {internal::Kind::SET_UNIVERSE, Kind::SET_UNIVERSE},
        {internal::Kind::SET_COMPREHENSION, Kind::SET_COMPREHENSION},
        {internal::Kind::SET_CHOOSE, Kind::SET_CHOOSE},
        {internal::Kind::SET_IS_EMPTY, Kind::SET_IS_EMPTY},
        {internal::Kind::SET_IS_SINGLETON, Kind::SET_IS_SINGLETON},
        {internal::Kind::SET_MAP, Kind::SET_MAP},
        {internal::Kind::SET_FILTER, Kind::SET_FILTER},
        {internal::Kind::SET_ALL, Kind::SET_ALL},
        {internal::Kind::SET_SOME, Kind::SET_SOME},
        {internal::Kind::SET_FOLD, Kind::SET_FOLD},
        /* Relations ------------------------------------------------------- */
        {internal::Kind::RELATION_JOIN, Kind::RELATION_JOIN},
        {internal::Kind::RELATION_TABLE_JOIN, Kind::RELATION_TABLE_JOIN},
        {internal::Kind::RELATION_TABLE_JOIN_OP, Kind::RELATION_TABLE_JOIN},
        {internal::Kind::RELATION_PRODUCT, Kind::RELATION_PRODUCT},
        {internal::Kind::RELATION_TRANSPOSE, Kind::RELATION_TRANSPOSE},
        {internal::Kind::RELATION_TCLOSURE, Kind::RELATION_TCLOSURE},
        {internal::Kind::RELATION_JOIN_IMAGE, Kind::RELATION_JOIN_IMAGE},
        {internal::Kind::RELATION_IDEN, Kind::RELATION_IDEN},
        {internal::Kind::RELATION_GROUP, Kind::RELATION_GROUP},
        {internal::Kind::RELATION_AGGREGATE_OP, Kind::RELATION_AGGREGATE},
        {internal::Kind::RELATION_AGGREGATE, Kind::RELATION_AGGREGATE},
        {internal::Kind::RELATION_PROJECT_OP, Kind::RELATION_PROJECT},
        {internal::Kind::RELATION_PROJECT, Kind::RELATION_PROJECT},
        /* Bags ------------------------------------------------------------ */
        {internal::Kind::BAG_UNION_MAX, Kind::BAG_UNION_MAX},
        {internal::Kind::BAG_UNION_DISJOINT, Kind::BAG_UNION_DISJOINT},
        {internal::Kind::BAG_INTER_MIN, Kind::BAG_INTER_MIN},
        {internal::Kind::BAG_DIFFERENCE_SUBTRACT,
         Kind::BAG_DIFFERENCE_SUBTRACT},
        {internal::Kind::BAG_DIFFERENCE_REMOVE, Kind::BAG_DIFFERENCE_REMOVE},
        {internal::Kind::BAG_SUBBAG, Kind::BAG_SUBBAG},
        {internal::Kind::BAG_COUNT, Kind::BAG_COUNT},
        {internal::Kind::BAG_MEMBER, Kind::BAG_MEMBER},
        {internal::Kind::BAG_SETOF, Kind::BAG_SETOF},
        {internal::Kind::BAG_MAKE, Kind::BAG_MAKE},
        {internal::Kind::BAG_EMPTY, Kind::BAG_EMPTY},
        {internal::Kind::BAG_CARD, Kind::BAG_CARD},
        {internal::Kind::BAG_CHOOSE, Kind::BAG_CHOOSE},
        {internal::Kind::BAG_MAP, Kind::BAG_MAP},
        {internal::Kind::BAG_FILTER, Kind::BAG_FILTER},
        {internal::Kind::BAG_ALL, Kind::BAG_ALL},
        {internal::Kind::BAG_SOME, Kind::BAG_SOME},
        {internal::Kind::BAG_FOLD, Kind::BAG_FOLD},
        {internal::Kind::BAG_PARTITION, Kind::BAG_PARTITION},
        {internal::Kind::TABLE_PRODUCT, Kind::TABLE_PRODUCT},
        {internal::Kind::TABLE_PROJECT, Kind::TABLE_PROJECT},
        {internal::Kind::TABLE_PROJECT_OP, Kind::TABLE_PROJECT},
        {internal::Kind::TABLE_AGGREGATE_OP, Kind::TABLE_AGGREGATE},
        {internal::Kind::TABLE_AGGREGATE, Kind::TABLE_AGGREGATE},
        {internal::Kind::TABLE_JOIN_OP, Kind::TABLE_JOIN},
        {internal::Kind::TABLE_JOIN, Kind::TABLE_JOIN},
        {internal::Kind::TABLE_GROUP_OP, Kind::TABLE_GROUP},
        {internal::Kind::TABLE_GROUP, Kind::TABLE_GROUP},
        /* Strings --------------------------------------------------------- */
        {internal::Kind::STRING_CONCAT, Kind::STRING_CONCAT},
        {internal::Kind::STRING_IN_REGEXP, Kind::STRING_IN_REGEXP},
        {internal::Kind::STRING_LENGTH, Kind::STRING_LENGTH},
        {internal::Kind::STRING_SUBSTR, Kind::STRING_SUBSTR},
        {internal::Kind::STRING_UPDATE, Kind::STRING_UPDATE},
        {internal::Kind::STRING_CHARAT, Kind::STRING_CHARAT},
        {internal::Kind::STRING_CONTAINS, Kind::STRING_CONTAINS},
        {internal::Kind::STRING_INDEXOF, Kind::STRING_INDEXOF},
        {internal::Kind::STRING_INDEXOF_RE, Kind::STRING_INDEXOF_RE},
        {internal::Kind::STRING_REPLACE, Kind::STRING_REPLACE},
        {internal::Kind::STRING_REPLACE_ALL, Kind::STRING_REPLACE_ALL},
        {internal::Kind::STRING_REPLACE_RE, Kind::STRING_REPLACE_RE},
        {internal::Kind::STRING_REPLACE_RE_ALL, Kind::STRING_REPLACE_RE_ALL},
        {internal::Kind::STRING_TO_LOWER, Kind::STRING_TO_LOWER},
        {internal::Kind::STRING_TO_UPPER, Kind::STRING_TO_UPPER},
        {internal::Kind::STRING_REV, Kind::STRING_REV},
        {internal::Kind::STRING_FROM_CODE, Kind::STRING_FROM_CODE},
        {internal::Kind::STRING_TO_CODE, Kind::STRING_TO_CODE},
        {internal::Kind::STRING_LT, Kind::STRING_LT},
        {internal::Kind::STRING_LEQ, Kind::STRING_LEQ},
        {internal::Kind::STRING_PREFIX, Kind::STRING_PREFIX},
        {internal::Kind::STRING_SUFFIX, Kind::STRING_SUFFIX},
        {internal::Kind::STRING_IS_DIGIT, Kind::STRING_IS_DIGIT},
        {internal::Kind::STRING_ITOS, Kind::STRING_FROM_INT},
        {internal::Kind::STRING_STOI, Kind::STRING_TO_INT},
        {internal::Kind::CONST_STRING, Kind::CONST_STRING},
        {internal::Kind::STRING_TO_REGEXP, Kind::STRING_TO_REGEXP},
        {internal::Kind::REGEXP_CONCAT, Kind::REGEXP_CONCAT},
        {internal::Kind::REGEXP_UNION, Kind::REGEXP_UNION},
        {internal::Kind::REGEXP_INTER, Kind::REGEXP_INTER},
        {internal::Kind::REGEXP_DIFF, Kind::REGEXP_DIFF},
        {internal::Kind::REGEXP_STAR, Kind::REGEXP_STAR},
        {internal::Kind::REGEXP_PLUS, Kind::REGEXP_PLUS},
        {internal::Kind::REGEXP_OPT, Kind::REGEXP_OPT},
        {internal::Kind::REGEXP_RANGE, Kind::REGEXP_RANGE},
        {internal::Kind::REGEXP_REPEAT, Kind::REGEXP_REPEAT},
        {internal::Kind::REGEXP_REPEAT_OP, Kind::REGEXP_REPEAT},
        {internal::Kind::REGEXP_LOOP, Kind::REGEXP_LOOP},
        {internal::Kind::REGEXP_LOOP_OP, Kind::REGEXP_LOOP},
        {internal::Kind::REGEXP_NONE, Kind::REGEXP_NONE},
        {internal::Kind::REGEXP_ALL, Kind::REGEXP_ALL},
        {internal::Kind::REGEXP_ALLCHAR, Kind::REGEXP_ALLCHAR},
        {internal::Kind::REGEXP_COMPLEMENT, Kind::REGEXP_COMPLEMENT},
        {internal::Kind::CONST_SEQUENCE, Kind::CONST_SEQUENCE},
        {internal::Kind::SEQ_UNIT, Kind::SEQ_UNIT},
        {internal::Kind::SEQ_NTH, Kind::SEQ_NTH},
        /* Quantifiers ----------------------------------------------------- */
        {internal::Kind::FORALL, Kind::FORALL},
        {internal::Kind::EXISTS, Kind::EXISTS},
        {internal::Kind::BOUND_VAR_LIST, Kind::VARIABLE_LIST},
        {internal::Kind::INST_PATTERN, Kind::INST_PATTERN},
        {internal::Kind::INST_NO_PATTERN, Kind::INST_NO_PATTERN},
        {internal::Kind::INST_POOL, Kind::INST_POOL},
        {internal::Kind::INST_ADD_TO_POOL, Kind::INST_ADD_TO_POOL},
        {internal::Kind::SKOLEM_ADD_TO_POOL, Kind::SKOLEM_ADD_TO_POOL},
        {internal::Kind::INST_ATTRIBUTE, Kind::INST_ATTRIBUTE},
        {internal::Kind::INST_PATTERN_LIST, Kind::INST_PATTERN_LIST},
        /* ----------------------------------------------------------------- */
        {internal::Kind::LAST_KIND, Kind::LAST_KIND},
    };

/* Mapping from internal kind to external (API) sort kind. */
const static std::
    unordered_map<internal::Kind, SortKind, internal::kind::KindHashFunction>
        s_sort_kinds_internal{
            {internal::Kind::UNDEFINED_KIND, SortKind::UNDEFINED_SORT_KIND},
            {internal::Kind::NULL_EXPR, SortKind::NULL_SORT},
            {internal::Kind::ABSTRACT_TYPE, SortKind::ABSTRACT_SORT},
            {internal::Kind::ARRAY_TYPE, SortKind::ARRAY_SORT},
            {internal::Kind::BAG_TYPE, SortKind::BAG_SORT},
            {internal::Kind::BITVECTOR_TYPE, SortKind::BITVECTOR_SORT},
            {internal::Kind::DATATYPE_TYPE, SortKind::DATATYPE_SORT},
            {internal::Kind::FINITE_FIELD_TYPE, SortKind::FINITE_FIELD_SORT},
            {internal::Kind::FLOATINGPOINT_TYPE, SortKind::FLOATINGPOINT_SORT},
            {internal::Kind::FUNCTION_TYPE, SortKind::FUNCTION_SORT},
            {internal::Kind::SEQUENCE_TYPE, SortKind::SEQUENCE_SORT},
            {internal::Kind::SET_TYPE, SortKind::SET_SORT},
            {internal::Kind::SORT_TYPE, SortKind::UNINTERPRETED_SORT},
            {internal::Kind::TUPLE_TYPE, SortKind::TUPLE_SORT},
            {internal::Kind::NULLABLE_TYPE, SortKind::NULLABLE_SORT},
        };

/* Set of kinds for indexed operators */
const static std::unordered_set<Kind> s_indexed_kinds(
    {Kind::DIVISIBLE,
     Kind::IAND,
     Kind::BITVECTOR_REPEAT,
     Kind::BITVECTOR_ZERO_EXTEND,
     Kind::BITVECTOR_SIGN_EXTEND,
     Kind::BITVECTOR_ROTATE_LEFT,
     Kind::BITVECTOR_ROTATE_RIGHT,
     Kind::INT_TO_BITVECTOR,
     Kind::BITVECTOR_BIT,
     Kind::FLOATINGPOINT_TO_UBV,
     Kind::FLOATINGPOINT_TO_SBV,
     Kind::BITVECTOR_EXTRACT,
     Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV,
     Kind::FLOATINGPOINT_TO_FP_FROM_FP,
     Kind::FLOATINGPOINT_TO_FP_FROM_REAL,
     Kind::FLOATINGPOINT_TO_FP_FROM_SBV,
     Kind::FLOATINGPOINT_TO_FP_FROM_UBV});

/**
 * Mapping from external (API) kind to the corresponding internal operator kind.
 */
const static std::unordered_map<Kind, internal::Kind> s_op_kinds{
    {Kind::BITVECTOR_BIT, internal::Kind::BITVECTOR_BIT_OP},
    {Kind::BITVECTOR_EXTRACT, internal::Kind::BITVECTOR_EXTRACT_OP},
    {Kind::BITVECTOR_REPEAT, internal::Kind::BITVECTOR_REPEAT_OP},
    {Kind::BITVECTOR_ROTATE_LEFT, internal::Kind::BITVECTOR_ROTATE_LEFT_OP},
    {Kind::BITVECTOR_ROTATE_RIGHT, internal::Kind::BITVECTOR_ROTATE_RIGHT_OP},
    {Kind::BITVECTOR_SIGN_EXTEND, internal::Kind::BITVECTOR_SIGN_EXTEND_OP},
    {Kind::BITVECTOR_ZERO_EXTEND, internal::Kind::BITVECTOR_ZERO_EXTEND_OP},
    {Kind::DIVISIBLE, internal::Kind::DIVISIBLE_OP},
    {Kind::FLOATINGPOINT_TO_SBV, internal::Kind::FLOATINGPOINT_TO_SBV_OP},
    {Kind::FLOATINGPOINT_TO_UBV, internal::Kind::FLOATINGPOINT_TO_UBV_OP},
    {Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV,
     internal::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV_OP},
    {Kind::FLOATINGPOINT_TO_FP_FROM_FP,
     internal::Kind::FLOATINGPOINT_TO_FP_FROM_FP_OP},
    {Kind::FLOATINGPOINT_TO_FP_FROM_REAL,
     internal::Kind::FLOATINGPOINT_TO_FP_FROM_REAL_OP},
    {Kind::FLOATINGPOINT_TO_FP_FROM_SBV,
     internal::Kind::FLOATINGPOINT_TO_FP_FROM_SBV_OP},
    {Kind::FLOATINGPOINT_TO_FP_FROM_UBV,
     internal::Kind::FLOATINGPOINT_TO_FP_FROM_UBV_OP},
    {Kind::IAND, internal::Kind::IAND_OP},
    {Kind::INT_TO_BITVECTOR, internal::Kind::INT_TO_BITVECTOR_OP},
    {Kind::REGEXP_REPEAT, internal::Kind::REGEXP_REPEAT_OP},
    {Kind::REGEXP_LOOP, internal::Kind::REGEXP_LOOP_OP},
    {Kind::TUPLE_PROJECT, internal::Kind::TUPLE_PROJECT_OP},
    {Kind::RELATION_AGGREGATE, internal::Kind::RELATION_AGGREGATE_OP},
    {Kind::RELATION_GROUP, internal::Kind::RELATION_GROUP_OP},
    {Kind::RELATION_PROJECT, internal::Kind::RELATION_PROJECT_OP},
    {Kind::RELATION_TABLE_JOIN, internal::Kind::RELATION_TABLE_JOIN_OP},
    {Kind::TABLE_PROJECT, internal::Kind::TABLE_PROJECT_OP},
    {Kind::TABLE_AGGREGATE, internal::Kind::TABLE_AGGREGATE_OP},
    {Kind::TABLE_JOIN, internal::Kind::TABLE_JOIN_OP},
    {Kind::TABLE_GROUP, internal::Kind::TABLE_GROUP_OP},
};

/* -------------------------------------------------------------------------- */
/* Rounding Mode for Floating Points                                          */
/* -------------------------------------------------------------------------- */

const static std::unordered_map<RoundingMode, cvc5::internal::RoundingMode>
    s_rmodes{
        {RoundingMode::ROUND_NEAREST_TIES_TO_EVEN,
         cvc5::internal::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN},
        {RoundingMode::ROUND_TOWARD_POSITIVE,
         cvc5::internal::RoundingMode::ROUND_TOWARD_POSITIVE},
        {RoundingMode::ROUND_TOWARD_NEGATIVE,
         cvc5::internal::RoundingMode::ROUND_TOWARD_NEGATIVE},
        {RoundingMode::ROUND_TOWARD_ZERO,
         cvc5::internal::RoundingMode::ROUND_TOWARD_ZERO},
        {RoundingMode::ROUND_NEAREST_TIES_TO_AWAY,
         cvc5::internal::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY},
    };

const static std::unordered_map<cvc5::internal::RoundingMode, RoundingMode>
    s_rmodes_internal{
        {cvc5::internal::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN,
         RoundingMode::ROUND_NEAREST_TIES_TO_EVEN},
        {cvc5::internal::RoundingMode::ROUND_TOWARD_POSITIVE,
         RoundingMode::ROUND_TOWARD_POSITIVE},
        {cvc5::internal::RoundingMode::ROUND_TOWARD_NEGATIVE,
         RoundingMode::ROUND_TOWARD_NEGATIVE},
        {cvc5::internal::RoundingMode::ROUND_TOWARD_ZERO,
         RoundingMode::ROUND_TOWARD_ZERO},
        {cvc5::internal::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY,
         RoundingMode::ROUND_NEAREST_TIES_TO_AWAY},
    };

/* -------------------------------------------------------------------------- */
/* Helpers                                                                    */
/* -------------------------------------------------------------------------- */

namespace {

/** Convert a internal::Kind (internal) to a cvc5::Kind (external).
 */
cvc5::Kind intToExtKind(internal::Kind k)
{
  auto it = s_kinds_internal.find(k);
  if (it == s_kinds_internal.end())
  {
    return Kind::INTERNAL_KIND;
  }
  return it->second;
}
/** Convert a internal::Kind (internal) to a cvc5::Kind (external).
 */
SortKind intToExtSortKind(internal::Kind k)
{
  auto it = s_sort_kinds_internal.find(k);
  if (it == s_sort_kinds_internal.end())
  {
    return SortKind::INTERNAL_SORT_KIND;
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

/** Convert a cvc5::SortKind (external) to a internal::Kind (internal).
 */
internal::Kind extToIntSortKind(SortKind k)
{
  auto it = s_sort_kinds.find(k);
  if (it == s_sort_kinds.end())
  {
    return internal::Kind::UNDEFINED_KIND;
  }
  return it->second.first;
}

/** Return true if given kind is a defined external kind. */
bool isDefinedKind(Kind k)
{
  return k > Kind::UNDEFINED_KIND && k < Kind::LAST_KIND;
}

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

/**
 * Class that acts as a converter from an external to an internal plugin.
 */
class PluginInternal : public internal::Plugin
{
 public:
  PluginInternal(internal::NodeManager* nm,
                 cvc5::TermManager& tm,
                 cvc5::Plugin& e)
      : internal::Plugin(nm), d_tm(tm), d_external(e)
  {
  }
  /** Check method */
  std::vector<internal::Node> check() override
  {
    std::vector<Term> lemsExt = d_external.check();
    return Term::termVectorToNodes(lemsExt);
  }
  /** Notify SAT clause method */
  void notifySatClause(const internal::Node& n) override
  {
    Term t = Term(&d_tm, n);
    return d_external.notifySatClause(t);
  }
  /** Notify theory lemma method */
  void notifyTheoryLemma(const internal::Node& n) override
  {
    Term t = Term(&d_tm, n);
    return d_external.notifyTheoryLemma(t);
  }
  /** Get name */
  std::string getName() override { return d_external.getName(); }

 private:
  /** Reference to the term manager */
  cvc5::TermManager& d_tm;
  /** Reference to the external (user-provided) plugin */
  cvc5::Plugin& d_external;
};

std::string kindToString(Kind k)
{
  auto it = s_kinds.find(k);
  if (it == s_kinds.end())
  {
    return "Kind::UNDEFINED_KIND";
  }
  return it->second.second;
}

std::ostream& operator<<(std::ostream& out, Kind k)
{
  return out << std::to_string(k);
}

std::string sortKindToString(SortKind k)
{
  auto it = s_sort_kinds.find(k);
  if (it == s_sort_kinds.end())
  {
    return "Kind::UNDEFINED_SORT_KIND";
  }
  return it->second.second;
}

std::ostream& operator<<(std::ostream& out, SortKind k)
{
  return out << std::to_string(k);
}

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

}  // namespace cvc5

namespace std {

size_t hash<cvc5::Result>::operator()(const cvc5::Result& result) const
{
  return std::hash<std::string>{}(result.toString());
}
}  // namespace std

namespace cvc5 {

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

bool SynthResult::operator==(const SynthResult& r) const
{
  return *d_result == *r.d_result;
}

bool SynthResult::operator!=(const SynthResult& r) const
{
  return *d_result != *r.d_result;
}

std::string SynthResult::toString(void) const { return d_result->toString(); }

std::ostream& operator<<(std::ostream& out, const SynthResult& sr)
{
  out << sr.toString();
  return out;
}

}  // namespace cvc5

namespace std {

size_t hash<cvc5::SynthResult>::operator()(
    const cvc5::SynthResult& result) const
{
  return std::hash<std::string>{}(result.toString());
}
}  // namespace std

namespace cvc5 {

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

Sort::Sort(TermManager* tm, const internal::TypeNode& t)
    : d_tm(tm), d_type(new internal::TypeNode(t))
{
}

Sort::Sort() : d_tm(nullptr), d_type(new internal::TypeNode()) {}

Sort::~Sort()
{
  Assert(isNull() || d_tm != nullptr);
  d_type.reset();
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
    TermManager* tm, const std::vector<internal::TypeNode>& types)
{
  std::vector<Sort> sorts;
  for (size_t i = 0, tsize = types.size(); i < tsize; i++)
  {
    sorts.push_back(Sort(tm, types[i]));
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

SortKind Sort::getKind() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  internal::Kind tk = d_type->getKind();
  // Base types are type constants, which have to be special cased to return
  // the appropriate kind.
  if (tk == internal::Kind::TYPE_CONSTANT)
  {
    switch (d_type->getConst<internal::TypeConstant>())
    {
      case internal::BOOLEAN_TYPE: return SortKind::BOOLEAN_SORT; break;
      case internal::REAL_TYPE: return SortKind::REAL_SORT; break;
      case internal::INTEGER_TYPE: return SortKind::INTEGER_SORT; break;
      case internal::STRING_TYPE: return SortKind::STRING_SORT; break;
      case internal::REGEXP_TYPE: return SortKind::REGLAN_SORT; break;
      case internal::ROUNDINGMODE_TYPE:
        return SortKind::ROUNDINGMODE_SORT;
        break;
      default: return SortKind::INTERNAL_SORT_KIND; break;
    }
  }
  // otherwise we rely on the mapping
  return intToExtSortKind(tk);
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Sort::hasSymbol() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_type->hasName();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Sort::getSymbol() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->hasName())
      << "invalid call to '" << __PRETTY_FUNCTION__
      << "', expected the sort to have a symbol.";
  //////// all checks before this line
  return d_type->getName();
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

bool Sort::isNullable() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isNullable();
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

bool Sort::isFiniteField() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isFiniteField();
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

bool Sort::isAbstract() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_type->isAbstract();
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
      << "expected instantiated uninterpreted sort.";
  //////// all checks before this line
  return Sort(d_tm, d_type->getUninterpretedSortConstructor());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Datatype Sort::getDatatype() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatype()) << "expected datatype sort.";
  //////// all checks before this line
  return Datatype(d_tm, d_type->getDType());
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
      << "expected parametric datatype or sort constructor sort.";
  CVC5_API_CHECK(!d_type->isParametricDatatype()
                 || d_type->getNumChildren() == params.size() + 1)
      << "arity mismatch for instantiated parametric datatype";
  CVC5_API_CHECK(!d_type->isUninterpretedSortConstructor()
                 || d_type->getUninterpretedSortConstructorArity()
                        == params.size())
      << "arity mismatch for instantiated sort constructor";
  //////// all checks before this line
  std::vector<internal::TypeNode> tparams = sortVectorToTypeNodes(params);
  return Sort(d_tm, d_type->instantiate(tparams));
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Sort> Sort::getInstantiatedParameters() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isInstantiated())
      << "expected instantiated parametric sort";
  //////// all checks before this line
  return typeNodeVectorToSorts(d_tm, d_type->getInstantiatedParamTypes());
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
      d_tm, d_type->substitute(sort.getTypeNode(), replacement.getTypeNode()));
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
  return Sort(d_tm,
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
      << "not a constructor sort: " << (*this);
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
      << "not a constructor sort: " << (*this);
  //////// all checks before this line
  return typeNodeVectorToSorts(d_tm, d_type->getArgTypes());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::getDatatypeConstructorCodomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatypeConstructor())
      << "not a constructor sort: " << (*this);
  //////// all checks before this line
  return Sort(d_tm, d_type->getDatatypeConstructorRangeType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Selector sort ------------------------------------------------------- */

Sort Sort::getDatatypeSelectorDomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatypeSelector())
      << "not a selector sort: " << (*this);
  //////// all checks before this line
  return Sort(d_tm, d_type->getDatatypeSelectorDomainType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::getDatatypeSelectorCodomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatypeSelector())
      << "not a selector sort: " << (*this);
  //////// all checks before this line
  return Sort(d_tm, d_type->getDatatypeSelectorRangeType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Tester sort ------------------------------------------------------- */

Sort Sort::getDatatypeTesterDomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatypeTester())
      << "not a tester sort: " << (*this);
  //////// all checks before this line
  return Sort(d_tm, d_type->getDatatypeTesterDomainType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::getDatatypeTesterCodomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isDatatypeTester())
      << "not a tester sort: " << (*this);
  //////// all checks before this line
  return Sort(d_tm, d_tm->d_nm->booleanType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Function sort ------------------------------------------------------- */

size_t Sort::getFunctionArity() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isFunction()) << "not a function sort: " << (*this);
  //////// all checks before this line
  return d_type->getNumChildren() - 1;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Sort> Sort::getFunctionDomainSorts() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isFunction()) << "not a function sort: " << (*this);
  //////// all checks before this line
  return typeNodeVectorToSorts(d_tm, d_type->getArgTypes());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::getFunctionCodomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isFunction()) << "not a function sort" << (*this);
  //////// all checks before this line
  return Sort(d_tm, d_type->getRangeType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Array sort ---------------------------------------------------------- */

Sort Sort::getArrayIndexSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isArray()) << "not an array sort.";
  //////// all checks before this line
  return Sort(d_tm, d_type->getArrayIndexType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::getArrayElementSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isArray()) << "not an array sort.";
  //////// all checks before this line
  return Sort(d_tm, d_type->getArrayConstituentType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Set sort ------------------------------------------------------------ */

Sort Sort::getSetElementSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isSet()) << "not a set sort.";
  //////// all checks before this line
  return Sort(d_tm, d_type->getSetElementType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Bag sort ------------------------------------------------------------ */

Sort Sort::getBagElementSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isBag()) << "not a bag sort.";
  //////// all checks before this line
  return Sort(d_tm, d_type->getBagElementType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Sequence sort ------------------------------------------------------- */

Sort Sort::getSequenceElementSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isSequence()) << "not a sequence sort.";
  //////// all checks before this line
  return Sort(d_tm, d_type->getSequenceElementType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Abstract sort ------------------------------------------------------- */

SortKind Sort::getAbstractedKind() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isAbstract()) << "not an abstract sort.";
  //////// all checks before this line
  return intToExtSortKind(d_type->getAbstractedKind());
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Sort constructor sort ----------------------------------------------- */

size_t Sort::getUninterpretedSortConstructorArity() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isUninterpretedSortConstructor())
      << "not a sort constructor sort.";
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
  CVC5_API_CHECK(isBitVector()) << "not a bit-vector sort.";
  //////// all checks before this line
  return d_type->getBitVectorSize();
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Finite field sort --------------------------------------------------- */

std::string Sort::getFiniteFieldSize() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isFiniteField()) << "not a finite field sort.";
  //////// all checks before this line
  return d_type->getFfSize().toString();
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Floating-point sort ------------------------------------------------- */

uint32_t Sort::getFloatingPointExponentSize() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isFloatingPoint()) << "not a floating-point sort.";
  //////// all checks before this line
  return d_type->getFloatingPointExponentSize();
  ////////
  CVC5_API_TRY_CATCH_END;
}

uint32_t Sort::getFloatingPointSignificandSize() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isFloatingPoint()) << "not a floating-point sort.";
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
  CVC5_API_CHECK(d_type->isDatatype()) << "not a datatype sort.";
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
  CVC5_API_CHECK(isTuple()) << "not a tuple sort.";
  //////// all checks before this line
  return d_type->getTupleLength();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Sort> Sort::getTupleSorts() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_type->isTuple()) << "not a tuple sort.";
  //////// all checks before this line
  return typeNodeVectorToSorts(d_tm, d_type->getTupleTypes());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Sort::getNullableElementSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(isNullable()) << "not a nullable sort.";
  //////// all checks before this line
  return Sort(d_tm, d_type->getNullableElementType());
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

Op::Op() : d_tm(nullptr), d_kind(Kind::NULL_TERM), d_node(new internal::Node())
{
}

Op::Op(TermManager* tm, const Kind k)
    : d_tm(tm), d_kind(k), d_node(new internal::Node())
{
}

Op::Op(TermManager* tm, const Kind k, const internal::Node& n)
    : d_tm(tm), d_kind(k), d_node(new internal::Node(n))
{
}

Op::~Op()
{
  Assert(isNull() || d_tm != nullptr);
  d_node.reset();
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
  CVC5_API_CHECK(d_kind != Kind::NULL_TERM) << "expected a non-null Kind";
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
    case Kind::DIVISIBLE: size = 1; break;
    case Kind::BITVECTOR_REPEAT: size = 1; break;
    case Kind::BITVECTOR_ZERO_EXTEND: size = 1; break;
    case Kind::BITVECTOR_SIGN_EXTEND: size = 1; break;
    case Kind::BITVECTOR_ROTATE_LEFT: size = 1; break;
    case Kind::BITVECTOR_ROTATE_RIGHT: size = 1; break;
    case Kind::BITVECTOR_BIT: size = 1; break;
    case Kind::INT_TO_BITVECTOR: size = 1; break;
    case Kind::IAND: size = 1; break;
    case Kind::FLOATINGPOINT_TO_UBV: size = 1; break;
    case Kind::FLOATINGPOINT_TO_SBV: size = 1; break;
    case Kind::REGEXP_REPEAT: size = 1; break;
    case Kind::BITVECTOR_EXTRACT: size = 2; break;
    case Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV: size = 2; break;
    case Kind::FLOATINGPOINT_TO_FP_FROM_FP: size = 2; break;
    case Kind::FLOATINGPOINT_TO_FP_FROM_REAL: size = 2; break;
    case Kind::FLOATINGPOINT_TO_FP_FROM_SBV: size = 2; break;
    case Kind::FLOATINGPOINT_TO_FP_FROM_UBV: size = 2; break;
    case Kind::REGEXP_LOOP: size = 2; break;
    case Kind::TUPLE_PROJECT:
    case Kind::RELATION_AGGREGATE:
    case Kind::RELATION_GROUP:
    case Kind::RELATION_PROJECT:
    case Kind::RELATION_TABLE_JOIN:
    case Kind::TABLE_AGGREGATE:
    case Kind::TABLE_GROUP:
    case Kind::TABLE_JOIN:
    case Kind::TABLE_PROJECT:
    {
      size = d_node->getConst<internal::ProjectOp>().getIndices().size();
      break;
    }
    default: CVC5_API_CHECK(false) << "Unhandled kind " << k;
  }
  return size;
}

Term Op::operator[](size_t index) { return getIndexHelper(index); }

Term Op::getIndexHelper(size_t index)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(!d_node->isNull())
      << "expected a non-null internal expression. This Op is not indexed.";
  CVC5_API_CHECK(index < getNumIndicesHelper()) << "index out of bound";
  Kind k = intToExtKind(d_node->getKind());
  Term t;
  switch (k)
  {
    case Kind::DIVISIBLE:
    {
      t = d_tm->mkRationalValHelper(
          internal::Rational(d_node->getConst<internal::Divisible>().k), true);
      break;
    }
    case Kind::BITVECTOR_REPEAT:
    {
      t = d_tm->mkRationalValHelper(
          d_node->getConst<internal::BitVectorRepeat>().d_repeatAmount, true);
      break;
    }
    case Kind::BITVECTOR_ZERO_EXTEND:
    {
      t = d_tm->mkRationalValHelper(
          d_node->getConst<internal::BitVectorZeroExtend>().d_zeroExtendAmount,
          true);
      break;
    }
    case Kind::BITVECTOR_SIGN_EXTEND:
    {
      t = d_tm->mkRationalValHelper(
          d_node->getConst<internal::BitVectorSignExtend>().d_signExtendAmount,
          true);
      break;
    }
    case Kind::BITVECTOR_ROTATE_LEFT:
    {
      t = d_tm->mkRationalValHelper(
          d_node->getConst<internal::BitVectorRotateLeft>().d_rotateLeftAmount,
          true);
      break;
    }
    case Kind::BITVECTOR_ROTATE_RIGHT:
    {
      t = d_tm->mkRationalValHelper(
          d_node->getConst<internal::BitVectorRotateRight>()
              .d_rotateRightAmount,
          true);
      break;
    }
    case Kind::INT_TO_BITVECTOR:
    {
      t = d_tm->mkRationalValHelper(
          d_node->getConst<internal::IntToBitVector>().d_size, true);
      break;
    }
    case Kind::BITVECTOR_BIT:
    {
      t = d_tm->mkRationalValHelper(
          d_node->getConst<internal::BitVectorBit>().d_bitIndex, true);
      break;
    }
    case Kind::IAND:
    {
      t = d_tm->mkRationalValHelper(d_node->getConst<internal::IntAnd>().d_size,
                                    true);
      break;
    }
    case Kind::FLOATINGPOINT_TO_UBV:
    {
      t = d_tm->mkRationalValHelper(
          d_node->getConst<internal::FloatingPointToUBV>().d_bv_size.d_size,
          true);
      break;
    }
    case Kind::FLOATINGPOINT_TO_SBV:
    {
      t = d_tm->mkRationalValHelper(
          d_node->getConst<internal::FloatingPointToSBV>().d_bv_size.d_size,
          true);
      break;
    }
    case Kind::REGEXP_REPEAT:
    {
      t = d_tm->mkRationalValHelper(
          d_node->getConst<internal::RegExpRepeat>().d_repeatAmount, true);
      break;
    }
    case Kind::BITVECTOR_EXTRACT:
    {
      internal::BitVectorExtract ext =
          d_node->getConst<internal::BitVectorExtract>();
      t = index == 0 ? d_tm->mkRationalValHelper(ext.d_high, true)
                     : d_tm->mkRationalValHelper(ext.d_low, true);
      break;
    }
    case Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV:
    {
      internal::FloatingPointToFPIEEEBitVector ext =
          d_node->getConst<internal::FloatingPointToFPIEEEBitVector>();

      t = index == 0
              ? d_tm->mkRationalValHelper(ext.getSize().exponentWidth(), true)
              : d_tm->mkRationalValHelper(ext.getSize().significandWidth(),
                                          true);
      break;
    }
    case Kind::FLOATINGPOINT_TO_FP_FROM_FP:
    {
      internal::FloatingPointToFPFloatingPoint ext =
          d_node->getConst<internal::FloatingPointToFPFloatingPoint>();
      t = index == 0
              ? d_tm->mkRationalValHelper(ext.getSize().exponentWidth(), true)
              : d_tm->mkRationalValHelper(ext.getSize().significandWidth(),
                                          true);
      break;
    }
    case Kind::FLOATINGPOINT_TO_FP_FROM_REAL:
    {
      internal::FloatingPointToFPReal ext =
          d_node->getConst<internal::FloatingPointToFPReal>();

      t = index == 0
              ? d_tm->mkRationalValHelper(ext.getSize().exponentWidth(), true)
              : d_tm->mkRationalValHelper(ext.getSize().significandWidth(),
                                          true);
      break;
    }
    case Kind::FLOATINGPOINT_TO_FP_FROM_SBV:
    {
      internal::FloatingPointToFPSignedBitVector ext =
          d_node->getConst<internal::FloatingPointToFPSignedBitVector>();
      t = index == 0
              ? d_tm->mkRationalValHelper(ext.getSize().exponentWidth(), true)
              : d_tm->mkRationalValHelper(ext.getSize().significandWidth(),
                                          true);
      break;
    }
    case Kind::FLOATINGPOINT_TO_FP_FROM_UBV:
    {
      internal::FloatingPointToFPUnsignedBitVector ext =
          d_node->getConst<internal::FloatingPointToFPUnsignedBitVector>();
      t = index == 0
              ? d_tm->mkRationalValHelper(ext.getSize().exponentWidth(), true)
              : d_tm->mkRationalValHelper(ext.getSize().significandWidth(),
                                          true);
      break;
    }
    case Kind::REGEXP_LOOP:
    {
      internal::RegExpLoop ext = d_node->getConst<internal::RegExpLoop>();
      t = index == 0 ? d_tm->mkRationalValHelper(ext.d_loopMinOcc, true)
                     : d_tm->mkRationalValHelper(ext.d_loopMaxOcc, true);

      break;
    }
    case Kind::TUPLE_PROJECT:
    case Kind::RELATION_AGGREGATE:
    case Kind::RELATION_GROUP:
    case Kind::RELATION_PROJECT:
    case Kind::RELATION_TABLE_JOIN:
    case Kind::TABLE_AGGREGATE:
    case Kind::TABLE_GROUP:
    case Kind::TABLE_JOIN:
    case Kind::TABLE_PROJECT:
    {
      const std::vector<uint32_t>& projectionIndices =
          d_node->getConst<internal::ProjectOp>().getIndices();
      t = d_tm->mkRationalValHelper(projectionIndices[index], true);
      break;
    }
    default:
    {
      CVC5_API_CHECK(false) << "Unhandled kind " << k;
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
    return std::to_string(d_kind);
  }
  else
  {
    CVC5_API_CHECK(!d_node->isNull())
        << "expected a non-null internal expression";
    Assert(isNull() || d_tm != nullptr);
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
  return (d_node->isNull() && (d_kind == Kind::NULL_TERM));
}

bool Op::isIndexedHelper() const { return !d_node->isNull(); }

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

Term::Term() : d_tm(nullptr), d_node(new internal::Node()) {}

Term::Term(TermManager* tm, const internal::Node& n) : d_tm(tm)
{
  d_node.reset(new internal::Node(n));
}

Term::~Term()
{
  Assert(isNull() || d_tm != nullptr);
  d_node.reset();
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
      << "expected apply kind to have operator when accessing child of Term";
  //////// all checks before this line

  // special cases for apply kinds
  if (isApplyKind(d_node->getKind()))
  {
    if (index == 0)
    {
      // return the operator
      return Term(d_tm, d_node->getOperator());
    }
    else
    {
      index -= 1;
    }
  }
  // otherwise we are looking up child at (index-1)
  return Term(d_tm, (*d_node)[index]);
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
  return Sort(d_tm, d_node->getType());
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
      << "expected terms of the same sort in substitute";
  //////// all checks before this line
  return Term(d_tm,
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
      << "expected vectors of the same arity in substitute";
  CVC5_API_TERM_CHECK_TERMS_WITH_TERMS_SORT_EQUAL_TO(terms, replacements);
  //////// all checks before this line
  std::vector<internal::Node> nodes = Term::termVectorToNodes(terms);
  std::vector<internal::Node> nodeReplacements =
      Term::termVectorToNodes(replacements);
  return Term(d_tm,
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
      << "expected Term to have an Op when calling getOp()";
  //////// all checks before this line

  // special cases for parameterized operators that are not indexed operators
  // the API level differs from the internal structure
  // indexed operators are stored in Ops
  // whereas functions and datatype operators are terms, and the Op
  // is one of the APPLY_* kinds
  if (isApplyKind(d_node->getKind()))
  {
    return Op(d_tm, intToExtKind(d_node->getKind()));
  }
  else if (d_node->getMetaKind() == internal::kind::metakind::PARAMETERIZED)
  {
    // it's an indexed operator
    // so we should return the indexed op
    internal::Node op = d_node->getOperator();
    return Op(d_tm, intToExtKind(d_node->getKind()), op);
  }
  // Notice this is the only case where getKindHelper is used, since the
  // cases above do not have special cases for intToExtKind.
  return Op(d_tm, getKindHelper());
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::hasSymbol() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->hasName();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Term::getSymbol() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_node->hasName())
      << "invalid call to '" << __PRETTY_FUNCTION__
      << "', expected the term to have a symbol.";
  //////// all checks before this line
  return d_node->getName();
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
  return Term(d_tm, res);
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
  return Term(d_tm, res);
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
  return Term(d_tm, res);
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
  return Term(d_tm, res);
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
  return Term(d_tm, res);
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
  return Term(d_tm, res);
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
  return Term(d_tm, res);
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
    : d_tm(nullptr), d_origNode(nullptr), d_pos(0)
{
}

Term::const_iterator::const_iterator(TermManager* tm,
                                     const std::shared_ptr<internal::Node>& n,
                                     uint32_t p)
    : d_tm(tm), d_origNode(n), d_pos(p)
{
}

Term::const_iterator::const_iterator(const const_iterator& it)
    : d_tm(nullptr), d_origNode(nullptr)
{
  if (it.d_origNode != nullptr)
  {
    d_tm = it.d_tm;
    d_origNode = it.d_origNode;
    d_pos = it.d_pos;
  }
}

Term::const_iterator& Term::const_iterator::operator=(const const_iterator& it)
{
  d_tm = it.d_tm;
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
  return (d_tm == it.d_tm && *d_origNode == *it.d_origNode)
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
    return Term(d_tm, d_origNode->getOperator());
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
    return Term(d_tm, (*d_origNode)[idx]);
  }
}

Term::const_iterator Term::begin() const
{
  return Term::const_iterator(d_tm, d_node, 0);
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
  return Term::const_iterator(d_tm, d_node, endpos);
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

std::u32string Term::getU32StringValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(d_node->getKind() == internal::Kind::CONST_STRING,
                              *d_node)
      << "Term to be a string value when calling getU32StringValue()";
  //////// all checks before this line
  return d_node->getConst<internal::String>().toU32String();
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
    TermManager* tm, const std::vector<internal::Node>& nodes)
{
  std::vector<Term> res;
  for (const internal::Node& n : nodes)
  {
    res.push_back(Term(tm, n));
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
  return Term(d_tm, ar.getValue());
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

bool Term::isFiniteFieldValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::CONST_FINITE_FIELD;
  ////////
  CVC5_API_TRY_CATCH_END;
}
std::string Term::getFiniteFieldValue() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(
      d_node->getKind() == internal::Kind::CONST_FINITE_FIELD, *d_node)
      << "Term to be a finite field value when calling getFiniteFieldValue()";
  //////// all checks before this line
  return d_node->getConst<internal::FiniteFieldValue>()
      .toSignedInteger()
      .toString();
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
    res.emplace_back(Term(d_tm, (*d_node)[i]));
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
                         d_tm->mkValHelper((fp.pack())));
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
                      TermManager* tm)
{
  // We asserted that node has a set type, and node.isConst()
  // Thus, node only contains of SET_EMPTY, SET_UNION and SET_SINGLETON.
  switch (node.getKind())
  {
    case internal::Kind::SET_EMPTY: break;
    case internal::Kind::SET_SINGLETON: set.emplace(Term(tm, node[0])); break;
    case internal::Kind::SET_UNION:
    {
      for (const auto& sub : node)
      {
        collectSet(set, sub, tm);
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
  Term::collectSet(res, *d_node, d_tm);
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
  for (const auto& node : seq.getVec())
  {
    res.emplace_back(Term(d_tm, node));
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
  return std::make_pair(Sort(d_tm, cc.getType()),
                        cc.getUpperBound().getUnsignedInt());
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isRealAlgebraicNumber() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::REAL_ALGEBRAIC_NUMBER;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::getRealAlgebraicNumberDefiningPolynomial(const Term& v) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(
      d_node->getKind() == internal::Kind::REAL_ALGEBRAIC_NUMBER, *d_node)
      << "Term to be a real algebraic number when calling "
         "getRealAlgebraicNumberDefiningPolynomial()";
  CVC5_API_ARG_CHECK_EXPECTED(v.getKind() == Kind::VARIABLE, v)
      << "expected a variable as argument when calling "
         "getRealAlgebraicNumberDefiningPolynomial()";
#ifndef CVC5_POLY_IMP
  throw CVC5ApiException(
      "expected libpoly enabled build when calling "
      "getRealAlgebraicNumberDefiningPolynomial");
#endif
  //////// all checks before this line
#ifdef CVC5_POLY_IMP
  const internal::RealAlgebraicNumber& ran =
      d_node->getOperator().getConst<internal::RealAlgebraicNumber>();
  return Term(d_tm,
              internal::PolyConverter::ran_to_defining_polynomial(
                  ran, *v.d_node.get()));
#else
  return Term();
#endif
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::getRealAlgebraicNumberLowerBound() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(
      d_node->getKind() == internal::Kind::REAL_ALGEBRAIC_NUMBER, *d_node)
      << "Term to be a real algebraic number when calling "
         "getRealAlgebraicNumberDefiningPolynomial()";
#ifndef CVC5_POLY_IMP
  throw CVC5ApiException(
      "expected libpoly enabled build when calling "
      "getRealAlgebraicNumberLowerBound");
#endif
  //////// all checks before this line
#ifdef CVC5_POLY_IMP
  const internal::RealAlgebraicNumber& ran =
      d_node->getOperator().getConst<internal::RealAlgebraicNumber>();
  return Term(d_tm,
              internal::PolyConverter::ran_to_lower(d_tm->d_nm.get(), ran));
#else
  return Term();
#endif
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Term::getRealAlgebraicNumberUpperBound() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(
      d_node->getKind() == internal::Kind::REAL_ALGEBRAIC_NUMBER, *d_node)
      << "Term to be a real algebraic number when calling "
         "getRealAlgebraicNumberDefiningPolynomial()";
#ifndef CVC5_POLY_IMP
  throw CVC5ApiException(
      "expected libpoly enabled build when calling "
      "getRealAlgebraicNumberUpperBound");
#endif
  //////// all checks before this line
#ifdef CVC5_POLY_IMP
  const internal::RealAlgebraicNumber& ran =
      d_node->getOperator().getConst<internal::RealAlgebraicNumber>();
  return Term(d_tm,
              internal::PolyConverter::ran_to_upper(d_tm->d_nm.get(), ran));
#else
  return Term();
#endif
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Term::isSkolem() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_node->getKind() == internal::Kind::SKOLEM;
  ////////
  CVC5_API_TRY_CATCH_END;
}

SkolemId Term::getSkolemId() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(d_node->isSkolem(), *d_node)
      << "Term to be a skolem when calling getSkolemId";
  //////// all checks before this line
  return d_node->getSkolemId();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Term> Term::getSkolemIndices() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_EXPECTED(d_node->isSkolem(), *d_node)
      << "Term to be a skolem when calling getSkolemIndices";
  //////// all checks before this line
  std::vector<internal::Node> indices = d_node->getSkolemIndices();
  return Term::nodeVectorToTerms(d_tm, indices);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::ostream& operator<<(std::ostream& out, const Term& t)
{
  // Note that this ignores the options::ioutils properties of `out`.
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
      case internal::Kind::STRING_CONCAT: return Kind::SEQ_CONCAT;
      case internal::Kind::STRING_LENGTH: return Kind::SEQ_LENGTH;
      case internal::Kind::STRING_SUBSTR: return Kind::SEQ_EXTRACT;
      case internal::Kind::STRING_UPDATE: return Kind::SEQ_UPDATE;
      case internal::Kind::STRING_CHARAT: return Kind::SEQ_AT;
      case internal::Kind::STRING_CONTAINS: return Kind::SEQ_CONTAINS;
      case internal::Kind::STRING_INDEXOF: return Kind::SEQ_INDEXOF;
      case internal::Kind::STRING_REPLACE: return Kind::SEQ_REPLACE;
      case internal::Kind::STRING_REPLACE_ALL: return Kind::SEQ_REPLACE_ALL;
      case internal::Kind::STRING_REV: return Kind::SEQ_REV;
      case internal::Kind::STRING_PREFIX: return Kind::SEQ_PREFIX;
      case internal::Kind::STRING_SUFFIX: return Kind::SEQ_SUFFIX;
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
    : d_tm(nullptr), d_ctor(nullptr)
{
}

DatatypeConstructorDecl::DatatypeConstructorDecl(TermManager* tm,
                                                 const std::string& name)
    : d_tm(tm), d_ctor(new internal::DTypeConstructor(name))
{
}
DatatypeConstructorDecl::~DatatypeConstructorDecl()
{
  if (d_ctor != nullptr)
  {
    d_ctor.reset();
  }
}

bool DatatypeConstructorDecl::operator==(
    const DatatypeConstructorDecl& decl) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_ctor == decl.d_ctor;
  ////////
  CVC5_API_TRY_CATCH_END;
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
      d_tm->d_nm->mkUnresolvedDatatypeSort(unresDataypeName);
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

DatatypeDecl::DatatypeDecl() : d_tm(nullptr), d_dtype(nullptr) {}

DatatypeDecl::DatatypeDecl(TermManager* tm,
                           const std::string& name,
                           bool isCoDatatype)
    : d_tm(tm), d_dtype(new internal::DType(name, isCoDatatype))
{
}

DatatypeDecl::DatatypeDecl(TermManager* tm,
                           const std::string& name,
                           const std::vector<Sort>& params,
                           bool isCoDatatype)
    : d_tm(tm)
{
  std::vector<internal::TypeNode> tparams = Sort::sortVectorToTypeNodes(params);
  d_dtype = std::shared_ptr<internal::DType>(
      new internal::DType(name, tparams, isCoDatatype));
}

bool DatatypeDecl::operator==(const DatatypeDecl& decl) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype == decl.d_dtype;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool DatatypeDecl::isNullHelper() const { return !d_dtype; }

DatatypeDecl::~DatatypeDecl()
{
  if (d_dtype != nullptr)
  {
    d_dtype.reset();
  }
}

bool DatatypeDecl::isResolved() const
{
  if (d_dtype == nullptr)
  {
    return true;
  }
  // We are resolved if a constructor is resolved. Note that since
  // internal::DType objects are copied in Solver::mkDatatypeSorts, the
  // constructors of d_dtype are passed to NodeManager but not d_type itself.
  // Thus, we must check whether our constructors are resolved.
  // This is a workaround; a clearer implementation would avoid the
  // copying of DType in Solver::mkDatatypeSorts.
  const std::vector<std::shared_ptr<internal::DTypeConstructor>>& cons =
      d_dtype->getConstructors();
  for (const std::shared_ptr<internal::DTypeConstructor>& c : cons)
  {
    if (c->isResolved())
    {
      return true;
    }
  }
  Assert(!d_dtype->isResolved());
  return false;
}

void DatatypeDecl::addConstructor(const DatatypeConstructorDecl& ctor)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_ARG_CHECK_NOT_NULL(ctor);
  CVC5_API_ARG_CHECK_TM("datatype constructor declaration", ctor);
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

DatatypeSelector::DatatypeSelector() : d_tm(nullptr), d_stor(nullptr) {}

DatatypeSelector::DatatypeSelector(TermManager* tm,
                                   const internal::DTypeSelector& stor)
    : d_tm(tm), d_stor(new internal::DTypeSelector(stor))
{
  CVC5_API_CHECK(d_stor->isResolved()) << "expected resolved datatype selector";
}

DatatypeSelector::~DatatypeSelector()
{
  if (d_stor != nullptr)
  {
    d_stor.reset();
  }
}

bool DatatypeSelector::operator==(const DatatypeSelector& sel) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_stor == sel.d_stor;
  ////////
  CVC5_API_TRY_CATCH_END;
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
  return Term(d_tm, d_stor->getSelector());
  ////////
  CVC5_API_TRY_CATCH_END;
}
Term DatatypeSelector::getUpdaterTerm() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Term(d_tm, d_stor->getUpdater());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort DatatypeSelector::getCodomainSort() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Sort(d_tm, d_stor->getRangeType());
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

DatatypeConstructor::DatatypeConstructor() : d_tm(nullptr), d_ctor(nullptr) {}

DatatypeConstructor::DatatypeConstructor(TermManager* tm,
                                         const internal::DTypeConstructor& ctor)
    : d_tm(tm), d_ctor(new internal::DTypeConstructor(ctor))
{
  CVC5_API_CHECK(d_ctor->isResolved())
      << "expected resolved datatype constructor";
}

DatatypeConstructor::~DatatypeConstructor()
{
  if (d_ctor != nullptr)
  {
    d_ctor.reset();
  }
}

bool DatatypeConstructor::operator==(const DatatypeConstructor& cons) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_ctor == cons.d_ctor;
  ////////
  CVC5_API_TRY_CATCH_END;
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
  return Term(d_tm, d_ctor->getConstructor());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term DatatypeConstructor::getInstantiatedTerm(const Sort& retSort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(d_ctor->isResolved())
      << "expected resolved datatype constructor";
  CVC5_API_CHECK(retSort.isDatatype())
      << "cannot get specialized constructor type for non-datatype type "
      << retSort;
  //////// all checks before this line
  internal::Node ret = d_ctor->getInstantiatedConstructor(*retSort.d_type);
  (void)ret.getType(true); /* kick off type checking */
  // apply type ascription to the operator
  Term sctor = Term(d_tm, ret);
  return sctor;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term DatatypeConstructor::getTesterTerm() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return Term(d_tm, d_ctor->getTester());
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
  CVC5_API_CHECK(index < d_ctor->getNumArgs()) << "index out of bounds";
  //////// all checks before this line
  return DatatypeSelector(d_tm, (*d_ctor)[index]);
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
  return DatatypeConstructor::const_iterator(d_tm, *d_ctor, true);
}

DatatypeConstructor::const_iterator DatatypeConstructor::end() const
{
  return DatatypeConstructor::const_iterator(d_tm, *d_ctor, false);
}

DatatypeConstructor::const_iterator::const_iterator(
    TermManager* tm, const internal::DTypeConstructor& ctor, bool begin)
{
  d_tm = tm;
  d_int_stors = &ctor.getArgs();

  const std::vector<std::shared_ptr<internal::DTypeSelector>>& sels =
      ctor.getArgs();
  for (const std::shared_ptr<internal::DTypeSelector>& s : sels)
  {
    /* Can not use emplace_back here since constructor is private. */
    d_stors.push_back(DatatypeSelector(d_tm, *s.get()));
  }
  d_idx = begin ? 0 : sels.size();
}

DatatypeConstructor::const_iterator::const_iterator()
    : d_tm(nullptr), d_int_stors(nullptr), d_idx(0)
{
}

DatatypeConstructor::const_iterator&
DatatypeConstructor::const_iterator::operator=(
    const DatatypeConstructor::const_iterator& it)
{
  d_tm = it.d_tm;
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
    CVC5_API_CHECK(foundSel) << "no selector " << name << " for constructor "
                             << getName() << " exists among " << snames.str();
  }
  return DatatypeSelector(d_tm, (*d_ctor)[index]);
}

std::ostream& operator<<(std::ostream& out, const DatatypeConstructor& ctor)
{
  out << ctor.toString();
  return out;
}

/* Datatype ----------------------------------------------------------------- */

Datatype::Datatype(TermManager* tm, const internal::DType& dtype)
    : d_tm(tm), d_dtype(new internal::DType(dtype))
{
  CVC5_API_CHECK(d_dtype->isResolved()) << "expected resolved datatype";
}

Datatype::Datatype() : d_tm(nullptr), d_dtype(nullptr) {}

Datatype::~Datatype()
{
  if (d_dtype != nullptr)
  {
    d_dtype.reset();
  }
}

bool Datatype::operator==(const Datatype& dt) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  //////// all checks before this line
  return d_dtype == dt.d_dtype;
  ////////
  CVC5_API_TRY_CATCH_END;
}

DatatypeConstructor Datatype::operator[](size_t idx) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK_NOT_NULL;
  CVC5_API_CHECK(idx < getNumConstructors()) << "index out of bounds.";
  //////// all checks before this line
  return DatatypeConstructor(d_tm, (*d_dtype)[idx]);
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
  CVC5_API_CHECK(isParametric()) << "expected parametric datatype";
  //////// all checks before this line
  std::vector<internal::TypeNode> params = d_dtype->getParameters();
  return Sort::typeNodeVectorToSorts(d_tm, params);
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
      << "invalid call to 'isFinite()', expected non-parametric datatype";
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
  return Datatype::const_iterator(d_tm, *d_dtype, true);
}

Datatype::const_iterator Datatype::end() const
{
  return Datatype::const_iterator(d_tm, *d_dtype, false);
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
    CVC5_API_CHECK(foundCons) << "no constructor " << name << " for datatype "
                              << getName() << " exists, among " << snames.str();
  }
  return DatatypeConstructor(d_tm, (*d_dtype)[index]);
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
        << "no selector " << name << " for datatype " << getName() << " exists";
  }
  return DatatypeSelector(d_tm, (*d_dtype)[index][sindex]);
}

Datatype::const_iterator::const_iterator(TermManager* tm,
                                         const internal::DType& dtype,
                                         bool begin)
    : d_tm(tm), d_int_ctors(&dtype.getConstructors())
{
  const std::vector<std::shared_ptr<internal::DTypeConstructor>>& cons =
      dtype.getConstructors();
  for (const std::shared_ptr<internal::DTypeConstructor>& c : cons)
  {
    /* Can not use emplace_back here since constructor is private. */
    d_ctors.push_back(DatatypeConstructor(d_tm, *c.get()));
  }
  d_idx = begin ? 0 : cons.size();
}

Datatype::const_iterator::const_iterator()
    : d_tm(nullptr), d_int_ctors(nullptr), d_idx(0)
{
}

Datatype::const_iterator& Datatype::const_iterator::operator=(
    const Datatype::const_iterator& it)
{
  d_tm = it.d_tm;
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

Grammar::Grammar() : d_tm(nullptr) {}

Grammar::Grammar(TermManager* tm,
                 const std::vector<Term>& sygusVars,
                 const std::vector<Term>& ntSymbols)
    : d_tm(tm),
      d_grammar(std::make_shared<internal::SygusGrammar>(
          Term::termVectorToNodes(sygusVars),
          Term::termVectorToNodes(ntSymbols)))
{
}

Grammar::~Grammar() { d_grammar.reset(); }

bool Grammar::isNull() const { return d_grammar == nullptr; }

bool contains(const std::vector<internal::Node>& ns, const internal::Node& n)
{
  return std::find(ns.cbegin(), ns.cend(), n) != ns.cend();
}

void Grammar::addRule(const Term& ntSymbol, const Term& rule)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_grammar->isResolved())
      << "Grammar cannot be modified after passing "
         "it as an argument to synthFun";
  CVC5_API_CHECK_TERM(ntSymbol);
  CVC5_API_CHECK_TERM(rule);
  CVC5_API_ARG_CHECK_EXPECTED(
      contains(d_grammar->getNtSyms(), *ntSymbol.d_node), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  CVC5_API_CHECK(
      ntSymbol.d_node->getType().isInstanceOf(rule.d_node->getType()))
      << "expected ntSymbol and rule to have the same sort";
  //////// all checks before this line
  d_grammar->addRule(*ntSymbol.d_node, *rule.d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Grammar::addRules(const Term& ntSymbol, const std::vector<Term>& rules)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_grammar->isResolved())
      << "Grammar cannot be modified after passing "
         "it as an argument to synthFun";
  CVC5_API_CHECK_TERM(ntSymbol);
  CVC5_API_CHECK_TERMS_WITH_SORT(rules, ntSymbol.getSort());
  CVC5_API_ARG_CHECK_EXPECTED(
      contains(d_grammar->getNtSyms(), *ntSymbol.d_node), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  //////// all checks before this line
  d_grammar->addRules(*ntSymbol.d_node, Term::termVectorToNodes(rules));
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Grammar::addAnyConstant(const Term& ntSymbol)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_grammar->isResolved())
      << "Grammar cannot be modified after passing "
         "it as an argument to synthFun";
  CVC5_API_CHECK_TERM(ntSymbol);
  CVC5_API_ARG_CHECK_EXPECTED(
      contains(d_grammar->getNtSyms(), *ntSymbol.d_node), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  //////// all checks before this line
  d_grammar->addAnyConstant(*ntSymbol.d_node, ntSymbol.d_node->getType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Grammar::addAnyVariable(const Term& ntSymbol)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_grammar->isResolved())
      << "Grammar cannot be modified after passing "
         "it as an argument to synthFun";
  CVC5_API_CHECK_TERM(ntSymbol);
  CVC5_API_ARG_CHECK_EXPECTED(
      contains(d_grammar->getNtSyms(), *ntSymbol.d_node), ntSymbol)
      << "ntSymbol to be one of the non-terminal symbols given in the "
         "predeclaration";
  //////// all checks before this line
  d_grammar->addAnyVariable(*ntSymbol.d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Grammar::toString() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_grammar == nullptr || !d_grammar->hasRules() ? ""
                                                        : d_grammar->toString();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Grammar::resolve()
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(d_tm, d_grammar->resolve());
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::ostream& operator<<(std::ostream& out, const Grammar& grammar)
{
  CVC5_API_TRY_CATCH_BEGIN;
  return out << grammar.toString();
  CVC5_API_TRY_CATCH_END;
}

bool Grammar::operator==(const Grammar& grammar) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_grammar == grammar.d_grammar;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Grammar::operator!=(const Grammar& grammar) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_grammar != grammar.d_grammar;
  ////////
  CVC5_API_TRY_CATCH_END;
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
Stat::Stat(const Stat& s) : d_internal(s.d_internal), d_default(s.d_default)
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
  CVC5_API_RECOVERABLE_CHECK(static_cast<bool>(d_data))
      << "Stat holds no value";
  CVC5_API_RECOVERABLE_CHECK(isInt()) << "expected Stat of type int64_t.";
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
  CVC5_API_RECOVERABLE_CHECK(static_cast<bool>(d_data))
      << "Stat holds no value";
  CVC5_API_RECOVERABLE_CHECK(isDouble()) << "expected Stat of type double.";
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
  CVC5_API_RECOVERABLE_CHECK(static_cast<bool>(d_data))
      << "Stat holds no value";
  CVC5_API_RECOVERABLE_CHECK(isString())
      << "expected Stat of type std::string.";
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
  CVC5_API_RECOVERABLE_CHECK(static_cast<bool>(d_data))
      << "Stat holds no value";
  CVC5_API_RECOVERABLE_CHECK(isHistogram())
      << "expected Stat of type histogram.";
  return std::get<HistogramData>(d_data->data);
  CVC5_API_TRY_CATCH_END;
}

Stat::Stat(bool internal, bool defaulted, StatData&& sd)
    : d_internal(internal),
      d_default(defaulted),
      d_data(std::make_unique<StatData>(std::move(sd)))
{
}

std::string Stat::toString() const
{
  std::stringstream ss;
  internal::detail::print(ss, d_data->data);
  return ss.str();
}

std::ostream& operator<<(std::ostream& os, const Stat& stat)
{
  return internal::detail::print(os, stat.d_data->data);
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
    : d_it(it),
      d_base(&base),
      d_showInternal(internal),
      d_showDefault(defaulted)
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
      << "no statistic with name \"" << name << "\" exists.";
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

std::string Statistics::toString() const
{
  std::stringstream ss;
  for (const auto& stat : *this)
  {
    ss << stat.first << " = " << stat.second << std::endl;
  }
  return ss.str();
}

std::ostream& operator<<(std::ostream& out, const Statistics& stats)
{
  out << stats.toString();
  return out;
}

/*--------------------------------------------------------------------------- */
/* Proof                                                                      */
/* -------------------------------------------------------------------------- */

Proof::Proof() : d_tm(nullptr) {}

Proof::Proof(TermManager* tm, const std::shared_ptr<internal::ProofNode> p)
    : d_proofNode(p), d_tm(tm)
{
}

Proof::~Proof() {}

bool Proof::isNull() const { return d_proofNode == nullptr; }

ProofRule Proof::getRule() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (d_proofNode != nullptr)
  {
    return d_proofNode->getRule();
  }
  return ProofRule::UNKNOWN;
  ////////
  CVC5_API_TRY_CATCH_END;
}

ProofRewriteRule Proof::getRewriteRule() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_proofNode->getRule() == ProofRule::DSL_REWRITE
                 || d_proofNode->getRule() == ProofRule::THEORY_REWRITE)
      << "expected `getRule()` to return `DSL_REWRITE` or `THEORY_REWRITE`, "
         "got "
      << d_proofNode->getRule() << " instead.";
  //////// all checks before this line
  if (d_proofNode != nullptr)
  {
    return static_cast<ProofRewriteRule>(
        detail::getInteger(d_proofNode->getArguments()[0]).getUnsignedInt());
  }
  return ProofRewriteRule::NONE;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Proof::getResult() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (d_proofNode != nullptr)
  {
    return Term(d_tm, d_proofNode->getResult());
  }
  return Term();
  ////////
  CVC5_API_TRY_CATCH_END;
}

const std::vector<Proof> Proof::getChildren() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (d_proofNode != nullptr)
  {
    std::vector<Proof> children;
    std::vector<std::shared_ptr<internal::ProofNode>> nodeChildren =
        d_proofNode->getChildren();
    for (size_t i = 0, psize = nodeChildren.size(); i < psize; i++)
    {
      children.push_back(Proof(d_tm, nodeChildren[i]));
    }
    return children;
  }
  return std::vector<Proof>();
  ////////
  CVC5_API_TRY_CATCH_END;
}

const std::vector<Term> Proof::getArguments() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (d_proofNode != nullptr)
  {
    std::vector<Term> args;
    const std::vector<internal::Node> nodeArgs = d_proofNode->getArguments();
    for (size_t i = 0, asize = nodeArgs.size(); i < asize; i++)
    {
      args.push_back(Term(d_tm, nodeArgs[i]));
    }
    return args;
  }
  return std::vector<Term>();
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Proof::operator==(const Proof& p) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_proofNode == p.d_proofNode;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Proof::operator!=(const Proof& p) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_proofNode != p.d_proofNode;
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* Plugin                                                                     */
/* -------------------------------------------------------------------------- */

Plugin::Plugin(TermManager& tm)
    : d_pExtToInt(new PluginInternal(tm.d_nm.get(), tm, *this))
{
}

std::vector<Term> Plugin::check() { return {}; }
void Plugin::notifySatClause(const Term& clause) {}
void Plugin::notifyTheoryLemma(const Term& lemma) {}

/* -------------------------------------------------------------------------- */
/* TermManager                                                                */
/* -------------------------------------------------------------------------- */

TermManager::TermManager() : d_nm(std::make_unique<internal::NodeManager>())
{
  if constexpr (internal::configuration::isStatisticsBuild())
  {
    d_statsReg.reset(new internal::StatisticsRegistry());
    resetStatistics();
  }
}

TermManager::~TermManager() {}

Statistics TermManager::getStatistics() const
{
  return Statistics(*d_statsReg);
}

void TermManager::printStatisticsSafe(int fd) const
{
  d_statsReg->printSafe(fd);
}

/* Helpers and private functions                                              */
/* -------------------------------------------------------------------------- */

void TermManager::increment_term_stats(Kind kind) const
{
  if constexpr (internal::configuration::isStatisticsBuild())
  {
    d_stats->d_terms << kind;
  }
}

void TermManager::increment_vars_consts_stats(const internal::TypeNode& type,
                                              bool is_var) const
{
  if constexpr (internal::configuration::isStatisticsBuild())
  {
    internal::TypeConstant tc = type.getKind() == internal::Kind::TYPE_CONSTANT
                                    ? type.getConst<internal::TypeConstant>()
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

void TermManager::resetStatistics()
{
  d_stats.reset(new APIStatistics{
      d_statsReg->registerHistogram<internal::TypeConstant>("cvc5::CONSTANT"),
      d_statsReg->registerHistogram<internal::TypeConstant>("cvc5::VARIABLE"),
      d_statsReg->registerHistogram<Kind>("cvc5::TERM"),
  });
}

TermManager* TermManager::currentTM()
{
  thread_local static TermManager tm;
  return &tm;
}

void TermManager::checkMkTerm(Kind kind, uint32_t nchildren) const
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
      << "Terms with kind " << std::to_string(kind) << " must have at least "
      << minArity(kind) << " children and at most " << maxArity(kind)
      << " children (the one under construction has " << nchildren << ")";
}

bool TermManager::isValidInteger(const std::string& s) const
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

// This helpers are split out to avoid nested API calls (problematic with API
// tracing).

internal::Node TermManager::mkVarHelper(
    const internal::TypeNode& type, const std::optional<std::string>& symbol)
{
  internal::Node res = symbol ? internal::NodeManager::mkBoundVar(*symbol, type)
                              : internal::NodeManager::mkBoundVar(type);
  (void)res.getType(true); /* kick off type checking */
  increment_vars_consts_stats(type, true);
  return res;
}

internal::Node TermManager::mkConstHelper(
    const internal::TypeNode& type,
    const std::optional<std::string>& symbol,
    bool fresh)
{
  Assert(fresh || symbol);
  internal::Node res =
      symbol ? d_nm->mkVar(*symbol, type, fresh) : d_nm->mkVar(type);
  (void)res.getType(true); /* kick off type checking */
  increment_vars_consts_stats(type, false);
  return res;
}

template <typename T>
Op TermManager::mkOpHelper(Kind kind, const T& t)
{
  //////// all checks before this line
  internal::Node res = d_nm->mkConst(s_op_kinds.at(kind), t);
  static_cast<void>(res.getType(true)); /* kick off type checking */
  return Op(this, kind, res);
}

template <typename T>
Term TermManager::mkValHelper(const T& t)
{
  //////// all checks before this line
  internal::Node res = d_nm->mkConst(t);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
}

Term TermManager::mkRationalValHelper(const internal::Rational& r, bool isInt)
{
  //////// all checks before this line
  internal::Node res = isInt ? d_nm->mkConstInt(r) : d_nm->mkConstReal(r);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
}

Term TermManager::mkRealOrIntegerFromStrHelper(const std::string& s, bool isInt)
{
  //////// all checks before this line
  try
  {
    internal::Rational r;
    size_t spos = s.find('/');
    if (spos != std::string::npos)
    {
      // Ensure the denominator contains a non-zero digit. We catch this here to
      // avoid a floating point exception in GMP. This exception will be caught
      // and given the standard error message below.
      if (s.find_first_not_of('0', spos + 1) == std::string::npos)
      {
        throw std::invalid_argument("Zero denominator encountered");
      }
      r = internal::Rational(s);
    }
    else
    {
      r = internal::Rational::fromDecimal(s);
    }
    return TermManager::mkRationalValHelper(r, isInt);
  }
  catch (const std::invalid_argument& e)
  {
    /* Catch to throw with a more meaningful error message. To be caught in
     * enclosing CVC5_API_TRY_CATCH_* block to throw CVC5ApiException. */
    std::stringstream message;
    message << "cannot construct Real or Int from string argument '" << s
            << "'";
    throw std::invalid_argument(message.str());
  }
}

Term TermManager::mkBVFromIntHelper(uint32_t size, uint64_t val)
{
  CVC5_API_ARG_CHECK_EXPECTED(size > 0, size) << "a bit-width > 0";
  //////// all checks before this line
  return mkValHelper(internal::BitVector(size, val));
}

Term TermManager::mkBVFromStrHelper(uint32_t size,
                                    const std::string& s,
                                    uint32_t base)
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
        << "overflow in bit-vector construction (specified bit-vector size "
        << size << " too small to hold value " << s << ")";
  }
  else
  {
    CVC5_API_CHECK(val.modByPow2(size) == val)
        << "overflow in bit-vector construction (specified bit-vector size "
        << size << " too small to hold value " << s << ")";
  }
  return mkValHelper(internal::BitVector(size, val));
}

Sort TermManager::mkTupleSortHelper(const std::vector<Sort>& sorts)
{
  // Note: Sorts are checked in the caller to avoid double checks
  //////// all checks before this line
  std::vector<internal::TypeNode> typeNodes =
      Sort::sortVectorToTypeNodes(sorts);
  return Sort(this, d_nm->mkTupleType(typeNodes));
}

Term TermManager::mkTermFromKind(Kind kind)
{
  CVC5_API_KIND_CHECK_EXPECTED(
      kind == Kind::PI || kind == Kind::REGEXP_NONE || kind == Kind::REGEXP_ALL
          || kind == Kind::REGEXP_ALLCHAR || kind == Kind::SEP_EMP,
      kind)
      << "PI, REGEXP_NONE, REGEXP_ALL, REGEXP_ALLCHAR or SEP_EMP";
  //////// all checks before this line
  internal::Node res;
  internal::Kind k = extToIntKind(kind);
  if (kind == Kind::REGEXP_NONE || kind == Kind::REGEXP_ALL
      || kind == Kind::REGEXP_ALLCHAR)
  {
    Assert(isDefinedIntKind(k));
    res = d_nm->mkNode(k, std::vector<internal::Node>());
  }
  else if (kind == Kind::SEP_EMP)
  {
    res = d_nm->mkNullaryOperator(d_nm->booleanType(), k);
  }
  else
  {
    Assert(kind == Kind::PI);
    res = d_nm->mkNullaryOperator(d_nm->realType(), k);
  }
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
}

Term TermManager::mkTermHelper(Kind kind, const std::vector<Term>& children)
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
    if (kind == Kind::INTS_DIVISION || kind == Kind::XOR || kind == Kind::SUB
        || kind == Kind::DIVISION || kind == Kind::HO_APPLY
        || kind == Kind::REGEXP_DIFF || kind == Kind::SET_UNION
        || kind == Kind::SET_INTER || kind == Kind::SET_MINUS
        || kind == Kind::BAG_INTER_MIN || kind == Kind::BAG_UNION_MAX
        || kind == Kind::BAG_UNION_DISJOINT
        || kind == Kind::BAG_DIFFERENCE_REMOVE
        || kind == Kind::BAG_DIFFERENCE_SUBTRACT)
    {
      // left-associative, but cvc5 internally only supports 2 args
      res = d_nm->mkLeftAssociative(k, echildren);
    }
    else if (kind == Kind::IMPLIES)
    {
      // right-associative, but cvc5 internally only supports 2 args
      res = d_nm->mkRightAssociative(k, echildren);
    }
    else if (kind == Kind::EQUAL || kind == Kind::LT || kind == Kind::GT
             || kind == Kind::LEQ || kind == Kind::GEQ)
    {
      // "chainable", but cvc5 internally only supports 2 args
      res = d_nm->mkChain(k, echildren);
    }
    else if (internal::kind::isAssociative(k))
    {
      // mkAssociative has special treatment for associative operators with lots
      // of children
      res = d_nm->mkAssociative(k, echildren);
    }
    else
    {
      // default case, must check kind
      checkMkTerm(kind, children.size());
      res = d_nm->mkNode(k, echildren);
    }
  }
  else if (internal::kind::isAssociative(k))
  {
    // associative case, same as above
    checkMkTerm(kind, children.size());
    res = d_nm->mkAssociative(k, echildren);
  }
  else
  {
    // default case, same as above
    checkMkTerm(kind, children.size());
    // make the term
    res = d_nm->mkNode(k, echildren);
  }

  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
}

Term TermManager::mkTermHelper(const Op& op, const std::vector<Term>& children)
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

  internal::NodeBuilder nb(d_nm.get(), int_kind);
  nb << *op.d_node;
  nb.append(echildren);
  internal::Node res = nb.constructNode();

  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
}

/* Sorts -------------------------------------------------------------------- */

Sort TermManager::getBooleanSort(void)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, d_nm->booleanType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::getIntegerSort(void)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, d_nm->integerType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::getRealSort(void)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, d_nm->realType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::getRegExpSort(void)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, d_nm->regExpType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::getStringSort(void)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, d_nm->stringType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::getRoundingModeSort(void)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, d_nm->roundingModeType());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkArraySort(const Sort& indexSort, const Sort& elemSort)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(indexSort);
  CVC5_API_TM_CHECK_SORT(elemSort);
  //////// all checks before this line
  return Sort(this, d_nm->mkArrayType(*indexSort.d_type, *elemSort.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkBitVectorSort(uint32_t size)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(size > 0, size) << "size > 0";
  //////// all checks before this line
  return Sort(this, d_nm->mkBitVectorType(size));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkFiniteFieldSort(const std::string& modulus, uint32_t base)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::Integer m(modulus, base);
  CVC5_API_ARG_CHECK_EXPECTED(m.isProbablePrime(), modulus)
      << "modulus is prime";
  return Sort(this, d_nm->mkFiniteFieldType(m));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkFloatingPointSort(uint32_t exp, uint32_t sig)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(exp > 1, exp) << "exponent size > 1";
  CVC5_API_ARG_CHECK_EXPECTED(sig > 1, sig) << "significand size > 1";
  //////// all checks before this line
  return Sort(this, d_nm->mkFloatingPointType(exp, sig));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkDatatypeSort(const DatatypeDecl& dtypedecl)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_DTDECL(dtypedecl);
  //////// all checks before this line
  Sort res = Sort(this, d_nm->mkDatatypeType(*dtypedecl.d_dtype));
  const Datatype& dt = res.getDatatype();
  CVC5_API_CHECK(dt.d_dtype->isCodatatype() || dt.d_dtype->isWellFounded())
      << "Datatype sort " << dt.d_dtype->getName() + " is not well-founded";
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Sort> TermManager::mkDatatypeSorts(
    const std::vector<DatatypeDecl>& dtypedecls)
{
  CVC5_API_TM_CHECK_DTDECLS(dtypedecls);
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  std::vector<internal::DType> datatypes;
  for (size_t i = 0, ndts = dtypedecls.size(); i < ndts; ++i)
  {
    datatypes.push_back(dtypedecls[i].getDatatype());
  }
  std::vector<internal::TypeNode> dtypes =
      d_nm->mkMutualDatatypeTypes(datatypes);
  std::vector<Sort> res = Sort::typeNodeVectorToSorts(this, dtypes);
  for (size_t i = 0, ndts = datatypes.size(); i < ndts; ++i)
  {
    const Datatype& dt = res[i].getDatatype();
    CVC5_API_CHECK(dt.d_dtype->isCodatatype() || dt.d_dtype->isWellFounded())
        << "Datatype sort " << dt.d_dtype->getName() + " is not well-founded";
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkFunctionSort(const std::vector<Sort>& sorts,
                                 const Sort& codomain)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_SIZE_CHECK_EXPECTED(sorts.size() >= 1, sorts)
      << "at least one parameter sort for function sort";
  CVC5_API_TM_CHECK_DOMAIN_SORTS(sorts);
  CVC5_API_TM_CHECK_CODOMAIN_SORT(codomain);
  //////// all checks before this line
  std::vector<internal::TypeNode> argTypes = Sort::sortVectorToTypeNodes(sorts);
  return Sort(this, d_nm->mkFunctionType(argTypes, *codomain.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkSkolem(SkolemId id, const std::vector<Term>& indices)
{
  CVC5_API_TRY_CATCH_BEGIN;
  cvc5::internal::SkolemManager* sm = d_nm->getSkolemManager();
  CVC5_API_CHECK(indices.size() == sm->getNumIndicesForSkolemId(id))
      << "invalid number of indices, expected "
      << sm->getNumIndicesForSkolemId(id) << " got " << indices.size();
  //////// all checks before this line
  // iterate over indices and convert the Terms to Nodes
  std::vector<internal::Node> nodeIndices = Term::termVectorToNodes(indices);
  // automatically sort if a commutative skolem
  if (internal::SkolemManager::isCommutativeSkolemId(id))
  {
    std::sort(nodeIndices.begin(), nodeIndices.end());
  }
  internal::Node res =
      d_nm->getSkolemManager()->mkSkolemFunction(id, nodeIndices);
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

size_t TermManager::getNumIndicesForSkolemId(SkolemId id)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_nm->getSkolemManager()->getNumIndicesForSkolemId(id);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkParamSort(const std::optional<std::string>& symbol)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::TypeNode tn = symbol ? d_nm->mkSort(*symbol) : d_nm->mkSort();
  return Sort(this, tn);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkPredicateSort(const std::vector<Sort>& sorts)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_SIZE_CHECK_EXPECTED(sorts.size() >= 1, sorts)
      << "at least one parameter sort for predicate sort";
  CVC5_API_TM_CHECK_DOMAIN_SORTS(sorts);
  //////// all checks before this line
  return Sort(this, d_nm->mkPredicateType(Sort::sortVectorToTypeNodes(sorts)));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkRecordSort(
    const std::vector<std::pair<std::string, Sort>>& fields)
{
  CVC5_API_TRY_CATCH_BEGIN;
  std::vector<std::pair<std::string, internal::TypeNode>> f;
  for (size_t i = 0, size = fields.size(); i < size; ++i)
  {
    const auto& p = fields[i];
    CVC5_API_TM_CHECK_SORT_AT_INDEX(p.second, fields, i);
    f.emplace_back(p.first, *p.second.d_type);
  }
  //////// all checks before this line
  return Sort(this, d_nm->mkRecordType(f));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkSetSort(const Sort& elemSort)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(elemSort);
  //////// all checks before this line
  return Sort(this, d_nm->mkSetType(*elemSort.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkBagSort(const Sort& elemSort)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(elemSort);
  //////// all checks before this line
  return Sort(this, d_nm->mkBagType(*elemSort.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkSequenceSort(const Sort& elemSort)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(elemSort);
  //////// all checks before this line
  return Sort(this, d_nm->mkSequenceType(*elemSort.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkAbstractSort(SortKind k)
{
  CVC5_API_TRY_CATCH_BEGIN;
  internal::Kind ik = extToIntSortKind(k);
  CVC5_API_CHECK(d_nm->isSortKindAbstractable(ik))
      << "cannot construct abstract type for kind " << k;
  //////// all checks before this line
  return Sort(this, d_nm->mkAbstractType(ik));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkUninterpretedSort(const std::optional<std::string>& symbol)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::TypeNode tn = symbol ? d_nm->mkSort(*symbol) : d_nm->mkSort();
  return Sort(this, tn);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkUnresolvedDatatypeSort(const std::string& symbol,
                                           size_t arity)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Sort(this, d_nm->mkUnresolvedDatatypeSort(symbol, arity));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkUninterpretedSortConstructorSort(
    size_t arity, const std::optional<std::string>& symbol)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(arity > 0, arity) << "an arity > 0";
  //////// all checks before this line
  if (symbol)
  {
    return Sort(this, d_nm->mkSortConstructor(*symbol, arity));
  }
  return Sort(this, d_nm->mkSortConstructor("", arity));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkTupleSort(const std::vector<Sort>& sorts)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_DOMAIN_SORTS(sorts);
  //////// all checks before this line
  return mkTupleSortHelper(sorts);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort TermManager::mkNullableSort(const Sort& sort)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_DOMAIN_SORT(sort);
  //////// all checks before this line
  return Sort(this, d_nm->mkNullableType(sort.getTypeNode()));
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Terms -------------------------------------------------------------------- */

Term TermManager::mkTerm(Kind kind, const std::vector<Term>& children)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_KIND_CHECK(kind);
  CVC5_API_TM_CHECK_TERMS(children);
  //////// all checks before this line
  Term res = mkTermHelper(kind, children);
  increment_term_stats(kind);
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkTerm(const Op& op, const std::vector<Term>& children)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_OP(op);
  CVC5_API_TM_CHECK_TERMS(children);
  //////// all checks before this line
  Term res = mkTermHelper(op, children);
  increment_term_stats(op.getKind());
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Operators ---------------------------------------------------------------- */

Op TermManager::mkOp(Kind kind, const std::vector<uint32_t>& args)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_KIND_CHECK(kind);
  //////// all checks before this line
  size_t nargs = args.size();

  Op res;
  switch (kind)
  {
    case Kind::BITVECTOR_EXTRACT:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      res = mkOpHelper(kind, internal::BitVectorExtract(args[0], args[1]));
      break;
    case Kind::BITVECTOR_REPEAT:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::BitVectorRepeat(args[0]));
      break;
    case Kind::BITVECTOR_ROTATE_LEFT:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::BitVectorRotateLeft(args[0]));
      break;
    case Kind::BITVECTOR_ROTATE_RIGHT:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::BitVectorRotateRight(args[0]));
      break;
    case Kind::BITVECTOR_SIGN_EXTEND:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::BitVectorSignExtend(args[0]));
      break;
    case Kind::BITVECTOR_ZERO_EXTEND:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::BitVectorZeroExtend(args[0]));
      break;
    case Kind::BITVECTOR_BIT:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::BitVectorBit(args[0]));
      break;
    case Kind::DIVISIBLE:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      CVC5_API_CHECK_OP_INDEX(args[0] != 0, args, 0) << "a value != 0";
      res = mkOpHelper(kind, internal::Divisible(args[0]));
      break;
    case Kind::FLOATINGPOINT_TO_SBV:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::FloatingPointToSBV(args[0]));
      break;
    case Kind::FLOATINGPOINT_TO_UBV:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::FloatingPointToUBV(args[0]));
      break;
    case Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      CVC5_API_CHECK_OP_INDEX(args[0] > 1, args, 0) << "a value > 1";
      CVC5_API_CHECK_OP_INDEX(args[1] > 1, args, 1) << "a value > 1";
      res = mkOpHelper(
          kind, internal::FloatingPointToFPIEEEBitVector(args[0], args[1]));
      break;
    case Kind::FLOATINGPOINT_TO_FP_FROM_FP:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      CVC5_API_CHECK_OP_INDEX(args[0] > 1, args, 0) << "a value > 1";
      CVC5_API_CHECK_OP_INDEX(args[1] > 1, args, 1) << "a value > 1";
      res = mkOpHelper(
          kind, internal::FloatingPointToFPFloatingPoint(args[0], args[1]));
      break;
    case Kind::FLOATINGPOINT_TO_FP_FROM_REAL:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      CVC5_API_CHECK_OP_INDEX(args[0] > 1, args, 0) << "a value > 1";
      CVC5_API_CHECK_OP_INDEX(args[1] > 1, args, 1) << "a value > 1";
      res = mkOpHelper(kind, internal::FloatingPointToFPReal(args[0], args[1]));
      break;
    case Kind::FLOATINGPOINT_TO_FP_FROM_SBV:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      CVC5_API_CHECK_OP_INDEX(args[0] > 1, args, 0) << "a value > 1";
      CVC5_API_CHECK_OP_INDEX(args[1] > 1, args, 1) << "a value > 1";
      res = mkOpHelper(
          kind, internal::FloatingPointToFPSignedBitVector(args[0], args[1]));
      break;
    case Kind::FLOATINGPOINT_TO_FP_FROM_UBV:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      CVC5_API_CHECK_OP_INDEX(args[0] > 1, args, 0) << "a value > 1";
      CVC5_API_CHECK_OP_INDEX(args[1] > 1, args, 1) << "a value > 1";
      res = mkOpHelper(
          kind, internal::FloatingPointToFPUnsignedBitVector(args[0], args[1]));
      break;
    case Kind::IAND:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::IntAnd(args[0]));
      break;
    case Kind::INT_TO_BITVECTOR:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::IntToBitVector(args[0]));
      break;
    case Kind::REGEXP_REPEAT:
      CVC5_API_OP_CHECK_ARITY(nargs, 1, kind);
      res = mkOpHelper(kind, internal::RegExpRepeat(args[0]));
      break;
    case Kind::REGEXP_LOOP:
      CVC5_API_OP_CHECK_ARITY(nargs, 2, kind);
      res = mkOpHelper(kind, internal::RegExpLoop(args[0], args[1]));
      break;
    case Kind::TUPLE_PROJECT:
    case Kind::RELATION_AGGREGATE:
    case Kind::RELATION_GROUP:
    case Kind::RELATION_PROJECT:
    case Kind::RELATION_TABLE_JOIN:
    case Kind::TABLE_AGGREGATE:
    case Kind::TABLE_GROUP:
    case Kind::TABLE_JOIN:
    case Kind::TABLE_PROJECT:
    {
      res = mkOpHelper(kind, internal::ProjectOp(args));
      break;
    }
    default:
      if (nargs == 0)
      {
        CVC5_API_CHECK(s_indexed_kinds.find(kind) == s_indexed_kinds.end())
            << "expected a kind for a non-indexed operator.";
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

Op TermManager::mkOp(Kind kind, const std::initializer_list<uint32_t>& args)
{
  return mkOp(kind, std::vector<uint32_t>(args));
}

Op TermManager::mkOp(Kind kind, const std::string& arg)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_KIND_CHECK(kind);
  CVC5_API_KIND_CHECK_EXPECTED((kind == Kind::DIVISIBLE), kind) << "DIVISIBLE";
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

/* Constants, Values and Special Terms -------------------------------------- */

Term TermManager::mkTrue(void)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Term(this, d_nm->mkConst<bool>(true));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkFalse(void)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Term(this, d_nm->mkConst<bool>(false));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkBoolean(bool val)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Term(this, d_nm->mkConst<bool>(val));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkPi()
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::Node res =
      d_nm->mkNullaryOperator(d_nm->realType(), internal::Kind::PI);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkInteger(const std::string& s)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(isValidInteger(s), s) << "an integer ";
  Term res = mkRealOrIntegerFromStrHelper(s);
  CVC5_API_ARG_CHECK_EXPECTED(res.getSort() == getIntegerSort(), s)
      << "a string representing an integer";
  //////// all checks before this line
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkInteger(int64_t val)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  Term res = TermManager::mkRationalValHelper(internal::Rational(val), true);
  Assert(res.getSort() == getIntegerSort());
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkReal(const std::string& s)
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

Term TermManager::mkReal(int64_t val)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return TermManager::mkRationalValHelper(internal::Rational(val), false);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkReal(int64_t num, int64_t den)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(den != 0) << "invalid denominator '" << den << "'";
  //////// all checks before this line
  return TermManager::mkRationalValHelper(internal::Rational(num, den), false);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkRegexpAll()
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::Node res =
      d_nm->mkNode(internal::Kind::REGEXP_ALL, std::vector<internal::Node>());
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkRegexpNone()
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::Node res =
      d_nm->mkNode(internal::Kind::REGEXP_NONE, std::vector<internal::Node>());
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkRegexpAllchar()
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::Node res = d_nm->mkNode(internal::Kind::REGEXP_ALLCHAR,
                                    std::vector<internal::Node>());
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkEmptySet(const Sort& sort)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(sort);
  CVC5_API_ARG_CHECK_EXPECTED(sort.isSet(), sort) << "null sort or set sort";
  //////// all checks before this line
  return mkValHelper(internal::EmptySet(*sort.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkEmptyBag(const Sort& sort)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(sort);
  CVC5_API_ARG_CHECK_EXPECTED(sort.isBag(), sort) << "null sort or bag sort";
  //////// all checks before this line
  return mkValHelper(internal::EmptyBag(*sort.d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkSepEmp()
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::Node res =
      d_nm->mkNullaryOperator(d_nm->booleanType(), internal::Kind::SEP_EMP);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkSepNil(const Sort& sort)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(sort);
  //////// all checks before this line
  internal::Node res =
      d_nm->mkNullaryOperator(*sort.d_type, internal::Kind::SEP_NIL);
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkString(const std::string& s, bool useEscSequences)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper(internal::String(s, useEscSequences));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkString(const std::wstring& s)
{
  CVC5_API_TRY_CATCH_BEGIN;
  for (size_t i = 0, n = s.size(); i < n; ++i)
  {
    CVC5_API_CHECK(static_cast<unsigned>(s[i]) < internal::String::num_codes())
        << "Expected unicode string whose characters are less than code point "
        << internal::String::num_codes();
  }
  //////// all checks before this line
  return mkValHelper(internal::String(s));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkString(const std::u32string& s)
{
  CVC5_API_TRY_CATCH_BEGIN;
  for (size_t i = 0, n = s.size(); i < n; ++i)
  {
    CVC5_API_CHECK(static_cast<unsigned>(s[i]) < internal::String::num_codes())
        << "Expected unicode string whose characters are less than code point "
        << internal::String::num_codes();
  }
  //////// all checks before this line
  return mkValHelper(internal::String(s));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkEmptySequence(const Sort& sort)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(sort);
  //////// all checks before this line
  std::vector<internal::Node> seq;
  internal::Node res = d_nm->mkConst(internal::Sequence(*sort.d_type, seq));
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkUniverseSet(const Sort& sort)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(sort);
  //////// all checks before this line
  internal::Node res =
      d_nm->mkNullaryOperator(*sort.d_type, internal::Kind::SET_UNIVERSE);
  // TODO(#2771): Reenable?
  // (void)res->getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkBitVector(uint32_t size, uint64_t val)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkBVFromIntHelper(size, val);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkBitVector(uint32_t size,
                              const std::string& s,
                              uint32_t base)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkBVFromStrHelper(size, s, base);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkFiniteFieldElem(const std::string& value,
                                    const Sort& sort,
                                    uint32_t base)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(sort);
  CVC5_API_ARG_CHECK_EXPECTED(sort.isFiniteField(), sort)
      << "a finite field sort";
  //////// all checks before this line
  internal::Integer v(value, base);
  internal::FiniteFieldValue f(v, sort.d_type->getFfSize());

  return mkValHelper<internal::FiniteFieldValue>(f);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkConstArray(const Sort& sort, const Term& val)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(sort);
  CVC5_API_TM_CHECK_TERM(val);
  CVC5_API_ARG_CHECK_EXPECTED(sort.isArray(), sort) << "an array sort";
  CVC5_API_CHECK(val.getSort() == sort.getArrayElementSort())
      << "value does not match element sort";
  internal::Node n = *val.d_node;
  CVC5_API_ARG_CHECK_EXPECTED(n.isConst(), val) << "a value";
  //////// all checks before this line
  Term res = mkValHelper(internal::ArrayStoreAll(*sort.d_type, n));
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkFloatingPointPosInf(uint32_t exp, uint32_t sig)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(exp > 1, exp) << "exponent size > 1";
  CVC5_API_ARG_CHECK_EXPECTED(sig > 1, sig) << "significand size > 1";
  //////// all checks before this line
  return mkValHelper(internal::FloatingPoint::makeInf(
      internal::FloatingPointSize(exp, sig), false));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkFloatingPointNegInf(uint32_t exp, uint32_t sig)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(exp > 1, exp) << "exponent size > 1";
  CVC5_API_ARG_CHECK_EXPECTED(sig > 1, sig) << "significand size > 1";
  //////// all checks before this line
  return mkValHelper(internal::FloatingPoint::makeInf(
      internal::FloatingPointSize(exp, sig), true));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkFloatingPointNaN(uint32_t exp, uint32_t sig)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(exp > 1, exp) << "exponent size > 1";
  CVC5_API_ARG_CHECK_EXPECTED(sig > 1, sig) << "significand size > 1";
  //////// all checks before this line
  return mkValHelper(
      internal::FloatingPoint::makeNaN(internal::FloatingPointSize(exp, sig)));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkFloatingPointPosZero(uint32_t exp, uint32_t sig)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(exp > 1, exp) << "exponent size > 1";
  CVC5_API_ARG_CHECK_EXPECTED(sig > 1, sig) << "significand size > 1";
  //////// all checks before this line
  return mkValHelper(internal::FloatingPoint::makeZero(
      internal::FloatingPointSize(exp, sig), false));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkFloatingPointNegZero(uint32_t exp, uint32_t sig)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_ARG_CHECK_EXPECTED(exp > 1, exp) << "exponent size > 1";
  CVC5_API_ARG_CHECK_EXPECTED(sig > 1, sig) << "significand size > 1";
  //////// all checks before this line
  return mkValHelper(internal::FloatingPoint::makeZero(
      internal::FloatingPointSize(exp, sig), true));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkRoundingMode(RoundingMode rm)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return mkValHelper(s_rmodes.at(rm));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkFloatingPoint(uint32_t exp, uint32_t sig, const Term& val)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_TERM(val);
  CVC5_API_ARG_CHECK_EXPECTED(exp > 1, exp) << "exponent size > 1";
  CVC5_API_ARG_CHECK_EXPECTED(sig > 1, sig) << "significand size > 1";
  uint32_t bw = exp + sig;
  CVC5_API_ARG_CHECK_EXPECTED(bw == val.d_node->getType().getBitVectorSize(),
                              val)
      << "a bit-vector value with bit-width '" << bw << "'";
  CVC5_API_ARG_CHECK_EXPECTED(
      val.d_node->getType().isBitVector() && val.d_node->isConst(), val)
      << "bit-vector value";
  //////// all checks before this line
  return mkValHelper(internal::FloatingPoint(
      exp, sig, val.d_node->getConst<internal::BitVector>()));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkFloatingPoint(const Term& sign,
                                  const Term& exp,
                                  const Term& sig)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_TERM(sign);
  CVC5_API_TM_CHECK_TERM(exp);
  CVC5_API_TM_CHECK_TERM(sig);
  CVC5_API_ARG_CHECK_EXPECTED(
      sign.d_node->getType().isBitVector() && sign.d_node->isConst(), sign)
      << "bit-vector value";
  CVC5_API_ARG_CHECK_EXPECTED(
      exp.d_node->getType().isBitVector() && exp.d_node->isConst(), exp)
      << "bit-vector value";
  CVC5_API_ARG_CHECK_EXPECTED(
      sig.d_node->getType().isBitVector() && sig.d_node->isConst(), sig)
      << "bit-vector value";
  CVC5_API_ARG_CHECK_EXPECTED(sign.d_node->getType().getBitVectorSize() == 1,
                              sign)
      << "a bit-vector value of size 1";
  CVC5_API_ARG_CHECK_EXPECTED(exp.d_node->getType().getBitVectorSize() > 1, exp)
      << "a bit-vector value of size > 1";
  //////// all checks before this line
  uint32_t esize = exp.d_node->getType().getBitVectorSize();
  uint32_t ssize = sig.d_node->getType().getBitVectorSize() + 1;
  return mkValHelper(internal::FloatingPoint(
      esize,
      ssize,
      sign.d_node->getConst<internal::BitVector>().concat(
          exp.d_node->getConst<internal::BitVector>().concat(
              sig.d_node->getConst<internal::BitVector>()))));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkCardinalityConstraint(const Sort& sort, uint32_t upperBound)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(sort);
  CVC5_API_ARG_CHECK_EXPECTED(sort.isUninterpretedSort(), sort)
      << "an uninterpreted sort";
  CVC5_API_ARG_CHECK_EXPECTED(upperBound > 0, upperBound) << "a value > 0";
  //////// all checks before this line
  internal::Node cco =
      d_nm->mkConst(internal::CardinalityConstraint(*sort.d_type, upperBound));
  internal::Node res =
      d_nm->mkNode(internal::Kind::CARDINALITY_CONSTRAINT, cco);
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkNullableLift(Kind kind, const std::vector<Term>& args)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  std::vector<internal::Node> vars;
  for (size_t i = 0, size = args.size(); i < size; ++i)
  {
    const Term& t = args[i];
    CVC5_API_TM_CHECK_TERM_AT_INDEX(t, args, i);
    internal::TypeNode type = t.d_node->getType();
    internal::TypeNode elementType = type[0];
    internal::Node var = mkVarHelper(elementType);
    vars.push_back(var);
  }
  internal::Node varList = d_nm->mkNode(internal::Kind::BOUND_VAR_LIST, vars);
  internal::Kind internalKind = extToIntKind(kind);
  internal::Node body = d_nm->mkNode(internalKind, vars);
  internal::Node lambda = d_nm->mkNode(internal::Kind::LAMBDA, varList, body);
  std::vector<internal::Node> nodes;
  nodes.push_back(lambda);
  auto argNodes = Term::termVectorToNodes(args);
  nodes.insert(nodes.end(), argNodes.begin(), argNodes.end());

  return Term(this, d_nm->mkNode(internal::Kind::NULLABLE_LIFT, nodes));
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Constants and Variables -------------------------------------------------- */

Term TermManager::mkConst(const Sort& sort,
                          const std::optional<std::string>& symbol)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(sort);
  //////// all checks before this line
  return Term(this, mkConstHelper(*sort.d_type, symbol));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkVar(const Sort& sort,
                        const std::optional<std::string>& symbol)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(sort);
  //////// all checks before this line
  return Term(this, mkVarHelper(*sort.d_type, symbol));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkTuple(const std::vector<Term>& terms)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_TERMS(terms);
  //////// all checks before this line
  std::vector<internal::Node> args;
  std::vector<internal::TypeNode> typeNodes;
  for (size_t i = 0, size = terms.size(); i < size; i++)
  {
    internal::Node n = *terms[i].d_node;
    args.push_back(n);
    typeNodes.push_back(n.getType());
  }
  internal::TypeNode tn = d_nm->mkTupleType(typeNodes);
  const internal::DType& dt = tn.getDType();
  internal::NodeBuilder nb(d_nm.get(), extToIntKind(Kind::APPLY_CONSTRUCTOR));
  nb << dt[0].getConstructor();
  nb.append(args);
  internal::Node res = nb.constructNode();
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkNullableSome(const Term& term)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_TERM(term);
  //////// all checks before this line
  internal::Node arg = *term.d_node;
  internal::TypeNode typeNode = arg.getType();
  internal::TypeNode tn = d_nm->mkNullableType(typeNode);
  const internal::DType& dt = tn.getDType();
  internal::NodeBuilder nb(d_nm.get(), extToIntKind(Kind::APPLY_CONSTRUCTOR));
  nb << dt[1].getConstructor();
  nb.append(arg);
  internal::Node res = nb.constructNode();
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkNullableNull(const Sort& sort)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORT(sort);
  CVC5_API_ARG_CHECK_EXPECTED(sort.isNullable(), sort) << "nullable sort";
  //////// all checks before this line
  internal::TypeNode tn = sort.getTypeNode();
  const internal::DType& dt = tn.getDType();
  internal::NodeBuilder nb(d_nm.get(), extToIntKind(Kind::APPLY_CONSTRUCTOR));
  nb << dt[0].getConstructor();
  internal::Node res = nb.constructNode();
  (void)res.getType(true); /* kick off type checking */
  return Term(this, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkNullableVal(const Term& term)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_TERM(term);
  Sort sort = term.getSort();
  CVC5_API_ARG_CHECK_EXPECTED(sort.isNullable(), sort) << "nullable sort";
  //////// all checks before this line
  internal::Node arg = (*term.d_node);
  internal::TypeNode tn = arg.getType();
  const internal::DType& dt = tn.getDType();
  internal::Node sel = dt[1][0].getSelector();
  internal::Node applySel =
      d_nm->mkNode(internal::Kind::APPLY_SELECTOR, sel, arg);
  (void)applySel.getType(true); /* kick off type checking */
  return Term(this, applySel);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkNullableIsNull(const Term& term)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_TERM(term);
  Sort sort = term.getSort();
  CVC5_API_ARG_CHECK_EXPECTED(sort.isNullable(), sort) << "nullable sort";
  //////// all checks before this line
  internal::Node arg = (*term.d_node);
  internal::TypeNode tn = arg.getType();
  const internal::DType& dt = tn.getDType();
  internal::Node tester = dt[0].getTester();
  internal::Node applyTester =
      d_nm->mkNode(internal::Kind::APPLY_TESTER, tester, arg);
  (void)applyTester.getType(true); /* kick off type checking */
  return Term(this, applyTester);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term TermManager::mkNullableIsSome(const Term& term)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_TERM(term);
  Sort sort = term.getSort();
  CVC5_API_ARG_CHECK_EXPECTED(sort.isNullable(), sort) << "nullable sort";
  //////// all checks before this line
  internal::Node arg = (*term.d_node);
  internal::TypeNode tn = arg.getType();
  const internal::DType& dt = tn.getDType();
  internal::Node tester = dt[1].getTester();
  internal::Node applyTester =
      d_nm->mkNode(internal::Kind::APPLY_TESTER, tester, arg);
  (void)applyTester.getType(true); /* kick off type checking */
  return Term(this, applyTester);
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Datatype Constructor Declaration ----------------------------------------- */

DatatypeConstructorDecl TermManager::mkDatatypeConstructorDecl(
    const std::string& name)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return DatatypeConstructorDecl(this, name);
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* Datatype Declaration ----------------------------------------------------- */

DatatypeDecl TermManager::mkDatatypeDecl(const std::string& name,
                                         bool isCoDatatype)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return DatatypeDecl(this, name, isCoDatatype);
  ////////
  CVC5_API_TRY_CATCH_END;
}

DatatypeDecl TermManager::mkDatatypeDecl(const std::string& name,
                                         const std::vector<Sort>& params,
                                         bool isCoDatatype)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_TM_CHECK_SORTS(params);
  //////// all checks before this line
  return DatatypeDecl(this, name, params, isCoDatatype);
  ////////
  CVC5_API_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* Solver                                                                     */
/* -------------------------------------------------------------------------- */

Solver::Solver(TermManager& tm, std::unique_ptr<internal::Options>&& original)
    : d_tm(tm)
{
  d_originalOptions = std::move(original);
  d_slv.reset(
      new internal::SolverEngine(tm.d_nm.get(), d_originalOptions.get()));
  d_slv->setSolver(this);
  d_rng.reset(new internal::Random(d_slv->getOptions().driver.seed));
}

Solver::Solver(TermManager& tm)
    : Solver(tm, std::make_unique<internal::Options>())
{
}

Solver::Solver()
    : Solver(*TermManager::currentTM(), std::make_unique<internal::Options>())
{
}

Solver::~Solver() {}

/* Helpers and private functions                                              */
/* -------------------------------------------------------------------------- */

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
      CVC5_API_CHECK(grammar->d_grammar->getNtSyms()[0].getType()
                     == *sort.d_type)
          << "invalid Start symbol for grammar, expected Start's sort to be "
          << *sort.d_type << " but found "
          << grammar->d_grammar->getNtSyms()[0].getType();
    }
    varTypes.push_back(bv.d_node->getType());
  }
  if (grammar)
  {
    for (const auto& sym : grammar->d_grammar->getNtSyms())
    {
      CVC5_API_CHECK(!grammar->d_grammar->getRulesFor(sym).empty())
          << "invalid grammar, must have at least one rule for each "
             "non-terminal symbol";
    }
  }
  //////// all checks before this line

  internal::TypeNode funType =
      varTypes.empty() ? *sort.d_type
                       : d_tm.d_nm->mkFunctionType(varTypes, *sort.d_type);

  internal::Node fun = d_tm.mkVarHelper(funType, symbol);

  std::vector<internal::Node> bvns = Term::termVectorToNodes(boundVars);

  d_slv->declareSynthFun(
      fun,
      grammar == nullptr ? funType : *grammar->resolve().d_type,
      isInv,
      bvns);

  return Term(&d_tm, fun);
}

void Solver::ensureWellFormedTerm(const Term& t) const
{
  // only check if option is set
  if (d_slv->getOptions().expr.wellFormedChecking)
  {
    // Call isWellFormedTerm of the underlying solver, which checks if the
    // given node has free variables. We do not check for variable shadowing,
    // since this can be handled by our rewriter.
    if (!d_slv->isWellFormedTerm(*t.d_node))
    {
      std::stringstream se;
      se << "cannot process term " << *t.d_node << " with free variables"
         << std::endl;
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

void Solver::printStatisticsSafe(int fd) const
{
  d_slv->printStatisticsSafe(fd);
}

/* Deprecated Functions                                                       */
/* -------------------------------------------------------------------------- */

Sort Solver::getBooleanSort(void) const { return d_tm.getBooleanSort(); }

Sort Solver::getIntegerSort(void) const { return d_tm.getIntegerSort(); }

Sort Solver::getRealSort(void) const { return d_tm.getRealSort(); }

Sort Solver::getRegExpSort(void) const { return d_tm.getRegExpSort(); }

Sort Solver::getStringSort(void) const { return d_tm.getStringSort(); }

Sort Solver::getRoundingModeSort(void) const
{
  return d_tm.getRoundingModeSort();
}

Sort Solver::mkArraySort(const Sort& indexSort, const Sort& elemSort) const
{
  return d_tm.mkArraySort(indexSort, elemSort);
}

Sort Solver::mkBitVectorSort(uint32_t size) const
{
  return d_tm.mkBitVectorSort(size);
}

Sort Solver::mkFiniteFieldSort(const std::string& modulus, uint32_t base) const
{
  return d_tm.mkFiniteFieldSort(modulus, base);
}

Sort Solver::mkFloatingPointSort(uint32_t exp, uint32_t sig) const
{
  return d_tm.mkFloatingPointSort(exp, sig);
}

Sort Solver::mkDatatypeSort(const DatatypeDecl& dtypedecl) const
{
  return d_tm.mkDatatypeSort(dtypedecl);
}

std::vector<Sort> Solver::mkDatatypeSorts(
    const std::vector<DatatypeDecl>& dtypedecls) const
{
  return d_tm.mkDatatypeSorts(dtypedecls);
}

Sort Solver::mkFunctionSort(const std::vector<Sort>& sorts,
                            const Sort& codomain) const
{
  return d_tm.mkFunctionSort(sorts, codomain);
}

Sort Solver::mkParamSort(const std::optional<std::string>& symbol) const
{
  return d_tm.mkParamSort(symbol);
}

Sort Solver::mkPredicateSort(const std::vector<Sort>& sorts) const
{
  return d_tm.mkPredicateSort(sorts);
}

Sort Solver::mkRecordSort(
    const std::vector<std::pair<std::string, Sort>>& fields) const
{
  return d_tm.mkRecordSort(fields);
}

Sort Solver::mkSetSort(const Sort& elemSort) const
{
  return d_tm.mkSetSort(elemSort);
}

Sort Solver::mkBagSort(const Sort& elemSort) const
{
  return d_tm.mkBagSort(elemSort);
}

Sort Solver::mkSequenceSort(const Sort& elemSort) const
{
  return d_tm.mkSequenceSort(elemSort);
}

Sort Solver::mkAbstractSort(SortKind k) const { return d_tm.mkAbstractSort(k); }

Sort Solver::mkUninterpretedSort(const std::optional<std::string>& symbol) const
{
  return d_tm.mkUninterpretedSort(symbol);
}

Sort Solver::mkUnresolvedDatatypeSort(const std::string& symbol,
                                      size_t arity) const
{
  return d_tm.mkUnresolvedDatatypeSort(symbol, arity);
}

Sort Solver::mkUninterpretedSortConstructorSort(
    size_t arity, const std::optional<std::string>& symbol) const
{
  return d_tm.mkUninterpretedSortConstructorSort(arity, symbol);
}

Sort Solver::mkTupleSort(const std::vector<Sort>& sorts) const
{
  return d_tm.mkTupleSort(sorts);
}

Sort Solver::mkNullableSort(const Sort& sort) const
{
  return d_tm.mkNullableSort(sort);
}

Term Solver::mkTrue(void) const { return d_tm.mkTrue(); }

Term Solver::mkFalse(void) const { return d_tm.mkFalse(); }

Term Solver::mkBoolean(bool val) const { return d_tm.mkBoolean(val); }

Term Solver::mkPi() const { return d_tm.mkPi(); }

Term Solver::mkInteger(const std::string& s) const { return d_tm.mkInteger(s); }

Term Solver::mkInteger(int64_t val) const { return d_tm.mkInteger(val); }

Term Solver::mkReal(const std::string& s) const { return d_tm.mkReal(s); }

Term Solver::mkReal(int64_t val) const { return d_tm.mkReal(val); }

Term Solver::mkReal(int64_t num, int64_t den) const
{
  return d_tm.mkReal(num, den);
}

Term Solver::mkRegexpAll() const { return d_tm.mkRegexpAll(); }

Term Solver::mkRegexpNone() const { return d_tm.mkRegexpNone(); }

Term Solver::mkRegexpAllchar() const { return d_tm.mkRegexpAllchar(); }

Term Solver::mkEmptySet(const Sort& sort) const
{
  return d_tm.mkEmptySet(sort);
}

Term Solver::mkEmptyBag(const Sort& sort) const
{
  return d_tm.mkEmptyBag(sort);
}

Term Solver::mkSepEmp() const { return d_tm.mkSepEmp(); }

Term Solver::mkSepNil(const Sort& sort) const { return d_tm.mkSepNil(sort); }

Term Solver::mkString(const std::string& s, bool useEscSequences) const
{
  return d_tm.mkString(s, useEscSequences);
}

Term Solver::mkString(const std::wstring& s) const { return d_tm.mkString(s); }

Term Solver::mkEmptySequence(const Sort& sort) const
{
  return d_tm.mkEmptySequence(sort);
}

Term Solver::mkUniverseSet(const Sort& sort) const
{
  return d_tm.mkUniverseSet(sort);
}

Term Solver::mkBitVector(uint32_t size, uint64_t val) const
{
  return d_tm.mkBitVector(size, val);
}

Term Solver::mkBitVector(uint32_t size,
                         const std::string& s,
                         uint32_t base) const
{
  return d_tm.mkBitVector(size, s, base);
}

Term Solver::mkFiniteFieldElem(const std::string& value,
                               const Sort& sort,
                               uint32_t base) const
{
  return d_tm.mkFiniteFieldElem(value, sort, base);
}

Term Solver::mkConstArray(const Sort& sort, const Term& val) const
{
  return d_tm.mkConstArray(sort, val);
}

Term Solver::mkFloatingPointPosInf(uint32_t exp, uint32_t sig) const
{
  return d_tm.mkFloatingPointPosInf(exp, sig);
}

Term Solver::mkFloatingPointNegInf(uint32_t exp, uint32_t sig) const
{
  return d_tm.mkFloatingPointNegInf(exp, sig);
}

Term Solver::mkFloatingPointNaN(uint32_t exp, uint32_t sig) const
{
  return d_tm.mkFloatingPointNaN(exp, sig);
}

Term Solver::mkFloatingPointPosZero(uint32_t exp, uint32_t sig) const
{
  return d_tm.mkFloatingPointPosZero(exp, sig);
}

Term Solver::mkFloatingPointNegZero(uint32_t exp, uint32_t sig) const
{
  return d_tm.mkFloatingPointNegZero(exp, sig);
}

Term Solver::mkRoundingMode(RoundingMode rm) const
{
  return d_tm.mkRoundingMode(rm);
}

Term Solver::mkFloatingPoint(uint32_t exp, uint32_t sig, const Term& val) const
{
  return d_tm.mkFloatingPoint(exp, sig, val);
}

Term Solver::mkFloatingPoint(const Term& sign,
                             const Term& exp,
                             const Term& sig) const
{
  return d_tm.mkFloatingPoint(sign, exp, sig);
}

Term Solver::mkCardinalityConstraint(const Sort& sort,
                                     uint32_t upperBound) const
{
  return d_tm.mkCardinalityConstraint(sort, upperBound);
}

Term Solver::mkNullableLift(Kind kind, const std::vector<Term>& args) const
{
  return d_tm.mkNullableLift(kind, args);
}

Term Solver::mkConst(const Sort& sort,
                     const std::optional<std::string>& symbol) const
{
  return d_tm.mkConst(sort, symbol);
}

Term Solver::mkVar(const Sort& sort,
                   const std::optional<std::string>& symbol) const
{
  return d_tm.mkVar(sort, symbol);
}

DatatypeConstructorDecl Solver::mkDatatypeConstructorDecl(
    const std::string& name)
{
  return d_tm.mkDatatypeConstructorDecl(name);
}

DatatypeDecl Solver::mkDatatypeDecl(const std::string& name, bool isCoDatatype)
{
  return d_tm.mkDatatypeDecl(name, isCoDatatype);
}

DatatypeDecl Solver::mkDatatypeDecl(const std::string& name,
                                    const std::vector<Sort>& params,
                                    bool isCoDatatype)
{
  return d_tm.mkDatatypeDecl(name, params, isCoDatatype);
}

Term Solver::mkTerm(Kind kind, const std::vector<Term>& children) const
{
  return d_tm.mkTerm(kind, children);
}

Term Solver::mkTerm(const Op& op, const std::vector<Term>& children) const
{
  return d_tm.mkTerm(op, children);
}

Term Solver::mkTuple(const std::vector<Term>& terms) const
{
  return d_tm.mkTuple(terms);
}

Term Solver::mkNullableSome(const Term& term) const
{
  return d_tm.mkNullableSome(term);
}

Term Solver::mkNullableNull(const Sort& sort) const
{
  return d_tm.mkNullableNull(sort);
}

Term Solver::mkNullableVal(const Term& term) const
{
  return d_tm.mkNullableVal(term);
}

Term Solver::mkNullableIsNull(const Term& term) const
{
  return d_tm.mkNullableIsNull(term);
}

Term Solver::mkNullableIsSome(const Term& term) const
{
  return d_tm.mkNullableIsSome(term);
}

Op Solver::mkOp(Kind kind, const std::vector<uint32_t>& args) const
{
  return d_tm.mkOp(kind, args);
}

Op Solver::mkOp(Kind kind, const std::initializer_list<uint32_t>& args) const
{
  return d_tm.mkOp(kind, args);
}

Op Solver::mkOp(Kind kind, const std::string& arg) const
{
  return d_tm.mkOp(kind, arg);
}

/* Non-SMT-LIB commands                                                       */
/* -------------------------------------------------------------------------- */

Term Solver::simplify(const Term& term, bool applySubs)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(term);
  //////// all checks before this line
  Term res = Term(&d_tm, d_slv->simplify(*term.d_node, applySubs));
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
      << "cannot make multiple queries unless incremental solving is enabled "
         "(try --"
      << internal::options::base::longName::incrementalSolving << ")";
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
      << "cannot make multiple queries unless incremental solving is enabled "
         "(try --"
      << internal::options::base::longName::incrementalSolving << ")";
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
      << "cannot make multiple queries unless incremental solving is enabled "
         "(try --"
      << internal::options::base::longName::incrementalSolving << ")";
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
  for (size_t i = 0, size = ctors.size(); i < size; i++)
  {
    CVC5_API_SOLVER_CHECK_DTCTORDECL_AT_INDEX(ctors[i], ctorsr, i);
    CVC5_API_CHECK(!ctors[i].isResolved())
        << "cannot use a constructor for multiple datatypes";
  }
  //////// all checks before this line
  DatatypeDecl dtdecl(&d_tm, symbol);
  for (size_t i = 0, size = ctors.size(); i < size; i++)
  {
    dtdecl.addConstructor(ctors[i]);
  }
  return Sort(&d_tm, d_tm.d_nm->mkDatatypeType(*dtdecl.d_dtype));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::declareFun(const std::string& symbol,
                        const std::vector<Sort>& sorts,
                        const Sort& sort,
                        bool fresh) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_DOMAIN_SORTS(sorts);
  CVC5_API_SOLVER_CHECK_CODOMAIN_SORT(sort);
  //////// all checks before this line

  internal::TypeNode type = *sort.d_type;
  if (!sorts.empty())
  {
    std::vector<internal::TypeNode> types = Sort::sortVectorToTypeNodes(sorts);
    type = d_tm.d_nm->mkFunctionType(types, type);
  }
  internal::Node res = d_tm.mkConstHelper(type, symbol, fresh);
  // notify the solver engine of the declaration
  d_slv->declareConst(res);
  return Term(&d_tm, res);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Sort Solver::declareSort(const std::string& symbol,
                         uint32_t arity,
                         bool fresh) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  internal::TypeNode type = d_tm.d_nm->mkSortConstructor(symbol, arity, fresh);
  // notify the solver engine of the declaration
  d_slv->declareSort(type);
  return Sort(&d_tm, type);
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
      << "invalid sort of function body '" << term << "', expected '" << sort
      << "', found '" << term.getSort() << "'";

  std::vector<Sort> domain_sorts;
  for (size_t i = 0, n = bound_vars.size(); i < n; ++i)
  {
    CVC5_API_SOLVER_CHECK_BOUND_VAR_AT_INDEX(bound_vars[i], bound_vars, i);
    domain_sorts.push_back(bound_vars[i].getSort());
  }
  Sort fun_sort =
      domain_sorts.empty()
          ? sort
          : Sort(&d_tm,
                 d_tm.d_nm->mkFunctionType(
                     Sort::sortVectorToTypeNodes(domain_sorts), *sort.d_type));
  Term fun = d_tm.mkConst(fun_sort, symbol);
  CVC5_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN_SORTS(bound_vars, domain_sorts);
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
      << "invalid sort of function body '" << term << "', expected '" << sort
      << "'";

  std::vector<Sort> domain_sorts;
  for (size_t i = 0, n = bound_vars.size(); i < n; ++i)
  {
    CVC5_API_SOLVER_CHECK_BOUND_VAR_AT_INDEX(bound_vars[i], bound_vars, i);
    domain_sorts.push_back(bound_vars[i].getSort());
  }
  Sort fun_sort =
      domain_sorts.empty()
          ? sort
          : Sort(&d_tm,
                 d_tm.d_nm->mkFunctionType(
                     Sort::sortVectorToTypeNodes(domain_sorts), *sort.d_type));
  Term fun = d_tm.mkConst(fun_sort, symbol);
  CVC5_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN_SORTS(bound_vars, domain_sorts);
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
    CVC5_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN_SORTS(bound_vars, domain_sorts);
    Sort codomain = fun.getSort().getFunctionCodomainSort();
    CVC5_API_CHECK(*codomain.d_type == term.d_node->getType())
        << "invalid sort of function body '" << term << "', expected '"
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
        d_tm.d_nm == fun.d_tm->d_nm, "function", funs, j)
        << "function associated with the node manager of this solver object";
    CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(
        d_tm.d_nm == term.d_tm->d_nm, "term", terms, j)
        << "term associated with the node manager of this solver object";

    if (fun.getSort().isFunction())
    {
      std::vector<Sort> domain_sorts = fun.getSort().getFunctionDomainSorts();
      CVC5_API_SOLVER_CHECK_BOUND_VARS(bvars);
      CVC5_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN_SORTS(bvars, domain_sorts);
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
  return Term::nodeVectorToTerms(&d_tm, assertions);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Solver::getInfo(const std::string& flag) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_UNSUPPORTED_CHECK(d_slv->isValidGetInfoFlag(flag))
      << "unrecognized flag: " << flag << ".";
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
template <class... Ts>
struct overloaded : Ts...
{
  using Ts::operator()...;
};
template <class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

OptionInfo& OptionInfo::operator=(OptionInfo&& info)
{
  name = std::move(info.name);
  aliases = std::move(info.aliases);
  noSupports = std::move(info.noSupports);
  setByUser = std::move(info.setByUser);
  category = std::move(info.category);
  valueInfo = std::move(info.valueInfo);
  return *this;
}

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

std::string OptionInfo::toString() const
{
  std::stringstream os;
  os << "OptionInfo{ " << name;
  if (setByUser)
  {
    os << " | set by user";
  }
  if (!aliases.empty())
  {
    internal::container_to_stream(os, aliases, ", ", "", ", ");
  }
  if (!noSupports.empty())
  {
    internal::container_to_stream(os, noSupports, ", ", "", ", ");
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
             valueInfo);
  os << " }";
  return os.str();
}

std::ostream& operator<<(std::ostream& os, const OptionInfo& oi)
{
  os << oi.toString();
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

// Helper function to convert internal category to external enum
modes::OptionCategory convertOptionCategory(
    internal::options::OptionInfo::Category internalCategory)
{
  switch (internalCategory)
  {
    case internal::options::OptionInfo::Category::REGULAR:
      return modes::OptionCategory::REGULAR;
    case internal::options::OptionInfo::Category::EXPERT:
      return modes::OptionCategory::EXPERT;
    case internal::options::OptionInfo::Category::COMMON:
      return modes::OptionCategory::COMMON;
    default:
      Assert(internalCategory
             == internal::options::OptionInfo::Category::UNDOCUMENTED);
      return modes::OptionCategory::UNDOCUMENTED;
  }
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
            auto cat = convertOptionCategory(info.category);
            return OptionInfo{info.name,
                              info.aliases,
                              info.noSupports,
                              info.setByUser,
                              cat == modes::OptionCategory::EXPERT,
                              cat == modes::OptionCategory::REGULAR,
                              convertOptionCategory(info.category),
                              OptionInfo::VoidInfo{}};
          },
          [&info](const internal::options::OptionInfo::ValueInfo<bool>& vi) {
            auto cat = convertOptionCategory(info.category);
            return OptionInfo{
                info.name,
                info.aliases,
                info.noSupports,
                info.setByUser,
                cat == modes::OptionCategory::EXPERT,
                cat == modes::OptionCategory::REGULAR,
                convertOptionCategory(info.category),
                OptionInfo::ValueInfo<bool>{vi.defaultValue, vi.currentValue}};
          },
          [&info](
              const internal::options::OptionInfo::ValueInfo<std::string>& vi) {
            auto cat = convertOptionCategory(info.category);
            return OptionInfo{info.name,
                              info.aliases,
                              info.noSupports,
                              info.setByUser,
                              cat == modes::OptionCategory::EXPERT,
                              cat == modes::OptionCategory::REGULAR,
                              convertOptionCategory(info.category),
                              OptionInfo::ValueInfo<std::string>{
                                  vi.defaultValue, vi.currentValue}};
          },
          [&info](
              const internal::options::OptionInfo::NumberInfo<int64_t>& vi) {
            auto cat = convertOptionCategory(info.category);
            return OptionInfo{
                info.name,
                info.aliases,
                info.noSupports,
                info.setByUser,
                cat == modes::OptionCategory::EXPERT,
                cat == modes::OptionCategory::REGULAR,
                convertOptionCategory(info.category),
                OptionInfo::NumberInfo<int64_t>{
                    vi.defaultValue, vi.currentValue, vi.minimum, vi.maximum}};
          },
          [&info](
              const internal::options::OptionInfo::NumberInfo<uint64_t>& vi) {
            auto cat = convertOptionCategory(info.category);
            return OptionInfo{
                info.name,
                info.aliases,
                info.noSupports,
                info.setByUser,
                cat == modes::OptionCategory::EXPERT,
                cat == modes::OptionCategory::REGULAR,
                convertOptionCategory(info.category),
                OptionInfo::NumberInfo<uint64_t>{
                    vi.defaultValue, vi.currentValue, vi.minimum, vi.maximum}};
          },
          [&info](const internal::options::OptionInfo::NumberInfo<double>& vi) {
            auto cat = convertOptionCategory(info.category);
            return OptionInfo{
                info.name,
                info.aliases,
                info.noSupports,
                info.setByUser,
                cat == modes::OptionCategory::EXPERT,
                cat == modes::OptionCategory::REGULAR,
                convertOptionCategory(info.category),
                OptionInfo::NumberInfo<double>{
                    vi.defaultValue, vi.currentValue, vi.minimum, vi.maximum}};
          },
          [&info](const internal::options::OptionInfo::ModeInfo& vi) {
            auto cat = convertOptionCategory(info.category);
            return OptionInfo{info.name,
                              info.aliases,
                              info.noSupports,
                              info.setByUser,
                              cat == modes::OptionCategory::EXPERT,
                              cat == modes::OptionCategory::REGULAR,
                              convertOptionCategory(info.category),
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
  CVC5_API_CHECK(d_slv->getOptions().smt.unsatAssumptions)
      << "cannot get unsat assumptions unless explicitly enabled "
         "(try --"
      << internal::options::smt::longName::unsatAssumptions << ")";
  CVC5_API_CHECK(d_slv->getSmtMode() == internal::SmtMode::UNSAT)
      << "cannot get unsat assumptions unless in unsat mode.";
  //////// all checks before this line

  std::vector<internal::Node> uassumptions = d_slv->getUnsatAssumptions();
  /* Cannot use
   *   return std::vector<Term>(uassumptions.begin(), uassumptions.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const internal::Node& n : uassumptions)
  {
    res.push_back(Term(&d_tm, n));
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Term> Solver::getUnsatCore(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceUnsatCores)
      << "cannot get unsat core unless explicitly enabled "
         "(try --"
      << internal::options::smt::longName::produceUnsatCores << ")";
  CVC5_API_RECOVERABLE_CHECK(d_slv->getSmtMode() == internal::SmtMode::UNSAT)
      << "cannot get unsat core unless in unsat mode.";
  //////// all checks before this line
  internal::UnsatCore core = d_slv->getUnsatCore();
  /* Can not use
   *   return std::vector<Term>(core.begin(), core.end());
   * here since constructor is private */
  std::vector<Term> res;
  for (const internal::Node& e : core)
  {
    res.push_back(Term(&d_tm, e));
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Term> Solver::getUnsatCoreLemmas(void) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceUnsatCores)
      << "cannot get unsat core lemmas unless explicitly enabled "
         "(try --"
      << internal::options::smt::longName::produceUnsatCores << ")";
  CVC5_API_CHECK(d_slv->getOptions().smt.unsatCoresMode
                 == internal::options::UnsatCoresMode::SAT_PROOF)
      << "cannot get unsat core lemmas unless SAT proofs are enabled";
  CVC5_API_RECOVERABLE_CHECK(d_slv->getSmtMode() == internal::SmtMode::UNSAT)
      << "cannot get unsat core unless in unsat mode.";
  //////// all checks before this line
  std::vector<internal::Node> lemmas = d_slv->getUnsatCoreLemmas();
  /* Can not use
   *   return std::vector<Term>(assertions.begin(), assertions.end());
   * here since constructor is private */
  return Term::nodeVectorToTerms(&d_tm, lemmas);
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
      << "cannot get difficulty unless after a UNSAT, SAT or UNKNOWN response.";
  //////// all checks before this line
  std::map<Term, Term> res;
  std::map<internal::Node, internal::Node> dmap;
  d_slv->getDifficultyMap(dmap);
  for (const std::pair<const internal::Node, internal::Node>& d : dmap)
  {
    res[Term(&d_tm, d.first)] = Term(&d_tm, d.second);
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::pair<Result, std::vector<Term>> Solver::getTimeoutCore() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceUnsatCores)
      << "cannot get timeout core unless unsat cores are enabled "
         "(try --"
      << internal::options::smt::longName::produceUnsatCores << ")";
  //////// all checks before this line
  return getTimeoutCoreHelper({});
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::pair<Result, std::vector<Term>> Solver::getTimeoutCoreAssuming(
    const std::vector<Term>& assumptions) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!assumptions.empty())
      << "cannot get timeout core assuming an empty set of assumptions";
  CVC5_API_CHECK(d_slv->getOptions().smt.produceUnsatCores)
      << "cannot get timeout core unless unsat cores are enabled "
         "(try --"
      << internal::options::smt::longName::produceUnsatCores << ")";
  //////// all checks before this line
  return getTimeoutCoreHelper(assumptions);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::pair<Result, std::vector<Term>> Solver::getTimeoutCoreHelper(
    const std::vector<Term>& assumptions) const
{
  std::vector<Term> res;
  std::pair<internal::Result, std::vector<internal::Node>> resi =
      d_slv->getTimeoutCore(Term::termVectorToNodes(assumptions));
  for (internal::Node& c : resi.second)
  {
    res.push_back(Term(&d_tm, c));
  }
  return std::pair<Result, std::vector<Term>>(Result(resi.first), res);
}

std::vector<Proof> Solver::getProof(modes::ProofComponent c) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceProofs)
      << "cannot get proof unless proofs are enabled (try --"
      << internal::options::smt::longName::produceProofs << ")";
  CVC5_API_RECOVERABLE_CHECK(d_slv->getSmtMode() == internal::SmtMode::UNSAT)
      << "cannot get proof unless in unsat mode.";
  //////// all checks before this line
  std::vector<std::shared_ptr<internal::ProofNode>> proof_nodes =
      d_slv->getProof(c);
  std::vector<Proof> proofs;
  for (auto& p : proof_nodes)
  {
    proofs.push_back(Proof(&d_tm, p));
  }
  return proofs;
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Solver::proofToString(
    Proof proof,
    modes::ProofFormat format,
    const std::map<cvc5::Term, std::string>& assertionNames) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  std::ostringstream ss;
  // convert the map's domain to use nodes rather than terms
  std::map<internal::Node, std::string> nodeAssertionNames;
  for (const auto& p : assertionNames)
  {
    nodeAssertionNames[p.first.getNode()] = p.second;
  }
  this->d_slv->printProof(ss, proof.d_proofNode, format, nodeAssertionNames);
  return ss.str();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Term> Solver::getLearnedLiterals(modes::LearnedLitType t) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceLearnedLiterals)
      << "cannot get learned literals unless enabled (try "
         "--"
      << internal::options::smt::longName::produceLearnedLiterals << ")";
  CVC5_API_RECOVERABLE_CHECK(d_slv->getSmtMode() == internal::SmtMode::UNSAT
                             || d_slv->getSmtMode() == internal::SmtMode::SAT
                             || d_slv->getSmtMode()
                                    == internal::SmtMode::SAT_UNKNOWN)
      << "cannot get learned literals unless after a UNSAT, SAT or UNKNOWN "
         "response.";
  //////// all checks before this line
  std::vector<internal::Node> lits = d_slv->getLearnedLiterals(t);
  return Term::nodeVectorToTerms(&d_tm, lits);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getValueHelper(const Term& term) const
{
  // Note: Term is checked in the caller to avoid double checks
  bool wasShadow = false;
  bool freeOrShadowedVar =
      internal::expr::hasFreeOrShadowedVar(term.getNode(), wasShadow);
  CVC5_API_RECOVERABLE_CHECK(!freeOrShadowedVar)
      << "cannot get value of term containing "
      << (wasShadow ? "shadowed" : "free") << " variables";
  //////// all checks before this line
  internal::Node value = d_slv->getValue(*term.d_node, true);
  Term res = Term(&d_tm, value);
  Assert(res.getSort() == term.getSort());
  return res;
}

Term Solver::getValue(const Term& term) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(d_slv->getOptions().smt.produceModels)
      << "cannot get value unless model generation is enabled "
         "(try --"
      << internal::options::smt::longName::produceModels << ")";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "cannot get value unless after a SAT or UNKNOWN response.";
  CVC5_API_SOLVER_CHECK_TERM(term);
  CVC5_API_RECOVERABLE_CHECK(
      d_slv->getEnv().isFirstClassType(term.getSort().getTypeNode()))
      << "cannot get value of a term that is not first class.";
  CVC5_API_RECOVERABLE_CHECK(!term.getSort().isDatatype()
                             || term.getSort().getDatatype().isWellFounded())
      << "cannot get value of a term of non-well-founded datatype sort.";
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
      << "cannot get value unless model generation is enabled "
         "(try --"
      << internal::options::smt::longName::produceModels << ")";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "cannot get value unless after a SAT or UNKNOWN response.";
  for (const Term& t : terms)
  {
    CVC5_API_RECOVERABLE_CHECK(
        d_slv->getEnv().isFirstClassType(t.getSort().getTypeNode()))
        << "cannot get value of a term that is not first class.";
    CVC5_API_RECOVERABLE_CHECK(!t.getSort().isDatatype()
                               || t.getSort().getDatatype().isWellFounded())
        << "cannot get value of a term of non-well-founded datatype sort.";
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
      << "cannot get domain elements unless model generation is enabled "
         "(try --"
      << internal::options::smt::longName::produceModels << ")";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "cannot get domain elements unless after a SAT or UNKNOWN response.";
  CVC5_API_SOLVER_CHECK_SORT(s);
  CVC5_API_RECOVERABLE_CHECK(s.isUninterpretedSort())
      << "expected an uninterpreted sort as argument to "
         "getModelDomainElements.";
  //////// all checks before this line
  std::vector<Term> res;
  std::vector<internal::Node> elements =
      d_slv->getModelDomainElements(s.getTypeNode());
  for (const internal::Node& n : elements)
  {
    res.push_back(Term(&d_tm, n));
  }
  return res;
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Solver::isModelCoreSymbol(const Term& v) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_RECOVERABLE_CHECK(d_slv->getOptions().smt.produceModels)
      << "cannot check if model core symbol unless model generation is enabled "
         "(try --"
      << internal::options::smt::longName::produceModels << ")";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "cannot check if model core symbol unless after a SAT or UNKNOWN "
         "response.";
  CVC5_API_SOLVER_CHECK_TERM(v);
  CVC5_API_RECOVERABLE_CHECK(v.getKind() == Kind::CONSTANT)
      << "expected a free constant as argument to isModelCoreSymbol.";
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
      << "cannot get model unless model generation is enabled "
         "(try --"
      << internal::options::smt::longName::produceModels << ")";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "cannot get model unless after a SAT or UNKNOWN response.";
  CVC5_API_SOLVER_CHECK_SORTS(sorts);
  for (const Sort& s : sorts)
  {
    CVC5_API_RECOVERABLE_CHECK(s.isUninterpretedSort())
        << "expected an uninterpreted sort as argument to "
           "getModel.";
  }
  CVC5_API_SOLVER_CHECK_TERMS(vars);
  for (const Term& v : vars)
  {
    CVC5_API_RECOVERABLE_CHECK(v.getKind() == Kind::CONSTANT)
        << "expected a free constant as argument to getModel.";
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
  return Term(&d_tm, d_slv->getQuantifierElimination(q.getNode(), true));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getQuantifierEliminationDisjunct(const Term& q) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(q);
  //////// all checks before this line
  return Term(&d_tm, d_slv->getQuantifierElimination(q.getNode(), false));
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::declareSepHeap(const Sort& locSort, const Sort& dataSort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(locSort);
  CVC5_API_SOLVER_CHECK_SORT(dataSort);
  CVC5_API_CHECK(d_slv->isLogicSet())
      << "cannot call 'declareSepHeap()' if logic is not set";
  CVC5_API_CHECK(
      d_slv->getLogicInfo().isTheoryEnabled(internal::theory::THEORY_SEP))
      << "cannot obtain separation logic expressions if not using the "
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
      << "cannot obtain separation logic expressions if not using the "
         "separation logic theory.";
  CVC5_API_CHECK(d_slv->getOptions().smt.produceModels)
      << "cannot get separation heap term unless model generation is enabled "
         "(try --"
      << internal::options::smt::longName::produceModels << ")";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "can only get separtion heap term after SAT or UNKNOWN response.";
  //////// all checks before this line
  return Term(&d_tm, d_slv->getSepHeapExpr());
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getValueSepNil() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(
      d_slv->getLogicInfo().isTheoryEnabled(internal::theory::THEORY_SEP))
      << "cannot obtain separation logic expressions if not using the "
         "separation logic theory.";
  CVC5_API_CHECK(d_slv->getOptions().smt.produceModels)
      << "cannot get separation nil term unless model generation is enabled "
         "(try --"
      << internal::options::smt::longName::produceModels << ")";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "can only get separtion nil term after SAT or UNKNOWN response.";
  //////// all checks before this line
  return Term(&d_tm, d_slv->getSepNilExpr());
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
  internal::TypeNode setType = d_tm.d_nm->mkSetType(*sort.d_type);
  internal::Node pool = d_tm.mkVarHelper(setType, symbol);
  std::vector<internal::Node> initv = Term::termVectorToNodes(initValue);
  d_slv->declarePool(pool, initv);
  d_tm.increment_vars_consts_stats(setType, true);
  return Term(&d_tm, pool);
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
      << "cannot call declareOracleFun unless oracles is enabled (use "
         "--"
      << internal::options::quantifiers::longName::oracles << ")";
  //////// all checks before this line
  internal::TypeNode type = *sort.d_type;
  if (!sorts.empty())
  {
    std::vector<internal::TypeNode> types = Sort::sortVectorToTypeNodes(sorts);
    type = d_tm.d_nm->mkFunctionType(types, type);
  }
  internal::Node fun = d_tm.mkConstHelper(type, symbol);
  // Wrap the terms-to-term function so that it is nodes-to-nodes. Note we
  // make the method return a vector of size one to conform to the interface
  // at the SolverEngine level.
  d_slv->declareOracleFun(
      fun, [&, fn](const std::vector<internal::Node> nodes) {
        std::vector<Term> terms = Term::nodeVectorToTerms(&d_tm, nodes);
        Term output = fn(terms);
        return Term::termVectorToNodes({output});
      });
  return Term(&d_tm, fun);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::addPlugin(Plugin& p)
{
  CVC5_API_TRY_CATCH_BEGIN;
  d_slv->addPlugin(p.d_pExtToInt.get());
  CVC5_API_TRY_CATCH_END;
}

void Solver::pop(uint32_t nscopes) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().base.incrementalSolving)
      << "cannot pop when not solving incrementally (use --"
      << internal::options::base::longName::incrementalSolving << ")";
  CVC5_API_CHECK(nscopes <= d_slv->getNumUserLevels())
      << "cannot pop beyond first pushed context";
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
  CVC5_API_CHECK(d_slv->getOptions().smt.produceInterpolants)
      << "cannot get interpolant unless interpolants are enabled (try "
         "--"
      << internal::options::smt::longName::produceInterpolants << ")";
  //////// all checks before this line
  internal::TypeNode nullType;
  internal::Node result = d_slv->getInterpolant(*conj.d_node, nullType);
  return Term(&d_tm, result);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getInterpolant(const Term& conj, Grammar& grammar) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(conj);
  CVC5_API_SOLVER_CHECK_GRAMMAR(grammar);
  CVC5_API_CHECK(d_slv->getOptions().smt.produceInterpolants)
      << "cannot get interpolant unless interpolants are enabled (try "
         "--"
      << internal::options::smt::longName::produceInterpolants << ")";
  for (const auto& sym : grammar.d_grammar->getNtSyms())
  {
    CVC5_API_CHECK(!grammar.d_grammar->getRulesFor(sym).empty())
        << "invalid grammar, must have at least one rule for each "
           "non-terminal symbol";
  }
  //////// all checks before this line
  internal::Node result =
      d_slv->getInterpolant(*conj.d_node, *grammar.resolve().d_type);
  return Term(&d_tm, result);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getInterpolantNext() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceInterpolants)
      << "cannot get interpolant unless interpolants are enabled (try "
         "--"
      << internal::options::smt::longName::produceInterpolants << ")";
  CVC5_API_CHECK(d_slv->getOptions().base.incrementalSolving)
      << "cannot get next interpolant when not solving incrementally (try "
         "--"
      << internal::options::base::longName::incrementalSolving << ")";
  //////// all checks before this line
  internal::Node result = d_slv->getInterpolantNext();
  return Term(&d_tm, result);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getAbduct(const Term& conj) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(conj);
  CVC5_API_CHECK(d_slv->getOptions().smt.produceAbducts)
      << "cannot get abduct unless abducts are enabled (try --"
      << internal::options::smt::longName::produceAbducts << ")";
  //////// all checks before this line
  internal::TypeNode nullType;
  internal::Node result = d_slv->getAbduct(*conj.d_node, nullType);
  return Term(&d_tm, result);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getAbduct(const Term& conj, Grammar& grammar) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(conj);
  CVC5_API_SOLVER_CHECK_GRAMMAR(grammar);
  CVC5_API_CHECK(d_slv->getOptions().smt.produceAbducts)
      << "cannot get abduct unless abducts are enabled (try --"
      << internal::options::smt::longName::produceAbducts << ")";
  for (const auto& sym : grammar.d_grammar->getNtSyms())
  {
    CVC5_API_CHECK(!grammar.d_grammar->getRulesFor(sym).empty())
        << "invalid grammar, must have at least one rule for each "
           "non-terminal symbol";
  }
  //////// all checks before this line
  internal::Node result =
      d_slv->getAbduct(*conj.d_node, *grammar.resolve().d_type);
  return Term(&d_tm, result);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getAbductNext() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceAbducts)
      << "cannot get next abduct unless abducts are enabled (try "
         "--"
      << internal::options::smt::longName::produceAbducts << ")";
  CVC5_API_CHECK(d_slv->getOptions().base.incrementalSolving)
      << "cannot get next abduct when not solving incrementally (try "
         "--"
      << internal::options::base::longName::incrementalSolving << ")";
  //////// all checks before this line
  internal::Node result = d_slv->getAbductNext();
  return Term(&d_tm, result);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::blockModel(modes::BlockModelsMode mode) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceModels)
      << "cannot get value unless model generation is enabled "
         "(try --"
      << internal::options::smt::longName::produceModels << ")";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "can only block model after SAT or UNKNOWN response.";
  //////// all checks before this line
  d_slv->blockModel(mode);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::blockModelValues(const std::vector<Term>& terms) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().smt.produceModels)
      << "cannot get value unless model generation is enabled "
         "(try --"
      << internal::options::smt::longName::produceModels << ")";
  CVC5_API_RECOVERABLE_CHECK(d_slv->isSmtModeSat())
      << "can only block model values after SAT or UNKNOWN response.";
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
      << "cannot get instantiations unless after a UNSAT, SAT or UNKNOWN "
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
      << "cannot push when not solving incrementally (use --"
      << internal::options::base::longName::incrementalSolving << ")";
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
      << "unrecognized keyword: " << keyword
      << ", expected 'source', 'category', 'difficulty', "
         "'filename', 'license', 'name', "
         "'notes', 'smt-lib-version' or 'status'";
  CVC5_API_RECOVERABLE_ARG_CHECK_EXPECTED(
      keyword != "smt-lib-version" || value == "2" || value == "2.0"
          || value == "2.5" || value == "2.6" || value == "2.7",
      value)
      << "'2.0', '2.5', '2.6', '2.7'";
  CVC5_API_ARG_CHECK_EXPECTED(keyword != "status" || value == "sat"
                                  || value == "unsat" || value == "unknown",
                              value)
      << "'sat', 'unsat' or 'unknown'";
  //////// all checks before this line
  if (keyword == "filename")
  {
    // only the Solver object has non-const access to the original options
    d_originalOptions->write_driver().filename = value;
  }
  d_slv->setInfo(keyword, value);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::setLogic(const std::string& logic) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(!d_slv->isLogicSet())
      << "invalid call to 'setLogic', logic is already set";
  CVC5_API_CHECK(!d_slv->isFullyInited())
      << "invalid call to 'setLogic', solver is already fully initialized";
  //////// all checks before this line
  internal::LogicInfo linfo(logic);
  d_slv->setLogic(linfo);
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool Solver::isLogicSet() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_slv->isLogicSet();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Solver::getLogic() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->isLogicSet())
      << "invalid call to 'getLogic', logic has not yet been set";
  //////// all checks before this line
  return d_slv->getUserLogicInfo().getLogicString();
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
      << "unrecognized option: " << option << '.';
  // this list includes options that are prescribed to be changable in any
  // context based on the SMT-LIB standard, as well as options (e.g. tlimit-per)
  // that have no impact on solver initialization or imply other options.
  static constexpr auto mutableOpts = {"diagnostic-output-channel",
                                       "print-success",
                                       "regular-output-channel",
                                       "reproducible-resource-limit",
                                       "verbosity",
                                       "tlimit-per"};
  if (std::find(mutableOpts.begin(), mutableOpts.end(), option)
      == mutableOpts.end())
  {
    CVC5_API_CHECK(!d_slv->isFullyInited())
        << "invalid call to 'setOption' for option '" << option
        << "', solver is already fully initialized";
  }
  //////// all checks before this line
  // mark that the option originated from the user here
  d_slv->setOption(option, value, true);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::declareSygusVar(const std::string& symbol, const Sort& sort) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_SORT(sort);
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "cannot call declareSygusVar unless sygus is enabled (use --"
      << internal::options::quantifiers::longName::sygus << ")";
  //////// all checks before this line
  internal::Node res = d_tm.mkVarHelper(*sort.d_type, symbol);
  d_slv->declareSygusVar(res);
  return Term(&d_tm, res);
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
  return Grammar(&d_tm, boundVars, ntSymbols);
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
      << "cannot call synthFun unless sygus is enabled (use --"
      << internal::options::quantifiers::longName::sygus << ")";
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
  CVC5_API_SOLVER_CHECK_GRAMMAR(grammar);
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "cannot call synthFun unless sygus is enabled (use --"
      << internal::options::quantifiers::longName::sygus << ")";
  //////// all checks before this line
  return synthFunHelper(symbol, boundVars, sort, false, &grammar);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::addSygusConstraint(const Term& term) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(term);
  CVC5_API_ARG_CHECK_EXPECTED(
      term.d_node->getType() == d_tm.d_nm->booleanType(), term)
      << "boolean term";
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "cannot addSygusConstraint unless sygus is enabled (use --"
      << internal::options::quantifiers::longName::sygus << ")";
  //////// all checks before this line
  d_slv->assertSygusConstraint(*term.d_node, false);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Term> Solver::getSygusConstraints() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  std::vector<internal::Node> constraints = d_slv->getSygusConstraints();
  return Term::nodeVectorToTerms(&d_tm, constraints);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::addSygusAssume(const Term& term) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(term);
  CVC5_API_ARG_CHECK_EXPECTED(
      term.d_node->getType() == d_tm.d_nm->booleanType(), term)
      << "boolean term";
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "cannot addSygusAssume unless sygus is enabled (use --"
      << internal::options::quantifiers::longName::sygus << ")";
  //////// all checks before this line
  d_slv->assertSygusConstraint(*term.d_node, true);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::vector<Term> Solver::getSygusAssumptions() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  std::vector<internal::Node> assumptions = d_slv->getSygusAssumptions();
  return Term::nodeVectorToTerms(&d_tm, assumptions);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Solver::addSygusInvConstraint(const Term& inv,
                                   const Term& pre,
                                   const Term& trans,
                                   const Term& post) const
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
      << "expected inv and pre to have the same sort";

  CVC5_API_CHECK(post.d_node->getType() == invType)
      << "expected inv and post to have the same sort";
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "cannot addSygusInvConstraint unless sygus is enabled (use --"
      << internal::options::quantifiers::longName::sygus << ")";
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
      d_tm.d_nm->mkFunctionType(expectedTypes);

  CVC5_API_CHECK(trans.d_node->getType() == expectedTransType)
      << "expected the sort of trans sort to be " << invType;

  d_slv->assertSygusInvConstraint(
      *inv.d_node, *pre.d_node, *trans.d_node, *post.d_node);
  ////////
  CVC5_API_TRY_CATCH_END;
}

SynthResult Solver::checkSynth() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "cannot check for a synthesis solution unless sygus is enabled (use --"
      << internal::options::quantifiers::longName::sygus << ")";
  CVC5_API_CHECK(!d_slv->isQueryMade()
                 || d_slv->getOptions().base.incrementalSolving)
      << "cannot make multiple check synthesis solution calls unless "
         "incremental solving is "
         "enabled (try --"
      << internal::options::base::longName::incrementalSolving << ")";
  //////// all checks before this line
  return d_slv->checkSynth();
  ////////
  CVC5_API_TRY_CATCH_END;
}

SynthResult Solver::checkSynthNext() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_CHECK(d_slv->getOptions().quantifiers.sygus)
      << "cannot check for a next synth solution unless sygus is enabled (use "
         "--"
      << internal::options::quantifiers::longName::sygus << ")";
  CVC5_API_CHECK(d_slv->getOptions().base.incrementalSolving)
      << "cannot check for a next synthesis solution when not solving "
         "incrementally (use "
         "--"
      << internal::options::base::longName::incrementalSolving << ")";
  //////// all checks before this line
  return d_slv->checkSynth(true);
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::getSynthSolution(const Term& term) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_TERM(term);

  std::map<internal::Node, internal::Node> map;
  CVC5_API_CHECK(d_slv->getSynthSolutions(map))
      << "solver is not in a state immediately preceded by a "
         "successful call to checkSynth";

  std::map<internal::Node, internal::Node>::const_iterator it =
      map.find(*term.d_node);

  CVC5_API_CHECK(it != map.cend())
      << "synthesis solution not found for given term";
  //////// all checks before this line
  return Term(&d_tm, it->second);
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
      << "solver is not in a state immediately preceded by a "
         "successful call to checkSynth";
  //////// all checks before this line

  std::vector<Term> synthSolution;
  synthSolution.reserve(terms.size());

  for (size_t i = 0, n = terms.size(); i < n; ++i)
  {
    std::map<internal::Node, internal::Node>::const_iterator it =
        map.find(*terms[i].d_node);

    CVC5_API_CHECK(it != map.cend())
        << "synthesis solution not found for term at index " << i;

    synthSolution.push_back(Term(&d_tm, it->second));
  }

  return synthSolution;
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::findSynth(modes::FindSynthTarget fst) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Term(&d_tm, d_slv->findSynth(fst, internal::TypeNode::null()));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::findSynth(modes::FindSynthTarget fst, Grammar& grammar) const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_API_SOLVER_CHECK_GRAMMAR(grammar);
  for (const auto& sym : grammar.d_grammar->getNtSyms())
  {
    CVC5_API_CHECK(!grammar.d_grammar->getRulesFor(sym).empty())
        << "invalid grammar, must have at least one rule for each "
           "non-terminal symbol";
  }
  //////// all checks before this line
  return Term(&d_tm, d_slv->findSynth(fst, *grammar.resolve().d_type));
  ////////
  CVC5_API_TRY_CATCH_END;
}

Term Solver::findSynthNext() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return Term(&d_tm, d_slv->findSynthNext());
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
    throw CVC5ApiException("invalid output tag " + tag);
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
    throw CVC5ApiException("invalid output tag " + tag);
  }
}

std::string Solver::getVersion() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  return internal::Configuration::getVersionString();
  CVC5_API_TRY_CATCH_END;
}

TermManager& Solver::getTermManager() const { return d_tm; }

}  // namespace cvc5

namespace std {

size_t hash<cvc5::Kind>::operator()(cvc5::Kind k) const
{
  return static_cast<size_t>(k);
}

std::string to_string(cvc5::Kind k)
{
  auto it = cvc5::s_kinds.find(k);
  if (it == cvc5::s_kinds.end())
  {
    return "UNDEFINED_KIND";
  }
  return it->second.second;
}

size_t hash<cvc5::SortKind>::operator()(cvc5::SortKind k) const
{
  return static_cast<size_t>(k);
}

std::string to_string(cvc5::SortKind k)
{
  auto it = cvc5::s_sort_kinds.find(k);
  if (it == cvc5::s_sort_kinds.end())
  {
    return "UNDEFINED_SORT_KIND";
  }
  return it->second.second;
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

size_t std::hash<cvc5::DatatypeConstructorDecl>::operator()(
    const cvc5::DatatypeConstructorDecl& decl) const
{
  if (decl.isNull())
  {
    return 0;
  }
  return std::hash<cvc5::internal::DTypeConstructor>()(*decl.d_ctor);
}

size_t std::hash<cvc5::DatatypeDecl>::operator()(
    const cvc5::DatatypeDecl& decl) const
{
  if (decl.isNull())
  {
    return 0;
  }
  return std::hash<cvc5::internal::DType>()(*decl.d_dtype);
}

size_t std::hash<cvc5::DatatypeSelector>::operator()(
    const cvc5::DatatypeSelector& sel) const
{
  if (sel.isNull())
  {
    return 0;
  }
  return std::hash<cvc5::internal::DTypeSelector>()(*sel.d_stor);
}

size_t std::hash<cvc5::DatatypeConstructor>::operator()(
    const cvc5::DatatypeConstructor& cons) const
{
  if (cons.isNull())
  {
    return 0;
  }
  return std::hash<cvc5::internal::DTypeConstructor>()(*cons.d_ctor);
}

size_t hash<cvc5::Datatype>::operator()(const cvc5::Datatype& dt) const
{
  if (dt.isNull())
  {
    return 0;
  }
  return std::hash<cvc5::internal::DType>()(*dt.d_dtype);
}

size_t hash<cvc5::Proof>::operator()(const cvc5::Proof& proof) const
{
  if (proof.isNull())
  {
    return 0;
  }
  return std::hash<cvc5::internal::ProofNode>{}(*proof.d_proofNode);
}

size_t hash<cvc5::Grammar>::operator()(const cvc5::Grammar& grammar) const
{
  if (grammar.isNull())
  {
    return 0;
  }
  return std::hash<cvc5::internal::SygusGrammar>{}(*grammar.d_grammar);
}

}  // namespace std

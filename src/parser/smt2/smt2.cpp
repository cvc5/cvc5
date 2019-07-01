/*********************                                                        */
/*! \file smt2.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definitions of SMT2 constants.
 **
 ** Definitions of SMT2 constants.
 **/
#include "parser/smt2/smt2.h"

#include "expr/type.h"
#include "options/options.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"
#include "parser/smt1/smt1.h"
#include "parser/smt2/smt2_input.h"
#include "printer/sygus_print_callback.h"
#include "util/bitvector.h"

#include <algorithm>

// ANTLR defines these, which is really bad!
#undef true
#undef false

namespace CVC4 {
namespace parser {

Smt2::Smt2(api::Solver* solver, Input* input, bool strictMode, bool parseOnly)
    : Parser(solver, input, strictMode, parseOnly),
      d_logicSet(false),
      d_seenSetLogic(false)
{
  if (!strictModeEnabled())
  {
    addTheory(Smt2::THEORY_CORE);
  }
}

void Smt2::addArithmeticOperators() {
  addOperator(kind::PLUS, "+");
  addOperator(kind::MINUS, "-");
  // kind::MINUS is converted to kind::UMINUS if there is only a single operand
  Parser::addOperator(kind::UMINUS);
  addOperator(kind::MULT, "*");
  addOperator(kind::LT, "<");
  addOperator(kind::LEQ, "<=");
  addOperator(kind::GT, ">");
  addOperator(kind::GEQ, ">=");

  if (!strictModeEnabled())
  {
    // NOTE: this operator is non-standard
    addOperator(kind::POW, "^");
  }
}

void Smt2::addTranscendentalOperators()
{
  addOperator(kind::EXPONENTIAL, "exp");
  addOperator(kind::SINE, "sin");
  addOperator(kind::COSINE, "cos");
  addOperator(kind::TANGENT, "tan");
  addOperator(kind::COSECANT, "csc");
  addOperator(kind::SECANT, "sec");
  addOperator(kind::COTANGENT, "cot");
  addOperator(kind::ARCSINE, "arcsin");
  addOperator(kind::ARCCOSINE, "arccos");
  addOperator(kind::ARCTANGENT, "arctan");
  addOperator(kind::ARCCOSECANT, "arccsc");
  addOperator(kind::ARCSECANT, "arcsec");
  addOperator(kind::ARCCOTANGENT, "arccot");
  addOperator(kind::SQRT, "sqrt");
}

void Smt2::addQuantifiersOperators()
{
  if (!strictModeEnabled())
  {
    addOperator(kind::INST_CLOSURE, "inst-closure");
  }
}

void Smt2::addBitvectorOperators() {
  addOperator(kind::BITVECTOR_CONCAT, "concat");
  addOperator(kind::BITVECTOR_NOT, "bvnot");
  addOperator(kind::BITVECTOR_AND, "bvand");
  addOperator(kind::BITVECTOR_OR, "bvor");
  addOperator(kind::BITVECTOR_NEG, "bvneg");
  addOperator(kind::BITVECTOR_PLUS, "bvadd");
  addOperator(kind::BITVECTOR_MULT, "bvmul");
  addOperator(kind::BITVECTOR_UDIV, "bvudiv");
  addOperator(kind::BITVECTOR_UREM, "bvurem");
  addOperator(kind::BITVECTOR_SHL, "bvshl");
  addOperator(kind::BITVECTOR_LSHR, "bvlshr");
  addOperator(kind::BITVECTOR_ULT, "bvult");
  addOperator(kind::BITVECTOR_NAND, "bvnand");
  addOperator(kind::BITVECTOR_NOR, "bvnor");
  addOperator(kind::BITVECTOR_XOR, "bvxor");
  addOperator(kind::BITVECTOR_XNOR, "bvxnor");
  addOperator(kind::BITVECTOR_COMP, "bvcomp");
  addOperator(kind::BITVECTOR_SUB, "bvsub");
  addOperator(kind::BITVECTOR_SDIV, "bvsdiv");
  addOperator(kind::BITVECTOR_SREM, "bvsrem");
  addOperator(kind::BITVECTOR_SMOD, "bvsmod");
  addOperator(kind::BITVECTOR_ASHR, "bvashr");
  addOperator(kind::BITVECTOR_ULE, "bvule");
  addOperator(kind::BITVECTOR_UGT, "bvugt");
  addOperator(kind::BITVECTOR_UGE, "bvuge");
  addOperator(kind::BITVECTOR_SLT, "bvslt");
  addOperator(kind::BITVECTOR_SLE, "bvsle");
  addOperator(kind::BITVECTOR_SGT, "bvsgt");
  addOperator(kind::BITVECTOR_SGE, "bvsge");
  addOperator(kind::BITVECTOR_REDOR, "bvredor");
  addOperator(kind::BITVECTOR_REDAND, "bvredand");
  addOperator(kind::BITVECTOR_TO_NAT, "bv2nat");

  addIndexedOperator(
      kind::BITVECTOR_EXTRACT, api::BITVECTOR_EXTRACT_OP, "extract");
  addIndexedOperator(
      kind::BITVECTOR_REPEAT, api::BITVECTOR_REPEAT_OP, "repeat");
  addIndexedOperator(kind::BITVECTOR_ZERO_EXTEND,
                     api::BITVECTOR_ZERO_EXTEND_OP,
                     "zero_extend");
  addIndexedOperator(kind::BITVECTOR_SIGN_EXTEND,
                     api::BITVECTOR_SIGN_EXTEND_OP,
                     "sign_extend");
  addIndexedOperator(kind::BITVECTOR_ROTATE_LEFT,
                     api::BITVECTOR_ROTATE_LEFT_OP,
                     "rotate_left");
  addIndexedOperator(kind::BITVECTOR_ROTATE_RIGHT,
                     api::BITVECTOR_ROTATE_RIGHT_OP,
                     "rotate_right");
  addIndexedOperator(
      kind::INT_TO_BITVECTOR, api::INT_TO_BITVECTOR_OP, "int2bv");
}

void Smt2::addDatatypesOperators()
{
  Parser::addOperator(kind::APPLY_CONSTRUCTOR);
  Parser::addOperator(kind::APPLY_TESTER);
  Parser::addOperator(kind::APPLY_SELECTOR);
  Parser::addOperator(kind::APPLY_SELECTOR_TOTAL);

  if (!strictModeEnabled())
  {
    addOperator(kind::DT_SIZE, "dt.size");
  }
}

void Smt2::addStringOperators() {
  defineVar("re.all",
            getSolver()
                ->mkTerm(api::REGEXP_STAR, getSolver()->mkRegexpSigma())
                .getExpr());

  addOperator(kind::STRING_CONCAT, "str.++");
  addOperator(kind::STRING_LENGTH, "str.len");
  addOperator(kind::STRING_SUBSTR, "str.substr" );
  addOperator(kind::STRING_STRCTN, "str.contains" );
  addOperator(kind::STRING_CHARAT, "str.at" );
  addOperator(kind::STRING_STRIDOF, "str.indexof" );
  addOperator(kind::STRING_STRREPL, "str.replace" );
  addOperator(kind::STRING_STRREPLALL, "str.replaceall");
  addOperator(kind::STRING_PREFIX, "str.prefixof" );
  addOperator(kind::STRING_SUFFIX, "str.suffixof" );
  // at the moment, we only use this syntax for smt2.6.1
  if (getLanguage() == language::input::LANG_SMTLIB_V2_6_1)
  {
    addOperator(kind::STRING_ITOS, "str.from-int");
    addOperator(kind::STRING_STOI, "str.to-int");
    addOperator(kind::STRING_IN_REGEXP, "str.in-re");
    addOperator(kind::STRING_TO_REGEXP, "str.to-re");
  }
  else
  {
    addOperator(kind::STRING_ITOS, "int.to.str");
    addOperator(kind::STRING_STOI, "str.to.int");
    addOperator(kind::STRING_IN_REGEXP, "str.in.re");
    addOperator(kind::STRING_TO_REGEXP, "str.to.re");
  }

  addOperator(kind::REGEXP_CONCAT, "re.++");
  addOperator(kind::REGEXP_UNION, "re.union");
  addOperator(kind::REGEXP_INTER, "re.inter");
  addOperator(kind::REGEXP_STAR, "re.*");
  addOperator(kind::REGEXP_PLUS, "re.+");
  addOperator(kind::REGEXP_OPT, "re.opt");
  addOperator(kind::REGEXP_RANGE, "re.range");
  addOperator(kind::REGEXP_LOOP, "re.loop");
  addOperator(kind::STRING_CODE, "str.code");
  addOperator(kind::STRING_LT, "str.<");
  addOperator(kind::STRING_LEQ, "str.<=");
}

void Smt2::addFloatingPointOperators() {
  addOperator(kind::FLOATINGPOINT_FP, "fp");
  addOperator(kind::FLOATINGPOINT_EQ, "fp.eq");
  addOperator(kind::FLOATINGPOINT_ABS, "fp.abs");
  addOperator(kind::FLOATINGPOINT_NEG, "fp.neg");
  addOperator(kind::FLOATINGPOINT_PLUS, "fp.add");
  addOperator(kind::FLOATINGPOINT_SUB, "fp.sub");
  addOperator(kind::FLOATINGPOINT_MULT, "fp.mul");
  addOperator(kind::FLOATINGPOINT_DIV, "fp.div");
  addOperator(kind::FLOATINGPOINT_FMA, "fp.fma");
  addOperator(kind::FLOATINGPOINT_SQRT, "fp.sqrt");
  addOperator(kind::FLOATINGPOINT_REM, "fp.rem");
  addOperator(kind::FLOATINGPOINT_RTI, "fp.roundToIntegral");
  addOperator(kind::FLOATINGPOINT_MIN, "fp.min");
  addOperator(kind::FLOATINGPOINT_MAX, "fp.max");
  addOperator(kind::FLOATINGPOINT_LEQ, "fp.leq");
  addOperator(kind::FLOATINGPOINT_LT, "fp.lt");
  addOperator(kind::FLOATINGPOINT_GEQ, "fp.geq");
  addOperator(kind::FLOATINGPOINT_GT, "fp.gt");
  addOperator(kind::FLOATINGPOINT_ISN, "fp.isNormal");
  addOperator(kind::FLOATINGPOINT_ISSN, "fp.isSubnormal");
  addOperator(kind::FLOATINGPOINT_ISZ, "fp.isZero");
  addOperator(kind::FLOATINGPOINT_ISINF, "fp.isInfinite");
  addOperator(kind::FLOATINGPOINT_ISNAN, "fp.isNaN");
  addOperator(kind::FLOATINGPOINT_ISNEG, "fp.isNegative");
  addOperator(kind::FLOATINGPOINT_ISPOS, "fp.isPositive");
  addOperator(kind::FLOATINGPOINT_TO_REAL, "fp.to_real");

  addIndexedOperator(kind::FLOATINGPOINT_TO_FP_GENERIC,
                     api::FLOATINGPOINT_TO_FP_GENERIC_OP,
                     "to_fp");
  addIndexedOperator(kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
                     api::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP,
                     "to_fp_unsigned");
  addIndexedOperator(
      kind::FLOATINGPOINT_TO_UBV, api::FLOATINGPOINT_TO_UBV_OP, "fp.to_ubv");
  addIndexedOperator(
      kind::FLOATINGPOINT_TO_SBV, api::FLOATINGPOINT_TO_SBV_OP, "fp.to_sbv");

  if (!strictModeEnabled())
  {
    addIndexedOperator(kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR,
                       api::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP,
                       "to_fp_bv");
    addIndexedOperator(kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT,
                       api::FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP,
                       "to_fp_fp");
    addIndexedOperator(kind::FLOATINGPOINT_TO_FP_REAL,
                       api::FLOATINGPOINT_TO_FP_REAL_OP,
                       "to_fp_real");
    addIndexedOperator(kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
                       api::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP,
                       "to_fp_signed");
  }
}

void Smt2::addSepOperators() {
  addOperator(kind::SEP_STAR, "sep");
  addOperator(kind::SEP_PTO, "pto");
  addOperator(kind::SEP_WAND, "wand");
  addOperator(kind::SEP_EMP, "emp");
  Parser::addOperator(kind::SEP_STAR);
  Parser::addOperator(kind::SEP_PTO);
  Parser::addOperator(kind::SEP_WAND);
  Parser::addOperator(kind::SEP_EMP);
}

void Smt2::addTheory(Theory theory) {
  switch(theory) {
  case THEORY_ARRAYS:
    addOperator(kind::SELECT, "select");
    addOperator(kind::STORE, "store");
    break;

  case THEORY_BITVECTORS:
    addBitvectorOperators();
    break;

  case THEORY_CORE:
    defineType("Bool", getExprManager()->booleanType());
    defineVar("true", getExprManager()->mkConst(true));
    defineVar("false", getExprManager()->mkConst(false));
    addOperator(kind::AND, "and");
    addOperator(kind::DISTINCT, "distinct");
    addOperator(kind::EQUAL, "=");
    addOperator(kind::IMPLIES, "=>");
    addOperator(kind::ITE, "ite");
    addOperator(kind::NOT, "not");
    addOperator(kind::OR, "or");
    addOperator(kind::XOR, "xor");
    break;

  case THEORY_REALS_INTS:
    defineType("Real", getExprManager()->realType());
    addOperator(kind::DIVISION, "/");
    addOperator(kind::TO_INTEGER, "to_int");
    addOperator(kind::IS_INTEGER, "is_int");
    addOperator(kind::TO_REAL, "to_real");
    // falling through on purpose, to add Ints part of Reals_Ints
  case THEORY_INTS:
    defineType("Int", getExprManager()->integerType());
    addArithmeticOperators();
    addOperator(kind::INTS_DIVISION, "div");
    addOperator(kind::INTS_MODULUS, "mod");
    addOperator(kind::ABS, "abs");
    addIndexedOperator(kind::DIVISIBLE, api::DIVISIBLE_OP, "divisible");
    break;

  case THEORY_REALS:
    defineType("Real", getExprManager()->realType());
    addArithmeticOperators();
    addOperator(kind::DIVISION, "/");
    if (!strictModeEnabled())
    {
      addOperator(kind::ABS, "abs");
    }
    break;

  case THEORY_TRANSCENDENTALS:
    defineVar("real.pi",
              getExprManager()->mkNullaryOperator(getExprManager()->realType(),
                                                  CVC4::kind::PI));
    addTranscendentalOperators();
    break;

  case THEORY_QUANTIFIERS: addQuantifiersOperators(); break;

  case THEORY_SETS:
    defineVar("emptyset",
              d_solver->mkEmptySet(d_solver->getNullSort()).getExpr());
    // the Boolean sort is a placeholder here since we don't have type info
    // without type annotation
    defineVar("univset",
              d_solver->mkUniverseSet(d_solver->getBooleanSort()).getExpr());

    addOperator(kind::UNION, "union");
    addOperator(kind::INTERSECTION, "intersection");
    addOperator(kind::SETMINUS, "setminus");
    addOperator(kind::SUBSET, "subset");
    addOperator(kind::MEMBER, "member");
    addOperator(kind::SINGLETON, "singleton");
    addOperator(kind::INSERT, "insert");
    addOperator(kind::CARD, "card");
    addOperator(kind::COMPLEMENT, "complement");
    addOperator(kind::JOIN, "join");
    addOperator(kind::PRODUCT, "product");
    addOperator(kind::TRANSPOSE, "transpose");
    addOperator(kind::TCLOSURE, "tclosure");
    break;

  case THEORY_DATATYPES:
  {
    const std::vector<Type> types;
    defineType("Tuple", getExprManager()->mkTupleType(types));
    addDatatypesOperators();
    break;
  }

  case THEORY_STRINGS:
    defineType("String", getExprManager()->stringType());
    defineType("RegLan", getExprManager()->regExpType());
    defineType("Int", getExprManager()->integerType());

    defineVar("re.nostr", d_solver->mkRegexpEmpty().getExpr());
    defineVar("re.allchar", d_solver->mkRegexpSigma().getExpr());

    addStringOperators();
    break;

  case THEORY_UF:
    Parser::addOperator(kind::APPLY_UF);

    if (!strictModeEnabled() && d_logic.hasCardinalityConstraints())
    {
      addOperator(kind::CARDINALITY_CONSTRAINT, "fmf.card");
      addOperator(kind::CARDINALITY_VALUE, "fmf.card.val");
    }
    break;

  case THEORY_FP:
    defineType("RoundingMode", getExprManager()->roundingModeType());
    defineType("Float16", getExprManager()->mkFloatingPointType(5, 11));
    defineType("Float32", getExprManager()->mkFloatingPointType(8, 24));
    defineType("Float64", getExprManager()->mkFloatingPointType(11, 53));
    defineType("Float128", getExprManager()->mkFloatingPointType(15, 113));

    defineVar(
        "RNE",
        d_solver->mkRoundingMode(api::ROUND_NEAREST_TIES_TO_EVEN).getExpr());
    defineVar(
        "roundNearestTiesToEven",
        d_solver->mkRoundingMode(api::ROUND_NEAREST_TIES_TO_EVEN).getExpr());
    defineVar(
        "RNA",
        d_solver->mkRoundingMode(api::ROUND_NEAREST_TIES_TO_AWAY).getExpr());
    defineVar(
        "roundNearestTiesToAway",
        d_solver->mkRoundingMode(api::ROUND_NEAREST_TIES_TO_AWAY).getExpr());
    defineVar("RTP",
              d_solver->mkRoundingMode(api::ROUND_TOWARD_POSITIVE).getExpr());
    defineVar("roundTowardPositive",
              d_solver->mkRoundingMode(api::ROUND_TOWARD_POSITIVE).getExpr());
    defineVar("RTN",
              d_solver->mkRoundingMode(api::ROUND_TOWARD_NEGATIVE).getExpr());
    defineVar("roundTowardNegative",
              d_solver->mkRoundingMode(api::ROUND_TOWARD_NEGATIVE).getExpr());
    defineVar("RTZ",
              d_solver->mkRoundingMode(api::ROUND_TOWARD_ZERO).getExpr());
    defineVar("roundTowardZero",
              d_solver->mkRoundingMode(api::ROUND_TOWARD_ZERO).getExpr());

    addFloatingPointOperators();
    break;
    
  case THEORY_SEP:
    // the Boolean sort is a placeholder here since we don't have type info
    // without type annotation
    defineVar("sep.nil",
              d_solver->mkSepNil(d_solver->getBooleanSort()).getExpr());

    addSepOperators();
    break;
    
  default:
    std::stringstream ss;
    ss << "internal error: unsupported theory " << theory;
    throw ParserException(ss.str());
  }
}

void Smt2::addOperator(Kind kind, const std::string& name) {
  Debug("parser") << "Smt2::addOperator( " << kind << ", " << name << " )"
                  << std::endl;
  Parser::addOperator(kind);
  operatorKindMap[name] = kind;
}

void Smt2::addIndexedOperator(Kind tKind,
                              api::Kind opKind,
                              const std::string& name)
{
  Parser::addOperator(tKind);
  d_indexedOpKindMap[name] = opKind;
}

Kind Smt2::getOperatorKind(const std::string& name) const {
  // precondition: isOperatorEnabled(name)
  return operatorKindMap.find(name)->second;
}

bool Smt2::isOperatorEnabled(const std::string& name) const {
  return operatorKindMap.find(name) != operatorKindMap.end();
}

bool Smt2::isTheoryEnabled(Theory theory) const {
  switch(theory) {
  case THEORY_ARRAYS:
    return d_logic.isTheoryEnabled(theory::THEORY_ARRAYS);
  case THEORY_BITVECTORS:
    return d_logic.isTheoryEnabled(theory::THEORY_BV);
  case THEORY_CORE:
    return true;
  case THEORY_DATATYPES:
    return d_logic.isTheoryEnabled(theory::THEORY_DATATYPES);
  case THEORY_INTS:
    return d_logic.isTheoryEnabled(theory::THEORY_ARITH) &&
      d_logic.areIntegersUsed() && ( !d_logic.areRealsUsed() );
  case THEORY_REALS:
    return d_logic.isTheoryEnabled(theory::THEORY_ARITH) &&
      ( !d_logic.areIntegersUsed() ) && d_logic.areRealsUsed();
  case THEORY_REALS_INTS:
    return d_logic.isTheoryEnabled(theory::THEORY_ARITH) &&
      d_logic.areIntegersUsed() && d_logic.areRealsUsed();
  case THEORY_QUANTIFIERS:
    return d_logic.isQuantified();
  case THEORY_SETS:
    return d_logic.isTheoryEnabled(theory::THEORY_SETS);
  case THEORY_STRINGS:
    return d_logic.isTheoryEnabled(theory::THEORY_STRINGS);
  case THEORY_UF:
    return d_logic.isTheoryEnabled(theory::THEORY_UF);
  case THEORY_FP:
    return d_logic.isTheoryEnabled(theory::THEORY_FP);
  case THEORY_SEP:
    return d_logic.isTheoryEnabled(theory::THEORY_SEP);
  default:
    std::stringstream ss;
    ss << "internal error: unsupported theory " << theory;
    throw ParserException(ss.str());
  }
}

bool Smt2::logicIsSet() {
  return d_logicSet;
}

Expr Smt2::getExpressionForNameAndType(const std::string& name, Type t) {
  if (sygus_v1() && name[0] == '-'
      && name.find_first_not_of("0123456789", 1) == std::string::npos)
  {
    // allow unary minus in sygus version 1
    return getExprManager()->mkConst(Rational(name));
  }
  else if (isAbstractValue(name))
  {
    return mkAbstractValue(name);
  }
  return Parser::getExpressionForNameAndType(name, t);
}

api::Term Smt2::mkIndexedConstant(const std::string& name,
                                  const std::vector<uint64_t>& numerals)
{
  if (isTheoryEnabled(THEORY_FP))
  {
    if (name == "+oo")
    {
      return d_solver->mkPosInf(numerals[0], numerals[1]);
    }
    else if (name == "-oo")
    {
      return d_solver->mkNegInf(numerals[0], numerals[1]);
    }
    else if (name == "NaN")
    {
      return d_solver->mkNaN(numerals[0], numerals[1]);
    }
    else if (name == "+zero")
    {
      return d_solver->mkPosZero(numerals[0], numerals[1]);
    }
    else if (name == "-zero")
    {
      return d_solver->mkNegZero(numerals[0], numerals[1]);
    }
  }

  if (isTheoryEnabled(THEORY_BITVECTORS) && name.find("bv") == 0)
  {
    std::string bvStr = name.substr(2);
    return d_solver->mkBitVector(numerals[0], bvStr, 10);
  }

  // NOTE: Theory parametric constants go here

  parseError(std::string("Unknown indexed literal `") + name + "'");
  return api::Term();
}

api::OpTerm Smt2::mkIndexedOp(const std::string& name,
                              const std::vector<uint64_t>& numerals)
{
  const auto& kIt = d_indexedOpKindMap.find(name);
  if (kIt != d_indexedOpKindMap.end())
  {
    api::Kind k = (*kIt).second;
    if (numerals.size() == 1)
    {
      return d_solver->mkOpTerm(k, numerals[0]);
    }
    else if (numerals.size() == 2)
    {
      return d_solver->mkOpTerm(k, numerals[0], numerals[1]);
    }
  }

  parseError(std::string("Unknown indexed function `") + name + "'");
  return api::OpTerm();
}

Expr Smt2::mkDefineFunRec(
    const std::string& fname,
    const std::vector<std::pair<std::string, Type> >& sortedVarNames,
    Type t,
    std::vector<Expr>& flattenVars)
{
  std::vector<Type> sorts;
  for (const std::pair<std::string, CVC4::Type>& svn : sortedVarNames)
  {
    sorts.push_back(svn.second);
  }

  // make the flattened function type, add bound variables
  // to flattenVars if the defined function was given a function return type.
  Type ft = mkFlatFunctionType(sorts, t, flattenVars);

  // allow overloading
  return mkVar(fname, ft, ExprManager::VAR_FLAG_NONE, true);
}

void Smt2::pushDefineFunRecScope(
    const std::vector<std::pair<std::string, Type> >& sortedVarNames,
    Expr func,
    const std::vector<Expr>& flattenVars,
    std::vector<Expr>& bvs,
    bool bindingLevel)
{
  pushScope(bindingLevel);

  // bound variables are those that are explicitly named in the preamble
  // of the define-fun(s)-rec command, we define them here
  for (const std::pair<std::string, CVC4::Type>& svn : sortedVarNames)
  {
    Expr v = mkBoundVar(svn.first, svn.second);
    bvs.push_back(v);
  }

  bvs.insert(bvs.end(), flattenVars.begin(), flattenVars.end());
}

void Smt2::reset() {
  d_logicSet = false;
  d_logic = LogicInfo();
  operatorKindMap.clear();
  d_lastNamedTerm = std::pair<Expr, std::string>();
  this->Parser::reset();

  if( !strictModeEnabled() ) {
    addTheory(Smt2::THEORY_CORE);
  }
}

void Smt2::resetAssertions() {
  // Remove all declarations except the ones at level 0.
  while (this->scopeLevel() > 0) {
    this->popScope();
  }
}

Command* Smt2::setLogic(std::string name, bool fromCommand)
{
  if (fromCommand)
  {
    if (d_seenSetLogic)
    {
      parseError("Only one set-logic is allowed.");
    }
    d_seenSetLogic = true;

    if (logicIsForced())
    {
      // If the logic is forced, we ignore all set-logic requests from commands.
      return new EmptyCommand();
    }
  }

  if (sygus_v1())
  {
    // non-smt2-standard sygus logic names go here (http://sygus.seas.upenn.edu/files/sygus.pdf Section 3.2)
    if(name == "Arrays") {
      name = "A";
    }else if(name == "Reals") {
      name = "LRA";
    }
  }

  d_logicSet = true;
  d_logic = name;

  // if sygus is enabled, we must enable UF, datatypes, integer arithmetic and
  // higher-order
  if(sygus()) {
    if (!d_logic.isQuantified())
    {
      warning("Logics in sygus are assumed to contain quantifiers.");
      warning("Omit QF_ from the logic to avoid this warning.");
    }
    // get unlocked copy, modify, copy and relock
    LogicInfo log(d_logic.getUnlockedCopy());
    log.enableQuantifiers();
    log.enableTheory(theory::THEORY_UF);
    log.enableTheory(theory::THEORY_DATATYPES);
    log.enableIntegers();
    log.enableHigherOrder();
    d_logic = log;
    d_logic.lock();
  }

  // Core theory belongs to every logic
  addTheory(THEORY_CORE);

  if(d_logic.isTheoryEnabled(theory::THEORY_UF)) {
    addTheory(THEORY_UF);
  }

  if(d_logic.isTheoryEnabled(theory::THEORY_ARITH)) {
    if(d_logic.areIntegersUsed()) {
      if(d_logic.areRealsUsed()) {
        addTheory(THEORY_REALS_INTS);
      } else {
        addTheory(THEORY_INTS);
      }
    } else if(d_logic.areRealsUsed()) {
      addTheory(THEORY_REALS);
    }

    if (d_logic.areTranscendentalsUsed())
    {
      addTheory(THEORY_TRANSCENDENTALS);
    }
  }

  if(d_logic.isTheoryEnabled(theory::THEORY_ARRAYS)) {
    addTheory(THEORY_ARRAYS);
  }

  if(d_logic.isTheoryEnabled(theory::THEORY_BV)) {
    addTheory(THEORY_BITVECTORS);
  }

  if(d_logic.isTheoryEnabled(theory::THEORY_DATATYPES)) {
    addTheory(THEORY_DATATYPES);
  }

  if(d_logic.isTheoryEnabled(theory::THEORY_SETS)) {
    addTheory(THEORY_SETS);
  }

  if(d_logic.isTheoryEnabled(theory::THEORY_STRINGS)) {
    addTheory(THEORY_STRINGS);
  }

  if(d_logic.isQuantified()) {
    addTheory(THEORY_QUANTIFIERS);
  }

  if (d_logic.isTheoryEnabled(theory::THEORY_FP)) {
    addTheory(THEORY_FP);
  }

  if (d_logic.isTheoryEnabled(theory::THEORY_SEP)) {
    addTheory(THEORY_SEP);
  }

  if (sygus())
  {
    return new SetBenchmarkLogicCommand(d_logic.getLogicString());
  }
  else
  {
    return new SetBenchmarkLogicCommand(name);
  }
} /* Smt2::setLogic() */

bool Smt2::sygus() const
{
  InputLanguage ilang = getLanguage();
  return ilang == language::input::LANG_SYGUS
         || ilang == language::input::LANG_SYGUS_V2;
}
bool Smt2::sygus_v1() const
{
  return getLanguage() == language::input::LANG_SYGUS;
}

void Smt2::setInfo(const std::string& flag, const SExpr& sexpr) {
  // TODO: ???
}

void Smt2::setOption(const std::string& flag, const SExpr& sexpr) {
  // TODO: ???
}

void Smt2::checkThatLogicIsSet()
{
  if (!logicIsSet())
  {
    if (strictModeEnabled())
    {
      parseError("set-logic must appear before this point.");
    }
    else
    {
      Command* cmd = nullptr;
      if (logicIsForced())
      {
        cmd = setLogic(getForcedLogic(), false);
      }
      else
      {
        warning("No set-logic command was given before this point.");
        warning("CVC4 will make all theories available.");
        warning(
            "Consider setting a stricter logic for (likely) better "
            "performance.");
        warning("To suppress this warning in the future use (set-logic ALL).");

        cmd = setLogic("ALL", false);
      }
      preemptCommand(cmd);
    }
  }
}

/* The include are managed in the lexer but called in the parser */
// Inspired by http://www.antlr3.org/api/C/interop.html

static bool newInputStream(const std::string& filename, pANTLR3_LEXER lexer) {
  Debug("parser") << "Including " << filename << std::endl;
  // Create a new input stream and take advantage of built in stream stacking
  // in C target runtime.
  //
  pANTLR3_INPUT_STREAM    in;
#ifdef CVC4_ANTLR3_OLD_INPUT_STREAM
  in = antlr3AsciiFileStreamNew((pANTLR3_UINT8) filename.c_str());
#else /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  in = antlr3FileStreamNew((pANTLR3_UINT8) filename.c_str(), ANTLR3_ENC_8BIT);
#endif /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  if( in == NULL ) {
    Debug("parser") << "Can't open " << filename << std::endl;
    return false;
  }
  // Same thing as the predefined PUSHSTREAM(in);
  lexer->pushCharStream(lexer, in);
  // restart it
  //lexer->rec->state->tokenStartCharIndex      = -10;
  //lexer->emit(lexer);

  // Note that the input stream is not closed when it EOFs, I don't bother
  // to do it here, but it is up to you to track streams created like this
  // and destroy them when the whole parse session is complete. Remember that you
  // don't want to do this until all tokens have been manipulated all the way through
  // your tree parsers etc as the token does not store the text it just refers
  // back to the input stream and trying to get the text for it will abort if you
  // close the input stream too early.

  //TODO what said before
  return true;
}

void Smt2::includeFile(const std::string& filename) {
  // security for online version
  if(!canIncludeFile()) {
    parseError("include-file feature was disabled for this run.");
  }

  // Get the lexer
  AntlrInput* ai = static_cast<AntlrInput*>(getInput());
  pANTLR3_LEXER lexer = ai->getAntlr3Lexer();
  // get the name of the current stream "Does it work inside an include?"
  const std::string inputName = ai->getInputStreamName();

  // Find the directory of the current input file
  std::string path;
  size_t pos = inputName.rfind('/');
  if(pos != std::string::npos) {
    path = std::string(inputName, 0, pos + 1);
  }
  path.append(filename);
  if(!newInputStream(path, lexer)) {
    parseError("Couldn't open include file `" + path + "'");
  }
}

void Smt2::mkSygusConstantsForType( const Type& type, std::vector<CVC4::Expr>& ops ) {
  if( type.isInteger() ){
    ops.push_back(getExprManager()->mkConst(Rational(0)));
    ops.push_back(getExprManager()->mkConst(Rational(1)));
  }else if( type.isBitVector() ){
    unsigned sz = ((BitVectorType)type).getSize();
    BitVector bval0(sz, (unsigned int)0);
    ops.push_back( getExprManager()->mkConst(bval0) );
    BitVector bval1(sz, (unsigned int)1);
    ops.push_back( getExprManager()->mkConst(bval1) );
  }else if( type.isBoolean() ){
    ops.push_back(getExprManager()->mkConst(true));
    ops.push_back(getExprManager()->mkConst(false));
  }
  //TODO : others?
}

//  This method adds N operators to ops[index], N names to cnames[index] and N type argument vectors to cargs[index] (where typically N=1)
//  This method may also add new elements pairwise into datatypes/sorts/ops/cnames/cargs in the case of non-flat gterms.
void Smt2::processSygusGTerm( CVC4::SygusGTerm& sgt, int index,
                              std::vector< CVC4::Datatype >& datatypes,
                              std::vector< CVC4::Type>& sorts,
                              std::vector< std::vector<CVC4::Expr> >& ops,
                              std::vector< std::vector<std::string> >& cnames,
                              std::vector< std::vector< std::vector< CVC4::Type > > >& cargs,
                              std::vector< bool >& allow_const,
                              std::vector< std::vector< std::string > >& unresolved_gterm_sym,
                              std::vector<CVC4::Expr>& sygus_vars,
                              std::map< CVC4::Type, CVC4::Type >& sygus_to_builtin, std::map< CVC4::Type, CVC4::Expr >& sygus_to_builtin_expr,
                              CVC4::Type& ret, bool isNested ){
  if( sgt.d_gterm_type==SygusGTerm::gterm_op || sgt.d_gterm_type==SygusGTerm::gterm_let ){
    Debug("parser-sygus") << "Add " << sgt.d_expr << " to datatype " << index
                          << ", isLet = "
                          << (sgt.d_gterm_type == SygusGTerm::gterm_let)
                          << std::endl;
    Kind oldKind;
    Kind newKind = kind::UNDEFINED_KIND;
    //convert to UMINUS if one child of MINUS
    if( sgt.d_children.size()==1 && sgt.d_expr==getExprManager()->operatorOf(kind::MINUS) ){
      oldKind = kind::MINUS;
      newKind = kind::UMINUS;
    }
    if( newKind!=kind::UNDEFINED_KIND ){
      Expr newExpr = getExprManager()->operatorOf(newKind);
      Debug("parser-sygus") << "Replace " << sgt.d_expr << " with " << newExpr << std::endl;
      sgt.d_expr = newExpr;
      std::string oldName = kind::kindToString(oldKind);
      std::string newName = kind::kindToString(newKind);
      size_t pos = 0;
      if((pos = sgt.d_name.find(oldName, pos)) != std::string::npos){
        sgt.d_name.replace(pos, oldName.length(), newName);
      }
    }
    ops[index].push_back( sgt.d_expr );
    cnames[index].push_back( sgt.d_name );
    cargs[index].push_back( std::vector< CVC4::Type >() );
    for( unsigned i=0; i<sgt.d_children.size(); i++ ){
      std::stringstream ss;
      ss << datatypes[index].getName() << "_" << ops[index].size() << "_arg_" << i;
      std::string sub_dname = ss.str();
      //add datatype for child
      Type null_type;
      pushSygusDatatypeDef( null_type, sub_dname, datatypes, sorts, ops, cnames, cargs, allow_const, unresolved_gterm_sym );
      int sub_dt_index = datatypes.size()-1;
      //process child
      Type sub_ret;
      processSygusGTerm( sgt.d_children[i], sub_dt_index, datatypes, sorts, ops, cnames, cargs, allow_const, unresolved_gterm_sym,
                         sygus_vars, sygus_to_builtin, sygus_to_builtin_expr, sub_ret, true );
      //process the nested gterm (either pop the last datatype, or flatten the argument)
      Type tt = processSygusNestedGTerm( sub_dt_index, sub_dname, datatypes, sorts, ops, cnames, cargs, allow_const, unresolved_gterm_sym,
                                         sygus_to_builtin, sygus_to_builtin_expr, sub_ret );
      cargs[index].back().push_back(tt);
    }
    //if let, must create operator
    if( sgt.d_gterm_type==SygusGTerm::gterm_let ){
      processSygusLetConstructor( sgt.d_let_vars, index, datatypes, sorts, ops, cnames, cargs,
                                  sygus_vars, sygus_to_builtin, sygus_to_builtin_expr );
    }
  }else if( sgt.d_gterm_type==SygusGTerm::gterm_constant ){
    if( sgt.getNumChildren()!=0 ){
      parseError("Bad syntax for Sygus Constant.");
    }
    std::vector< Expr > consts;
    mkSygusConstantsForType( sgt.d_type, consts );
    Debug("parser-sygus") << "...made " << consts.size() << " constants." << std::endl;
    for( unsigned i=0; i<consts.size(); i++ ){
      std::stringstream ss;
      ss << consts[i];
      Debug("parser-sygus") << "...add for constant " << ss.str() << std::endl;
      ops[index].push_back( consts[i] );
      cnames[index].push_back( ss.str() );
      cargs[index].push_back( std::vector< CVC4::Type >() );
    }
    allow_const[index] = true;
  }else if( sgt.d_gterm_type==SygusGTerm::gterm_variable || sgt.d_gterm_type==SygusGTerm::gterm_input_variable ){
    if( sgt.getNumChildren()!=0 ){
      parseError("Bad syntax for Sygus Variable.");
    }
    Debug("parser-sygus") << "...process " << sygus_vars.size() << " variables." << std::endl;
    for( unsigned i=0; i<sygus_vars.size(); i++ ){
      if( sygus_vars[i].getType()==sgt.d_type ){
        std::stringstream ss;
        ss << sygus_vars[i];
        Debug("parser-sygus") << "...add for variable " << ss.str() << std::endl;
        ops[index].push_back( sygus_vars[i] );
        cnames[index].push_back( ss.str() );
        cargs[index].push_back( std::vector< CVC4::Type >() );
      }
    }
  }else if( sgt.d_gterm_type==SygusGTerm::gterm_nested_sort ){
    ret = sgt.d_type;
  }else if( sgt.d_gterm_type==SygusGTerm::gterm_unresolved ){
    if( isNested ){
      if( isUnresolvedType(sgt.d_name) ){
        ret = getSort(sgt.d_name);
      }else{
        //nested, unresolved symbol...fail
        std::stringstream ss;
        ss << "Cannot handle nested unresolved symbol " << sgt.d_name << std::endl;
        parseError(ss.str());
      }
    }else{
      //will resolve when adding constructors
      unresolved_gterm_sym[index].push_back(sgt.d_name);
    }
  }else if( sgt.d_gterm_type==SygusGTerm::gterm_ignore ){

  }
}

bool Smt2::pushSygusDatatypeDef( Type t, std::string& dname,
                                  std::vector< CVC4::Datatype >& datatypes,
                                  std::vector< CVC4::Type>& sorts,
                                  std::vector< std::vector<CVC4::Expr> >& ops,
                                  std::vector< std::vector<std::string> >& cnames,
                                  std::vector< std::vector< std::vector< CVC4::Type > > >& cargs,
                                  std::vector< bool >& allow_const,
                                  std::vector< std::vector< std::string > >& unresolved_gterm_sym ){
  sorts.push_back(t);
  datatypes.push_back(Datatype(dname));
  ops.push_back(std::vector<Expr>());
  cnames.push_back(std::vector<std::string>());
  cargs.push_back(std::vector<std::vector<CVC4::Type> >());
  allow_const.push_back(false);
  unresolved_gterm_sym.push_back(std::vector< std::string >());
  return true;
}

bool Smt2::popSygusDatatypeDef( std::vector< CVC4::Datatype >& datatypes,
                                 std::vector< CVC4::Type>& sorts,
                                 std::vector< std::vector<CVC4::Expr> >& ops,
                                 std::vector< std::vector<std::string> >& cnames,
                                 std::vector< std::vector< std::vector< CVC4::Type > > >& cargs,
                                 std::vector< bool >& allow_const,
                                 std::vector< std::vector< std::string > >& unresolved_gterm_sym ){
  sorts.pop_back();
  datatypes.pop_back();
  ops.pop_back();
  cnames.pop_back();
  cargs.pop_back();
  allow_const.pop_back();
  unresolved_gterm_sym.pop_back();
  return true;
}

Type Smt2::processSygusNestedGTerm( int sub_dt_index, std::string& sub_dname, std::vector< CVC4::Datatype >& datatypes,
                                    std::vector< CVC4::Type>& sorts,
                                    std::vector< std::vector<CVC4::Expr> >& ops,
                                    std::vector< std::vector<std::string> >& cnames,
                                    std::vector< std::vector< std::vector< CVC4::Type > > >& cargs,
                                    std::vector< bool >& allow_const,
                                    std::vector< std::vector< std::string > >& unresolved_gterm_sym,
                                    std::map< CVC4::Type, CVC4::Type >& sygus_to_builtin,
                                    std::map< CVC4::Type, CVC4::Expr >& sygus_to_builtin_expr, Type sub_ret ) {
  Type t = sub_ret;
  Debug("parser-sygus") << "Argument is ";
  if( t.isNull() ){
    //then, it is the datatype we constructed, which should have a single constructor
    t = mkUnresolvedType(sub_dname);
    Debug("parser-sygus") << "inline flattening of (auxiliary, local) datatype " << t << std::endl;
    Debug("parser-sygus") << ": to compute type, construct ground term witnessing the grammar, #cons=" << cargs[sub_dt_index].size() << std::endl;
    if( cargs[sub_dt_index].empty() ){
      parseError(std::string("Internal error : datatype for nested gterm does not have a constructor."));
    }
    Expr sop = ops[sub_dt_index][0];
    Type curr_t;
    if( sop.getKind() != kind::BUILTIN && ( sop.isConst() || cargs[sub_dt_index][0].empty() ) ){
      curr_t = sop.getType();
      Debug("parser-sygus") << ": it is constant/0-arg cons " << sop << " with type " << sop.getType() << ", debug=" << sop.isConst() << " " << cargs[sub_dt_index][0].size() << std::endl;
      // only cache if it is a singleton datatype (has unique expr)
      if (ops[sub_dt_index].size() == 1)
      {
        sygus_to_builtin_expr[t] = sop;
        // store that term sop has dedicated sygus type t
        if (d_sygus_bound_var_type.find(sop) == d_sygus_bound_var_type.end())
        {
          d_sygus_bound_var_type[sop] = t;
        }
      }
    }else{
      std::vector< Expr > children;
      if( sop.getKind() != kind::BUILTIN ){
        children.push_back( sop );
      }
      for( unsigned i=0; i<cargs[sub_dt_index][0].size(); i++ ){
        std::map< CVC4::Type, CVC4::Expr >::iterator it = sygus_to_builtin_expr.find( cargs[sub_dt_index][0][i] );
        if( it==sygus_to_builtin_expr.end() ){
          if( sygus_to_builtin.find( cargs[sub_dt_index][0][i] )==sygus_to_builtin.end() ){
            std::stringstream ss;
            ss << "Missing builtin type for type " << cargs[sub_dt_index][0][i] << "!" << std::endl;
            ss << "Builtin types are currently : " << std::endl;
            for( std::map< CVC4::Type, CVC4::Type >::iterator itb = sygus_to_builtin.begin(); itb != sygus_to_builtin.end(); ++itb ){
              ss << "  " << itb->first << " -> " << itb->second << std::endl;
            }
            parseError(ss.str());
          }
          Type bt = sygus_to_builtin[cargs[sub_dt_index][0][i]];
          Debug("parser-sygus") << ":  child " << i << " introduce type elem for " << cargs[sub_dt_index][0][i] << " " << bt << std::endl;
          std::stringstream ss;
          ss << t << "_x_" << i;
          Expr bv = mkBoundVar(ss.str(), bt);
          children.push_back( bv );
          d_sygus_bound_var_type[bv] = cargs[sub_dt_index][0][i];
        }else{
          Debug("parser-sygus") << ":  child " << i << " existing sygus to builtin expr : " << it->second << std::endl;
          children.push_back( it->second );
        }
      }
      Kind sk = sop.getKind() != kind::BUILTIN
                    ? kind::APPLY_UF
                    : getExprManager()->operatorToKind(sop);
      Debug("parser-sygus") << ": operator " << sop << " with " << sop.getKind() << " " << sk << std::endl;
      Expr e = getExprManager()->mkExpr( sk, children );
      Debug("parser-sygus") << ": constructed " << e << ", which has type " << e.getType() << std::endl;
      curr_t = e.getType();
      sygus_to_builtin_expr[t] = e;
    }
    sorts[sub_dt_index] = curr_t;
    sygus_to_builtin[t] = curr_t;
  }else{
    Debug("parser-sygus") << "simple argument " << t << std::endl;
    Debug("parser-sygus") << "...removing " << datatypes.back().getName() << std::endl;
    //otherwise, datatype was unecessary
    //pop argument datatype definition
    popSygusDatatypeDef( datatypes, sorts, ops, cnames, cargs, allow_const, unresolved_gterm_sym );
  }
  return t;
}

void Smt2::processSygusLetConstructor( std::vector< CVC4::Expr >& let_vars,
                                       int index,
                                       std::vector< CVC4::Datatype >& datatypes,
                                       std::vector< CVC4::Type>& sorts,
                                       std::vector< std::vector<CVC4::Expr> >& ops,
                                       std::vector< std::vector<std::string> >& cnames,
                                       std::vector< std::vector< std::vector< CVC4::Type > > >& cargs,
                                       std::vector<CVC4::Expr>& sygus_vars,
                                       std::map< CVC4::Type, CVC4::Type >& sygus_to_builtin,
                                       std::map< CVC4::Type, CVC4::Expr >& sygus_to_builtin_expr ) {
  std::vector< CVC4::Expr > let_define_args;
  Expr let_body;
  int dindex = cargs[index].size()-1;
  Debug("parser-sygus") << "Process let constructor for datatype " << datatypes[index].getName() << ", #subtypes = " << cargs[index][dindex].size() << std::endl;
  for( unsigned i=0; i<cargs[index][dindex].size(); i++ ){
    Debug("parser-sygus") << "  " << i << " : " << cargs[index][dindex][i] << std::endl;
    if( i+1==cargs[index][dindex].size() ){
      std::map< CVC4::Type, CVC4::Expr >::iterator it = sygus_to_builtin_expr.find( cargs[index][dindex][i] );
      if( it!=sygus_to_builtin_expr.end() ){
        let_body = it->second;
      }else{
        std::stringstream ss;
        ss << datatypes[index].getName() << "_body";
        let_body = mkBoundVar(ss.str(), sygus_to_builtin[cargs[index][dindex][i]]);
        d_sygus_bound_var_type[let_body] = cargs[index][dindex][i];
      }
    }
  }
  Debug("parser-sygus") << std::endl;
  Debug("parser-sygus") << "Body is " << let_body << std::endl;
  Debug("parser-sygus") << "# let vars = " << let_vars.size() << std::endl;
  for( unsigned i=0; i<let_vars.size(); i++ ){
    Debug("parser-sygus") << "  let var " << i << " : " << let_vars[i] << " " << let_vars[i].getType() << std::endl;
    let_define_args.push_back( let_vars[i] );
  }
  /*
  Debug("parser-sygus") << "index = " << index << ", start index = " << start_index << ", #Current datatypes = " << datatypes.size() << std::endl;
  for( unsigned i=start_index; i<datatypes.size(); i++ ){
    Debug("parser-sygus") << "  datatype " << i << " : " << datatypes[i].getName() << ", #cons = " << cargs[i].size() << std::endl;
    if( !cargs[i].empty() ){
      Debug("parser-sygus") << "  operator 0 is " << ops[i][0] << std::endl;
      Debug("parser-sygus") << "  cons 0 has " << cargs[i][0].size() << " sub fields." << std::endl;
      for( unsigned j=0; j<cargs[i][0].size(); j++ ){
        Type bt = sygus_to_builtin[cargs[i][0][j]];
        Debug("parser-sygus") << "    cons 0, selector " << j << " : " << cargs[i][0][j] << " " << bt << std::endl;
      }
    }
  }
  */
  //last argument is the return, pop
  cargs[index][dindex].pop_back();
  collectSygusLetArgs( let_body, cargs[index][dindex], let_define_args );

  Debug("parser-sygus") << "Make define-fun with "
                        << cargs[index][dindex].size()
                        << " operator arguments and " << let_define_args.size()
                        << " provided arguments..." << std::endl;
  if (cargs[index][dindex].size() != let_define_args.size())
  {
    std::stringstream ss;
    ss << "Wrong number of let body terms." << std::endl;
    parseError(ss.str());
  }
  std::vector<CVC4::Type> fsorts;
  for( unsigned i=0; i<cargs[index][dindex].size(); i++ ){
    Debug("parser-sygus") << "  " << i << " : " << let_define_args[i] << " " << let_define_args[i].getType() << " " << cargs[index][dindex][i] << std::endl;
    fsorts.push_back(let_define_args[i].getType());
  }

  Type ft = getExprManager()->mkFunctionType(fsorts, let_body.getType());
  std::stringstream ss;
  ss << datatypes[index].getName() << "_let";
  Expr let_func = mkFunction(ss.str(), ft, ExprManager::VAR_FLAG_DEFINED);
  d_sygus_defined_funs.push_back( let_func );
  preemptCommand( new DefineFunctionCommand(ss.str(), let_func, let_define_args, let_body) );

  ops[index].pop_back();
  ops[index].push_back( let_func );
  cnames[index].pop_back();
  cnames[index].push_back(ss.str());

  //mark function as let constructor
  d_sygus_let_func_to_vars[let_func].insert( d_sygus_let_func_to_vars[let_func].end(), let_define_args.begin(), let_define_args.end() );
  d_sygus_let_func_to_body[let_func] = let_body;
  d_sygus_let_func_to_num_input_vars[let_func] = let_vars.size();
}


void Smt2::collectSygusLetArgs( CVC4::Expr e, std::vector< CVC4::Type >& sygusArgs, std::vector< CVC4::Expr >& builtinArgs ) {
  if( e.getKind()==kind::BOUND_VARIABLE ){
    if( std::find( builtinArgs.begin(), builtinArgs.end(), e )==builtinArgs.end() ){
      builtinArgs.push_back( e );
      sygusArgs.push_back( d_sygus_bound_var_type[e] );
      if( d_sygus_bound_var_type[e].isNull() ){
        std::stringstream ss;
        ss << "While constructing body of let gterm, can't map " << e << " to sygus type." << std::endl;
        parseError(ss.str());
      }
    }
  }else{
    for( unsigned i=0; i<e.getNumChildren(); i++ ){
      collectSygusLetArgs( e[i], sygusArgs, builtinArgs );
    }
  }
}

void Smt2::setSygusStartIndex( std::string& fun, int startIndex,
                               std::vector< CVC4::Datatype >& datatypes,
                               std::vector< CVC4::Type>& sorts,
                               std::vector< std::vector<CVC4::Expr> >& ops ) {
  if( startIndex>0 ){
    CVC4::Datatype tmp_dt = datatypes[0];
    Type tmp_sort = sorts[0];
    std::vector< Expr > tmp_ops;
    tmp_ops.insert( tmp_ops.end(), ops[0].begin(), ops[0].end() );
    datatypes[0] = datatypes[startIndex];
    sorts[0] = sorts[startIndex];
    ops[0].clear();
    ops[0].insert( ops[0].end(), ops[startIndex].begin(), ops[startIndex].end() );
    datatypes[startIndex] = tmp_dt;
    sorts[startIndex] = tmp_sort;
    ops[startIndex].clear();
    ops[startIndex].insert( ops[startIndex].begin(), tmp_ops.begin(), tmp_ops.end() );
  }else if( startIndex<0 ){
    std::stringstream ss;
    ss << "warning: no symbol named Start for synth-fun " << fun << std::endl;
    warning(ss.str());
  }
}

void Smt2::mkSygusDatatype( CVC4::Datatype& dt, std::vector<CVC4::Expr>& ops,
                            std::vector<std::string>& cnames, std::vector< std::vector< CVC4::Type > >& cargs,
                            std::vector<std::string>& unresolved_gterm_sym,
                            std::map< CVC4::Type, CVC4::Type >& sygus_to_builtin ) {
  Debug("parser-sygus") << "Making sygus datatype " << dt.getName() << std::endl;
  Debug("parser-sygus") << "  add constructors..." << std::endl;
  
  Debug("parser-sygus") << "SMT2 sygus parser : Making constructors for sygus datatype " << dt.getName() << std::endl;
  Debug("parser-sygus") << "  add constructors..." << std::endl;
  // size of cnames changes, this loop must check size
  for (unsigned i = 0; i < cnames.size(); i++)
  {
    bool is_dup = false;
    bool is_dup_op = false;
    for (unsigned j = 0; j < i; j++)
    {
      if( ops[i]==ops[j] ){
        is_dup_op = true;
        if( cargs[i].size()==cargs[j].size() ){
          is_dup = true;
          for( unsigned k=0; k<cargs[i].size(); k++ ){
            if( cargs[i][k]!=cargs[j][k] ){
              is_dup = false;
              break;
            }
          }
        }
        if( is_dup ){
          break;
        }
      }
    }
    Debug("parser-sygus") << "SYGUS CONS " << i << " : ";
    if( is_dup ){
      Debug("parser-sygus") << "--> Duplicate gterm : " << ops[i] << std::endl;
      ops.erase( ops.begin() + i, ops.begin() + i + 1 );
      cnames.erase( cnames.begin() + i, cnames.begin() + i + 1 );
      cargs.erase( cargs.begin() + i, cargs.begin() + i + 1 );
      i--;
    }
    else
    {
      std::shared_ptr<SygusPrintCallback> spc;
      if (is_dup_op)
      {
        Debug("parser-sygus") << "--> Duplicate gterm operator : " << ops[i]
                              << std::endl;
        // make into define-fun
        std::vector<Type> ltypes;
        for (unsigned j = 0, size = cargs[i].size(); j < size; j++)
        {
          ltypes.push_back(sygus_to_builtin[cargs[i][j]]);
        }
        std::vector<Expr> largs;
        Expr lbvl = makeSygusBoundVarList(dt, i, ltypes, largs);

        // make the let_body
        std::vector<Expr> children;
        if (ops[i].getKind() != kind::BUILTIN)
        {
          children.push_back(ops[i]);
        }
        children.insert(children.end(), largs.begin(), largs.end());
        Kind sk = ops[i].getKind() != kind::BUILTIN
                      ? kind::APPLY_UF
                      : getExprManager()->operatorToKind(ops[i]);
        Expr body = getExprManager()->mkExpr(sk, children);
        // replace by lambda
        ops[i] = getExprManager()->mkExpr(kind::LAMBDA, lbvl, body);
        Debug("parser-sygus") << "  ...replace op : " << ops[i] << std::endl;
        // callback prints as the expression
        spc = std::make_shared<printer::SygusExprPrintCallback>(body, largs);
      }
      else
      {
        std::map<Expr, Expr>::iterator it =
            d_sygus_let_func_to_body.find(ops[i]);
        if (it != d_sygus_let_func_to_body.end())
        {
          Debug("parser-sygus") << "--> Let expression " << ops[i] << std::endl;
          Expr let_body = it->second;
          std::vector<Expr> let_args = d_sygus_let_func_to_vars[ops[i]];
          unsigned let_num_input_args =
              d_sygus_let_func_to_num_input_vars[ops[i]];
          // the operator is just the body for the arguments
          std::vector<Type> ltypes;
          for (unsigned j = 0, size = let_args.size(); j < size; j++)
          {
            ltypes.push_back(let_args[j].getType());
          }
          std::vector<Expr> largs;
          Expr lbvl = makeSygusBoundVarList(dt, i, ltypes, largs);
          Expr sbody = let_body.substitute(let_args, largs);
          ops[i] = getExprManager()->mkExpr(kind::LAMBDA, lbvl, sbody);
          Debug("parser-sygus") << "  ...replace op : " << ops[i] << std::endl;
          // callback prints as a let expression
          spc = std::make_shared<printer::SygusLetExprPrintCallback>(
              let_body, let_args, let_num_input_args);
        }
        else if (ops[i].getType().isBitVector() && ops[i].isConst())
        {
          Debug("parser-sygus") << "--> Bit-vector constant " << ops[i] << " ("
                                << cnames[i] << ")" << std::endl;
          // Since there are multiple output formats for bit-vectors and
          // we are required by sygus standards to print in the exact input
          // format given by the user, we use a print callback to custom print
          // the given name.
          spc = std::make_shared<printer::SygusNamedPrintCallback>(cnames[i]);
        }
        else if (isDefinedFunction(ops[i]))
        {
          Debug("parser-sygus") << "--> Defined function " << ops[i]
                                << std::endl;
          // turn f into (lammbda (x) (f x))
          // in a degenerate case, ops[i] may be a defined constant,
          // in which case we do not replace by a lambda.
          if (ops[i].getType().isFunction())
          {
            std::vector<Type> ftypes =
                static_cast<FunctionType>(ops[i].getType()).getArgTypes();
            std::vector<Expr> largs;
            Expr lbvl = makeSygusBoundVarList(dt, i, ftypes, largs);
            largs.insert(largs.begin(), ops[i]);
            Expr body = getExprManager()->mkExpr(kind::APPLY_UF, largs);
            ops[i] = getExprManager()->mkExpr(kind::LAMBDA, lbvl, body);
            Debug("parser-sygus") << "  ...replace op : " << ops[i]
                                  << std::endl;
          }
          else
          {
            Debug("parser-sygus") << "  ...replace op : " << ops[i]
                                  << std::endl;
          }
          // keep a callback to say it should be printed with the defined name
          spc = std::make_shared<printer::SygusNamedPrintCallback>(cnames[i]);
        }
        else
        {
          Debug("parser-sygus") << "--> Default case " << ops[i] << std::endl;
        }
      }
      // must rename to avoid duplication
      std::stringstream ss;
      ss << dt.getName() << "_" << i << "_" << cnames[i];
      cnames[i] = ss.str();
      Debug("parser-sygus") << "  construct the datatype " << cnames[i] << "..."
                            << std::endl;
      // add the sygus constructor
      dt.addSygusConstructor(ops[i], cnames[i], cargs[i], spc);
      Debug("parser-sygus") << "  finished constructing the datatype"
                            << std::endl;
    }
  }

  Debug("parser-sygus") << "  add constructors for unresolved symbols..." << std::endl;
  if( !unresolved_gterm_sym.empty() ){
    std::vector< Type > types;
    Debug("parser-sygus") << "...resolve " << unresolved_gterm_sym.size() << " symbols..." << std::endl;
    for( unsigned i=0; i<unresolved_gterm_sym.size(); i++ ){
      Debug("parser-sygus") << "  resolve : " << unresolved_gterm_sym[i] << std::endl;
      if( isUnresolvedType(unresolved_gterm_sym[i]) ){
        Debug("parser-sygus") << "    it is an unresolved type." << std::endl;
        Type t = getSort(unresolved_gterm_sym[i]);
        if( std::find( types.begin(), types.end(), t )==types.end() ){
          types.push_back( t );
          //identity element
          Type bt = dt.getSygusType();
          Debug("parser-sygus") << ":  make identity function for " << bt << ", argument type " << t << std::endl;

          std::stringstream ss;
          ss << t << "_x";
          Expr var = mkBoundVar(ss.str(), bt);
          std::vector<Expr> lchildren;
          lchildren.push_back(
              getExprManager()->mkExpr(kind::BOUND_VAR_LIST, var));
          lchildren.push_back(var);
          Expr id_op = getExprManager()->mkExpr(kind::LAMBDA, lchildren);

          // empty sygus callback (should not be printed)
          std::shared_ptr<SygusPrintCallback> sepc =
              std::make_shared<printer::SygusEmptyPrintCallback>();

          //make the sygus argument list
          std::vector< Type > id_carg;
          id_carg.push_back( t );
          dt.addSygusConstructor(id_op, unresolved_gterm_sym[i], id_carg, sepc);

          //add to operators
          ops.push_back( id_op );
        }
      }else{
        Debug("parser-sygus") << "    ignore. (likely a free let variable)" << std::endl;
      }
    }
  }
}

Expr Smt2::makeSygusBoundVarList(Datatype& dt,
                                 unsigned i,
                                 const std::vector<Type>& ltypes,
                                 std::vector<Expr>& lvars)
{
  for (unsigned j = 0, size = ltypes.size(); j < size; j++)
  {
    std::stringstream ss;
    ss << dt.getName() << "_x_" << i << "_" << j;
    Expr v = mkBoundVar(ss.str(), ltypes[j]);
    lvars.push_back(v);
  }
  return getExprManager()->mkExpr(kind::BOUND_VAR_LIST, lvars);
}

void Smt2::addSygusConstructorTerm(Datatype& dt,
                                   Expr term,
                                   std::map<Expr, Type>& ntsToUnres) const
{
  Trace("parser-sygus2") << "Add sygus cons term " << term << std::endl;
  // purify each occurrence of a non-terminal symbol in term, replace by
  // free variables. These become arguments to constructors. Notice we must do
  // a tree traversal in this function, since unique paths to the same term
  // should be treated as distinct terms.
  // Notice that let expressions are forbidden in the input syntax of term, so
  // this does not lead to exponential behavior with respect to input size.
  std::vector<Expr> args;
  std::vector<Type> cargs;
  Expr op = purifySygusGTerm(term, ntsToUnres, args, cargs);
  Trace("parser-sygus2") << "Purified operator " << op
                         << ", #args/cargs=" << args.size() << "/"
                         << cargs.size() << std::endl;
  std::shared_ptr<SygusPrintCallback> spc;
  // callback prints as the expression
  spc = std::make_shared<printer::SygusExprPrintCallback>(op, args);
  if (!args.empty())
  {
    bool pureVar = false;
    if (op.getNumChildren() == args.size())
    {
      pureVar = true;
      for (unsigned i = 0, nchild = op.getNumChildren(); i < nchild; i++)
      {
        if (op[i] != args[i])
        {
          pureVar = false;
          break;
        }
      }
    }
    Trace("parser-sygus2") << "Pure var is " << pureVar
                           << ", hasOp=" << op.hasOperator() << std::endl;
    if (pureVar && op.hasOperator())
    {
      // optimization: use just the operator if it an application to only vars
      op = op.getOperator();
    }
    else
    {
      Expr lbvl = getExprManager()->mkExpr(kind::BOUND_VAR_LIST, args);
      // its operator is a lambda
      op = getExprManager()->mkExpr(kind::LAMBDA, lbvl, op);
    }
  }
  Trace("parser-sygus2") << "Generated operator " << op << std::endl;
  std::stringstream ss;
  ss << op.getKind();
  dt.addSygusConstructor(op, ss.str(), cargs, spc);
}

Expr Smt2::purifySygusGTerm(Expr term,
                            std::map<Expr, Type>& ntsToUnres,
                            std::vector<Expr>& args,
                            std::vector<Type>& cargs) const
{
  Trace("parser-sygus2-debug")
      << "purifySygusGTerm: " << term << " #nchild=" << term.getNumChildren()
      << std::endl;
  std::map<Expr, Type>::iterator itn = ntsToUnres.find(term);
  if (itn != ntsToUnres.end())
  {
    Expr ret = getExprManager()->mkBoundVar(term.getType());
    Trace("parser-sygus2-debug")
        << "...unresolved non-terminal, intro " << ret << std::endl;
    args.push_back(ret);
    cargs.push_back(itn->second);
    return ret;
  }
  std::vector<Expr> pchildren;
  // To test whether the operator should be passed to mkExpr below, we check
  // whether this term has an operator which is not constant. This includes
  // APPLY_UF terms, but excludes applications of interpreted symbols.
  if (term.hasOperator() && !term.getOperator().isConst())
  {
    pchildren.push_back(term.getOperator());
  }
  bool childChanged = false;
  for (unsigned i = 0, nchild = term.getNumChildren(); i < nchild; i++)
  {
    Trace("parser-sygus2-debug")
        << "......purify child " << i << " : " << term[i] << std::endl;
    Expr ptermc = purifySygusGTerm(term[i], ntsToUnres, args, cargs);
    pchildren.push_back(ptermc);
    childChanged = childChanged || ptermc != term[i];
  }
  if (!childChanged)
  {
    Trace("parser-sygus2-debug") << "...no child changed" << std::endl;
    return term;
  }
  Expr nret = getExprManager()->mkExpr(term.getKind(), pchildren);
  Trace("parser-sygus2-debug")
      << "...child changed, return " << nret << std::endl;
  return nret;
}

void Smt2::addSygusConstructorVariables(Datatype& dt,
                                        std::vector<Expr>& sygusVars,
                                        Type type) const
{
  // each variable of appropriate type becomes a sygus constructor in dt.
  for (unsigned i = 0, size = sygusVars.size(); i < size; i++)
  {
    Expr v = sygusVars[i];
    if (v.getType() == type)
    {
      std::stringstream ss;
      ss << v;
      std::vector<CVC4::Type> cargs;
      dt.addSygusConstructor(v, ss.str(), cargs);
    }
  }
}

InputLanguage Smt2::getLanguage() const
{
  ExprManager* em = getExprManager();
  return em->getOptions().getInputLanguage();
}

}  // namespace parser
}/* CVC4 namespace */

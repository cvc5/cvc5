/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definitions of SMT2 constants.
 */
#include "parser/smt2/smt2.h"

#include <algorithm>

#include "base/check.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"
#include "parser/smt2/smt2_input.h"

// ANTLR defines these, which is really bad!
#undef true
#undef false
// ANTLR pulls in arpa/nameser_compat.h which defines this (again, bad!)
#undef ADD

namespace cvc5 {
namespace parser {

Smt2::Smt2(cvc5::Solver* solver,
           SymbolManager* sm,
           bool strictMode,
           bool parseOnly)
    : Parser(solver, sm, strictMode, parseOnly),
      d_logicSet(false),
      d_seenSetLogic(false)
{
}

Smt2::~Smt2() {}

void Smt2::addArithmeticOperators() {
  addOperator(cvc5::ADD, "+");
  addOperator(cvc5::SUB, "-");
  // cvc5::SUB is converted to cvc5::NEG if there is only a single operand
  Parser::addOperator(cvc5::NEG);
  addOperator(cvc5::MULT, "*");
  addOperator(cvc5::LT, "<");
  addOperator(cvc5::LEQ, "<=");
  addOperator(cvc5::GT, ">");
  addOperator(cvc5::GEQ, ">=");

  if (!strictModeEnabled())
  {
    // NOTE: this operator is non-standard
    addOperator(cvc5::POW, "^");
  }
}

void Smt2::addTranscendentalOperators()
{
  addOperator(cvc5::EXPONENTIAL, "exp");
  addOperator(cvc5::SINE, "sin");
  addOperator(cvc5::COSINE, "cos");
  addOperator(cvc5::TANGENT, "tan");
  addOperator(cvc5::COSECANT, "csc");
  addOperator(cvc5::SECANT, "sec");
  addOperator(cvc5::COTANGENT, "cot");
  addOperator(cvc5::ARCSINE, "arcsin");
  addOperator(cvc5::ARCCOSINE, "arccos");
  addOperator(cvc5::ARCTANGENT, "arctan");
  addOperator(cvc5::ARCCOSECANT, "arccsc");
  addOperator(cvc5::ARCSECANT, "arcsec");
  addOperator(cvc5::ARCCOTANGENT, "arccot");
  addOperator(cvc5::SQRT, "sqrt");
}

void Smt2::addQuantifiersOperators()
{
}

void Smt2::addBitvectorOperators() {
  addOperator(cvc5::BITVECTOR_CONCAT, "concat");
  addOperator(cvc5::BITVECTOR_NOT, "bvnot");
  addOperator(cvc5::BITVECTOR_AND, "bvand");
  addOperator(cvc5::BITVECTOR_OR, "bvor");
  addOperator(cvc5::BITVECTOR_NEG, "bvneg");
  addOperator(cvc5::BITVECTOR_ADD, "bvadd");
  addOperator(cvc5::BITVECTOR_MULT, "bvmul");
  addOperator(cvc5::BITVECTOR_UDIV, "bvudiv");
  addOperator(cvc5::BITVECTOR_UREM, "bvurem");
  addOperator(cvc5::BITVECTOR_SHL, "bvshl");
  addOperator(cvc5::BITVECTOR_LSHR, "bvlshr");
  addOperator(cvc5::BITVECTOR_ULT, "bvult");
  addOperator(cvc5::BITVECTOR_NAND, "bvnand");
  addOperator(cvc5::BITVECTOR_NOR, "bvnor");
  addOperator(cvc5::BITVECTOR_XOR, "bvxor");
  addOperator(cvc5::BITVECTOR_XNOR, "bvxnor");
  addOperator(cvc5::BITVECTOR_COMP, "bvcomp");
  addOperator(cvc5::BITVECTOR_SUB, "bvsub");
  addOperator(cvc5::BITVECTOR_SDIV, "bvsdiv");
  addOperator(cvc5::BITVECTOR_SREM, "bvsrem");
  addOperator(cvc5::BITVECTOR_SMOD, "bvsmod");
  addOperator(cvc5::BITVECTOR_ASHR, "bvashr");
  addOperator(cvc5::BITVECTOR_ULE, "bvule");
  addOperator(cvc5::BITVECTOR_UGT, "bvugt");
  addOperator(cvc5::BITVECTOR_UGE, "bvuge");
  addOperator(cvc5::BITVECTOR_SLT, "bvslt");
  addOperator(cvc5::BITVECTOR_SLE, "bvsle");
  addOperator(cvc5::BITVECTOR_SGT, "bvsgt");
  addOperator(cvc5::BITVECTOR_SGE, "bvsge");
  addOperator(cvc5::BITVECTOR_REDOR, "bvredor");
  addOperator(cvc5::BITVECTOR_REDAND, "bvredand");

  addIndexedOperator(cvc5::BITVECTOR_EXTRACT, "extract");
  addIndexedOperator(cvc5::BITVECTOR_REPEAT, "repeat");
  addIndexedOperator(cvc5::BITVECTOR_ZERO_EXTEND, "zero_extend");
  addIndexedOperator(cvc5::BITVECTOR_SIGN_EXTEND, "sign_extend");
  addIndexedOperator(cvc5::BITVECTOR_ROTATE_LEFT, "rotate_left");
  addIndexedOperator(cvc5::BITVECTOR_ROTATE_RIGHT, "rotate_right");
}

void Smt2::addDatatypesOperators()
{
  Parser::addOperator(cvc5::APPLY_CONSTRUCTOR);
  Parser::addOperator(cvc5::APPLY_TESTER);
  Parser::addOperator(cvc5::APPLY_SELECTOR);

  if (!strictModeEnabled())
  {
    Parser::addOperator(cvc5::APPLY_UPDATER);
    // Notice that tuple operators, we use the generic APPLY_SELECTOR and
    // APPLY_UPDATER kinds. These are processed based on the context
    // in which they are parsed, e.g. when parsing identifiers.
    addIndexedOperator(cvc5::APPLY_SELECTOR, "tuple.select");
    addIndexedOperator(cvc5::APPLY_UPDATER, "tuple.update");
  }
}

void Smt2::addStringOperators() {
  defineVar("re.all", getSolver()->mkRegexpAll());
  addOperator(cvc5::STRING_CONCAT, "str.++");
  addOperator(cvc5::STRING_LENGTH, "str.len");
  addOperator(cvc5::STRING_SUBSTR, "str.substr");
  addOperator(cvc5::STRING_CONTAINS, "str.contains");
  addOperator(cvc5::STRING_CHARAT, "str.at");
  addOperator(cvc5::STRING_INDEXOF, "str.indexof");
  addOperator(cvc5::STRING_REPLACE, "str.replace");
  addOperator(cvc5::STRING_PREFIX, "str.prefixof");
  addOperator(cvc5::STRING_SUFFIX, "str.suffixof");
  addOperator(cvc5::STRING_FROM_CODE, "str.from_code");
  addOperator(cvc5::STRING_IS_DIGIT, "str.is_digit");
  addOperator(cvc5::STRING_REPLACE_RE, "str.replace_re");
  addOperator(cvc5::STRING_REPLACE_RE_ALL, "str.replace_re_all");
  if (!strictModeEnabled())
  {
    addOperator(cvc5::STRING_INDEXOF_RE, "str.indexof_re");
    addOperator(cvc5::STRING_UPDATE, "str.update");
    addOperator(cvc5::STRING_TO_LOWER, "str.to_lower");
    addOperator(cvc5::STRING_TO_UPPER, "str.to_upper");
    addOperator(cvc5::STRING_REV, "str.rev");
    // sequence versions
    addOperator(cvc5::SEQ_CONCAT, "seq.++");
    addOperator(cvc5::SEQ_LENGTH, "seq.len");
    addOperator(cvc5::SEQ_EXTRACT, "seq.extract");
    addOperator(cvc5::SEQ_UPDATE, "seq.update");
    addOperator(cvc5::SEQ_AT, "seq.at");
    addOperator(cvc5::SEQ_CONTAINS, "seq.contains");
    addOperator(cvc5::SEQ_INDEXOF, "seq.indexof");
    addOperator(cvc5::SEQ_REPLACE, "seq.replace");
    addOperator(cvc5::SEQ_PREFIX, "seq.prefixof");
    addOperator(cvc5::SEQ_SUFFIX, "seq.suffixof");
    addOperator(cvc5::SEQ_REV, "seq.rev");
    addOperator(cvc5::SEQ_REPLACE_ALL, "seq.replace_all");
    addOperator(cvc5::SEQ_UNIT, "seq.unit");
    addOperator(cvc5::SEQ_NTH, "seq.nth");
  }
  addOperator(cvc5::STRING_FROM_INT, "str.from_int");
  addOperator(cvc5::STRING_TO_INT, "str.to_int");
  addOperator(cvc5::STRING_IN_REGEXP, "str.in_re");
  addOperator(cvc5::STRING_TO_REGEXP, "str.to_re");
  addOperator(cvc5::STRING_TO_CODE, "str.to_code");
  addOperator(cvc5::STRING_REPLACE_ALL, "str.replace_all");

  addOperator(cvc5::REGEXP_CONCAT, "re.++");
  addOperator(cvc5::REGEXP_UNION, "re.union");
  addOperator(cvc5::REGEXP_INTER, "re.inter");
  addOperator(cvc5::REGEXP_STAR, "re.*");
  addOperator(cvc5::REGEXP_PLUS, "re.+");
  addOperator(cvc5::REGEXP_OPT, "re.opt");
  addIndexedOperator(cvc5::REGEXP_REPEAT, "re.^");
  addIndexedOperator(cvc5::REGEXP_LOOP, "re.loop");
  addOperator(cvc5::REGEXP_RANGE, "re.range");
  addOperator(cvc5::REGEXP_COMPLEMENT, "re.comp");
  addOperator(cvc5::REGEXP_DIFF, "re.diff");
  addOperator(cvc5::STRING_LT, "str.<");
  addOperator(cvc5::STRING_LEQ, "str.<=");
}

void Smt2::addFloatingPointOperators() {
  addOperator(cvc5::FLOATINGPOINT_FP, "fp");
  addOperator(cvc5::FLOATINGPOINT_EQ, "fp.eq");
  addOperator(cvc5::FLOATINGPOINT_ABS, "fp.abs");
  addOperator(cvc5::FLOATINGPOINT_NEG, "fp.neg");
  addOperator(cvc5::FLOATINGPOINT_ADD, "fp.add");
  addOperator(cvc5::FLOATINGPOINT_SUB, "fp.sub");
  addOperator(cvc5::FLOATINGPOINT_MULT, "fp.mul");
  addOperator(cvc5::FLOATINGPOINT_DIV, "fp.div");
  addOperator(cvc5::FLOATINGPOINT_FMA, "fp.fma");
  addOperator(cvc5::FLOATINGPOINT_SQRT, "fp.sqrt");
  addOperator(cvc5::FLOATINGPOINT_REM, "fp.rem");
  addOperator(cvc5::FLOATINGPOINT_RTI, "fp.roundToIntegral");
  addOperator(cvc5::FLOATINGPOINT_MIN, "fp.min");
  addOperator(cvc5::FLOATINGPOINT_MAX, "fp.max");
  addOperator(cvc5::FLOATINGPOINT_LEQ, "fp.leq");
  addOperator(cvc5::FLOATINGPOINT_LT, "fp.lt");
  addOperator(cvc5::FLOATINGPOINT_GEQ, "fp.geq");
  addOperator(cvc5::FLOATINGPOINT_GT, "fp.gt");
  addOperator(cvc5::FLOATINGPOINT_IS_NORMAL, "fp.isNormal");
  addOperator(cvc5::FLOATINGPOINT_IS_SUBNORMAL, "fp.isSubnormal");
  addOperator(cvc5::FLOATINGPOINT_IS_ZERO, "fp.isZero");
  addOperator(cvc5::FLOATINGPOINT_IS_INF, "fp.isInfinite");
  addOperator(cvc5::FLOATINGPOINT_IS_NAN, "fp.isNaN");
  addOperator(cvc5::FLOATINGPOINT_IS_NEG, "fp.isNegative");
  addOperator(cvc5::FLOATINGPOINT_IS_POS, "fp.isPositive");
  addOperator(cvc5::FLOATINGPOINT_TO_REAL, "fp.to_real");

  addIndexedOperator(cvc5::UNDEFINED_KIND, "to_fp");
  addIndexedOperator(cvc5::FLOATINGPOINT_TO_FP_FROM_UBV, "to_fp_unsigned");
  addIndexedOperator(cvc5::FLOATINGPOINT_TO_UBV, "fp.to_ubv");
  addIndexedOperator(cvc5::FLOATINGPOINT_TO_SBV, "fp.to_sbv");

  if (!strictModeEnabled())
  {
    addIndexedOperator(cvc5::FLOATINGPOINT_TO_FP_FROM_IEEE_BV, "to_fp_bv");
    addIndexedOperator(cvc5::FLOATINGPOINT_TO_FP_FROM_FP, "to_fp_fp");
    addIndexedOperator(cvc5::FLOATINGPOINT_TO_FP_FROM_REAL, "to_fp_real");
    addIndexedOperator(cvc5::FLOATINGPOINT_TO_FP_FROM_SBV, "to_fp_signed");
  }
}

void Smt2::addSepOperators() {
  defineVar("sep.emp", d_solver->mkSepEmp());
  // the Boolean sort is a placeholder here since we don't have type info
  // without type annotation
  defineVar("sep.nil", d_solver->mkSepNil(d_solver->getBooleanSort()));
  addOperator(cvc5::SEP_STAR, "sep");
  addOperator(cvc5::SEP_PTO, "pto");
  addOperator(cvc5::SEP_WAND, "wand");
  Parser::addOperator(cvc5::SEP_STAR);
  Parser::addOperator(cvc5::SEP_PTO);
  Parser::addOperator(cvc5::SEP_WAND);
}

void Smt2::addCoreSymbols()
{
  defineType("Bool", d_solver->getBooleanSort(), true);
  defineVar("true", d_solver->mkTrue(), true);
  defineVar("false", d_solver->mkFalse(), true);
  addOperator(cvc5::AND, "and");
  addOperator(cvc5::DISTINCT, "distinct");
  addOperator(cvc5::EQUAL, "=");
  addOperator(cvc5::IMPLIES, "=>");
  addOperator(cvc5::ITE, "ite");
  addOperator(cvc5::NOT, "not");
  addOperator(cvc5::OR, "or");
  addOperator(cvc5::XOR, "xor");
}

void Smt2::addOperator(cvc5::Kind kind, const std::string& name)
{
  Trace("parser") << "Smt2::addOperator( " << kind << ", " << name << " )"
                  << std::endl;
  Parser::addOperator(kind);
  d_operatorKindMap[name] = kind;
}

void Smt2::addIndexedOperator(cvc5::Kind tKind, const std::string& name)
{
  Parser::addOperator(tKind);
  d_indexedOpKindMap[name] = tKind;
}

bool Smt2::isIndexedOperatorEnabled(const std::string& name) const
{
  return d_indexedOpKindMap.find(name) != d_indexedOpKindMap.end();
}

cvc5::Kind Smt2::getOperatorKind(const std::string& name) const
{
  // precondition: isOperatorEnabled(name)
  return d_operatorKindMap.find(name)->second;
}

bool Smt2::isOperatorEnabled(const std::string& name) const {
  return d_operatorKindMap.find(name) != d_operatorKindMap.end();
}

modes::BlockModelsMode Smt2::getBlockModelsMode(const std::string& mode)
{
  if (mode == "literals")
  {
    return modes::BlockModelsMode::LITERALS;
  }
  else if (mode == "values")
  {
    return modes::BlockModelsMode::VALUES;
  }
  parseError(std::string("Unknown block models mode `") + mode + "'");
  return modes::BlockModelsMode::LITERALS;
}

bool Smt2::isTheoryEnabled(internal::theory::TheoryId theory) const
{
  return d_logic.isTheoryEnabled(theory);
}

bool Smt2::isHoEnabled() const { return d_logic.isHigherOrder(); }

bool Smt2::hasCardinalityConstraints() const { return d_logic.hasCardinalityConstraints(); }

bool Smt2::logicIsSet() {
  return d_logicSet;
}

bool Smt2::getTesterName(cvc5::Term cons, std::string& name)
{
  if ((v2_6() || sygus()) && strictModeEnabled())
  {
    // 2.6 or above uses indexed tester symbols, if we are in strict mode,
    // we do not automatically define is-cons for constructor cons.
    return false;
  }
  std::stringstream ss;
  ss << "is-" << cons;
  name = ss.str();
  return true;
}

cvc5::Term Smt2::mkIndexedConstant(const std::string& name,
                                   const std::vector<uint32_t>& numerals)
{
  if (d_logic.isTheoryEnabled(internal::theory::THEORY_FP))
  {
    if (name == "+oo")
    {
      return d_solver->mkFloatingPointPosInf(numerals[0], numerals[1]);
    }
    else if (name == "-oo")
    {
      return d_solver->mkFloatingPointNegInf(numerals[0], numerals[1]);
    }
    else if (name == "NaN")
    {
      return d_solver->mkFloatingPointNaN(numerals[0], numerals[1]);
    }
    else if (name == "+zero")
    {
      return d_solver->mkFloatingPointPosZero(numerals[0], numerals[1]);
    }
    else if (name == "-zero")
    {
      return d_solver->mkFloatingPointNegZero(numerals[0], numerals[1]);
    }
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_BV)
      && name.find("bv") == 0)
  {
    std::string bvStr = name.substr(2);
    return d_solver->mkBitVector(numerals[0], bvStr, 10);
  }

  // NOTE: Theory parametric constants go here

  parseError(std::string("Unknown indexed literal `") + name + "'");
  return cvc5::Term();
}

cvc5::Kind Smt2::getIndexedOpKind(const std::string& name)
{
  const auto& kIt = d_indexedOpKindMap.find(name);
  if (kIt != d_indexedOpKindMap.end())
  {
    return (*kIt).second;
  }
  parseError(std::string("Unknown indexed function `") + name + "'");
  return cvc5::UNDEFINED_KIND;
}

cvc5::Term Smt2::bindDefineFunRec(
    const std::string& fname,
    const std::vector<std::pair<std::string, cvc5::Sort>>& sortedVarNames,
    cvc5::Sort t,
    std::vector<cvc5::Term>& flattenVars)
{
  std::vector<cvc5::Sort> sorts;
  for (const std::pair<std::string, cvc5::Sort>& svn : sortedVarNames)
  {
    sorts.push_back(svn.second);
  }

  // make the flattened function type, add bound variables
  // to flattenVars if the defined function was given a function return type.
  cvc5::Sort ft = mkFlatFunctionType(sorts, t, flattenVars);

  // allow overloading
  return bindVar(fname, ft, true);
}

void Smt2::pushDefineFunRecScope(
    const std::vector<std::pair<std::string, cvc5::Sort>>& sortedVarNames,
    cvc5::Term func,
    const std::vector<cvc5::Term>& flattenVars,
    std::vector<cvc5::Term>& bvs)
{
  pushScope();

  // bound variables are those that are explicitly named in the preamble
  // of the define-fun(s)-rec command, we define them here
  for (const std::pair<std::string, cvc5::Sort>& svn : sortedVarNames)
  {
    cvc5::Term v = bindBoundVar(svn.first, svn.second);
    bvs.push_back(v);
  }

  bvs.insert(bvs.end(), flattenVars.begin(), flattenVars.end());
}

void Smt2::reset() {
  d_logicSet = false;
  d_seenSetLogic = false;
  d_logic = internal::LogicInfo();
  d_operatorKindMap.clear();
  d_lastNamedTerm = std::pair<cvc5::Term, std::string>();
}

std::unique_ptr<Command> Smt2::invConstraint(
    const std::vector<std::string>& names)
{
  checkThatLogicIsSet();
  Trace("parser-sygus") << "Sygus : define sygus funs..." << std::endl;
  Trace("parser-sygus") << "Sygus : read inv-constraint..." << std::endl;

  if (names.size() != 4)
  {
    parseError(
        "Bad syntax for inv-constraint: expected 4 "
        "arguments.");
  }

  std::vector<cvc5::Term> terms;
  for (const std::string& name : names)
  {
    if (!isDeclared(name))
    {
      std::stringstream ss;
      ss << "Function " << name << " in inv-constraint is not defined.";
      parseError(ss.str());
    }

    terms.push_back(getVariable(name));
  }

  return std::unique_ptr<Command>(new SygusInvConstraintCommand(terms));
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

  d_logicSet = true;
  d_logic = name;

  // if sygus is enabled, we must enable UF, datatypes, and integer arithmetic
  if(sygus()) {
    if (!d_logic.isQuantified())
    {
      warning("Logics in sygus are assumed to contain quantifiers.");
      warning("Omit QF_ from the logic to avoid this warning.");
    }
  }

  // Core theory belongs to every logic
  addCoreSymbols();

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_UF))
  {
    Parser::addOperator(cvc5::APPLY_UF);
  }

  if (d_logic.isHigherOrder())
  {
    addOperator(cvc5::HO_APPLY, "@");
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_ARITH))
  {
    if(d_logic.areIntegersUsed()) {
      defineType("Int", d_solver->getIntegerSort(), true);
      addArithmeticOperators();
      if (!strictModeEnabled() || !d_logic.isLinear())
      {
        addOperator(cvc5::INTS_DIVISION, "div");
        addOperator(cvc5::INTS_MODULUS, "mod");
        addOperator(cvc5::ABS, "abs");
      }
      addIndexedOperator(cvc5::DIVISIBLE, "divisible");
    }

    if (d_logic.areRealsUsed())
    {
      defineType("Real", d_solver->getRealSort(), true);
      addArithmeticOperators();
      addOperator(cvc5::DIVISION, "/");
      if (!strictModeEnabled())
      {
        addOperator(cvc5::ABS, "abs");
      }
    }

    if (d_logic.areIntegersUsed() && d_logic.areRealsUsed())
    {
      addOperator(cvc5::TO_INTEGER, "to_int");
      addOperator(cvc5::IS_INTEGER, "is_int");
      addOperator(cvc5::TO_REAL, "to_real");
    }

    if (d_logic.areTranscendentalsUsed())
    {
      defineVar("real.pi", d_solver->mkPi());
      addTranscendentalOperators();
    }
    if (!strictModeEnabled())
    {
      // integer version of AND
      addIndexedOperator(cvc5::IAND, "iand");
      // pow2
      addOperator(cvc5::POW2, "int.pow2");
    }
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_ARRAYS))
  {
    addOperator(cvc5::SELECT, "select");
    addOperator(cvc5::STORE, "store");
    addOperator(cvc5::EQ_RANGE, "eqrange");
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_BV))
  {
    addBitvectorOperators();

    if (!strictModeEnabled()
        && d_logic.isTheoryEnabled(internal::theory::THEORY_ARITH)
        && d_logic.areIntegersUsed())
    {
      // Conversions between bit-vectors and integers
      addOperator(cvc5::BITVECTOR_TO_NAT, "bv2nat");
      addIndexedOperator(cvc5::INT_TO_BITVECTOR, "int2bv");
    }
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_DATATYPES))
  {
    const std::vector<cvc5::Sort> types;
    defineType("Tuple", d_solver->mkTupleSort(types), true);
    addDatatypesOperators();
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_SETS))
  {
    defineVar("set.empty", d_solver->mkEmptySet(d_solver->getNullSort()));
    // the Boolean sort is a placeholder here since we don't have type info
    // without type annotation
    defineVar("set.universe",
              d_solver->mkUniverseSet(d_solver->getBooleanSort()));

    addOperator(cvc5::SET_UNION, "set.union");
    addOperator(cvc5::SET_INTER, "set.inter");
    addOperator(cvc5::SET_MINUS, "set.minus");
    addOperator(cvc5::SET_SUBSET, "set.subset");
    addOperator(cvc5::SET_MEMBER, "set.member");
    addOperator(cvc5::SET_SINGLETON, "set.singleton");
    addOperator(cvc5::SET_INSERT, "set.insert");
    addOperator(cvc5::SET_CARD, "set.card");
    addOperator(cvc5::SET_COMPLEMENT, "set.complement");
    addOperator(cvc5::SET_CHOOSE, "set.choose");
    addOperator(cvc5::SET_IS_SINGLETON, "set.is_singleton");
    addOperator(cvc5::SET_MAP, "set.map");
    addOperator(cvc5::RELATION_JOIN, "rel.join");
    addOperator(cvc5::RELATION_PRODUCT, "rel.product");
    addOperator(cvc5::RELATION_TRANSPOSE, "rel.transpose");
    addOperator(cvc5::RELATION_TCLOSURE, "rel.tclosure");
    addOperator(cvc5::RELATION_JOIN_IMAGE, "rel.join_image");
    addOperator(cvc5::RELATION_IDEN, "rel.iden");
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_BAGS))
  {
    defineVar("bag.empty", d_solver->mkEmptyBag(d_solver->getNullSort()));
    addOperator(cvc5::BAG_UNION_MAX, "bag.union_max");
    addOperator(cvc5::BAG_UNION_DISJOINT, "bag.union_disjoint");
    addOperator(cvc5::BAG_INTER_MIN, "bag.inter_min");
    addOperator(cvc5::BAG_DIFFERENCE_SUBTRACT, "bag.difference_subtract");
    addOperator(cvc5::BAG_DIFFERENCE_REMOVE, "bag.difference_remove");
    addOperator(cvc5::BAG_SUBBAG, "bag.subbag");
    addOperator(cvc5::BAG_COUNT, "bag.count");
    addOperator(cvc5::BAG_MEMBER, "bag.member");
    addOperator(cvc5::BAG_DUPLICATE_REMOVAL, "bag.duplicate_removal");
    addOperator(cvc5::BAG_MAKE, "bag");
    addOperator(cvc5::BAG_CARD, "bag.card");
    addOperator(cvc5::BAG_CHOOSE, "bag.choose");
    addOperator(cvc5::BAG_IS_SINGLETON, "bag.is_singleton");
    addOperator(cvc5::BAG_FROM_SET, "bag.from_set");
    addOperator(cvc5::BAG_TO_SET, "bag.to_set");
    addOperator(cvc5::BAG_MAP, "bag.map");
    addOperator(cvc5::BAG_FILTER, "bag.filter");
    addOperator(cvc5::BAG_FOLD, "bag.fold");
    addOperator(cvc5::TABLE_PRODUCT, "table.product");
  }
  if (d_logic.isTheoryEnabled(internal::theory::THEORY_STRINGS))
  {
    defineType("String", d_solver->getStringSort(), true);
    defineType("RegLan", d_solver->getRegExpSort(), true);
    defineType("Int", d_solver->getIntegerSort(), true);

    defineVar("re.none", d_solver->mkRegexpNone());
    defineVar("re.allchar", d_solver->mkRegexpAllchar());

    // Boolean is a placeholder
    defineVar("seq.empty",
              d_solver->mkEmptySequence(d_solver->getBooleanSort()));

    addStringOperators();
  }

  if(d_logic.isQuantified()) {
    addQuantifiersOperators();
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_FP))
  {
    defineType("RoundingMode", d_solver->getRoundingModeSort(), true);
    defineType("Float16", d_solver->mkFloatingPointSort(5, 11), true);
    defineType("Float32", d_solver->mkFloatingPointSort(8, 24), true);
    defineType("Float64", d_solver->mkFloatingPointSort(11, 53), true);
    defineType("Float128", d_solver->mkFloatingPointSort(15, 113), true);

    defineVar("RNE",
              d_solver->mkRoundingMode(cvc5::ROUND_NEAREST_TIES_TO_EVEN));
    defineVar("roundNearestTiesToEven",
              d_solver->mkRoundingMode(cvc5::ROUND_NEAREST_TIES_TO_EVEN));
    defineVar("RNA",
              d_solver->mkRoundingMode(cvc5::ROUND_NEAREST_TIES_TO_AWAY));
    defineVar("roundNearestTiesToAway",
              d_solver->mkRoundingMode(cvc5::ROUND_NEAREST_TIES_TO_AWAY));
    defineVar("RTP", d_solver->mkRoundingMode(cvc5::ROUND_TOWARD_POSITIVE));
    defineVar("roundTowardPositive",
              d_solver->mkRoundingMode(cvc5::ROUND_TOWARD_POSITIVE));
    defineVar("RTN", d_solver->mkRoundingMode(cvc5::ROUND_TOWARD_NEGATIVE));
    defineVar("roundTowardNegative",
              d_solver->mkRoundingMode(cvc5::ROUND_TOWARD_NEGATIVE));
    defineVar("RTZ", d_solver->mkRoundingMode(cvc5::ROUND_TOWARD_ZERO));
    defineVar("roundTowardZero",
              d_solver->mkRoundingMode(cvc5::ROUND_TOWARD_ZERO));

    addFloatingPointOperators();
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_SEP))
  {
    addSepOperators();
  }

  // builtin symbols of the logic are declared at context level zero, hence
  // we push the outermost scope here
  pushScope(true);

  std::string logic = sygus() ? d_logic.getLogicString() : name;
  if (!fromCommand)
  {
    // If not from a command, just set the logic directly. Notice this is
    // important since we do not want to enqueue a set-logic command and
    // fully initialize the underlying SolverEngine in the meantime before the
    // command has a chance to execute, which would lead to an error.
    d_solver->setLogic(logic);
    return nullptr;
  }
  Command* cmd = new SetBenchmarkLogicCommand(logic);
  return cmd;
} /* Smt2::setLogic() */

cvc5::Grammar* Smt2::mkGrammar(const std::vector<cvc5::Term>& boundVars,
                               const std::vector<cvc5::Term>& ntSymbols)
{
  d_allocGrammars.emplace_back(
      new cvc5::Grammar(d_solver->mkGrammar(boundVars, ntSymbols)));
  return d_allocGrammars.back().get();
}

bool Smt2::sygus() const
{
  return d_solver->getOption("input-language") == "LANG_SYGUS_V2";
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
      // the calls to setLogic below set the logic on the solver directly
      if (logicIsForced())
      {
        setLogic(getForcedLogic(), false);
      }
      else
      {
        warning("No set-logic command was given before this point.");
        warning("cvc5 will make all theories available.");
        warning(
            "Consider setting a stricter logic for (likely) better "
            "performance.");
        warning("To suppress this warning in the future use (set-logic ALL).");

        setLogic("ALL", false);
      }
    }
  }
}

void Smt2::checkLogicAllowsFreeSorts()
{
  if (!d_logic.isTheoryEnabled(internal::theory::THEORY_UF)
      && !d_logic.isTheoryEnabled(internal::theory::THEORY_ARRAYS)
      && !d_logic.isTheoryEnabled(internal::theory::THEORY_DATATYPES)
      && !d_logic.isTheoryEnabled(internal::theory::THEORY_SETS)
      && !d_logic.isTheoryEnabled(internal::theory::THEORY_BAGS))
  {
    parseErrorLogic("Free sort symbols not allowed in ");
  }
}

void Smt2::checkLogicAllowsFunctions()
{
  if (!d_logic.isTheoryEnabled(internal::theory::THEORY_UF) && !isHoEnabled())
  {
    parseError(
        "Functions (of non-zero arity) cannot "
        "be declared in logic "
        + d_logic.getLogicString()
        + ". Try including UF or adding the prefix HO_.");
  }
}

/* The include are managed in the lexer but called in the parser */
// Inspired by http://www.antlr3.org/api/C/interop.html

static bool newInputStream(const std::string& filename, pANTLR3_LEXER lexer) {
  Trace("parser") << "Including " << filename << std::endl;
  // Create a new input stream and take advantage of built in stream stacking
  // in C target runtime.
  //
  pANTLR3_INPUT_STREAM    in;
#ifdef CVC5_ANTLR3_OLD_INPUT_STREAM
  in = antlr3AsciiFileStreamNew((pANTLR3_UINT8) filename.c_str());
#else  /* CVC5_ANTLR3_OLD_INPUT_STREAM */
  in = antlr3FileStreamNew((pANTLR3_UINT8) filename.c_str(), ANTLR3_ENC_8BIT);
#endif /* CVC5_ANTLR3_OLD_INPUT_STREAM */
  if( in == NULL ) {
    Trace("parser") << "Can't open " << filename << std::endl;
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
bool Smt2::isAbstractValue(const std::string& name)
{
  return name.length() >= 2 && name[0] == '@' && name[1] != '0'
         && name.find_first_not_of("0123456789", 1) == std::string::npos;
}

void Smt2::parseOpApplyTypeAscription(ParseOp& p, cvc5::Sort type)
{
  Trace("parser") << "parseOpApplyTypeAscription : " << p << " " << type
                  << std::endl;
  // (as const (Array T1 T2))
  if (p.d_kind == cvc5::CONST_ARRAY)
  {
    if (!type.isArray())
    {
      std::stringstream ss;
      ss << "expected array constant term, but cast is not of array type"
         << std::endl
         << "cast type: " << type;
      parseError(ss.str());
    }
    p.d_type = type;
    return;
  }
  if (p.d_expr.isNull())
  {
    Trace("parser-overloading")
        << "Getting variable expression with name " << p.d_name << " and type "
        << type << std::endl;
    // get the variable expression for the type
    if (isDeclared(p.d_name, SYM_VARIABLE))
    {
      p.d_expr = getExpressionForNameAndType(p.d_name, type);
      p.d_name = std::string("");
    }
    if (p.d_expr.isNull())
    {
      std::stringstream ss;
      ss << "Could not resolve expression with name " << p.d_name
         << " and type " << type << std::endl;
      parseError(ss.str());
    }
  }
  Trace("parser-qid") << "Resolve ascription " << type << " on " << p.d_expr;
  Trace("parser-qid") << " " << p.d_expr.getKind() << " " << p.d_expr.getSort();
  Trace("parser-qid") << std::endl;
  // otherwise, we process the type ascription
  p.d_expr = applyTypeAscription(p.d_expr, type);
}

cvc5::Term Smt2::parseOpToExpr(ParseOp& p)
{
  Trace("parser") << "parseOpToExpr: " << p << std::endl;
  cvc5::Term expr;
  if (p.d_kind != cvc5::NULL_TERM || !p.d_type.isNull())
  {
    parseError(
        "Bad syntax for qualified identifier operator in term position.");
  }
  else if (!p.d_expr.isNull())
  {
    expr = p.d_expr;
  }
  else if (!isDeclared(p.d_name, SYM_VARIABLE))
  {
    std::stringstream ss;
    ss << "Symbol " << p.d_name << " is not declared.";
    parseError(ss.str());
  }
  else
  {
    expr = getExpressionForName(p.d_name);
  }
  Assert(!expr.isNull());
  return expr;
}

cvc5::Term Smt2::applyParseOp(ParseOp& p, std::vector<cvc5::Term>& args)
{
  bool isBuiltinOperator = false;
  // the builtin kind of the overall return expression
  cvc5::Kind kind = cvc5::NULL_TERM;
  // First phase: process the operator
  if (TraceIsOn("parser"))
  {
    Trace("parser") << "applyParseOp: " << p << " to:" << std::endl;
    for (std::vector<cvc5::Term>::iterator i = args.begin(); i != args.end();
         ++i)
    {
      Trace("parser") << "++ " << *i << std::endl;
    }
  }
  cvc5::Op op;
  if (p.d_kind == cvc5::UNDEFINED_KIND && isIndexedOperatorEnabled(p.d_name))
  {
    // Resolve indexed symbols that cannot be resolved without knowing the type
    // of the arguments. This is currently limited to `to_fp`.
    Assert(p.d_name == "to_fp");
    size_t nchildren = args.size();
    if (nchildren == 1)
    {
      kind = cvc5::FLOATINGPOINT_TO_FP_FROM_IEEE_BV;
      op = d_solver->mkOp(kind, p.d_indices);
    }
    else if (nchildren > 2)
    {
      std::stringstream ss;
      ss << "Wrong number of arguments for indexed operator to_fp, expected "
            "1 or 2, got "
         << nchildren;
      parseError(ss.str());
    }
    else if (!args[0].getSort().isRoundingMode())
    {
      std::stringstream ss;
      ss << "Expected a rounding mode as the first argument, got "
         << args[0].getSort();
      parseError(ss.str());
    }
    else
    {
      cvc5::Sort t = args[1].getSort();

      if (t.isFloatingPoint())
      {
        kind = cvc5::FLOATINGPOINT_TO_FP_FROM_FP;
        op = d_solver->mkOp(kind, p.d_indices);
      }
      else if (t.isInteger() || t.isReal())
      {
        kind = cvc5::FLOATINGPOINT_TO_FP_FROM_REAL;
        op = d_solver->mkOp(kind, p.d_indices);
      }
      else
      {
        kind = cvc5::FLOATINGPOINT_TO_FP_FROM_SBV;
        op = d_solver->mkOp(kind, p.d_indices);
      }
    }
  }
  else if (p.d_kind != cvc5::NULL_TERM)
  {
    // It is a special case, e.g. tuple.select or array constant specification.
    // We have to wait until the arguments are parsed to resolve it.
  }
  else if (!p.d_expr.isNull())
  {
    // An explicit operator, e.g. an apply function
    cvc5::Kind fkind = getKindForFunction(p.d_expr);
    if (fkind != cvc5::UNDEFINED_KIND)
    {
      // Some operators may require a specific kind.
      // Testers are handled differently than other indexed operators,
      // since they require a kind.
      kind = fkind;
      Trace("parser") << "Got function kind " << kind << " for expression "
                      << std::endl;
    }
    args.insert(args.begin(), p.d_expr);
  }
  else if (!p.d_op.isNull())
  {
    // it was given an operator
    op = p.d_op;
  }
  else
  {
    isBuiltinOperator = isOperatorEnabled(p.d_name);
    if (isBuiltinOperator)
    {
      // a builtin operator, convert to kind
      kind = getOperatorKind(p.d_name);
      Trace("parser") << "Got builtin kind " << kind << " for name"
                      << std::endl;
    }
    else
    {
      // A non-built-in function application, get the expression
      checkDeclaration(p.d_name, CHECK_DECLARED, SYM_VARIABLE);
      cvc5::Term v = getVariable(p.d_name);
      if (!v.isNull())
      {
        checkFunctionLike(v);
        kind = getKindForFunction(v);
        args.insert(args.begin(), v);
      }
      else
      {
        // Overloaded symbol?
        // Could not find the expression. It may be an overloaded symbol,
        // in which case we may find it after knowing the types of its
        // arguments.
        std::vector<cvc5::Sort> argTypes;
        for (std::vector<cvc5::Term>::iterator i = args.begin();
             i != args.end();
             ++i)
        {
          argTypes.push_back((*i).getSort());
        }
        cvc5::Term fop = getOverloadedFunctionForTypes(p.d_name, argTypes);
        if (!fop.isNull())
        {
          checkFunctionLike(fop);
          kind = getKindForFunction(fop);
          args.insert(args.begin(), fop);
        }
        else
        {
          parseError(
              "Cannot find unambiguous overloaded function for argument "
              "types.");
        }
      }
    }
  }
  // handle special cases
  if (p.d_kind == cvc5::CONST_ARRAY && !p.d_type.isNull())
  {
    if (args.size() != 1)
    {
      parseError("Too many arguments to array constant.");
    }
    cvc5::Term constVal = args[0];

    if (p.d_type.getArrayElementSort() != constVal.getSort())
    {
      std::stringstream ss;
      ss << "type mismatch inside array constant term:" << std::endl
         << "array type:          " << p.d_type << std::endl
         << "expected const type: " << p.d_type.getArrayElementSort()
         << std::endl
         << "computed const type: " << constVal.getSort();
      parseError(ss.str());
    }
    cvc5::Term ret = d_solver->mkConstArray(p.d_type, constVal);
    Trace("parser") << "applyParseOp: return store all " << ret << std::endl;
    return ret;
  }
  else if ((p.d_kind == cvc5::APPLY_SELECTOR || p.d_kind == cvc5::APPLY_UPDATER)
           && !p.d_expr.isNull())
  {
    // tuple selector case
    if (!p.d_expr.isUInt64Value())
    {
      parseError(
          "index of tuple select or update is larger than size of uint64_t");
    }
    uint64_t n = p.d_expr.getUInt64Value();
    if (args.size() != (p.d_kind == cvc5::APPLY_SELECTOR ? 1 : 2))
    {
      parseError("wrong number of arguments for tuple select or update");
    }
    cvc5::Sort t = args[0].getSort();
    if (!t.isTuple())
    {
      parseError("tuple select or update applied to non-tuple");
    }
    size_t length = t.getTupleLength();
    if (n >= length)
    {
      std::stringstream ss;
      ss << "tuple is of length " << length << "; cannot access index " << n;
      parseError(ss.str());
    }
    const cvc5::Datatype& dt = t.getDatatype();
    cvc5::Term ret;
    if (p.d_kind == cvc5::APPLY_SELECTOR)
    {
      ret =
          d_solver->mkTerm(cvc5::APPLY_SELECTOR, {dt[0][n].getTerm(), args[0]});
    }
    else
    {
      ret = d_solver->mkTerm(cvc5::APPLY_UPDATER,
                             {dt[0][n].getUpdaterTerm(), args[0], args[1]});
    }
    Trace("parser") << "applyParseOp: return selector " << ret << std::endl;
    return ret;
  }
  else if (p.d_kind == cvc5::TUPLE_PROJECT)
  {
    cvc5::Term ret = d_solver->mkTerm(p.d_op, args);
    Trace("parser") << "applyParseOp: return projection " << ret << std::endl;
    return ret;
  }
  else if (p.d_kind != cvc5::NULL_TERM)
  {
    // it should not have an expression or type specified at this point
    if (!p.d_expr.isNull() || !p.d_type.isNull())
    {
      std::stringstream ss;
      ss << "Could not process parsed qualified identifier kind " << p.d_kind;
      parseError(ss.str());
    }
    // otherwise it is a simple application
    kind = p.d_kind;
  }
  else if (isBuiltinOperator)
  {
    if (!isHoEnabled() && (kind == cvc5::EQUAL || kind == cvc5::DISTINCT))
    {
      // need hol if these operators are applied over function args
      for (std::vector<cvc5::Term>::iterator i = args.begin(); i != args.end();
           ++i)
      {
        if ((*i).getSort().isFunction())
        {
          parseError(
              "Cannot apply equality to functions unless logic is prefixed by "
              "HO_.");
        }
      }
    }
    if (!strictModeEnabled() && (kind == cvc5::AND || kind == cvc5::OR)
        && args.size() == 1)
    {
      // Unary AND/OR can be replaced with the argument.
      Trace("parser") << "applyParseOp: return unary " << args[0] << std::endl;
      return args[0];
    }
    else if (kind == cvc5::SUB && args.size() == 1)
    {
      if (isConstInt(args[0]) && args[0].getRealOrIntegerValueSign() > 0)
      {
        // (- n) denotes a negative value
        std::stringstream suminus;
        suminus << "-" << args[0].getIntegerValue();
        cvc5::Term ret = d_solver->mkInteger(suminus.str());
        Trace("parser") << "applyParseOp: return negative constant " << ret
                        << std::endl;
        return ret;
      }
      cvc5::Term ret = d_solver->mkTerm(cvc5::NEG, {args[0]});
      Trace("parser") << "applyParseOp: return uminus " << ret << std::endl;
      return ret;
    }
    else if (kind == cvc5::DIVISION && args.size() == 2 && isConstInt(args[0])
             && isConstInt(args[1]) && args[1].getRealOrIntegerValueSign() > 0)
    {
      // (/ m n) or (/ (- m) n) denote values in reals
      std::stringstream sdiv;
      sdiv << args[0].getIntegerValue() << "/" << args[1].getIntegerValue();
      cvc5::Term ret = d_solver->mkReal(sdiv.str());
      Trace("parser") << "applyParseOp: return rational constant " << ret
                      << std::endl;
      return ret;
    }
    if (kind == cvc5::SET_SINGLETON && args.size() == 1)
    {
      cvc5::Term ret = d_solver->mkTerm(cvc5::SET_SINGLETON, {args[0]});
      Trace("parser") << "applyParseOp: return set.singleton " << ret
                      << std::endl;
      return ret;
    }
    else if (kind == cvc5::CARDINALITY_CONSTRAINT)
    {
      if (args.size() != 2)
      {
        parseError("Incorrect arguments for cardinality constraint");
      }
      cvc5::Sort sort = args[0].getSort();
      if (!sort.isUninterpretedSort())
      {
        parseError("Expected uninterpreted sort for cardinality constraint");
      }
      uint64_t ubound = args[1].getUInt32Value();
      cvc5::Term ret = d_solver->mkCardinalityConstraint(sort, ubound);
      return ret;
    }
    cvc5::Term ret = d_solver->mkTerm(kind, args);
    Trace("parser") << "applyParseOp: return default builtin " << ret
                    << std::endl;
    return ret;
  }

  if (args.size() >= 2)
  {
    // may be partially applied function, in this case we use HO_APPLY
    cvc5::Sort argt = args[0].getSort();
    if (argt.isFunction())
    {
      unsigned arity = argt.getFunctionArity();
      if (args.size() - 1 < arity)
      {
        if (!isHoEnabled())
        {
          parseError(
              "Cannot partially apply functions unless logic is prefixed by "
              "HO_.");
        }
        Trace("parser") << "Partial application of " << args[0];
        Trace("parser") << " : #argTypes = " << arity;
        Trace("parser") << ", #args = " << args.size() - 1 << std::endl;
        cvc5::Term ret = d_solver->mkTerm(cvc5::HO_APPLY, args);
        Trace("parser") << "applyParseOp: return curry higher order " << ret
                        << std::endl;
        // must curry the partial application
        return ret;
      }
    }
  }
  if (!op.isNull())
  {
    cvc5::Term ret = d_solver->mkTerm(op, args);
    Trace("parser") << "applyParseOp: return op : " << ret << std::endl;
    return ret;
  }
  if (kind == cvc5::NULL_TERM)
  {
    // should never happen in the new API
    parseError("do not know how to process parse op");
  }
  Trace("parser") << "Try default term construction for kind " << kind
                  << " #args = " << args.size() << "..." << std::endl;
  cvc5::Term ret = d_solver->mkTerm(kind, args);
  Trace("parser") << "applyParseOp: return : " << ret << std::endl;
  return ret;
}

void Smt2::notifyNamedExpression(cvc5::Term& expr, std::string name)
{
  checkUserSymbol(name);
  // remember the expression name in the symbol manager
  if (getSymbolManager()->setExpressionName(expr, name, false)
      == NamingResult::ERROR_IN_BINDER)
  {
    parseError(
        "Cannot name a term in a binder (e.g., quantifiers, definitions)");
  }
  // define the variable
  defineVar(name, expr);
  // set the last named term, which ensures that we catch when assertions are
  // named
  setLastNamedTerm(expr, name);
}

cvc5::Term Smt2::mkAnd(const std::vector<cvc5::Term>& es) const
{
  if (es.size() == 0)
  {
    return d_solver->mkTrue();
  }
  else if (es.size() == 1)
  {
    return es[0];
  }
  return d_solver->mkTerm(cvc5::AND, es);
}

bool Smt2::isConstInt(const cvc5::Term& t)
{
  cvc5::Kind k = t.getKind();
  // !!! Note when arithmetic subtyping is eliminated, this will update to
  // CONST_INTEGER.
  return k == cvc5::CONST_RATIONAL && t.getSort().isInteger();
}

}  // namespace parser
}  // namespace cvc5

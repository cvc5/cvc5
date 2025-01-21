/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definitions of SMT2 constants.
 */
#include "parser/smt2/smt2_state.h"

#include <algorithm>

#include "base/check.h"
#include "base/output.h"
#include "parser/commands.h"
#include "util/floatingpoint_size.h"

namespace cvc5 {
namespace parser {

Smt2State::Smt2State(ParserStateCallback* psc,
                     Solver* solver,
                     SymManager* sm,
                     ParsingMode parsingMode,
                     bool isSygus)
    : ParserState(psc, solver, sm, parsingMode),
      d_isSygus(isSygus),
      d_logicSet(false),
      d_seenSetLogic(false)
{
  d_freshBinders = (d_solver->getOption("fresh-binders") == "true");
}

Smt2State::~Smt2State() {}

void Smt2State::addArithmeticOperators()
{
  addOperator(Kind::ADD, "+");
  addOperator(Kind::SUB, "-");
  // SUB is converted to NEG if there is only a single operand
  ParserState::addOperator(Kind::NEG);
  addOperator(Kind::MULT, "*");
  addOperator(Kind::LT, "<");
  addOperator(Kind::LEQ, "<=");
  addOperator(Kind::GT, ">");
  addOperator(Kind::GEQ, ">=");

  if (!strictModeEnabled())
  {
    // NOTE: this operator is non-standard
    addOperator(Kind::POW, "^");
  }
}

void Smt2State::addTranscendentalOperators()
{
  addOperator(Kind::EXPONENTIAL, "exp");
  addOperator(Kind::SINE, "sin");
  addOperator(Kind::COSINE, "cos");
  addOperator(Kind::TANGENT, "tan");
  addOperator(Kind::COSECANT, "csc");
  addOperator(Kind::SECANT, "sec");
  addOperator(Kind::COTANGENT, "cot");
  addOperator(Kind::ARCSINE, "arcsin");
  addOperator(Kind::ARCCOSINE, "arccos");
  addOperator(Kind::ARCTANGENT, "arctan");
  addOperator(Kind::ARCCOSECANT, "arccsc");
  addOperator(Kind::ARCSECANT, "arcsec");
  addOperator(Kind::ARCCOTANGENT, "arccot");
  addOperator(Kind::SQRT, "sqrt");
}

void Smt2State::addQuantifiersOperators() {}

void Smt2State::addBitvectorOperators()
{
  addOperator(Kind::BITVECTOR_CONCAT, "concat");
  addOperator(Kind::BITVECTOR_NOT, "bvnot");
  addOperator(Kind::BITVECTOR_AND, "bvand");
  addOperator(Kind::BITVECTOR_OR, "bvor");
  addOperator(Kind::BITVECTOR_NEG, "bvneg");
  addOperator(Kind::BITVECTOR_ADD, "bvadd");
  addOperator(Kind::BITVECTOR_MULT, "bvmul");
  addOperator(Kind::BITVECTOR_UDIV, "bvudiv");
  addOperator(Kind::BITVECTOR_UREM, "bvurem");
  addOperator(Kind::BITVECTOR_SHL, "bvshl");
  addOperator(Kind::BITVECTOR_LSHR, "bvlshr");
  addOperator(Kind::BITVECTOR_ULT, "bvult");
  addOperator(Kind::BITVECTOR_NAND, "bvnand");
  addOperator(Kind::BITVECTOR_NOR, "bvnor");
  addOperator(Kind::BITVECTOR_XOR, "bvxor");
  addOperator(Kind::BITVECTOR_XNOR, "bvxnor");
  addOperator(Kind::BITVECTOR_COMP, "bvcomp");
  addOperator(Kind::BITVECTOR_SUB, "bvsub");
  addOperator(Kind::BITVECTOR_SDIV, "bvsdiv");
  addOperator(Kind::BITVECTOR_SREM, "bvsrem");
  addOperator(Kind::BITVECTOR_SMOD, "bvsmod");
  addOperator(Kind::BITVECTOR_ASHR, "bvashr");
  addOperator(Kind::BITVECTOR_ULE, "bvule");
  addOperator(Kind::BITVECTOR_UGT, "bvugt");
  addOperator(Kind::BITVECTOR_UGE, "bvuge");
  addOperator(Kind::BITVECTOR_SLT, "bvslt");
  addOperator(Kind::BITVECTOR_SLE, "bvsle");
  addOperator(Kind::BITVECTOR_SGT, "bvsgt");
  addOperator(Kind::BITVECTOR_SGE, "bvsge");
  addOperator(Kind::BITVECTOR_REDOR, "bvredor");
  addOperator(Kind::BITVECTOR_REDAND, "bvredand");
  addOperator(Kind::BITVECTOR_NEGO, "bvnego");
  addOperator(Kind::BITVECTOR_UADDO, "bvuaddo");
  addOperator(Kind::BITVECTOR_SADDO, "bvsaddo");
  addOperator(Kind::BITVECTOR_UMULO, "bvumulo");
  addOperator(Kind::BITVECTOR_SMULO, "bvsmulo");
  addOperator(Kind::BITVECTOR_USUBO, "bvusubo");
  addOperator(Kind::BITVECTOR_SSUBO, "bvssubo");
  addOperator(Kind::BITVECTOR_SDIVO, "bvsdivo");
  if (!strictModeEnabled())
  {
    addOperator(Kind::BITVECTOR_ITE, "bvite");
  }


  addIndexedOperator(Kind::BITVECTOR_EXTRACT, "extract");
  addIndexedOperator(Kind::BITVECTOR_REPEAT, "repeat");
  addIndexedOperator(Kind::BITVECTOR_ZERO_EXTEND, "zero_extend");
  addIndexedOperator(Kind::BITVECTOR_SIGN_EXTEND, "sign_extend");
  addIndexedOperator(Kind::BITVECTOR_ROTATE_LEFT, "rotate_left");
  addIndexedOperator(Kind::BITVECTOR_ROTATE_RIGHT, "rotate_right");
}

void Smt2State::addFiniteFieldOperators()
{
  addOperator(cvc5::Kind::FINITE_FIELD_ADD, "ff.add");
  addOperator(cvc5::Kind::FINITE_FIELD_MULT, "ff.mul");
  addOperator(cvc5::Kind::FINITE_FIELD_NEG, "ff.neg");
  addOperator(cvc5::Kind::FINITE_FIELD_BITSUM, "ff.bitsum");
}

void Smt2State::addDatatypesOperators()
{
  ParserState::addOperator(Kind::APPLY_CONSTRUCTOR);
  ParserState::addOperator(Kind::APPLY_TESTER);
  ParserState::addOperator(Kind::APPLY_SELECTOR);

  addIndexedOperator(Kind::APPLY_TESTER, "is");
  if (!strictModeEnabled())
  {
    ParserState::addOperator(Kind::APPLY_UPDATER);
    addIndexedOperator(Kind::APPLY_UPDATER, "update");
    // Tuple projection is both indexed and non-indexed (when indices are empty)
    addOperator(Kind::TUPLE_PROJECT, "tuple.project");
    addIndexedOperator(Kind::TUPLE_PROJECT, "tuple.project");
    // Notice that tuple operators, we use the UNDEFINED_KIND kind.
    // These are processed based on the context in which they are parsed, e.g.
    // when parsing identifiers.
    // For the tuple constructor "tuple", this is both a nullary operator
    // (for the 0-ary tuple), and a operator, hence we call both addOperator
    // and defineVar here.
    addOperator(Kind::APPLY_CONSTRUCTOR, "tuple");
    defineVar("tuple.unit", d_tm.mkTuple({}));
    addIndexedOperator(Kind::UNDEFINED_KIND, "tuple.select");
    addIndexedOperator(Kind::UNDEFINED_KIND, "tuple.update");
    Sort btype = d_tm.getBooleanSort();
    defineVar("nullable.null", d_tm.mkNullableNull(d_tm.mkNullableSort(btype)));
    addOperator(Kind::APPLY_CONSTRUCTOR, "nullable.some");
    addOperator(Kind::APPLY_SELECTOR, "nullable.val");
    addOperator(Kind::NULLABLE_LIFT, "nullable.lift");
    addOperator(Kind::APPLY_TESTER, "nullable.is_null");
    addOperator(Kind::APPLY_TESTER, "nullable.is_some");
    addIndexedOperator(Kind::NULLABLE_LIFT, "nullable.lift");
  }
}

void Smt2State::addStringOperators()
{
  defineVar("re.all", d_tm.mkRegexpAll());
  addOperator(Kind::STRING_CONCAT, "str.++");
  addOperator(Kind::STRING_LENGTH, "str.len");
  addOperator(Kind::STRING_SUBSTR, "str.substr");
  addOperator(Kind::STRING_CONTAINS, "str.contains");
  addOperator(Kind::STRING_CHARAT, "str.at");
  addOperator(Kind::STRING_INDEXOF, "str.indexof");
  addOperator(Kind::STRING_REPLACE, "str.replace");
  addOperator(Kind::STRING_PREFIX, "str.prefixof");
  addOperator(Kind::STRING_SUFFIX, "str.suffixof");
  addOperator(Kind::STRING_FROM_CODE, "str.from_code");
  addOperator(Kind::STRING_IS_DIGIT, "str.is_digit");
  addOperator(Kind::STRING_REPLACE_RE, "str.replace_re");
  addOperator(Kind::STRING_REPLACE_RE_ALL, "str.replace_re_all");
  if (!strictModeEnabled())
  {
    addOperator(Kind::STRING_INDEXOF_RE, "str.indexof_re");
    addOperator(Kind::STRING_UPDATE, "str.update");
    addOperator(Kind::STRING_TO_LOWER, "str.to_lower");
    addOperator(Kind::STRING_TO_UPPER, "str.to_upper");
    addOperator(Kind::STRING_REV, "str.rev");
    // sequence versions
    addOperator(Kind::SEQ_CONCAT, "seq.++");
    addOperator(Kind::SEQ_LENGTH, "seq.len");
    addOperator(Kind::SEQ_EXTRACT, "seq.extract");
    addOperator(Kind::SEQ_UPDATE, "seq.update");
    addOperator(Kind::SEQ_AT, "seq.at");
    addOperator(Kind::SEQ_CONTAINS, "seq.contains");
    addOperator(Kind::SEQ_INDEXOF, "seq.indexof");
    addOperator(Kind::SEQ_REPLACE, "seq.replace");
    addOperator(Kind::SEQ_PREFIX, "seq.prefixof");
    addOperator(Kind::SEQ_SUFFIX, "seq.suffixof");
    addOperator(Kind::SEQ_REV, "seq.rev");
    addOperator(Kind::SEQ_REPLACE_ALL, "seq.replace_all");
    addOperator(Kind::SEQ_UNIT, "seq.unit");
    addOperator(Kind::SEQ_NTH, "seq.nth");
  }
  addOperator(Kind::STRING_FROM_INT, "str.from_int");
  addOperator(Kind::STRING_TO_INT, "str.to_int");
  addOperator(Kind::STRING_IN_REGEXP, "str.in_re");
  addOperator(Kind::STRING_TO_REGEXP, "str.to_re");
  addOperator(Kind::STRING_TO_CODE, "str.to_code");
  addOperator(Kind::STRING_REPLACE_ALL, "str.replace_all");

  addOperator(Kind::REGEXP_CONCAT, "re.++");
  addOperator(Kind::REGEXP_UNION, "re.union");
  addOperator(Kind::REGEXP_INTER, "re.inter");
  addOperator(Kind::REGEXP_STAR, "re.*");
  addOperator(Kind::REGEXP_PLUS, "re.+");
  addOperator(Kind::REGEXP_OPT, "re.opt");
  addIndexedOperator(Kind::REGEXP_REPEAT, "re.^");
  addIndexedOperator(Kind::REGEXP_LOOP, "re.loop");
  addOperator(Kind::REGEXP_RANGE, "re.range");
  addOperator(Kind::REGEXP_COMPLEMENT, "re.comp");
  addOperator(Kind::REGEXP_DIFF, "re.diff");
  addOperator(Kind::STRING_LT, "str.<");
  addOperator(Kind::STRING_LEQ, "str.<=");
}

void Smt2State::addFloatingPointOperators()
{
  addOperator(Kind::FLOATINGPOINT_FP, "fp");
  addOperator(Kind::FLOATINGPOINT_EQ, "fp.eq");
  addOperator(Kind::FLOATINGPOINT_ABS, "fp.abs");
  addOperator(Kind::FLOATINGPOINT_NEG, "fp.neg");
  addOperator(Kind::FLOATINGPOINT_ADD, "fp.add");
  addOperator(Kind::FLOATINGPOINT_SUB, "fp.sub");
  addOperator(Kind::FLOATINGPOINT_MULT, "fp.mul");
  addOperator(Kind::FLOATINGPOINT_DIV, "fp.div");
  addOperator(Kind::FLOATINGPOINT_FMA, "fp.fma");
  addOperator(Kind::FLOATINGPOINT_SQRT, "fp.sqrt");
  addOperator(Kind::FLOATINGPOINT_REM, "fp.rem");
  addOperator(Kind::FLOATINGPOINT_RTI, "fp.roundToIntegral");
  addOperator(Kind::FLOATINGPOINT_MIN, "fp.min");
  addOperator(Kind::FLOATINGPOINT_MAX, "fp.max");
  addOperator(Kind::FLOATINGPOINT_LEQ, "fp.leq");
  addOperator(Kind::FLOATINGPOINT_LT, "fp.lt");
  addOperator(Kind::FLOATINGPOINT_GEQ, "fp.geq");
  addOperator(Kind::FLOATINGPOINT_GT, "fp.gt");
  addOperator(Kind::FLOATINGPOINT_IS_NORMAL, "fp.isNormal");
  addOperator(Kind::FLOATINGPOINT_IS_SUBNORMAL, "fp.isSubnormal");
  addOperator(Kind::FLOATINGPOINT_IS_ZERO, "fp.isZero");
  addOperator(Kind::FLOATINGPOINT_IS_INF, "fp.isInfinite");
  addOperator(Kind::FLOATINGPOINT_IS_NAN, "fp.isNaN");
  addOperator(Kind::FLOATINGPOINT_IS_NEG, "fp.isNegative");
  addOperator(Kind::FLOATINGPOINT_IS_POS, "fp.isPositive");
  addOperator(Kind::FLOATINGPOINT_TO_REAL, "fp.to_real");

  addIndexedOperator(Kind::UNDEFINED_KIND, "to_fp");
  addIndexedOperator(Kind::FLOATINGPOINT_TO_FP_FROM_UBV, "to_fp_unsigned");
  addIndexedOperator(Kind::FLOATINGPOINT_TO_UBV, "fp.to_ubv");
  addIndexedOperator(Kind::FLOATINGPOINT_TO_SBV, "fp.to_sbv");

  if (!strictModeEnabled())
  {
    addIndexedOperator(Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV, "to_fp_bv");
    addIndexedOperator(Kind::FLOATINGPOINT_TO_FP_FROM_FP, "to_fp_fp");
    addIndexedOperator(Kind::FLOATINGPOINT_TO_FP_FROM_REAL, "to_fp_real");
    addIndexedOperator(Kind::FLOATINGPOINT_TO_FP_FROM_SBV, "to_fp_signed");
  }
}

void Smt2State::addSepOperators()
{
  defineVar("sep.emp", d_tm.mkSepEmp());
  // the Boolean sort is a placeholder here since we don't have type info
  // without type annotation
  defineVar("sep.nil", d_tm.mkSepNil(d_tm.getBooleanSort()));
  addOperator(Kind::SEP_STAR, "sep");
  addOperator(Kind::SEP_PTO, "pto");
  addOperator(Kind::SEP_WAND, "wand");
  ParserState::addOperator(Kind::SEP_STAR);
  ParserState::addOperator(Kind::SEP_PTO);
  ParserState::addOperator(Kind::SEP_WAND);
}

void Smt2State::addCoreSymbols()
{
  defineType("Bool", d_tm.getBooleanSort(), false);
  Sort tupleSort = d_tm.mkTupleSort({});
  defineType("Relation", d_tm.mkSetSort(tupleSort), false);
  defineType("Table", d_tm.mkBagSort(tupleSort), false);
  defineVar("true", d_tm.mkTrue(), true);
  defineVar("false", d_tm.mkFalse(), true);
  addOperator(Kind::AND, "and");
  addOperator(Kind::DISTINCT, "distinct");
  addOperator(Kind::EQUAL, "=");
  addOperator(Kind::IMPLIES, "=>");
  addOperator(Kind::ITE, "ite");
  addOperator(Kind::NOT, "not");
  addOperator(Kind::OR, "or");
  addOperator(Kind::XOR, "xor");
  addClosureKind(Kind::FORALL, "forall");
  addClosureKind(Kind::EXISTS, "exists");
}

void Smt2State::addSkolemSymbols()
{
  for (int32_t s = static_cast<int32_t>(SkolemId::INTERNAL);
       s <= static_cast<int32_t>(SkolemId::NONE);
       ++s)
  {
    auto skolem = static_cast<SkolemId>(s);
    std::stringstream ss;
    ss << "@" << skolem;
    addSkolemId(skolem, ss.str());
  }
}

void Smt2State::addOperator(Kind kind, const std::string& name)
{
  Trace("parser") << "Smt2State::addOperator( " << kind << ", " << name << " )"
                  << std::endl;
  ParserState::addOperator(kind);
  d_operatorKindMap[name] = kind;
}

void Smt2State::addIndexedOperator(Kind tKind, const std::string& name)
{
  ParserState::addOperator(tKind);
  d_indexedOpKindMap[name] = tKind;
}

void Smt2State::addClosureKind(Kind tKind, const std::string& name)
{
  // also include it as a normal operator
  addOperator(tKind, name);
  d_closureKindMap[name] = tKind;
}

void Smt2State::addSkolemId(SkolemId skolemID, const std::string& name)
{
  addOperator(Kind::SKOLEM, name);
  d_skolemMap[name] = skolemID;
}

bool Smt2State::isIndexedOperatorEnabled(const std::string& name) const
{
  return d_indexedOpKindMap.find(name) != d_indexedOpKindMap.end();
}

Kind Smt2State::getOperatorKind(const std::string& name) const
{
  // precondition: isOperatorEnabled(name)
  return d_operatorKindMap.find(name)->second;
}

bool Smt2State::isOperatorEnabled(const std::string& name) const
{
  return d_operatorKindMap.find(name) != d_operatorKindMap.end();
}

modes::BlockModelsMode Smt2State::getBlockModelsMode(const std::string& mode)
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

modes::LearnedLitType Smt2State::getLearnedLitType(const std::string& mode)
{
  if (mode == "preprocess_solved")
  {
    return modes::LearnedLitType::PREPROCESS_SOLVED;
  }
  else if (mode == "preprocess")
  {
    return modes::LearnedLitType::PREPROCESS;
  }
  else if (mode == "input")
  {
    return modes::LearnedLitType::INPUT;
  }
  else if (mode == "solvable")
  {
    return modes::LearnedLitType::SOLVABLE;
  }
  else if (mode == "constant_prop")
  {
    return modes::LearnedLitType::CONSTANT_PROP;
  }
  else if (mode == "internal")
  {
    return modes::LearnedLitType::INTERNAL;
  }
  parseError(std::string("Unknown learned literal type `") + mode + "'");
  return modes::LearnedLitType::UNKNOWN;
}

modes::ProofComponent Smt2State::getProofComponent(const std::string& pc)
{
  if (pc == "raw_preprocess")
  {
    return modes::ProofComponent::RAW_PREPROCESS;
  }
  else if (pc == "preprocess")
  {
    return modes::ProofComponent::PREPROCESS;
  }
  else if (pc == "sat")
  {
    return modes::ProofComponent::SAT;
  }
  else if (pc == "theory_lemmas")
  {
    return modes::ProofComponent::THEORY_LEMMAS;
  }
  else if (pc == "full")
  {
    return modes::ProofComponent::FULL;
  }
  parseError(std::string("Unknown proof component `") + pc + "'");
  return modes::ProofComponent::FULL;
}

modes::FindSynthTarget Smt2State::getFindSynthTarget(const std::string& fst)
{
  if (fst == "enum")
  {
    return modes::FindSynthTarget::ENUM;
  }
  else if (fst == "rewrite")
  {
    return modes::FindSynthTarget::REWRITE;
  }
  else if (fst == "rewrite_unsound")
  {
    return modes::FindSynthTarget::REWRITE_UNSOUND;
  }
  else if (fst == "rewrite_input")
  {
    return modes::FindSynthTarget::REWRITE_INPUT;
  }
  else if (fst == "query")
  {
    return modes::FindSynthTarget::QUERY;
  }
  parseError(std::string("Unknown find synth target `") + fst + "'");
  return modes::FindSynthTarget::ENUM;
}

bool Smt2State::isTheoryEnabled(internal::theory::TheoryId theory) const
{
  return d_logic.isTheoryEnabled(theory);
}

bool Smt2State::isHoEnabled() const { return d_logic.isHigherOrder(); }

bool Smt2State::hasCardinalityConstraints() const
{
  return d_logic.hasCardinalityConstraints();
}

bool Smt2State::logicIsSet() { return d_logicSet; }

bool Smt2State::getTesterName(Term cons, std::string& name)
{
  if (strictModeEnabled())
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

Term Smt2State::mkIndexedConstant(const std::string& name,
                                  const std::vector<uint32_t>& numerals)
{
  if (d_logic.isTheoryEnabled(internal::theory::THEORY_FP))
  {
    if (name == "+oo")
    {
      if (numerals.size() != 2)
      {
        parseError("Unexpected number of numerals for +oo.");
      }
      return d_tm.mkFloatingPointPosInf(numerals[0], numerals[1]);
    }
    else if (name == "-oo")
    {
      if (numerals.size() != 2)
      {
        parseError("Unexpected number of numerals for -oo.");
      }
      return d_tm.mkFloatingPointNegInf(numerals[0], numerals[1]);
    }
    else if (name == "NaN")
    {
      if (numerals.size() != 2)
      {
        parseError("Unexpected number of numerals for NaN.");
      }
      return d_tm.mkFloatingPointNaN(numerals[0], numerals[1]);
    }
    else if (name == "+zero")
    {
      if (numerals.size() != 2)
      {
        parseError("Unexpected number of numerals for +zero.");
      }
      return d_tm.mkFloatingPointPosZero(numerals[0], numerals[1]);
    }
    else if (name == "-zero")
    {
      if (numerals.size() != 2)
      {
        parseError("Unexpected number of numerals for -zero.");
      }
      return d_tm.mkFloatingPointNegZero(numerals[0], numerals[1]);
    }
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_BV)
      && name.find("bv") == 0)
  {
    if (numerals.size() != 1)
    {
      parseError("Unexpected number of numerals for bit-vector constant.");
    }
    std::string bvStr = name.substr(2);
    return d_tm.mkBitVector(numerals[0], bvStr, 10);
  }

  // NOTE: Theory parametric constants go here

  parseError(std::string("Unknown indexed literal `") + name + "'");
  return Term();
}

Term Smt2State::mkIndexedConstant(const std::string& name,
                                  const std::vector<std::string>& symbols)
{
  if (d_logic.isTheoryEnabled(internal::theory::THEORY_STRINGS))
  {
    if (name == "char")
    {
      if (symbols.size() != 1)
      {
        parseError("Unexpected number of indices for char");
      }
      if (symbols[0].length() <= 2 || symbols[0].substr(0, 2) != "#x")
      {
        parseError(std::string("Unexpected index for char: `") + symbols[0]
                   + "'");
      }
      return mkCharConstant(symbols[0].substr(2));
    }
  }
  else if (d_logic.hasCardinalityConstraints())
  {
    if (name == "fmf.card")
    {
      if (symbols.size() != 2)
      {
        parseError("Unexpected number of indices for fmf.card");
      }
      Sort t = getSort(symbols[0]);
      // convert second symbol back to a numeral
      uint32_t ubound = stringToUnsigned(symbols[1]);
      return d_tm.mkCardinalityConstraint(t, ubound);
    }
  }
  parseError(std::string("Unknown indexed literal `") + name + "'");
  return Term();
}

Term Smt2State::mkIndexedOp(Kind k,
                            const std::vector<std::string>& symbols,
                            const std::vector<Term>& args)
{
  if (k == Kind::APPLY_TESTER || k == Kind::APPLY_UPDATER)
  {
    Assert(symbols.size() == 1);
    if (args.empty())
    {
      parseError("Expected argument to tester/updater");
    }
    const std::string& cname = symbols[0];
    // must be declared
    checkDeclaration(cname, CHECK_DECLARED, SYM_VARIABLE);
    Term f = getExpressionForNameAndType(cname, args[0].getSort());
    if (f.getKind() == Kind::APPLY_CONSTRUCTOR && f.getNumChildren() == 1)
    {
      // for nullary constructors, must get the operator
      f = f[0];
    }
    if (k == Kind::APPLY_TESTER)
    {
      if (!f.getSort().isDatatypeConstructor())
      {
        parseError("Bad syntax for (_ is X), X must be a constructor.");
      }
      // get the datatype that f belongs to
      Sort sf = f.getSort().getDatatypeConstructorCodomainSort();
      Datatype d = sf.getDatatype();
      // lookup by name
      DatatypeConstructor dc = d.getConstructor(f.toString());
      return dc.getTesterTerm();
    }
    else
    {
      Assert(k == Kind::APPLY_UPDATER);
      if (!f.getSort().isDatatypeSelector())
      {
        parseError("Bad syntax for (_ update X), X must be a selector.");
      }
      std::string sname = f.toString();
      // get the datatype that f belongs to
      Sort sf = f.getSort().getDatatypeSelectorDomainSort();
      Datatype d = sf.getDatatype();
      // find the selector
      DatatypeSelector ds = d.getSelector(f.toString());
      // get the updater term
      return ds.getUpdaterTerm();
    }
  }
  std::stringstream ss;
  ss << "Unknown indexed op kind " << k;
  parseError(ss.str());
  return Term();
}

Kind Smt2State::getIndexedOpKind(const std::string& name)
{
  const auto& kIt = d_indexedOpKindMap.find(name);
  if (kIt != d_indexedOpKindMap.end())
  {
    return (*kIt).second;
  }
  parseError(std::string("Unknown indexed function `") + name + "'");
  return Kind::UNDEFINED_KIND;
}

Kind Smt2State::getClosureKind(const std::string& name)
{
  const auto& kIt = d_closureKindMap.find(name);
  if (kIt != d_closureKindMap.end())
  {
    return (*kIt).second;
  }
  parseError(std::string("Unknown closure `") + name + "'");
  return Kind::UNDEFINED_KIND;
}

Term Smt2State::setupDefineFunRecScope(
    const std::string& fname,
    const std::vector<std::pair<std::string, Sort>>& sortedVarNames,
    Sort t,
    std::vector<Term>& flattenVars)
{
  std::vector<Sort> sorts;
  for (const std::pair<std::string, Sort>& svn : sortedVarNames)
  {
    sorts.push_back(svn.second);
  }

  // make the flattened function type, add bound variables
  // to flattenVars if the defined function was given a function return type.
  Sort ft = flattenFunctionType(sorts, t, flattenVars);

  if (!sorts.empty())
  {
    ft = d_tm.mkFunctionSort(sorts, ft);
  }
  // bind now, with overloading
  return bindVar(fname, ft, true);
}

void Smt2State::pushDefineFunRecScope(
    const std::vector<std::pair<std::string, Sort>>& sortedVarNames,
    Term func,
    const std::vector<Term>& flattenVars,
    std::vector<Term>& bvs)
{
  pushScope();
  // bound variables are those that are explicitly named in the preamble
  // of the define-fun(s)-rec command, we define them here
  for (const std::pair<std::string, Sort>& svn : sortedVarNames)
  {
    Term v = bindBoundVar(svn.first, svn.second);
    bvs.push_back(v);
  }

  bvs.insert(bvs.end(), flattenVars.begin(), flattenVars.end());
}

void Smt2State::reset()
{
  d_logicSet = false;
  d_logic = internal::LogicInfo();
  d_operatorKindMap.clear();
  d_lastNamedTerm = std::pair<Term, std::string>();
}

std::unique_ptr<Cmd> Smt2State::invConstraint(
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

  std::vector<Term> terms;
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

  return std::unique_ptr<Cmd>(new SygusInvConstraintCommand(terms));
}

void Smt2State::setLogic(std::string name)
{
  bool smLogicAlreadySet = getSymbolManager()->isLogicSet();
  // if logic is already set, this is an error
  if (d_logicSet)
  {
    parseError("Only one set-logic is allowed.");
  }
  d_logicSet = true;
  d_logic = name;

  // if sygus is enabled, we must enable UF, datatypes, and integer arithmetic
  if (sygus())
  {
    if (!d_logic.isQuantified())
    {
      warning("Logics in sygus are assumed to contain quantifiers.");
      warning("Omit QF_ from the logic to avoid this warning.");
    }
  }

  // Core theory belongs to every logic
  addCoreSymbols();

  // add skolems
  if (d_solver->getOption("parse-skolem-definitions") == "true")
  {
    addSkolemSymbols();
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_UF))
  {
    ParserState::addOperator(Kind::APPLY_UF);
  }

  if (d_logic.isHigherOrder())
  {
    addOperator(Kind::HO_APPLY, "@");
    // lambda is a closure kind
    addClosureKind(Kind::LAMBDA, "lambda");
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_ARITH))
  {
    if (d_logic.areIntegersUsed())
    {
      defineType("Int", d_tm.getIntegerSort(), false);
      addArithmeticOperators();
      if (!strictModeEnabled() || !d_logic.isLinear())
      {
        addOperator(Kind::INTS_DIVISION, "div");
        addOperator(Kind::INTS_MODULUS, "mod");
        addOperator(Kind::ABS, "abs");
      }
      if (!strictModeEnabled())
      {
        addOperator(Kind::INTS_DIVISION_TOTAL, "div_total");
        addOperator(Kind::INTS_MODULUS_TOTAL, "mod_total");
      }
      addIndexedOperator(Kind::DIVISIBLE, "divisible");
    }

    if (d_logic.areRealsUsed())
    {
      defineType("Real", d_tm.getRealSort(), false);
      addArithmeticOperators();
      addOperator(Kind::DIVISION, "/");
      if (!strictModeEnabled())
      {
        addOperator(Kind::ABS, "abs");
        addOperator(Kind::DIVISION_TOTAL, "/_total");
      }
    }

    if (d_logic.areIntegersUsed() && d_logic.areRealsUsed())
    {
      addOperator(Kind::TO_INTEGER, "to_int");
      addOperator(Kind::IS_INTEGER, "is_int");
      addOperator(Kind::TO_REAL, "to_real");
    }

    if (d_logic.areTranscendentalsUsed())
    {
      defineVar("real.pi", d_tm.mkPi());
      addTranscendentalOperators();
    }
    if (!strictModeEnabled())
    {
      // integer version of AND
      addIndexedOperator(Kind::IAND, "iand");
      // pow2
      addOperator(Kind::POW2, "int.pow2");
    }
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_ARRAYS))
  {
    addOperator(Kind::SELECT, "select");
    addOperator(Kind::STORE, "store");
    addOperator(Kind::EQ_RANGE, "eqrange");
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_BV))
  {
    addBitvectorOperators();

    if (!strictModeEnabled()
        && d_logic.isTheoryEnabled(internal::theory::THEORY_ARITH)
        && d_logic.areIntegersUsed())
    {
      // Conversions between bit-vectors and integers
      addOperator(Kind::BITVECTOR_TO_NAT, "bv2nat");
      addIndexedOperator(Kind::INT_TO_BITVECTOR, "int2bv");
    }
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_DATATYPES))
  {
    const std::vector<Sort> types;
    defineType("UnitTuple", d_tm.mkTupleSort(types), false);
    addDatatypesOperators();
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_SETS))
  {
    // the Boolean sort is a placeholder here since we don't have type info
    // without type annotation
    Sort btype = d_tm.getBooleanSort();
    defineVar("set.empty", d_tm.mkEmptySet(d_tm.mkSetSort(btype)));
    defineVar("set.universe", d_tm.mkUniverseSet(btype));

    addOperator(Kind::SET_UNION, "set.union");
    addOperator(Kind::SET_INTER, "set.inter");
    addOperator(Kind::SET_MINUS, "set.minus");
    addOperator(Kind::SET_SUBSET, "set.subset");
    addOperator(Kind::SET_MEMBER, "set.member");
    addOperator(Kind::SET_SINGLETON, "set.singleton");
    addOperator(Kind::SET_INSERT, "set.insert");
    addOperator(Kind::SET_CARD, "set.card");
    addOperator(Kind::SET_COMPLEMENT, "set.complement");
    addOperator(Kind::SET_CHOOSE, "set.choose");
    addOperator(Kind::SET_IS_EMPTY, "set.is_empty");
    addOperator(Kind::SET_IS_SINGLETON, "set.is_singleton");
    addOperator(Kind::SET_MAP, "set.map");
    addOperator(Kind::SET_FILTER, "set.filter");
    addOperator(Kind::SET_ALL, "set.all");
    addOperator(Kind::SET_SOME, "set.some");
    addOperator(Kind::SET_FOLD, "set.fold");
    addOperator(Kind::RELATION_JOIN, "rel.join");
    addOperator(Kind::RELATION_TABLE_JOIN, "rel.table_join");
    addOperator(Kind::RELATION_PRODUCT, "rel.product");
    addOperator(Kind::RELATION_TRANSPOSE, "rel.transpose");
    addOperator(Kind::RELATION_TCLOSURE, "rel.tclosure");
    addOperator(Kind::RELATION_JOIN_IMAGE, "rel.join_image");
    addOperator(Kind::RELATION_IDEN, "rel.iden");
    // these operators can be with/without indices
    addOperator(Kind::RELATION_GROUP, "rel.group");
    addOperator(Kind::RELATION_AGGREGATE, "rel.aggr");
    addOperator(Kind::RELATION_PROJECT, "rel.project");
    addIndexedOperator(Kind::RELATION_GROUP, "rel.group");
    addIndexedOperator(Kind::RELATION_TABLE_JOIN, "rel.table_join");
    addIndexedOperator(Kind::RELATION_AGGREGATE, "rel.aggr");
    addIndexedOperator(Kind::RELATION_PROJECT, "rel.project");
    // set.comprehension is a closure kind
    addClosureKind(Kind::SET_COMPREHENSION, "set.comprehension");
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_BAGS))
  {
    // the Boolean sort is a placeholder here since we don't have type info
    // without type annotation
    Sort btype = d_tm.getBooleanSort();
    defineVar("bag.empty", d_tm.mkEmptyBag(d_tm.mkBagSort(btype)));
    addOperator(Kind::BAG_UNION_MAX, "bag.union_max");
    addOperator(Kind::BAG_UNION_DISJOINT, "bag.union_disjoint");
    addOperator(Kind::BAG_INTER_MIN, "bag.inter_min");
    addOperator(Kind::BAG_DIFFERENCE_SUBTRACT, "bag.difference_subtract");
    addOperator(Kind::BAG_DIFFERENCE_REMOVE, "bag.difference_remove");
    addOperator(Kind::BAG_SUBBAG, "bag.subbag");
    addOperator(Kind::BAG_COUNT, "bag.count");
    addOperator(Kind::BAG_MEMBER, "bag.member");
    addOperator(Kind::BAG_SETOF, "bag.setof");
    addOperator(Kind::BAG_MAKE, "bag");
    addOperator(Kind::BAG_CARD, "bag.card");
    addOperator(Kind::BAG_CHOOSE, "bag.choose");
    addOperator(Kind::BAG_MAP, "bag.map");
    addOperator(Kind::BAG_FILTER, "bag.filter");
    addOperator(Kind::BAG_FOLD, "bag.fold");
    addOperator(Kind::BAG_PARTITION, "bag.partition");
    addOperator(Kind::TABLE_PRODUCT, "table.product");
    addOperator(Kind::BAG_PARTITION, "table.group");
    // these operators can be with/without indices
    addOperator(Kind::TABLE_PROJECT, "table.project");
    addOperator(Kind::TABLE_AGGREGATE, "table.aggr");
    addOperator(Kind::TABLE_JOIN, "table.join");
    addOperator(Kind::TABLE_GROUP, "table.group");
    addIndexedOperator(Kind::TABLE_PROJECT, "table.project");
    addIndexedOperator(Kind::TABLE_AGGREGATE, "table.aggr");
    addIndexedOperator(Kind::TABLE_JOIN, "table.join");
    addIndexedOperator(Kind::TABLE_GROUP, "table.group");
  }
  if (d_logic.isTheoryEnabled(internal::theory::THEORY_STRINGS))
  {
    defineType("String", d_tm.getStringSort(), false);
    defineType("RegLan", d_tm.getRegExpSort(), false);
    defineType("Int", d_tm.getIntegerSort(), false);

    defineVar("re.none", d_tm.mkRegexpNone());
    defineVar("re.allchar", d_tm.mkRegexpAllchar());

    // Boolean is a placeholder
    defineVar("seq.empty", d_tm.mkEmptySequence(d_tm.getBooleanSort()));

    addStringOperators();
  }

  if (d_logic.isQuantified())
  {
    addQuantifiersOperators();
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_FP))
  {
    defineType("RoundingMode", d_tm.getRoundingModeSort(), false);
    defineType("Float16", d_tm.mkFloatingPointSort(5, 11), false);
    defineType("Float32", d_tm.mkFloatingPointSort(8, 24), false);
    defineType("Float64", d_tm.mkFloatingPointSort(11, 53), false);
    defineType("Float128", d_tm.mkFloatingPointSort(15, 113), false);

    defineVar("RNE",
              d_tm.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN));
    defineVar("roundNearestTiesToEven",
              d_tm.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN));
    defineVar("RNA",
              d_tm.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_AWAY));
    defineVar("roundNearestTiesToAway",
              d_tm.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_AWAY));
    defineVar("RTP", d_tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_POSITIVE));
    defineVar("roundTowardPositive",
              d_tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_POSITIVE));
    defineVar("RTN", d_tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_NEGATIVE));
    defineVar("roundTowardNegative",
              d_tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_NEGATIVE));
    defineVar("RTZ", d_tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_ZERO));
    defineVar("roundTowardZero",
              d_tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_ZERO));

    addFloatingPointOperators();
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_FF))
  {
    addFiniteFieldOperators();
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_SEP))
  {
    addSepOperators();
  }

  // Builtin symbols of the logic are declared at context level zero, hence
  // we push the outermost scope in the symbol manager here.
  // We only do this if the logic has not already been set, in which case we have already
  // pushed the outermost context (and this method redeclares the symbols which does
  // not impact the symbol manager).
  // TODO (cvc5-projects #693): refactor this so that this method is moved to the
  // symbol manager and only called once per symbol manager.
  if (!smLogicAlreadySet)
  {
    pushScope(true);
  }
}

Grammar* Smt2State::mkGrammar(const std::vector<Term>& boundVars,
                              const std::vector<Term>& ntSymbols)
{
  d_allocGrammars.emplace_back(
      new Grammar(d_solver->mkGrammar(boundVars, ntSymbols)));
  return d_allocGrammars.back().get();
}

bool Smt2State::sygus() const { return d_isSygus; }

bool Smt2State::hasGrammars() const
{
  return sygus() || d_solver->getOption("produce-abducts") == "true"
         || d_solver->getOption("produce-interpolants") == "true";
}

bool Smt2State::usingFreshBinders() const { return d_freshBinders; }

void Smt2State::checkThatLogicIsSet()
{
  if (!logicIsSet())
  {
    if (strictModeEnabled())
    {
      parseError("set-logic must appear before this point.");
    }
    else
    {
      SymManager* sm = getSymbolManager();
      // the calls to setLogic below set the logic on the solver directly
      if (sm->isLogicForced())
      {
        setLogic(sm->getLogic());
      }
      else
      {
        warning("No set-logic command was given before this point.");
        warning("cvc5 will make all theories available.");
        warning(
            "Consider setting a stricter logic for (likely) better "
            "performance.");
        warning("To suppress this warning in the future use (set-logic ALL).");

        setLogic("ALL");
      }
      // Set the logic directly in the solver, without a command. Notice this is
      // important since we do not want to enqueue a set-logic command and
      // fully initialize the underlying SolverEngine in the meantime before the
      // command has a chance to execute, which would lead to an error.
      std::string logic = d_logic.getLogicString();
      d_solver->setLogic(logic);
      // set the logic on the symbol manager as well, non-forced
      sm->setLogic(logic);
    }
  }
}

void Smt2State::checkLogicAllowsFreeSorts()
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

void Smt2State::checkLogicAllowsFunctions()
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

bool Smt2State::isAbstractValue(const std::string& name)
{
  return name.length() >= 2 && name[0] == '@' && name[1] != '0'
         && name.find_first_not_of("0123456789", 1) == std::string::npos;
}

Term Smt2State::mkRealOrIntFromNumeral(const std::string& str)
{
  // if arithmetic is enabled, and integers are disabled
  if (d_logic.isTheoryEnabled(internal::theory::THEORY_ARITH)
      && !d_logic.areIntegersUsed())
  {
    return d_tm.mkReal(str);
  }
  return d_tm.mkInteger(str);
}

void Smt2State::parseOpApplyTypeAscription(ParseOp& p, Sort type)
{
  Trace("parser") << "parseOpApplyTypeAscription : " << p << " " << type
                  << std::endl;
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
    if (p.d_name == "const")
    {
      // We use a placeholder as a way to store the type of the constant array.
      // Since ParseOp only contains a Term field, it is stored as a constant
      // of the given type. The kind INTERNAL_KIND is used to mark that we
      // are a placeholder.
      p.d_kind = Kind::INTERNAL_KIND;
      p.d_expr = d_tm.mkConst(type, "_placeholder_");
      return;
    }
    else if (p.d_name.find("ff") == 0)
    {
      std::string rest = p.d_name.substr(2);
      if (!type.isFiniteField())
      {
        std::stringstream ss;
        ss << "expected finite field sort to ascribe " << p.d_name
           << " but found sort: " << type;
        parseError(ss.str());
      }
      p.d_expr = d_tm.mkFiniteFieldElem(rest, type);
      return;
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

Term Smt2State::parseOpToExpr(ParseOp& p)
{
  Trace("parser") << "parseOpToExpr: " << p << std::endl;
  Term expr;
  if (p.d_kind != Kind::NULL_TERM)
  {
    parseError(
        "Bad syntax for qualified identifier operator in term position.");
  }
  else if (!p.d_expr.isNull())
  {
    expr = p.d_expr;
  }
  else
  {
    checkDeclaration(p.d_name, CHECK_DECLARED, SYM_VARIABLE);
    expr = getVariable(p.d_name);
  }
  Assert(!expr.isNull());
  return expr;
}

Term Smt2State::applyParseOp(const ParseOp& p, std::vector<Term>& args)
{
  bool isBuiltinOperator = false;
  // the builtin kind of the overall return expression
  Kind kind = Kind::NULL_TERM;
  // First phase: process the operator
  if (TraceIsOn("parser"))
  {
    Trace("parser") << "applyParseOp: " << p << " to:" << std::endl;
    for (std::vector<Term>::iterator i = args.begin(); i != args.end(); ++i)
    {
      Trace("parser") << "++ " << *i << std::endl;
    }
  }
  if (p.d_kind == Kind::NULLABLE_LIFT)
  {
    auto it = d_operatorKindMap.find(p.d_name);
    if (it == d_operatorKindMap.end())
    {
      // the lifted symbol is not a defined kind. So we construct a normal
      // term.
      // Input : ((_ nullable.lift f) x y)
      // output: (nullable.lift f x y)
      ParserState::checkDeclaration(p.d_name, DeclarationCheck::CHECK_DECLARED);
      Term function = getVariable(p.d_name);
      args.insert(args.begin(), function);
      return d_tm.mkTerm(Kind::NULLABLE_LIFT, args);
    }
    else
    {
      Kind liftedKind = getOperatorKind(p.d_name);
      return d_tm.mkNullableLift(liftedKind, args);
    }
  }
  if (!p.d_indices.empty())
  {
    Op op;
    Kind k = getIndexedOpKind(p.d_name);
    if (k == Kind::UNDEFINED_KIND)
    {
      // Resolve indexed symbols that cannot be resolved without knowing the
      // type of the arguments. This is currently limited to `to_fp`,
      // `tuple.select`, and `tuple.update`.
      size_t nchildren = args.size();
      if (p.d_name == "to_fp")
      {
        if (nchildren == 1)
        {
          kind = Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV;
          op = d_tm.mkOp(kind, p.d_indices);
        }
        else if (nchildren > 2 || nchildren == 0)
        {
          std::stringstream ss;
          ss << "Wrong number of arguments for indexed operator to_fp, "
                "expected "
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
          Sort t = args[1].getSort();

          if (t.isFloatingPoint())
          {
            kind = Kind::FLOATINGPOINT_TO_FP_FROM_FP;
            op = d_tm.mkOp(kind, p.d_indices);
          }
          else if (t.isInteger() || t.isReal())
          {
            kind = Kind::FLOATINGPOINT_TO_FP_FROM_REAL;
            op = d_tm.mkOp(kind, p.d_indices);
          }
          else
          {
            kind = Kind::FLOATINGPOINT_TO_FP_FROM_SBV;
            op = d_tm.mkOp(kind, p.d_indices);
          }
        }
      }
      else if (p.d_name == "tuple.select" || p.d_name == "tuple.update")
      {
        bool isSelect = (p.d_name == "tuple.select");
        if (p.d_indices.size() != 1)
        {
          parseError("wrong number of indices for tuple select or update");
        }
        uint64_t n = p.d_indices[0];
        if (args.size() != (isSelect ? 1 : 2))
        {
          parseError("wrong number of arguments for tuple select or update");
        }
        Sort t = args[0].getSort();
        if (!t.isTuple())
        {
          parseError("tuple select or update applied to non-tuple");
        }
        size_t length = t.getTupleLength();
        if (n >= length)
        {
          std::stringstream ss;
          ss << "tuple is of length " << length << "; cannot access index "
             << n;
          parseError(ss.str());
        }
        const Datatype& dt = t.getDatatype();
        Term ret;
        if (isSelect)
        {
          ret =
              d_tm.mkTerm(Kind::APPLY_SELECTOR, {dt[0][n].getTerm(), args[0]});
        }
        else
        {
          ret = d_tm.mkTerm(Kind::APPLY_UPDATER,
                            {dt[0][n].getUpdaterTerm(), args[0], args[1]});
        }
        Trace("parser") << "applyParseOp: return selector/updater " << ret
                        << std::endl;
        return ret;
      }
      else
      {
        Assert(false) << "Failed to resolve indexed operator " << p.d_name;
      }
    }
    else
    {
      // otherwise, an ordinary operator
      op = d_tm.mkOp(k, p.d_indices);
    }
    return d_tm.mkTerm(op, args);
  }
  else if (p.d_kind != Kind::NULL_TERM)
  {
    // It is a special case, e.g. tuple.select or array constant specification.
    // We have to wait until the arguments are parsed to resolve it.
  }
  else if (!p.d_expr.isNull())
  {
    // An explicit operator, e.g. an apply function
    Kind fkind = getKindForFunction(p.d_expr);
    if (fkind != Kind::UNDEFINED_KIND)
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
  else
  {
    isBuiltinOperator = isOperatorEnabled(p.d_name);
    if (isBuiltinOperator)
    {
      // a builtin operator, convert to kind
      kind = getOperatorKind(p.d_name);
      // special case: indexed operators with zero arguments
      if (kind == Kind::TUPLE_PROJECT || kind == Kind::TABLE_PROJECT
          || kind == Kind::TABLE_AGGREGATE || kind == Kind::TABLE_JOIN
          || kind == Kind::TABLE_GROUP || kind == Kind::RELATION_GROUP
          || kind == Kind::RELATION_AGGREGATE || kind == Kind::RELATION_PROJECT
          || kind == Kind::RELATION_TABLE_JOIN)
      {
        std::vector<uint32_t> indices;
        Op op = d_tm.mkOp(kind, indices);
        return d_tm.mkTerm(op, args);
      }
      else if (kind == Kind::APPLY_CONSTRUCTOR)
      {
        if (p.d_name == "tuple")
        {
          // tuple application
          return d_tm.mkTuple(args);
        }
        else if (p.d_name == "nullable.some")
        {
          if (args.size() == 1)
          {
            return d_tm.mkNullableSome(args[0]);
          }
          parseError("nullable.some requires exactly one argument.");
        }
        else
        {
          std::stringstream ss;
          ss << "Unknown APPLY_CONSTRUCTOR symbol '" << p.d_name << "'";
          parseError(ss.str());
        }
      }
      else if (kind == Kind::APPLY_SELECTOR)
      {
        if (p.d_name == "nullable.val")
        {
          if (args.size() == 1)
          {
            return d_tm.mkNullableVal(args[0]);
          }
          parseError("nullable.val requires exactly one argument.");
        }
        else
        {
          std::stringstream ss;
          ss << "Unknown APPLY_SELECTOR symbol '" << p.d_name << "'";
          parseError(ss.str());
        }
      }
      else if (kind == Kind::APPLY_TESTER)
      {
        if (p.d_name == "nullable.is_null")
        {
          if (args.size() == 1)
          {
            return d_tm.mkNullableIsNull(args[0]);
          }
          parseError("nullable.is_null requires exactly one argument.");
        }
        else if (p.d_name == "nullable.is_some")
        {
          if (args.size() == 1)
          {
            return d_tm.mkNullableIsSome(args[0]);
          }
          parseError("nullable.is_some requires exactly one argument.");
        }
        else
        {
          std::stringstream ss;
          ss << "Unknown APPLY_TESTER symbol '" << p.d_name << "'";
          parseError(ss.str());
        }
      }
      Trace("parser") << "Got builtin kind " << kind << " for name"
                      << std::endl;
    }
    else
    {
      // A non-built-in function application, get the expression
      checkDeclaration(p.d_name, CHECK_DECLARED, SYM_VARIABLE);
      Term v = getVariable(p.d_name);
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
        std::vector<Sort> argTypes;
        for (std::vector<Term>::iterator i = args.begin(); i != args.end(); ++i)
        {
          argTypes.push_back((*i).getSort());
        }
        Term fop = getOverloadedFunctionForTypes(p.d_name, argTypes);
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
  // If we marked the operator as "INTERNAL_KIND", then the name/expr
  // determine the operator. This handles constant arrays.
  if (p.d_kind == Kind::INTERNAL_KIND)
  {
    // (as const (Array T1 T2))
    if (!strictModeEnabled() && p.d_name == "const"
        && isTheoryEnabled(internal::theory::THEORY_ARRAYS))
    {
      if (args.size() != 1)
      {
        parseError("Too many arguments to array constant.");
      }
      Term constVal = args[0];

      Assert(!p.d_expr.isNull());
      Sort sort = p.d_expr.getSort();
      if (!sort.isArray())
      {
        std::stringstream ss;
        ss << "expected array constant term, but cast is not of array type"
           << std::endl
           << "cast type: " << sort;
        parseError(ss.str());
      }
      if (sort.getArrayElementSort() != constVal.getSort())
      {
        std::stringstream ss;
        ss << "type mismatch inside array constant term:" << std::endl
           << "array type:          " << sort << std::endl
           << "expected const type: " << sort.getArrayElementSort() << std::endl
           << "computed const type: " << constVal.getSort();
        parseError(ss.str());
      }
      Term ret = d_tm.mkConstArray(sort, constVal);
      Trace("parser") << "applyParseOp: return store all " << ret << std::endl;
      return ret;
    }
    else
    {
      // should never happen
      parseError("Could not process internal parsed operator");
    }
  }
  else if (p.d_kind == Kind::APPLY_TESTER || p.d_kind == Kind::APPLY_UPDATER)
  {
    Term iop = mkIndexedOp(p.d_kind, {p.d_name}, args);
    kind = p.d_kind;
    args.insert(args.begin(), iop);
  }
  else if (p.d_kind != Kind::NULL_TERM)
  {
    // it should not have an expression or type specified at this point
    if (!p.d_expr.isNull())
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
    if (kind == Kind::EQUAL || kind == Kind::DISTINCT)
    {
      bool isReal = false;
      // need hol if these operators are applied over function args
      for (const Term& i : args)
      {
        Sort s = i.getSort();
        if (!isHoEnabled())
        {
          if (s.isFunction())
          {
            parseError(
                "Cannot apply equality to functions unless logic is prefixed "
                "by HO_.");
          }
        }
        if (s.isReal())
        {
          isReal = true;
        }
      }
      // If strict mode is not enabled, we are permissive for Int and Real
      // subtyping. Note that other arithmetic operators and relations are
      // already permissive, e.g. <=, +.
      if (isReal && !strictModeEnabled())
      {
        for (Term& i : args)
        {
          Sort s = i.getSort();
          if (s.isInteger())
          {
            i = d_tm.mkTerm(Kind::TO_REAL, {i});
          }
        }
      }
    }
    if (!strictModeEnabled() && (kind == Kind::AND || kind == Kind::OR)
        && args.size() == 1)
    {
      // Unary AND/OR can be replaced with the argument.
      Trace("parser") << "applyParseOp: return unary " << args[0] << std::endl;
      return args[0];
    }
    else if (kind == Kind::SUB && args.size() == 1)
    {
      Term ret = d_tm.mkTerm(Kind::NEG, {args[0]});
      Trace("parser") << "applyParseOp: return uminus " << ret << std::endl;
      return ret;
    }
    else if (kind == Kind::FLOATINGPOINT_FP)
    {
      // (fp #bX #bY #bZ) denotes a floating-point value
      if (args.size() != 3)
      {
        parseError("expected 3 arguments to 'fp', got "
                   + std::to_string(args.size()));
      }
      if (isConstBv(args[0]) && isConstBv(args[1]) && isConstBv(args[2]))
      {
        Term ret = d_tm.mkFloatingPoint(args[0], args[1], args[2]);
        Trace("parser") << "applyParseOp: return floating-point value " << ret
                        << std::endl;
        return ret;
      }
    }
    else if (kind == Kind::SKOLEM)
    {
      Term ret;
      SkolemId skolemId = d_skolemMap[p.d_name];
      size_t numSkolemIndices = d_tm.getNumIndicesForSkolemId(skolemId);
      if (numSkolemIndices == args.size())
      {
        ret = d_tm.mkSkolem(skolemId, args);
      }
      else
      {
        std::vector<Term> skolemArgs(args.begin(),
                                     args.begin() + numSkolemIndices);
        Term skolem = d_tm.mkSkolem(skolemId, skolemArgs);
        std::vector<Term> finalArgs = {skolem};
        finalArgs.insert(
            finalArgs.end(), args.begin() + numSkolemIndices, args.end());
        ret = d_tm.mkTerm(Kind::APPLY_UF, finalArgs);
      }
      Trace("parser") << "applyParseOp: return skolem " << ret << std::endl;
      return ret;
    }
    Term ret = d_tm.mkTerm(kind, args);
    Trace("parser") << "applyParseOp: return default builtin " << ret
                    << std::endl;
    return ret;
  }

  if (args.size() >= 2)
  {
    // may be partially applied function, in this case we use HO_APPLY
    Sort argt = args[0].getSort();
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
        Term ret = d_tm.mkTerm(Kind::HO_APPLY, args);
        Trace("parser") << "applyParseOp: return curry higher order " << ret
                        << std::endl;
        // must curry the partial application
        return ret;
      }
    }
  }
  if (kind == Kind::NULL_TERM)
  {
    // should never happen in the new API
    parseError("do not know how to process parse op");
  }
  Trace("parser") << "Try default term construction for kind " << kind
                  << " #args = " << args.size() << "..." << std::endl;
  Term ret = d_tm.mkTerm(kind, args);
  Trace("parser") << "applyParseOp: return : " << ret << std::endl;
  return ret;
}

Sort Smt2State::getParametricSort(const std::string& name,
                                  const std::vector<Sort>& args)
{
  if (args.empty())
  {
    parseError(
        "Extra parentheses around sort name not "
        "permitted in SMT-LIB");
  }
  // builtin parametric sorts are handled manually
  Sort t;
  if (name == "Array" && isTheoryEnabled(internal::theory::THEORY_ARRAYS))
  {
    if (args.size() != 2)
    {
      parseError("Illegal array type.");
    }
    t = d_tm.mkArraySort(args[0], args[1]);
  }
  else if (name == "Set" && isTheoryEnabled(internal::theory::THEORY_SETS))
  {
    if (args.size() != 1)
    {
      parseError("Illegal set type.");
    }
    t = d_tm.mkSetSort(args[0]);
  }
  else if (name == "Bag" && isTheoryEnabled(internal::theory::THEORY_BAGS))
  {
    if (args.size() != 1)
    {
      parseError("Illegal bag type.");
    }
    t = d_tm.mkBagSort(args[0]);
  }
  else if (name == "Seq" && !strictModeEnabled()
           && isTheoryEnabled(internal::theory::THEORY_STRINGS))
  {
    if (args.size() != 1)
    {
      parseError("Illegal sequence type.");
    }
    t = d_tm.mkSequenceSort(args[0]);
  }
  else if (name == "Tuple" && !strictModeEnabled())
  {
    t = d_tm.mkTupleSort(args);
  }
  else if (name == "Nullable" && !strictModeEnabled())
  {
    if (args.size() != 1)
    {
      parseError("Illegal nullable type.");
    }
    t = d_tm.mkNullableSort(args[0]);
  }
  else if (name == "Relation" && !strictModeEnabled())
  {
    Sort tupleSort = d_tm.mkTupleSort(args);
    t = d_tm.mkSetSort(tupleSort);
  }
  else if (name == "Table" && !strictModeEnabled())
  {
    Sort tupleSort = d_tm.mkTupleSort(args);
    t = d_tm.mkBagSort(tupleSort);
  }
  else if (name == "->" && isHoEnabled())
  {
    if (args.size() < 2)
    {
      parseError("Arrow types must have at least 2 arguments");
    }
    // flatten the type
    Sort rangeType = args.back();
    std::vector<Sort> dargs(args.begin(), args.end() - 1);
    t = mkFlatFunctionType(dargs, rangeType);
  }
  else
  {
    t = ParserState::getParametricSort(name, args);
  }
  return t;
}

Sort Smt2State::getIndexedSort(const std::string& name,
                               const std::vector<std::string>& numerals)
{
  Sort ret;
  if (name == "BitVec")
  {
    if (numerals.size() != 1)
    {
      parseError("Illegal bitvector type.");
    }
    uint32_t n0 = stringToUnsigned(numerals[0]);
    if (n0 == 0)
    {
      parseError("Illegal bitvector size: 0");
    }
    ret = d_tm.mkBitVectorSort(n0);
  }
  else if (name == "FiniteField")
  {
    if (numerals.size() != 1)
    {
      parseError("Illegal finite field type.");
    }
    ret = d_tm.mkFiniteFieldSort(numerals.front());
  }
  else if (name == "FloatingPoint")
  {
    if (numerals.size() != 2)
    {
      parseError("Illegal floating-point type.");
    }
    uint32_t n0 = stringToUnsigned(numerals[0]);
    uint32_t n1 = stringToUnsigned(numerals[1]);
    if (!internal::validExponentSize(n0))
    {
      parseError("Illegal floating-point exponent size");
    }
    if (!internal::validSignificandSize(n1))
    {
      parseError("Illegal floating-point significand size");
    }
    ret = d_tm.mkFloatingPointSort(n0, n1);
  }
  else
  {
    std::stringstream ss;
    ss << "unknown indexed sort symbol `" << name << "'";
    parseError(ss.str());
  }
  return ret;
}

bool Smt2State::isClosure(const std::string& name)
{
  return d_closureKindMap.find(name) != d_closureKindMap.end();
}

std::unique_ptr<Cmd> Smt2State::handlePush(std::optional<uint32_t> nscopes)
{
  checkThatLogicIsSet();

  if (!nscopes)
  {
    if (strictModeEnabled())
    {
      parseError(
          "Strict compliance mode demands an integer to be provided to "
          "(push).  Maybe you want (push 1)?");
    }
    nscopes = 1;
  }

  for (uint32_t i = 0; i < *nscopes; i++)
  {
    pushScope(true);
  }
  return std::make_unique<PushCommand>(*nscopes);
}

std::unique_ptr<Cmd> Smt2State::handlePop(std::optional<uint32_t> nscopes)
{
  checkThatLogicIsSet();

  if (!nscopes)
  {
    if (strictModeEnabled())
    {
      parseError(
          "Strict compliance mode demands an integer to be provided to "
          "(pop).  Maybe you want (pop 1)?");
    }
    nscopes = 1;
  }

  for (uint32_t i = 0; i < *nscopes; i++)
  {
    popScope();
  }
  return std::make_unique<PopCommand>(*nscopes);
}

void Smt2State::notifyNamedExpression(Term& expr, std::string name)
{
  checkUserSymbol(name);
  // remember the expression name in the symbol manager
  NamingResult nr = getSymbolManager()->setExpressionName(expr, name, false);
  if (nr == NamingResult::ERROR_IN_BINDER)
  {
    parseError(
        "Cannot name a term in a binder (e.g., quantifiers, definitions)");
  }
  // define the variable. This needs to be done here so that in the rest of the
  // command we can use this name, which is required by the semantics of :named.
  //
  // Note that as we are defining the name to the expression here, names never
  // show up in "-o raw-benchmark" nor in proofs. To be able to do it it'd be
  // necessary to not define this variable here and create a
  // DefineFunctionCommand with the binding, so that names are handled as
  // defined functions. However, these commands would need to be processed
  // *before* the rest of the command in which the :named attribute appears, so
  // the name can be defined in the rest of the command. This would greatly
  // complicate the design of the parser and provide little gain, so we opt to
  // handle :named as a macro processed directly in the parser.
  defineVar(name, expr);
  // set the last named term, which ensures that we catch when assertions are
  // named
  setLastNamedTerm(expr, name);
}

Term Smt2State::mkAnd(const std::vector<Term>& es) const
{
  if (es.size() == 0)
  {
    return d_tm.mkTrue();
  }
  else if (es.size() == 1)
  {
    return es[0];
  }
  return d_tm.mkTerm(Kind::AND, es);
}

bool Smt2State::isConstInt(const Term& t)
{
  return t.getKind() == Kind::CONST_INTEGER;
}

bool Smt2State::isConstBv(const Term& t)
{
  return t.getKind() == Kind::CONST_BITVECTOR;
}

}  // namespace parser
}  // namespace cvc5

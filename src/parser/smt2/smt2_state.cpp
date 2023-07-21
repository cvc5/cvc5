/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "parser/api/cpp/command.h"
#include "util/floatingpoint_size.h"

namespace cvc5 {
namespace parser {

Smt2State::Smt2State(ParserStateCallback* psc,
                     Solver* solver,
                     SymbolManager* sm,
                     bool strictMode,
                     bool isSygus)
    : ParserState(psc, solver, sm, strictMode),
      d_isSygus(isSygus),
      d_logicSet(false),
      d_seenSetLogic(false)
{
}

Smt2State::~Smt2State() {}

void Smt2State::addArithmeticOperators()
{
  addOperator(ADD, "+");
  addOperator(SUB, "-");
  // SUB is converted to NEG if there is only a single operand
  ParserState::addOperator(NEG);
  addOperator(MULT, "*");
  addOperator(LT, "<");
  addOperator(LEQ, "<=");
  addOperator(GT, ">");
  addOperator(GEQ, ">=");

  if (!strictModeEnabled())
  {
    // NOTE: this operator is non-standard
    addOperator(POW, "^");
  }
}

void Smt2State::addTranscendentalOperators()
{
  addOperator(EXPONENTIAL, "exp");
  addOperator(SINE, "sin");
  addOperator(COSINE, "cos");
  addOperator(TANGENT, "tan");
  addOperator(COSECANT, "csc");
  addOperator(SECANT, "sec");
  addOperator(COTANGENT, "cot");
  addOperator(ARCSINE, "arcsin");
  addOperator(ARCCOSINE, "arccos");
  addOperator(ARCTANGENT, "arctan");
  addOperator(ARCCOSECANT, "arccsc");
  addOperator(ARCSECANT, "arcsec");
  addOperator(ARCCOTANGENT, "arccot");
  addOperator(SQRT, "sqrt");
}

void Smt2State::addQuantifiersOperators() {}

void Smt2State::addBitvectorOperators()
{
  addOperator(BITVECTOR_CONCAT, "concat");
  addOperator(BITVECTOR_NOT, "bvnot");
  addOperator(BITVECTOR_AND, "bvand");
  addOperator(BITVECTOR_OR, "bvor");
  addOperator(BITVECTOR_NEG, "bvneg");
  addOperator(BITVECTOR_ADD, "bvadd");
  addOperator(BITVECTOR_MULT, "bvmul");
  addOperator(BITVECTOR_UDIV, "bvudiv");
  addOperator(BITVECTOR_UREM, "bvurem");
  addOperator(BITVECTOR_SHL, "bvshl");
  addOperator(BITVECTOR_LSHR, "bvlshr");
  addOperator(BITVECTOR_ULT, "bvult");
  addOperator(BITVECTOR_NAND, "bvnand");
  addOperator(BITVECTOR_NOR, "bvnor");
  addOperator(BITVECTOR_XOR, "bvxor");
  addOperator(BITVECTOR_XNOR, "bvxnor");
  addOperator(BITVECTOR_COMP, "bvcomp");
  addOperator(BITVECTOR_SUB, "bvsub");
  addOperator(BITVECTOR_SDIV, "bvsdiv");
  addOperator(BITVECTOR_SREM, "bvsrem");
  addOperator(BITVECTOR_SMOD, "bvsmod");
  addOperator(BITVECTOR_ASHR, "bvashr");
  addOperator(BITVECTOR_ULE, "bvule");
  addOperator(BITVECTOR_UGT, "bvugt");
  addOperator(BITVECTOR_UGE, "bvuge");
  addOperator(BITVECTOR_SLT, "bvslt");
  addOperator(BITVECTOR_SLE, "bvsle");
  addOperator(BITVECTOR_SGT, "bvsgt");
  addOperator(BITVECTOR_SGE, "bvsge");
  addOperator(BITVECTOR_REDOR, "bvredor");
  addOperator(BITVECTOR_REDAND, "bvredand");
  addOperator(BITVECTOR_UADDO, "bvuaddo");
  addOperator(BITVECTOR_SADDO, "bvsaddo");
  addOperator(BITVECTOR_UMULO, "bvumulo");
  addOperator(BITVECTOR_SMULO, "bvsmulo");
  addOperator(BITVECTOR_USUBO, "bvusubo");
  addOperator(BITVECTOR_SSUBO, "bvssubo");
  addOperator(BITVECTOR_SDIVO, "bvsdivo");

  addIndexedOperator(BITVECTOR_EXTRACT, "extract");
  addIndexedOperator(BITVECTOR_REPEAT, "repeat");
  addIndexedOperator(BITVECTOR_ZERO_EXTEND, "zero_extend");
  addIndexedOperator(BITVECTOR_SIGN_EXTEND, "sign_extend");
  addIndexedOperator(BITVECTOR_ROTATE_LEFT, "rotate_left");
  addIndexedOperator(BITVECTOR_ROTATE_RIGHT, "rotate_right");
}

void Smt2State::addFiniteFieldOperators()
{
  addOperator(cvc5::FINITE_FIELD_ADD, "ff.add");
  addOperator(cvc5::FINITE_FIELD_MULT, "ff.mul");
  addOperator(cvc5::FINITE_FIELD_NEG, "ff.neg");
}

void Smt2State::addDatatypesOperators()
{
  ParserState::addOperator(APPLY_CONSTRUCTOR);
  ParserState::addOperator(APPLY_TESTER);
  ParserState::addOperator(APPLY_SELECTOR);

  addIndexedOperator(APPLY_TESTER, "is");
  if (!strictModeEnabled())
  {
    ParserState::addOperator(APPLY_UPDATER);
    addIndexedOperator(APPLY_UPDATER, "update");
    // Tuple projection is both indexed and non-indexed (when indices are empty)
    addOperator(TUPLE_PROJECT, "tuple.project");
    addIndexedOperator(TUPLE_PROJECT, "tuple.project");
    // Notice that tuple operators, we use the UNDEFINED_KIND kind.
    // These are processed based on the context in which they are parsed, e.g.
    // when parsing identifiers.
    // For the tuple constructor "tuple", this is both a nullary operator
    // (for the 0-ary tuple), and a operator, hence we call both addOperator
    // and defineVar here.
    addOperator(APPLY_CONSTRUCTOR, "tuple");
    defineVar("tuple", d_solver->mkTuple({}));
    addIndexedOperator(UNDEFINED_KIND, "tuple.select");
    addIndexedOperator(UNDEFINED_KIND, "tuple.update");
  }
}

void Smt2State::addStringOperators()
{
  defineVar("re.all", d_solver->mkRegexpAll());
  addOperator(STRING_CONCAT, "str.++");
  addOperator(STRING_LENGTH, "str.len");
  addOperator(STRING_SUBSTR, "str.substr");
  addOperator(STRING_CONTAINS, "str.contains");
  addOperator(STRING_CHARAT, "str.at");
  addOperator(STRING_INDEXOF, "str.indexof");
  addOperator(STRING_REPLACE, "str.replace");
  addOperator(STRING_PREFIX, "str.prefixof");
  addOperator(STRING_SUFFIX, "str.suffixof");
  addOperator(STRING_FROM_CODE, "str.from_code");
  addOperator(STRING_IS_DIGIT, "str.is_digit");
  addOperator(STRING_REPLACE_RE, "str.replace_re");
  addOperator(STRING_REPLACE_RE_ALL, "str.replace_re_all");
  if (!strictModeEnabled())
  {
    addOperator(STRING_INDEXOF_RE, "str.indexof_re");
    addOperator(STRING_UPDATE, "str.update");
    addOperator(STRING_TO_LOWER, "str.to_lower");
    addOperator(STRING_TO_UPPER, "str.to_upper");
    addOperator(STRING_REV, "str.rev");
    // sequence versions
    addOperator(SEQ_CONCAT, "seq.++");
    addOperator(SEQ_LENGTH, "seq.len");
    addOperator(SEQ_EXTRACT, "seq.extract");
    addOperator(SEQ_UPDATE, "seq.update");
    addOperator(SEQ_AT, "seq.at");
    addOperator(SEQ_CONTAINS, "seq.contains");
    addOperator(SEQ_INDEXOF, "seq.indexof");
    addOperator(SEQ_REPLACE, "seq.replace");
    addOperator(SEQ_PREFIX, "seq.prefixof");
    addOperator(SEQ_SUFFIX, "seq.suffixof");
    addOperator(SEQ_REV, "seq.rev");
    addOperator(SEQ_REPLACE_ALL, "seq.replace_all");
    addOperator(SEQ_UNIT, "seq.unit");
    addOperator(SEQ_NTH, "seq.nth");
  }
  addOperator(STRING_FROM_INT, "str.from_int");
  addOperator(STRING_TO_INT, "str.to_int");
  addOperator(STRING_IN_REGEXP, "str.in_re");
  addOperator(STRING_TO_REGEXP, "str.to_re");
  addOperator(STRING_TO_CODE, "str.to_code");
  addOperator(STRING_REPLACE_ALL, "str.replace_all");

  addOperator(REGEXP_CONCAT, "re.++");
  addOperator(REGEXP_UNION, "re.union");
  addOperator(REGEXP_INTER, "re.inter");
  addOperator(REGEXP_STAR, "re.*");
  addOperator(REGEXP_PLUS, "re.+");
  addOperator(REGEXP_OPT, "re.opt");
  addIndexedOperator(REGEXP_REPEAT, "re.^");
  addIndexedOperator(REGEXP_LOOP, "re.loop");
  addOperator(REGEXP_RANGE, "re.range");
  addOperator(REGEXP_COMPLEMENT, "re.comp");
  addOperator(REGEXP_DIFF, "re.diff");
  addOperator(STRING_LT, "str.<");
  addOperator(STRING_LEQ, "str.<=");
}

void Smt2State::addFloatingPointOperators()
{
  addOperator(FLOATINGPOINT_FP, "fp");
  addOperator(FLOATINGPOINT_EQ, "fp.eq");
  addOperator(FLOATINGPOINT_ABS, "fp.abs");
  addOperator(FLOATINGPOINT_NEG, "fp.neg");
  addOperator(FLOATINGPOINT_ADD, "fp.add");
  addOperator(FLOATINGPOINT_SUB, "fp.sub");
  addOperator(FLOATINGPOINT_MULT, "fp.mul");
  addOperator(FLOATINGPOINT_DIV, "fp.div");
  addOperator(FLOATINGPOINT_FMA, "fp.fma");
  addOperator(FLOATINGPOINT_SQRT, "fp.sqrt");
  addOperator(FLOATINGPOINT_REM, "fp.rem");
  addOperator(FLOATINGPOINT_RTI, "fp.roundToIntegral");
  addOperator(FLOATINGPOINT_MIN, "fp.min");
  addOperator(FLOATINGPOINT_MAX, "fp.max");
  addOperator(FLOATINGPOINT_LEQ, "fp.leq");
  addOperator(FLOATINGPOINT_LT, "fp.lt");
  addOperator(FLOATINGPOINT_GEQ, "fp.geq");
  addOperator(FLOATINGPOINT_GT, "fp.gt");
  addOperator(FLOATINGPOINT_IS_NORMAL, "fp.isNormal");
  addOperator(FLOATINGPOINT_IS_SUBNORMAL, "fp.isSubnormal");
  addOperator(FLOATINGPOINT_IS_ZERO, "fp.isZero");
  addOperator(FLOATINGPOINT_IS_INF, "fp.isInfinite");
  addOperator(FLOATINGPOINT_IS_NAN, "fp.isNaN");
  addOperator(FLOATINGPOINT_IS_NEG, "fp.isNegative");
  addOperator(FLOATINGPOINT_IS_POS, "fp.isPositive");
  addOperator(FLOATINGPOINT_TO_REAL, "fp.to_real");

  addIndexedOperator(UNDEFINED_KIND, "to_fp");
  addIndexedOperator(FLOATINGPOINT_TO_FP_FROM_UBV, "to_fp_unsigned");
  addIndexedOperator(FLOATINGPOINT_TO_UBV, "fp.to_ubv");
  addIndexedOperator(FLOATINGPOINT_TO_SBV, "fp.to_sbv");

  if (!strictModeEnabled())
  {
    addIndexedOperator(FLOATINGPOINT_TO_FP_FROM_IEEE_BV, "to_fp_bv");
    addIndexedOperator(FLOATINGPOINT_TO_FP_FROM_FP, "to_fp_fp");
    addIndexedOperator(FLOATINGPOINT_TO_FP_FROM_REAL, "to_fp_real");
    addIndexedOperator(FLOATINGPOINT_TO_FP_FROM_SBV, "to_fp_signed");
  }
}

void Smt2State::addSepOperators()
{
  defineVar("sep.emp", d_solver->mkSepEmp());
  // the Boolean sort is a placeholder here since we don't have type info
  // without type annotation
  defineVar("sep.nil", d_solver->mkSepNil(d_solver->getBooleanSort()));
  addOperator(SEP_STAR, "sep");
  addOperator(SEP_PTO, "pto");
  addOperator(SEP_WAND, "wand");
  ParserState::addOperator(SEP_STAR);
  ParserState::addOperator(SEP_PTO);
  ParserState::addOperator(SEP_WAND);
}

void Smt2State::addCoreSymbols()
{
  defineType("Bool", d_solver->getBooleanSort(), true);
  Sort tupleSort = d_solver->mkTupleSort({});
  defineType("Relation", d_solver->mkSetSort(tupleSort), true);
  defineType("Table", d_solver->mkBagSort(tupleSort), true);
  defineVar("true", d_solver->mkTrue(), true);
  defineVar("false", d_solver->mkFalse(), true);
  addOperator(AND, "and");
  addOperator(DISTINCT, "distinct");
  addOperator(EQUAL, "=");
  addOperator(IMPLIES, "=>");
  addOperator(ITE, "ite");
  addOperator(NOT, "not");
  addOperator(OR, "or");
  addOperator(XOR, "xor");
  addClosureKind(FORALL, "forall");
  addClosureKind(EXISTS, "exists");
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
    return modes::LEARNED_LIT_PREPROCESS_SOLVED;
  }
  else if (mode == "preprocess")
  {
    return modes::LEARNED_LIT_PREPROCESS;
  }
  else if (mode == "input")
  {
    return modes::LEARNED_LIT_INPUT;
  }
  else if (mode == "solvable")
  {
    return modes::LEARNED_LIT_SOLVABLE;
  }
  else if (mode == "constant_prop")
  {
    return modes::LEARNED_LIT_CONSTANT_PROP;
  }
  else if (mode == "internal")
  {
    return modes::LEARNED_LIT_INTERNAL;
  }
  parseError(std::string("Unknown learned literal type `") + mode + "'");
  return modes::LEARNED_LIT_UNKNOWN;
}

modes::ProofComponent Smt2State::getProofComponent(const std::string& pc)
{
  if (pc == "raw_preprocess")
  {
    return modes::ProofComponent::PROOF_COMPONENT_RAW_PREPROCESS;
  }
  else if (pc == "preprocess")
  {
    return modes::ProofComponent::PROOF_COMPONENT_PREPROCESS;
  }
  else if (pc == "sat")
  {
    return modes::ProofComponent::PROOF_COMPONENT_SAT;
  }
  else if (pc == "theory_lemmas")
  {
    return modes::ProofComponent::PROOF_COMPONENT_THEORY_LEMMAS;
  }
  else if (pc == "full")
  {
    return modes::ProofComponent::PROOF_COMPONENT_FULL;
  }
  parseError(std::string("Unknown proof component `") + pc + "'");
  return modes::ProofComponent::PROOF_COMPONENT_FULL;
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
      return d_solver->mkFloatingPointPosInf(numerals[0], numerals[1]);
    }
    else if (name == "-oo")
    {
      if (numerals.size() != 2)
      {
        parseError("Unexpected number of numerals for -oo.");
      }
      return d_solver->mkFloatingPointNegInf(numerals[0], numerals[1]);
    }
    else if (name == "NaN")
    {
      if (numerals.size() != 2)
      {
        parseError("Unexpected number of numerals for NaN.");
      }
      return d_solver->mkFloatingPointNaN(numerals[0], numerals[1]);
    }
    else if (name == "+zero")
    {
      if (numerals.size() != 2)
      {
        parseError("Unexpected number of numerals for +zero.");
      }
      return d_solver->mkFloatingPointPosZero(numerals[0], numerals[1]);
    }
    else if (name == "-zero")
    {
      if (numerals.size() != 2)
      {
        parseError("Unexpected number of numerals for -zero.");
      }
      return d_solver->mkFloatingPointNegZero(numerals[0], numerals[1]);
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
    return d_solver->mkBitVector(numerals[0], bvStr, 10);
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
      return d_solver->mkCardinalityConstraint(t, ubound);
    }
  }
  parseError(std::string("Unknown indexed literal `") + name + "'");
  return Term();
}

Term Smt2State::mkIndexedOp(Kind k,
                            const std::vector<std::string>& symbols,
                            const std::vector<Term>& args)
{
  if (k == APPLY_TESTER || k == APPLY_UPDATER)
  {
    Assert(symbols.size() == 1);
    Assert(!args.empty());
    const std::string& cname = symbols[0];
    // must be declared
    checkDeclaration(cname, CHECK_DECLARED, SYM_VARIABLE);
    Term f = getExpressionForNameAndType(cname, args[0].getSort());
    if (f.getKind() == APPLY_CONSTRUCTOR && f.getNumChildren() == 1)
    {
      // for nullary constructors, must get the operator
      f = f[0];
    }
    if (k == APPLY_TESTER)
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
      Assert(k == APPLY_UPDATER);
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
  return UNDEFINED_KIND;
}

Kind Smt2State::getClosureKind(const std::string& name)
{
  const auto& kIt = d_closureKindMap.find(name);
  if (kIt != d_closureKindMap.end())
  {
    return (*kIt).second;
  }
  parseError(std::string("Unknown closure `") + name + "'");
  return UNDEFINED_KIND;
}

Term Smt2State::bindDefineFunRec(
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
  Sort ft = mkFlatFunctionType(sorts, t, flattenVars);

  // allow overloading
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

std::unique_ptr<Command> Smt2State::invConstraint(
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

  return std::unique_ptr<Command>(new SygusInvConstraintCommand(terms));
}

void Smt2State::setLogic(std::string name)
{
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

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_UF))
  {
    ParserState::addOperator(APPLY_UF);
  }

  if (d_logic.isHigherOrder())
  {
    addOperator(HO_APPLY, "@");
    // lambda is a closure kind
    addClosureKind(LAMBDA, "lambda");
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_ARITH))
  {
    if (d_logic.areIntegersUsed())
    {
      defineType("Int", d_solver->getIntegerSort(), true);
      addArithmeticOperators();
      if (!strictModeEnabled() || !d_logic.isLinear())
      {
        addOperator(INTS_DIVISION, "div");
        addOperator(INTS_MODULUS, "mod");
        addOperator(ABS, "abs");
      }
      addIndexedOperator(DIVISIBLE, "divisible");
    }

    if (d_logic.areRealsUsed())
    {
      defineType("Real", d_solver->getRealSort(), true);
      addArithmeticOperators();
      addOperator(DIVISION, "/");
      if (!strictModeEnabled())
      {
        addOperator(ABS, "abs");
      }
    }

    if (d_logic.areIntegersUsed() && d_logic.areRealsUsed())
    {
      addOperator(TO_INTEGER, "to_int");
      addOperator(IS_INTEGER, "is_int");
      addOperator(TO_REAL, "to_real");
    }

    if (d_logic.areTranscendentalsUsed())
    {
      defineVar("real.pi", d_solver->mkPi());
      addTranscendentalOperators();
    }
    if (!strictModeEnabled())
    {
      // integer version of AND
      addIndexedOperator(IAND, "iand");
      // pow2
      addOperator(POW2, "int.pow2");
    }
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_ARRAYS))
  {
    addOperator(SELECT, "select");
    addOperator(STORE, "store");
    addOperator(EQ_RANGE, "eqrange");
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_BV))
  {
    addBitvectorOperators();

    if (!strictModeEnabled()
        && d_logic.isTheoryEnabled(internal::theory::THEORY_ARITH)
        && d_logic.areIntegersUsed())
    {
      // Conversions between bit-vectors and integers
      addOperator(BITVECTOR_TO_NAT, "bv2nat");
      addIndexedOperator(INT_TO_BITVECTOR, "int2bv");
    }
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_DATATYPES))
  {
    const std::vector<Sort> types;
    defineType("Tuple", d_solver->mkTupleSort(types), true);
    addDatatypesOperators();
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_SETS))
  {
    // the Boolean sort is a placeholder here since we don't have type info
    // without type annotation
    Sort btype = d_solver->getBooleanSort();
    defineVar("set.empty", d_solver->mkEmptySet(d_solver->mkSetSort(btype)));
    defineVar("set.universe", d_solver->mkUniverseSet(btype));

    addOperator(SET_UNION, "set.union");
    addOperator(SET_INTER, "set.inter");
    addOperator(SET_MINUS, "set.minus");
    addOperator(SET_SUBSET, "set.subset");
    addOperator(SET_MEMBER, "set.member");
    addOperator(SET_SINGLETON, "set.singleton");
    addOperator(SET_INSERT, "set.insert");
    addOperator(SET_CARD, "set.card");
    addOperator(SET_COMPLEMENT, "set.complement");
    addOperator(SET_CHOOSE, "set.choose");
    addOperator(SET_IS_SINGLETON, "set.is_singleton");
    addOperator(SET_MAP, "set.map");
    addOperator(SET_FILTER, "set.filter");
    addOperator(SET_FOLD, "set.fold");
    addOperator(RELATION_JOIN, "rel.join");
    addOperator(RELATION_PRODUCT, "rel.product");
    addOperator(RELATION_TRANSPOSE, "rel.transpose");
    addOperator(RELATION_TCLOSURE, "rel.tclosure");
    addOperator(RELATION_JOIN_IMAGE, "rel.join_image");
    addOperator(RELATION_IDEN, "rel.iden");
    // these operators can be with/without indices
    addOperator(RELATION_GROUP, "rel.group");
    addOperator(RELATION_AGGREGATE, "rel.aggr");
    addOperator(RELATION_PROJECT, "rel.project");
    addIndexedOperator(RELATION_GROUP, "rel.group");
    addIndexedOperator(RELATION_AGGREGATE, "rel.aggr");
    addIndexedOperator(RELATION_PROJECT, "rel.project");
    // set.comprehension is a closure kind
    addClosureKind(SET_COMPREHENSION, "set.comprehension");
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_BAGS))
  {
    // the Boolean sort is a placeholder here since we don't have type info
    // without type annotation
    Sort btype = d_solver->getBooleanSort();
    defineVar("bag.empty", d_solver->mkEmptyBag(d_solver->mkBagSort(btype)));
    addOperator(BAG_UNION_MAX, "bag.union_max");
    addOperator(BAG_UNION_DISJOINT, "bag.union_disjoint");
    addOperator(BAG_INTER_MIN, "bag.inter_min");
    addOperator(BAG_DIFFERENCE_SUBTRACT, "bag.difference_subtract");
    addOperator(BAG_DIFFERENCE_REMOVE, "bag.difference_remove");
    addOperator(BAG_SUBBAG, "bag.subbag");
    addOperator(BAG_COUNT, "bag.count");
    addOperator(BAG_MEMBER, "bag.member");
    addOperator(BAG_DUPLICATE_REMOVAL, "bag.duplicate_removal");
    addOperator(BAG_MAKE, "bag");
    addOperator(BAG_CARD, "bag.card");
    addOperator(BAG_CHOOSE, "bag.choose");
    addOperator(BAG_IS_SINGLETON, "bag.is_singleton");
    addOperator(BAG_FROM_SET, "bag.from_set");
    addOperator(BAG_TO_SET, "bag.to_set");
    addOperator(BAG_MAP, "bag.map");
    addOperator(BAG_FILTER, "bag.filter");
    addOperator(BAG_FOLD, "bag.fold");
    addOperator(BAG_PARTITION, "bag.partition");
    addOperator(TABLE_PRODUCT, "table.product");
    addOperator(BAG_PARTITION, "table.group");
    // these operators can be with/without indices
    addOperator(TABLE_PROJECT, "table.project");
    addOperator(TABLE_AGGREGATE, "table.aggr");
    addOperator(TABLE_JOIN, "table.join");
    addOperator(TABLE_GROUP, "table.group");
    addIndexedOperator(TABLE_PROJECT, "table.project");
    addIndexedOperator(TABLE_AGGREGATE, "table.aggr");
    addIndexedOperator(TABLE_JOIN, "table.join");
    addIndexedOperator(TABLE_GROUP, "table.group");
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

  if (d_logic.isQuantified())
  {
    addQuantifiersOperators();
  }

  if (d_logic.isTheoryEnabled(internal::theory::THEORY_FP))
  {
    defineType("RoundingMode", d_solver->getRoundingModeSort(), true);
    defineType("Float16", d_solver->mkFloatingPointSort(5, 11), true);
    defineType("Float32", d_solver->mkFloatingPointSort(8, 24), true);
    defineType("Float64", d_solver->mkFloatingPointSort(11, 53), true);
    defineType("Float128", d_solver->mkFloatingPointSort(15, 113), true);

    defineVar("RNE", d_solver->mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN));
    defineVar("roundNearestTiesToEven",
              d_solver->mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN));
    defineVar("RNA", d_solver->mkRoundingMode(ROUND_NEAREST_TIES_TO_AWAY));
    defineVar("roundNearestTiesToAway",
              d_solver->mkRoundingMode(ROUND_NEAREST_TIES_TO_AWAY));
    defineVar("RTP", d_solver->mkRoundingMode(ROUND_TOWARD_POSITIVE));
    defineVar("roundTowardPositive",
              d_solver->mkRoundingMode(ROUND_TOWARD_POSITIVE));
    defineVar("RTN", d_solver->mkRoundingMode(ROUND_TOWARD_NEGATIVE));
    defineVar("roundTowardNegative",
              d_solver->mkRoundingMode(ROUND_TOWARD_NEGATIVE));
    defineVar("RTZ", d_solver->mkRoundingMode(ROUND_TOWARD_ZERO));
    defineVar("roundTowardZero", d_solver->mkRoundingMode(ROUND_TOWARD_ZERO));

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

  // builtin symbols of the logic are declared at context level zero, hence
  // we push the outermost scope here
  pushScope(true);
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
      SymbolManager* sm = getSymbolManager();
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
      d_solver->setLogic(d_logic.getLogicString());
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
    return d_solver->mkReal(str);
  }
  return d_solver->mkInteger(str);
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
      p.d_kind = INTERNAL_KIND;
      p.d_expr = d_solver->mkConst(type, "_placeholder_");
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
      p.d_expr = d_solver->mkFiniteFieldElem(rest, type);
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
  if (p.d_kind != NULL_TERM)
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
  Kind kind = NULL_TERM;
  // First phase: process the operator
  if (TraceIsOn("parser"))
  {
    Trace("parser") << "applyParseOp: " << p << " to:" << std::endl;
    for (std::vector<Term>::iterator i = args.begin(); i != args.end(); ++i)
    {
      Trace("parser") << "++ " << *i << std::endl;
    }
  }
  if (!p.d_indices.empty())
  {
    Op op;
    Kind k = getIndexedOpKind(p.d_name);
    if (k == UNDEFINED_KIND)
    {
      // Resolve indexed symbols that cannot be resolved without knowing the
      // type of the arguments. This is currently limited to `to_fp`,
      // `tuple.select`, and `tuple.update`.
      size_t nchildren = args.size();
      if (p.d_name == "to_fp")
      {
        if (nchildren == 1)
        {
          kind = FLOATINGPOINT_TO_FP_FROM_IEEE_BV;
          op = d_solver->mkOp(kind, p.d_indices);
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
            kind = FLOATINGPOINT_TO_FP_FROM_FP;
            op = d_solver->mkOp(kind, p.d_indices);
          }
          else if (t.isInteger() || t.isReal())
          {
            kind = FLOATINGPOINT_TO_FP_FROM_REAL;
            op = d_solver->mkOp(kind, p.d_indices);
          }
          else
          {
            kind = FLOATINGPOINT_TO_FP_FROM_SBV;
            op = d_solver->mkOp(kind, p.d_indices);
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
          ret = d_solver->mkTerm(APPLY_SELECTOR, {dt[0][n].getTerm(), args[0]});
        }
        else
        {
          ret = d_solver->mkTerm(APPLY_UPDATER,
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
      op = d_solver->mkOp(k, p.d_indices);
    }
    return d_solver->mkTerm(op, args);
  }
  else if (p.d_kind != NULL_TERM)
  {
    // It is a special case, e.g. tuple.select or array constant specification.
    // We have to wait until the arguments are parsed to resolve it.
  }
  else if (!p.d_expr.isNull())
  {
    // An explicit operator, e.g. an apply function
    Kind fkind = getKindForFunction(p.d_expr);
    if (fkind != UNDEFINED_KIND)
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
      if (kind == TUPLE_PROJECT || kind == TABLE_PROJECT
          || kind == TABLE_AGGREGATE || kind == TABLE_JOIN
          || kind == TABLE_GROUP || kind == RELATION_GROUP
          || kind == RELATION_AGGREGATE || kind == RELATION_PROJECT)
      {
        std::vector<uint32_t> indices;
        Op op = d_solver->mkOp(kind, indices);
        return d_solver->mkTerm(op, args);
      }
      else if (kind == APPLY_CONSTRUCTOR)
      {
        // tuple application
        return d_solver->mkTuple(args);
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
  if (p.d_kind == INTERNAL_KIND)
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
      Term ret = d_solver->mkConstArray(sort, constVal);
      Trace("parser") << "applyParseOp: return store all " << ret << std::endl;
      return ret;
    }
    else
    {
      // should never happen
      parseError("Could not process internal parsed operator");
    }
  }
  else if (p.d_kind == APPLY_TESTER || p.d_kind == APPLY_UPDATER)
  {
    Term iop = mkIndexedOp(p.d_kind, {p.d_name}, args);
    kind = p.d_kind;
    args.insert(args.begin(), iop);
  }
  else if (p.d_kind != NULL_TERM)
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
    if (kind == EQUAL || kind == DISTINCT)
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
            i = d_solver->mkTerm(TO_REAL, {i});
          }
        }
      }
    }
    if (!strictModeEnabled() && (kind == AND || kind == OR) && args.size() == 1)
    {
      // Unary AND/OR can be replaced with the argument.
      Trace("parser") << "applyParseOp: return unary " << args[0] << std::endl;
      return args[0];
    }
    else if (kind == SUB && args.size() == 1)
    {
      if (isConstInt(args[0]) && args[0].getRealOrIntegerValueSign() > 0)
      {
        // (- n) denotes a negative value
        std::stringstream suminus;
        suminus << "-" << args[0].getIntegerValue();
        Term ret = d_solver->mkInteger(suminus.str());
        Trace("parser") << "applyParseOp: return negative constant " << ret
                        << std::endl;
        return ret;
      }
      Term ret = d_solver->mkTerm(NEG, {args[0]});
      Trace("parser") << "applyParseOp: return uminus " << ret << std::endl;
      return ret;
    }
    else if (kind == DIVISION && args.size() == 2 && isConstInt(args[0])
             && isConstInt(args[1]) && args[1].getRealOrIntegerValueSign() > 0)
    {
      // (/ m n) or (/ (- m) n) denote values in reals
      std::stringstream sdiv;
      sdiv << args[0].getIntegerValue() << "/" << args[1].getIntegerValue();
      Term ret = d_solver->mkReal(sdiv.str());
      Trace("parser") << "applyParseOp: return rational constant " << ret
                      << std::endl;
      return ret;
    }
    else if (kind == FLOATINGPOINT_FP)
    {
      // (fp #bX #bY #bZ) denotes a floating-point value
      if (args.size() != 3)
      {
        parseError("expected 3 arguments to 'fp', got "
                   + std::to_string(args.size()));
      }
      if (isConstBv(args[0]) && isConstBv(args[1]) && isConstBv(args[2]))
      {
        Term ret = d_solver->mkFloatingPoint(args[0], args[1], args[2]);
        Trace("parser") << "applyParseOp: return floating-point value " << ret
                        << std::endl;
        return ret;
      }
    }
    Term ret = d_solver->mkTerm(kind, args);
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
        Term ret = d_solver->mkTerm(HO_APPLY, args);
        Trace("parser") << "applyParseOp: return curry higher order " << ret
                        << std::endl;
        // must curry the partial application
        return ret;
      }
    }
  }
  if (kind == NULL_TERM)
  {
    // should never happen in the new API
    parseError("do not know how to process parse op");
  }
  Trace("parser") << "Try default term construction for kind " << kind
                  << " #args = " << args.size() << "..." << std::endl;
  Term ret = d_solver->mkTerm(kind, args);
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
    t = d_solver->mkArraySort(args[0], args[1]);
  }
  else if (name == "Set" && isTheoryEnabled(internal::theory::THEORY_SETS))
  {
    if (args.size() != 1)
    {
      parseError("Illegal set type.");
    }
    t = d_solver->mkSetSort(args[0]);
  }
  else if (name == "Bag" && isTheoryEnabled(internal::theory::THEORY_BAGS))
  {
    if (args.size() != 1)
    {
      parseError("Illegal bag type.");
    }
    t = d_solver->mkBagSort(args[0]);
  }
  else if (name == "Seq" && !strictModeEnabled()
           && isTheoryEnabled(internal::theory::THEORY_STRINGS))
  {
    if (args.size() != 1)
    {
      parseError("Illegal sequence type.");
    }
    t = d_solver->mkSequenceSort(args[0]);
  }
  else if (name == "Tuple" && !strictModeEnabled())
  {
    t = d_solver->mkTupleSort(args);
  }
  else if (name == "Relation" && !strictModeEnabled())
  {
    Sort tupleSort = d_solver->mkTupleSort(args);
    t = d_solver->mkSetSort(tupleSort);
  }
  else if (name == "Table" && !strictModeEnabled())
  {
    Sort tupleSort = d_solver->mkTupleSort(args);
    t = d_solver->mkBagSort(tupleSort);
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
    ret = d_solver->mkBitVectorSort(n0);
  }
  else if (name == "FiniteField")
  {
    if (numerals.size() != 1)
    {
      parseError("Illegal finite field type.");
    }
    ret = d_solver->mkFiniteFieldSort(numerals.front());
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
    ret = d_solver->mkFloatingPointSort(n0, n1);
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

std::unique_ptr<Command> Smt2State::handlePush(std::optional<uint32_t> nscopes)
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

std::unique_ptr<Command> Smt2State::handlePop(std::optional<uint32_t> nscopes)
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
    return d_solver->mkTrue();
  }
  else if (es.size() == 1)
  {
    return es[0];
  }
  return d_solver->mkTerm(AND, es);
}

bool Smt2State::isConstInt(const Term& t)
{
  return t.getKind() == CONST_INTEGER;
}

bool Smt2State::isConstBv(const Term& t)
{
  return t.getKind() == CONST_BITVECTOR;
}

}  // namespace parser
}  // namespace cvc5

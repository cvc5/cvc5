/*********************                                                        */
/*! \file smt2.cpp
 ** \verbatim
 ** Original author: Christopher L. Conway
 ** Major contributors: Kshitij Bansal, Morgan Deters
 ** Minor contributors (to current version): Andrew Reynolds, Clark Barrett, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Definitions of SMT2 constants.
 **
 ** Definitions of SMT2 constants.
 **/

#include "expr/type.h"
#include "expr/command.h"
#include "parser/parser.h"
#include "parser/smt1/smt1.h"
#include "parser/smt2/smt2.h"
#include "parser/antlr_input.h"

// ANTLR defines these, which is really bad!
#undef true
#undef false

namespace CVC4 {
namespace parser {

Smt2::Smt2(ExprManager* exprManager, Input* input, bool strictMode, bool parseOnly) :
  Parser(exprManager,input,strictMode,parseOnly),
  d_logicSet(false),
  d_nextSygusFun(0) {
  d_unsatCoreNames.push(std::map<Expr, std::string>());
  if( !strictModeEnabled() ) {
    addTheory(Smt2::THEORY_CORE);
  }
}

void Smt2::addArithmeticOperators() {
  Parser::addOperator(kind::PLUS);
  Parser::addOperator(kind::MINUS);
  Parser::addOperator(kind::UMINUS);
  Parser::addOperator(kind::MULT);
  Parser::addOperator(kind::LT);
  Parser::addOperator(kind::LEQ);
  Parser::addOperator(kind::GT);
  Parser::addOperator(kind::GEQ);
}

void Smt2::addBitvectorOperators() {
  Parser::addOperator(kind::BITVECTOR_CONCAT);
  Parser::addOperator(kind::BITVECTOR_AND);
  Parser::addOperator(kind::BITVECTOR_OR);
  Parser::addOperator(kind::BITVECTOR_XOR);
  Parser::addOperator(kind::BITVECTOR_NOT);
  Parser::addOperator(kind::BITVECTOR_NAND);
  Parser::addOperator(kind::BITVECTOR_NOR);
  Parser::addOperator(kind::BITVECTOR_XNOR);
  Parser::addOperator(kind::BITVECTOR_COMP);
  Parser::addOperator(kind::BITVECTOR_MULT);
  Parser::addOperator(kind::BITVECTOR_PLUS);
  Parser::addOperator(kind::BITVECTOR_SUB);
  Parser::addOperator(kind::BITVECTOR_NEG);
  Parser::addOperator(kind::BITVECTOR_UDIV);
  Parser::addOperator(kind::BITVECTOR_UREM);
  Parser::addOperator(kind::BITVECTOR_SDIV);
  Parser::addOperator(kind::BITVECTOR_SREM);
  Parser::addOperator(kind::BITVECTOR_SMOD);
  Parser::addOperator(kind::BITVECTOR_SHL);
  Parser::addOperator(kind::BITVECTOR_LSHR);
  Parser::addOperator(kind::BITVECTOR_ASHR);
  Parser::addOperator(kind::BITVECTOR_ULT);
  Parser::addOperator(kind::BITVECTOR_ULE);
  Parser::addOperator(kind::BITVECTOR_UGT);
  Parser::addOperator(kind::BITVECTOR_UGE);
  Parser::addOperator(kind::BITVECTOR_SLT);
  Parser::addOperator(kind::BITVECTOR_SLE);
  Parser::addOperator(kind::BITVECTOR_SGT);
  Parser::addOperator(kind::BITVECTOR_SGE);
  Parser::addOperator(kind::BITVECTOR_BITOF);
  Parser::addOperator(kind::BITVECTOR_EXTRACT);
  Parser::addOperator(kind::BITVECTOR_REPEAT);
  Parser::addOperator(kind::BITVECTOR_ZERO_EXTEND);
  Parser::addOperator(kind::BITVECTOR_SIGN_EXTEND);
  Parser::addOperator(kind::BITVECTOR_ROTATE_LEFT);
  Parser::addOperator(kind::BITVECTOR_ROTATE_RIGHT);

  Parser::addOperator(kind::INT_TO_BITVECTOR);
  Parser::addOperator(kind::BITVECTOR_TO_NAT);
}

void Smt2::addStringOperators() {
  Parser::addOperator(kind::STRING_CONCAT);
  Parser::addOperator(kind::STRING_LENGTH);
}

void Smt2::addFloatingPointOperators() {
  Parser::addOperator(kind::FLOATINGPOINT_FP);
  Parser::addOperator(kind::FLOATINGPOINT_EQ);
  Parser::addOperator(kind::FLOATINGPOINT_ABS);
  Parser::addOperator(kind::FLOATINGPOINT_NEG);
  Parser::addOperator(kind::FLOATINGPOINT_PLUS);
  Parser::addOperator(kind::FLOATINGPOINT_SUB);
  Parser::addOperator(kind::FLOATINGPOINT_MULT);
  Parser::addOperator(kind::FLOATINGPOINT_DIV);
  Parser::addOperator(kind::FLOATINGPOINT_FMA);
  Parser::addOperator(kind::FLOATINGPOINT_SQRT);
  Parser::addOperator(kind::FLOATINGPOINT_REM);
  Parser::addOperator(kind::FLOATINGPOINT_RTI);
  Parser::addOperator(kind::FLOATINGPOINT_MIN);
  Parser::addOperator(kind::FLOATINGPOINT_MAX);
  Parser::addOperator(kind::FLOATINGPOINT_LEQ);
  Parser::addOperator(kind::FLOATINGPOINT_LT);
  Parser::addOperator(kind::FLOATINGPOINT_GEQ);
  Parser::addOperator(kind::FLOATINGPOINT_GT);
  Parser::addOperator(kind::FLOATINGPOINT_ISN);
  Parser::addOperator(kind::FLOATINGPOINT_ISSN);
  Parser::addOperator(kind::FLOATINGPOINT_ISZ);
  Parser::addOperator(kind::FLOATINGPOINT_ISINF);
  Parser::addOperator(kind::FLOATINGPOINT_ISNAN);
  Parser::addOperator(kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR);
  Parser::addOperator(kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT);
  Parser::addOperator(kind::FLOATINGPOINT_TO_FP_REAL);
  Parser::addOperator(kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR);
  Parser::addOperator(kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR);
  Parser::addOperator(kind::FLOATINGPOINT_TO_UBV);
  Parser::addOperator(kind::FLOATINGPOINT_TO_SBV);
  Parser::addOperator(kind::FLOATINGPOINT_TO_REAL);
}


void Smt2::addTheory(Theory theory) {
  switch(theory) {
  case THEORY_ARRAYS:
    Parser::addOperator(kind::SELECT);
    Parser::addOperator(kind::STORE);
    break;

  case THEORY_BITVECTORS:
    addBitvectorOperators();
    break;

  case THEORY_CORE:
    defineType("Bool", getExprManager()->booleanType());
    defineVar("true", getExprManager()->mkConst(true));
    defineVar("false", getExprManager()->mkConst(false));
    Parser::addOperator(kind::AND);
    Parser::addOperator(kind::DISTINCT);
    Parser::addOperator(kind::EQUAL);
    Parser::addOperator(kind::IFF);
    Parser::addOperator(kind::IMPLIES);
    Parser::addOperator(kind::ITE);
    Parser::addOperator(kind::NOT);
    Parser::addOperator(kind::OR);
    Parser::addOperator(kind::XOR);
    break;

  case THEORY_REALS_INTS:
    defineType("Real", getExprManager()->realType());
    Parser::addOperator(kind::DIVISION);
    Parser::addOperator(kind::TO_INTEGER);
    Parser::addOperator(kind::IS_INTEGER);
    Parser::addOperator(kind::TO_REAL);
    // falling through on purpose, to add Ints part of Reals_Ints
  case THEORY_INTS:
    defineType("Int", getExprManager()->integerType());
    addArithmeticOperators();
    Parser::addOperator(kind::INTS_DIVISION);
    Parser::addOperator(kind::INTS_MODULUS);
    Parser::addOperator(kind::ABS);
    Parser::addOperator(kind::DIVISIBLE);
    break;

  case THEORY_REALS:
    defineType("Real", getExprManager()->realType());
    addArithmeticOperators();
    Parser::addOperator(kind::DIVISION);
    break;

  case THEORY_QUANTIFIERS:
    break;

  case THEORY_SETS:
    addOperator(kind::UNION, "union");
    addOperator(kind::INTERSECTION, "intersection");
    addOperator(kind::SETMINUS, "setminus");
    addOperator(kind::SUBSET, "subset");
    addOperator(kind::MEMBER, "member");
    addOperator(kind::SINGLETON, "singleton");
    addOperator(kind::INSERT, "insert");
    break;

  case THEORY_DATATYPES:
    Parser::addOperator(kind::APPLY_CONSTRUCTOR);
    Parser::addOperator(kind::APPLY_TESTER);
    Parser::addOperator(kind::APPLY_SELECTOR);
    Parser::addOperator(kind::APPLY_SELECTOR_TOTAL);
    break;

  case THEORY_STRINGS:
    defineType("String", getExprManager()->stringType());
    addStringOperators();
    break;

  case THEORY_UF:
    Parser::addOperator(kind::APPLY_UF);
    break;

  case THEORY_FP:
    defineType("RoundingMode", getExprManager()->roundingModeType());
    defineType("Float16", getExprManager()->mkFloatingPointType(5, 11));
    defineType("Float32", getExprManager()->mkFloatingPointType(8, 24));
    defineType("Float64", getExprManager()->mkFloatingPointType(11, 53));
    defineType("Float128", getExprManager()->mkFloatingPointType(15, 113));
    addFloatingPointOperators();
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
    return d_logic.isTheoryEnabled(theory::THEORY_ARRAY);
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
  default:
    std::stringstream ss;
    ss << "internal error: unsupported theory " << theory;
    throw ParserException(ss.str());
  }
}

bool Smt2::logicIsSet() {
  return d_logicSet;
}

void Smt2::reset() {
  d_logicSet = false;
  d_logic = LogicInfo();
  operatorKindMap.clear();
  d_lastNamedTerm = std::pair<Expr, std::string>();
  d_unsatCoreNames = std::stack< std::map<Expr, std::string> >();
  this->Parser::reset();

  d_unsatCoreNames.push(std::map<Expr, std::string>());
  if( !strictModeEnabled() ) {
    addTheory(Smt2::THEORY_CORE);
  }
}

void Smt2::resetAssertions() {
  this->Parser::reset();
}

void Smt2::setLogic(std::string name) {
  if(sygus()) {
    if(name == "Arrays") {
      name = "AUF";
    } else if(name == "Reals") {
      name = "UFLRA";
    } else if(name == "LIA") {
      name = "UFLIA";
    } else if(name == "LRA") {
      name = "UFLRA";
    } else if(name == "LIRA") {
      name = "UFLIRA";
    } else if(name == "BV") {
      name = "UFBV";
    } else {
      std::stringstream ss;
      ss << "Unknown SyGuS background logic `" << name << "'";
      parseError(ss.str());
    }
  }

  d_logicSet = true;
  if(logicIsForced()) {
    d_logic = getForcedLogic();
  } else {
    d_logic = name;
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
  }

  if(d_logic.isTheoryEnabled(theory::THEORY_ARRAY)) {
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

}/* Smt2::setLogic() */

void Smt2::setInfo(const std::string& flag, const SExpr& sexpr) {
  // TODO: ???
}

void Smt2::setOption(const std::string& flag, const SExpr& sexpr) {
  // TODO: ???
}

void Smt2::checkThatLogicIsSet() {
  if( ! logicIsSet() ) {
    if(strictModeEnabled()) {
      parseError("set-logic must appear before this point.");
    } else {
      if(sygus()) {
        setLogic("LIA");
      } else {
        warning("No set-logic command was given before this point.");
        warning("CVC4 will assume the non-standard ALL_SUPPORTED logic.");
        warning("Consider setting a stricter logic for (likely) better performance.");
        warning("To suppress this warning in the future use (set-logic ALL_SUPPORTED).");

        setLogic("ALL_SUPPORTED");
      }

      Command* c = new SetBenchmarkLogicCommand("ALL_SUPPORTED");
      c->setMuted(true);
      preemptCommand(c);
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



 void Smt2::defineSygusFuns() {
  // only define each one once
  while(d_nextSygusFun < d_sygusFuns.size()) {
    std::pair<std::string, Expr> p = d_sygusFuns[d_nextSygusFun];
    std::string fun = p.first;
    Debug("parser-sygus") << "Sygus : define fun " << fun << std::endl;
    Expr eval = p.second;
    FunctionType evalType = eval.getType();
    std::vector<Type> argTypes = evalType.getArgTypes();
    Type rangeType = evalType.getRangeType();
    Debug("parser-sygus") << "...eval type : " << evalType << ", #args=" << argTypes.size() << std::endl;

    // first make the function type
    std::vector<Expr> sygusVars;
    std::vector<Type> funType;
    for(size_t j = 1; j < argTypes.size(); ++j) {
      funType.push_back(argTypes[j]);
      std::stringstream ss;
      ss << fun << "_v_" << j;
      sygusVars.push_back(getExprManager()->mkBoundVar(ss.str(), argTypes[j]));
    }
    Type funt = getExprManager()->mkFunctionType(funType, rangeType);
    Debug("parser-sygus") << "...eval function type : " << funt << std::endl;

    // copy the bound vars
    /*
    std::vector<Expr> sygusVars;
    //std::vector<Type> types;
    for(size_t i = 0; i < d_sygusVars.size(); ++i) {
      std::stringstream ss;
      ss << d_sygusVars[i];
      Type type = d_sygusVars[i].getType();
      sygusVars.push_back(getExprManager()->mkBoundVar(ss.str(), type));
      //types.push_back(type);
    }
    Debug("parser-sygus") << "...made vars, #vars=" << sygusVars.size() << std::endl;
    */

    //Type t = getExprManager()->mkFunctionType(types, rangeType);
    //Debug("parser-sygus") << "...function type : " << t << std::endl;

    Expr lambda = mkFunction(fun, funt, ExprManager::VAR_FLAG_DEFINED);
    Debug("parser-sygus") << "...made function : " << lambda << std::endl;
    std::vector<Expr> applyv;
    Expr funbv = getExprManager()->mkBoundVar(std::string("f") + fun, argTypes[0]);
    d_sygusFunSymbols.push_back(funbv);
    applyv.push_back(eval);
    applyv.push_back(funbv);
    for(size_t i = 0; i < sygusVars.size(); ++i) {
      applyv.push_back(sygusVars[i]);
    }
    Expr apply = getExprManager()->mkExpr(kind::APPLY_UF, applyv);
    Debug("parser-sygus") << "...made apply " << apply << std::endl;
    Command* cmd = new DefineFunctionCommand(fun, lambda, sygusVars, apply);
    preemptCommand(cmd);

    ++d_nextSygusFun;
  }
}

void Smt2::mkSygusDatatype( CVC4::Datatype& dt, std::vector<CVC4::Expr>& ops,
                            std::vector<std::string>& cnames, std::vector< std::vector< CVC4::Type > >& cargs ) {
  for( unsigned i=0; i<cnames.size(); i++ ){
    std::string name = dt.getName() + "_" + cnames[i];
    std::string testerId("is-");
    testerId.append(name);
    checkDeclaration(name, CHECK_UNDECLARED, SYM_VARIABLE);
    checkDeclaration(testerId, CHECK_UNDECLARED, SYM_VARIABLE);
    CVC4::DatatypeConstructor c(name, testerId, ops[i] );
    for( unsigned j=0; j<cargs[i].size(); j++ ){
      std::stringstream sname;
      sname << name << "_" << j;
      c.addArg(sname.str(), cargs[i][j]);
    }
    dt.addConstructor(c);
  }
}

// i is index in datatypes/ops
// j is index is datatype
Expr Smt2::getSygusAssertion( std::vector<DatatypeType>& datatypeTypes, std::vector< std::vector<Expr> >& ops,
                              std::map<DatatypeType, Expr>& evals, std::vector<Expr>& terms,
                              Expr eval, const Datatype& dt, size_t i, size_t j ) {
  const DatatypeConstructor& ctor = dt[j];
  Debug("parser-sygus") << "Sygus : process constructor " << j << " : " << dt[j] << std::endl;
  std::vector<Expr> bvs, extraArgs;
  for(size_t k = 0; k < ctor.getNumArgs(); ++k) {
    std::string vname = "v_" + ctor[k].getName();
    Expr bv = getExprManager()->mkBoundVar(vname, SelectorType(ctor[k].getType()).getRangeType());
    bvs.push_back(bv);
    extraArgs.push_back(bv);
  }
  bvs.insert(bvs.end(), terms[0].begin(), terms[0].end());
  Expr bvl = getExprManager()->mkExpr(kind::BOUND_VAR_LIST, bvs);
  Debug("parser-sygus") << "...made bv list " << bvl << std::endl;
  std::vector<Expr> patv;
  patv.push_back(eval);
  std::vector<Expr> applyv;
  applyv.push_back(ctor.getConstructor());
  applyv.insert(applyv.end(), extraArgs.begin(), extraArgs.end());
  for(size_t k = 0; k < applyv.size(); ++k) {
  }
  Expr cpatv = getExprManager()->mkExpr(kind::APPLY_CONSTRUCTOR, applyv);
  Debug("parser-sygus") << "...made eval ctor apply " << cpatv << std::endl;
  patv.push_back(cpatv);
  patv.insert(patv.end(), terms[0].begin(), terms[0].end());
  Expr evalApply = getExprManager()->mkExpr(kind::APPLY_UF, patv);
  Debug("parser-sygus") << "...made eval apply " << evalApply << std::endl;
  std::vector<Expr> builtApply;
  for(size_t k = 0; k < extraArgs.size(); ++k) {
    std::vector<Expr> patvb;
    patvb.push_back(evals[DatatypeType(extraArgs[k].getType())]);
    patvb.push_back(extraArgs[k]);
    patvb.insert(patvb.end(), terms[0].begin(), terms[0].end());
    builtApply.push_back(getExprManager()->mkExpr(kind::APPLY_UF, patvb));
  }
  for(size_t k = 0; k < builtApply.size(); ++k) {
  }
  Expr builtTerm;
  //if( ops[i][j].getKind() == kind::BUILTIN ){
  if( !builtApply.empty() ){
    if( ops[i][j].getKind() != kind::BUILTIN ){
      builtTerm = getExprManager()->mkExpr(kind::APPLY, ops[i][j], builtApply);
    }else{
      builtTerm = getExprManager()->mkExpr(ops[i][j], builtApply);
    }
  }else{
    builtTerm = ops[i][j];
  }
  Debug("parser-sygus") << "...made built term " << builtTerm << std::endl;
  Expr assertion = getExprManager()->mkExpr(evalApply.getType().isBoolean() ? kind::IFF : kind::EQUAL, evalApply, builtTerm);
  Expr pattern = getExprManager()->mkExpr(kind::INST_PATTERN, evalApply);
  pattern = getExprManager()->mkExpr(kind::INST_PATTERN_LIST, pattern);
  assertion = getExprManager()->mkExpr(kind::FORALL, bvl, assertion, pattern);
  Debug("parser-sygus") << "...made assertion " << assertion << std::endl;

  //linearize multiplication if possible
  if( builtTerm.getKind()==kind::MULT ){
    for(size_t k = 0; k < ctor.getNumArgs(); ++k) {
      Type at = SelectorType(ctor[k].getType()).getRangeType();
      if( at.isDatatype() ){
        DatatypeType atd = (DatatypeType)SelectorType(ctor[k].getType()).getRangeType();
        Debug("parser-sygus") << "Argument " << k << " " << atd << std::endl;
        std::vector<DatatypeType>::iterator itd = std::find( datatypeTypes.begin(), datatypeTypes.end(), atd );
        if( itd!=datatypeTypes.end() ){
          Debug("parser-sygus2") << "Exists in datatypeTypes." << std::endl;
          unsigned index = itd-datatypeTypes.begin();
          Debug("parser-sygus2") << "index = " << index << std::endl;
          bool isConst = true;
          for( unsigned cc = 0; cc < ops[index].size(); cc++ ){
            Debug("parser-sygus2") << "ops[" << cc << "]=" << ops[index][cc] << std::endl;
            if( ops[index][cc].getKind() != kind::CONST_RATIONAL ){
              isConst = false;
              break;
            }
          }
          if( isConst ){
            Debug("parser-sygus") << "Linearize multiplication " << ctor << " based on argument " << k << std::endl;
            const Datatype & atdd = atd.getDatatype();
            std::vector<Expr> assertions;
            std::vector<Expr> nbvs;
            for( unsigned a=0; a<bvl.getNumChildren(); a++ ){
              if( a!=k ){
                nbvs.push_back( bvl[a] );
              }
            }
            Expr nbvl = getExprManager()->mkExpr( kind::BOUND_VAR_LIST, nbvs );
            for( unsigned cc = 0; cc < ops[index].size(); cc++ ){
              //Make new assertion based on partially instantiating existing
              applyv[k+1] = getExprManager()->mkExpr(kind::APPLY_CONSTRUCTOR, atdd[cc].getConstructor());
              Debug("parser-sygus") << "applyv " << applyv[k+1] << std::endl;
              cpatv = getExprManager()->mkExpr(kind::APPLY_CONSTRUCTOR, applyv);
              Debug("parser-sygus") << "cpatv " << cpatv << std::endl;
              patv[1] = cpatv;
              evalApply = getExprManager()->mkExpr(kind::APPLY_UF, patv);
              Debug("parser-sygus") << "evalApply " << evalApply << std::endl;
              builtApply[k] = ops[index][cc];
              Debug("parser-sygus") << "builtApply " << builtApply[k] << std::endl;
              builtTerm = getExprManager()->mkExpr(ops[i][j], builtApply);
              Debug("parser-sygus") << "builtTerm " << builtTerm << std::endl;
              Expr eassertion = getExprManager()->mkExpr(evalApply.getType().isBoolean() ? kind::IFF : kind::EQUAL, evalApply, builtTerm);
              Expr epattern = getExprManager()->mkExpr(kind::INST_PATTERN, evalApply);
              epattern = getExprManager()->mkExpr(kind::INST_PATTERN_LIST, epattern);
              eassertion = getExprManager()->mkExpr(kind::FORALL, nbvl, eassertion, epattern);
              assertions.push_back( eassertion );
            }
            assertion = assertions.size()==1 ? assertions[0] : getExprManager()->mkExpr( kind::AND, assertions );
            Debug("parser-sygus") << "...(linearized) assertion is: " << assertion << std::endl;
          }
        }
      }
    }
  }
  return assertion;
}


}/* CVC4::parser namespace */
}/* CVC4 namespace */

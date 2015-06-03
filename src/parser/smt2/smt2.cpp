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

#include "util/bitvector.h"

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
  addOperator(kind::STRING_CONCAT, "str.++");
  addOperator(kind::STRING_LENGTH, "str.len");
  addOperator(kind::STRING_SUBSTR, "str.substr" );
  addOperator(kind::STRING_STRCTN, "str.contains" );
  addOperator(kind::STRING_CHARAT, "str.at" );
  addOperator(kind::STRING_STRIDOF, "str.indexof" );
  addOperator(kind::STRING_STRREPL, "str.replace" );
  addOperator(kind::STRING_PREFIX, "str.prefixof" );
  addOperator(kind::STRING_SUFFIX, "str.suffixof" );
  addOperator(kind::STRING_ITOS, "int.to.str" );
  addOperator(kind::STRING_STOI, "str.to.int" );
  addOperator(kind::STRING_U16TOS, "u16.to.str" );
  addOperator(kind::STRING_STOU16, "str.to.u16" );
  addOperator(kind::STRING_U32TOS, "u32.to.str" );
  addOperator(kind::STRING_STOU32, "str.to.u32" );
  addOperator(kind::STRING_IN_REGEXP, "str.in.re");
  addOperator(kind::STRING_TO_REGEXP, "str.to.re");
  addOperator(kind::REGEXP_CONCAT, "re.++");
  addOperator(kind::REGEXP_UNION, "re.union");
  addOperator(kind::REGEXP_INTER, "re.inter");
  addOperator(kind::REGEXP_STAR, "re.*");
  addOperator(kind::REGEXP_PLUS, "re.+");
  addOperator(kind::REGEXP_OPT, "re.opt");
  addOperator(kind::REGEXP_RANGE, "re.range");
  addOperator(kind::REGEXP_LOOP, "re.loop");
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

  Parser::addOperator(kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR);
  Parser::addOperator(kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT);
  Parser::addOperator(kind::FLOATINGPOINT_TO_FP_REAL);
  Parser::addOperator(kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR);
  Parser::addOperator(kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR);
  Parser::addOperator(kind::FLOATINGPOINT_TO_UBV);
  Parser::addOperator(kind::FLOATINGPOINT_TO_SBV);
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
    defineType("Int", getExprManager()->integerType());
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

void Smt2::mkSygusDefaultGrammar( const Type& range, Expr& bvl, const std::string& fun, std::vector<CVC4::Datatype>& datatypes,
                                  std::vector<Type>& sorts, std::vector< std::vector<Expr> >& ops, std::vector<Expr> sygus_vars ) {

  Debug("parser-sygus") << "Construct default grammar for " << fun << " " << range << std::endl;

  std::stringstream ssb;
  ssb << fun << "_Bool";
  std::string dbname = ssb.str();

  std::stringstream ss;
  ss << fun << "_" << range;
  std::string dname = ss.str();
  datatypes.push_back(Datatype(dname));
  ops.push_back(std::vector<Expr>());
  std::vector<std::string> cnames;
  std::vector<std::vector<CVC4::Type> > cargs;
  //variables
  for( unsigned i=0; i<sygus_vars.size(); i++ ){
    if( sygus_vars[i].getType()==range ){
      std::stringstream ss;
      ss << sygus_vars[i];
      Debug("parser-sygus") << "...add for variable " << ss.str() << std::endl;
      ops.back().push_back( sygus_vars[i] );
      cnames.push_back( ss.str() );
      cargs.push_back( std::vector< CVC4::Type >() );
    }
  }
  //constants
  std::vector< Expr > consts;
  mkSygusConstantsForType( range, consts );
  for( unsigned i=0; i<consts.size(); i++ ){
    std::stringstream ss;
    ss << consts[i];
    Debug("parser-sygus") << "...add for constant " << ss.str() << std::endl;
    ops.back().push_back( consts[i] );
    cnames.push_back( ss.str() );
    cargs.push_back( std::vector< CVC4::Type >() );
  }
  //ITE
  CVC4::Kind k = kind::ITE;
  Debug("parser-sygus") << "...add for " << k << std::endl;
  ops.back().push_back(getExprManager()->operatorOf(k));
  cnames.push_back( kind::kindToString(k) );
  cargs.push_back( std::vector< CVC4::Type >() );
  cargs.back().push_back(mkUnresolvedType(ssb.str()));
  cargs.back().push_back(mkUnresolvedType(ss.str()));
  cargs.back().push_back(mkUnresolvedType(ss.str()));

  if( range.isInteger() ){
    for( unsigned i=0; i<2; i++ ){
      CVC4::Kind k = i==0 ? kind::PLUS : kind::MINUS;
      Debug("parser-sygus") << "...add for " << k << std::endl;
      ops.back().push_back(getExprManager()->operatorOf(k));
      cnames.push_back(kind::kindToString(k));
      cargs.push_back( std::vector< CVC4::Type >() );
      cargs.back().push_back(mkUnresolvedType(ss.str()));
      cargs.back().push_back(mkUnresolvedType(ss.str()));
    }
  }else{
    std::stringstream sserr;
    sserr << "Don't know default Sygus grammar for type " << range << std::endl;
    parseError(sserr.str());
  }
  Debug("parser-sygus") << "...make datatype " << datatypes.back() << std::endl;
  datatypes.back().setSygus( range, bvl, true, true );
  mkSygusDatatype( datatypes.back(), ops.back(), cnames, cargs );
  sorts.push_back( range );

  //Boolean type
  datatypes.push_back(Datatype(dbname));
  ops.push_back(std::vector<Expr>());
  cnames.clear();
  cargs.clear();
  for( unsigned i=0; i<4; i++ ){
    CVC4::Kind k = i==0 ? kind::NOT : ( i==1 ? kind::AND : ( i==2 ? kind::OR : kind::EQUAL ) );
    Debug("parser-sygus") << "...add for " << k << std::endl;
    ops.back().push_back(getExprManager()->operatorOf(k));
    cnames.push_back(kind::kindToString(k));
    cargs.push_back( std::vector< CVC4::Type >() );
    if( k==kind::NOT ){
      cargs.back().push_back(mkUnresolvedType(ssb.str()));
    }else if( k==kind::AND || k==kind::OR ){
      cargs.back().push_back(mkUnresolvedType(ssb.str()));
      cargs.back().push_back(mkUnresolvedType(ssb.str()));
    }else if( k==kind::EQUAL ){
      cargs.back().push_back(mkUnresolvedType(ss.str()));
      cargs.back().push_back(mkUnresolvedType(ss.str()));
    }
  }
  if( range.isInteger() ){
    CVC4::Kind k = kind::LEQ;
    Debug("parser-sygus") << "...add for " << k << std::endl;
    ops.back().push_back(getExprManager()->operatorOf(k));
    cnames.push_back(kind::kindToString(k));
    cargs.push_back( std::vector< CVC4::Type >() );
    cargs.back().push_back(mkUnresolvedType(ss.str()));
    cargs.back().push_back(mkUnresolvedType(ss.str()));
  }
  Debug("parser-sygus") << "...make datatype " << datatypes.back() << std::endl;
  Type btype = getExprManager()->booleanType();
  datatypes.back().setSygus( btype, bvl, true, true );
  mkSygusDatatype( datatypes.back(), ops.back(), cnames, cargs );
  sorts.push_back( btype );

  Debug("parser-sygus") << "...finished make default grammar for " << fun << " " << range << std::endl;
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
  }
  //TODO : others?
}

bool Smt2::pushSygusDatatypeDef( Type t, std::string& dname,
                                  std::vector< CVC4::Datatype >& datatypes,
                                  std::vector< CVC4::Type>& sorts,
                                  std::vector< std::vector<CVC4::Expr> >& ops,
                                  std::vector< std::vector<std::string> >& cnames,
                                  std::vector< std::vector< std::vector< CVC4::Type > > >& cargs ){
  sorts.push_back(t);
  datatypes.push_back(Datatype(dname));
  ops.push_back(std::vector<Expr>());
  cnames.push_back(std::vector<std::string>());
  cargs.push_back(std::vector<std::vector<CVC4::Type> >());
  return true;
}

bool Smt2::popSygusDatatypeDef( std::vector< CVC4::Datatype >& datatypes,
                                 std::vector< CVC4::Type>& sorts,
                                 std::vector< std::vector<CVC4::Expr> >& ops,
                                 std::vector< std::vector<std::string> >& cnames,
                                 std::vector< std::vector< std::vector< CVC4::Type > > >& cargs ){
  sorts.pop_back();
  datatypes.pop_back();
  ops.pop_back();
  cnames.pop_back();
  cargs.pop_back();
  return true;
}

Type Smt2::processSygusNestedGTerm( int sub_dt_index, std::string& sub_dname, std::vector< CVC4::Datatype >& datatypes,
                                    std::vector< CVC4::Type>& sorts,
                                    std::vector< std::vector<CVC4::Expr> >& ops,
                                    std::vector< std::vector<std::string> >& cnames,
                                    std::vector< std::vector< std::vector< CVC4::Type > > >& cargs,
                                    std::map< CVC4::Type, CVC4::Type >& sygus_to_builtin, Type sub_ret ) {
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
    if( sop.getKind() != kind::BUILTIN && sop.isConst() ){
      curr_t = sop.getType();
      Debug("parser-sygus") << ": it is constant with type " << sop.getType() << std::endl;
    }else{
      std::vector< Expr > children;
      if( sop.getKind() != kind::BUILTIN ){
        children.push_back( sop );
      }
      for( unsigned i=0; i<cargs[sub_dt_index][0].size(); i++ ){
        Type bt = sygus_to_builtin[cargs[sub_dt_index][0][i]];
        Debug("parser-sygus") << ":  type elem " << i << " " << cargs[sub_dt_index][0][i] << " " << bt << std::endl;
        children.push_back( mkVar("x", bt) );
      }
      Kind sk = sop.getKind() != kind::BUILTIN ? kind::APPLY : getExprManager()->operatorToKind(sop);
      Debug("parser-sygus") << ": operator " << sop << " with " << sop.getKind() << " " << sk << std::endl;
      Expr e = getExprManager()->mkExpr( sk, children );
      Debug("parser-sygus") << ": constructed " << e << ", which has type " << e.getType() << std::endl;
      curr_t = e.getType();
    }
    sorts[sub_dt_index] = curr_t;
    sygus_to_builtin[t] = curr_t;
  }else{
    Debug("parser-sygus") << "simple argument " << t << std::endl;
    Debug("parser-sygus") << "...removing " << datatypes.back().getName() << std::endl;
    //otherwise, datatype was unecessary
    //pop argument datatype definition
    popSygusDatatypeDef( datatypes, sorts, ops, cnames, cargs );
  }
  return t;
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
    Type funt;
    if( !funType.empty() ){
      funt = getExprManager()->mkFunctionType(funType, rangeType);
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
    }else{
      funt = rangeType;
    }
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
  for( int i=0; i<(int)cnames.size(); i++ ){
    bool is_dup = false;
    //FIXME : should allow multiple operators with different sygus type arguments
    //        for now, just ignore them (introduces incompleteness).
    for( int j=0; j<i; j++ ){
      if( ops[i]==ops[j] ){
        is_dup = true;
        break;
      }
      /*
      if( ops[i]==ops[j] && cargs[i].size()==cargs[j].size() ){
        is_dup = true;
        for( unsigned k=0; k<cargs[i].size(); k++ ){
          if( cargs[i][k]!=cargs[j][k] ){
            is_dup = false;
            break;
          }
        }
      }
      */
    }
    if( is_dup ){
      Debug("parser-sygus") << "--> Duplicate gterm : " << ops[i] << " at " << i << std::endl;
      ops.erase( ops.begin() + i, ops.begin() + i + 1 );
      cnames.erase( cnames.begin() + i, cnames.begin() + i + 1 );
      cargs.erase( cargs.begin() + i, cargs.begin() + i + 1 );
      i--;
    }else{
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
      Debug("parser-sygus") << "--> Add constructor " << cnames[i] << " to " << dt.getName() << std::endl;
      dt.addConstructor(c);
    }
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
  if( !terms[0].isNull() ){
    bvs.insert(bvs.end(), terms[0].begin(), terms[0].end());
  }
  Expr bvl;
  if( !bvs.empty() ){
    bvl = getExprManager()->mkExpr(kind::BOUND_VAR_LIST, bvs);
  }
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
  if( !terms[0].isNull() ){
    patv.insert(patv.end(), terms[0].begin(), terms[0].end());
  }
  Expr evalApply = getExprManager()->mkExpr(kind::APPLY_UF, patv);
  Debug("parser-sygus") << "...made eval apply " << evalApply << std::endl;
  std::vector<Expr> builtApply;
  for(size_t k = 0; k < extraArgs.size(); ++k) {
    std::vector<Expr> patvb;
    patvb.push_back(evals[DatatypeType(extraArgs[k].getType())]);
    patvb.push_back(extraArgs[k]);
    if( !terms[0].isNull() ){
      patvb.insert(patvb.end(), terms[0].begin(), terms[0].end());
    }
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
  if( !bvl.isNull() ){
    Expr pattern = getExprManager()->mkExpr(kind::INST_PATTERN, evalApply);
    pattern = getExprManager()->mkExpr(kind::INST_PATTERN_LIST, pattern);
    assertion = getExprManager()->mkExpr(kind::FORALL, bvl, assertion, pattern);
  }
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

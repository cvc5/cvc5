/*********************                                                        */
/*! \file smt2.cpp
 ** \verbatim
 ** Original author: Christopher L. Conway
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Clark Barrett, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
  d_logicSet(false) {
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
    addOperator(kind::SUBSET, "subseteq");
    addOperator(kind::MEMBER, "in");
    addOperator(kind::SET_SINGLETON, "setenum");
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
  default:
    std::stringstream ss;
    ss << "internal error: unsupported theory " << theory;
    throw ParserException(ss.str());
  }
}

bool Smt2::logicIsSet() {
  return d_logicSet;
}

void Smt2::setLogic(const std::string& name) {
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
}/* Smt2::setLogic() */

void Smt2::setInfo(const std::string& flag, const SExpr& sexpr) {
  // TODO: ???
}

void Smt2::setOption(const std::string& flag, const SExpr& sexpr) {
  // TODO: ???
}

void Smt2::checkThatLogicIsSet() {
  if( ! logicIsSet() ) {
    if( strictModeEnabled() ) {
      parseError("set-logic must appear before this point.");
    } else {
      warning("No set-logic command was given before this point.");
      warning("CVC4 will assume the non-standard ALL_SUPPORTED logic.");
      warning("Consider setting a stricter logic for (likely) better performance.");
      warning("To suppress this warning in the future use (set-logic ALL_SUPPORTED).");

      setLogic("ALL_SUPPORTED");

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

}/* CVC4::parser namespace */
}/* CVC4 namespace */

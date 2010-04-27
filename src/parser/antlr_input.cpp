/*********************                                                        */
/** antlr_input.cpp
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A super-class for ANTLR-generated input language parsers
 **/

#include <limits.h>
#include <antlr3.h>

#include "antlr_input.h"
#include "bounded_token_buffer.h"
#include "bounded_token_factory.h"
#include "memory_mapped_input_buffer.h"
#include "parser_exception.h"
#include "parser_state.h"

#include "util/output.h"
#include "util/Assert.h"
#include "expr/command.h"
#include "expr/type.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::kind;

namespace CVC4 {
namespace parser {

AntlrInput::AntlrInput(ExprManager* exprManager, const std::string& filename, unsigned int lookahead, bool useMmap) :
    Input(exprManager, filename),
    d_lookahead(lookahead),
    d_lexer(NULL),
    d_parser(NULL),
    d_tokenStream(NULL) {

  if( useMmap ) {
    d_input = MemoryMappedInputBufferNew(filename);
  } else {
    d_input = antlr3AsciiFileStreamNew((pANTLR3_UINT8) filename.c_str());
  }
  if( d_input == NULL ) {
    throw ParserException("Couldn't open file: " + filename);
  }
}

/*
AntlrParser::AntlrParser(ExprManager* exprManager, std::istream& input, const std::string& name, unsigned int lookahead)
  Parser(exprManager,name),
  d_lookahead(lookahead) {

}
*/

AntlrInput::AntlrInput(ExprManager* exprManager, const std::string& input, const std::string& name, unsigned int lookahead) :
  Input(exprManager,name),
  d_lookahead(lookahead),
  d_lexer(NULL),
  d_parser(NULL),
  d_tokenStream(NULL) {
  char* inputStr = strdup(input.c_str());
  char* nameStr = strdup(name.c_str());
  if( inputStr==NULL || nameStr==NULL ) {
    throw ParserException("Couldn't initialize string input: '" + input + "'");
  }
  d_input = antlr3NewAsciiStringInPlaceStream((pANTLR3_UINT8)inputStr,input.size(),(pANTLR3_UINT8)nameStr);
  if( d_input == NULL ) {
    throw ParserException("Couldn't create input stream for string: '" + input + "'");
  }
}

AntlrInput::~AntlrInput() {
  d_tokenStream->free(d_tokenStream);
  d_input->close(d_input);
}

pANTLR3_INPUT_STREAM AntlrInput::getInputStream() {
  return d_input;
}

pANTLR3_COMMON_TOKEN_STREAM AntlrInput::getTokenStream() {
  return d_tokenStream;
}

void AntlrInput::lexerError(pANTLR3_BASE_RECOGNIZER recognizer) {
  pANTLR3_LEXER lexer = (pANTLR3_LEXER)(recognizer->super);
  AlwaysAssert(lexer!=NULL);
  ParserState *parserState = (ParserState*)(lexer->super);
  AlwaysAssert(parserState!=NULL);

  // Call the error display routine
  parserState->parseError("Error finding next token.");
}

void AntlrInput::parseError(const std::string& message)
    throw (ParserException) {
  Debug("parser") << "Throwing exception: "
      << getParserState()->getFilename() << ":"
      << d_lexer->getLine(d_lexer) << "."
      << d_lexer->getCharPositionInLine(d_lexer) << ": "
      << message << endl;
  throw ParserException(message, getParserState()->getFilename(),
                        d_lexer->getLine(d_lexer),
                        d_lexer->getCharPositionInLine(d_lexer));
}


void AntlrInput::setLexer(pANTLR3_LEXER pLexer) {
  d_lexer = pLexer;

  pANTLR3_TOKEN_FACTORY pTokenFactory = d_lexer->rec->state->tokFactory;
  if( pTokenFactory != NULL ) {
    pTokenFactory->close(pTokenFactory);
  }

  /* 2*lookahead should be sufficient, but we give ourselves some breathing room. */
  pTokenFactory = BoundedTokenFactoryNew(d_input, 2*d_lookahead);
  if( pTokenFactory == NULL ) {
    throw ParserException("Couldn't create token factory.");
  }
  d_lexer->rec->state->tokFactory = pTokenFactory;

  pBOUNDED_TOKEN_BUFFER buffer = BoundedTokenBufferSourceNew(d_lookahead, d_lexer->rec->state->tokSource);
  if( buffer == NULL ) {
    throw ParserException("Couldn't create token buffer.");
  }

  d_tokenStream = buffer->commonTstream;

  // ANTLR isn't using super, AFAICT.
  d_lexer->super = getParserState();
  // Override default lexer error reporting
  d_lexer->rec->reportError = &lexerError;
}

void AntlrInput::setParser(pANTLR3_PARSER pParser) {
  d_parser = pParser;
  // ANTLR isn't using super, AFAICT.
  // We could also use @parser::context to add a field to the generated parser, but then
  // it would have to be declared separately in every input's grammar and we'd have to
  // pass it in as an address anyway.
  d_parser->super = getParserState();
//  d_parser->rec->match = &match;
  d_parser->rec->reportError = &reportError;
  /* Don't try to recover from a parse error. */
  // [chris 4/5/2010] Not clear on why this cast is necessary, but I get an error if I remove it.
  d_parser->rec->recoverFromMismatchedToken =
      (void* (*)(ANTLR3_BASE_RECOGNIZER_struct*, ANTLR3_UINT32, ANTLR3_BITSET_LIST_struct*))
      d_parser->rec->mismatch;
}


}/* CVC4::parser namespace */
}/* CVC4 namespace */

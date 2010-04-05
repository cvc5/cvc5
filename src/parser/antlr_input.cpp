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

#include <iostream>
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

void *
AntlrInput::recoverFromMismatchedToken(pANTLR3_BASE_RECOGNIZER recognizer,
                                       ANTLR3_UINT32 ttype,
                                       pANTLR3_BITSET_LIST follow) {

  pANTLR3_PARSER parser = (pANTLR3_PARSER) (recognizer->super);
  pANTLR3_INT_STREAM is = parser->tstream->istream;
  void *matchedSymbol;


  // Create an exception if we need one
  //
  if(recognizer->state->exception == NULL) {
    antlr3RecognitionExceptionNew(recognizer);
  }

  if(recognizer->mismatchIsUnwantedToken(recognizer, is, ttype) == ANTLR3_TRUE) {
    recognizer->state->exception->type = ANTLR3_UNWANTED_TOKEN_EXCEPTION;
    recognizer->state->exception->message
        = (void*)ANTLR3_UNWANTED_TOKEN_EXCEPTION_NAME;
  }

  if(recognizer->mismatchIsMissingToken(recognizer, is, follow)) {
    matchedSymbol = recognizer->getMissingSymbol(recognizer, is,
                                                 recognizer->state->exception,
                                                 ttype, follow);
    recognizer->state->exception->type = ANTLR3_MISSING_TOKEN_EXCEPTION;
    recognizer->state->exception->message = (void*)ANTLR3_MISSING_TOKEN_EXCEPTION_NAME;
    recognizer->state->exception->token = matchedSymbol;
    recognizer->state->exception->expecting = ttype;
  }

  reportError(recognizer);
  Unreachable("reportError should have thrown exception in AntlrInput::recoverFromMismatchedToken");
}

void AntlrInput::reportError(pANTLR3_BASE_RECOGNIZER recognizer) {
  pANTLR3_EXCEPTION ex = recognizer->state->exception;
  pANTLR3_UINT8 * tokenNames = recognizer->state->tokenNames;
  stringstream ss;
//  std::string msg;

  // Signal we are in error recovery now
  recognizer->state->errorRecovery = ANTLR3_TRUE;

  // Indicate this recognizer had an error while processing.
  recognizer->state->errorCount++;

  // Call the builtin error formatter
  // recognizer->displayRecognitionError(recognizer, recognizer->state->tokenNames);

  /* This switch statement is adapted from antlr3baserecognizer.c:displayRecognitionError in libantlr3c.
   * TODO: Make error messages more useful, maybe by including more expected tokens and information
   * about the current token. */
  switch(ex->type) {
  case ANTLR3_UNWANTED_TOKEN_EXCEPTION:

    // Indicates that the recognizer was fed a token which seems to be
    // spurious input. We can detect this when the token that follows
    // this unwanted token would normally be part of the syntactically
    // correct stream. Then we can see that the token we are looking at
    // is just something that should not be there and throw this exception.
    //
    if(tokenNames == NULL) {
      ss << "Unexpected token." ;
    } else {
      if(ex->expecting == ANTLR3_TOKEN_EOF) {
        ss << "Expected end of file.";
      } else {
        ss << "Expected " << tokenNames[ex->expecting]
           << ", found '" << tokenText((pANTLR3_COMMON_TOKEN)ex->token) << "'.";
      }
    }
    break;

  case ANTLR3_MISSING_TOKEN_EXCEPTION:

    // Indicates that the recognizer detected that the token we just
    // hit would be valid syntactically if preceded by a particular
    // token. Perhaps a missing ';' at line end or a missing ',' in an
    // expression list, and such like.
    //
    if(tokenNames == NULL) {
      ss << "Missing token (" << ex->expecting << ").";
    } else {
      if(ex->expecting == ANTLR3_TOKEN_EOF) {
        ss << "Missing end of file marker.";
      } else {
        ss << "Missing " << tokenNames[ex->expecting] << ".";
      }
    }
    break;

  case ANTLR3_RECOGNITION_EXCEPTION:

    // Indicates that the recognizer received a token
    // in the input that was not predicted. This is the basic exception type
    // from which all others are derived. So we assume it was a syntax error.
    // You may get this if there are not more tokens and more are needed
    // to complete a parse for instance.
    //
    ss <<"Syntax error.";
    break;

  case ANTLR3_MISMATCHED_TOKEN_EXCEPTION:

    // We were expecting to see one thing and got another. This is the
    // most common error if we could not detect a missing or unwanted token.
    // Here you can spend your efforts to
    // derive more useful error messages based on the expected
    // token set and the last token and so on. The error following
    // bitmaps do a good job of reducing the set that we were looking
    // for down to something small. Knowing what you are parsing may be
    // able to allow you to be even more specific about an error.
    //
    if(tokenNames == NULL) {
      ss << "Syntax error.";
    } else {
      if(ex->expecting == ANTLR3_TOKEN_EOF) {
        ss << "Expected end of file.";
      } else {
        ss << "Expected " << tokenNames[ex->expecting] << ".";
      }
    }
    break;

  case ANTLR3_NO_VIABLE_ALT_EXCEPTION:
    // We could not pick any alt decision from the input given
    // so god knows what happened - however when you examine your grammar,
    // you should. It means that at the point where the current token occurred
    // that the DFA indicates nowhere to go from here.
    //
    ss << "Unexpected token: '" << tokenText((pANTLR3_COMMON_TOKEN)ex->token) << "'.";
    break;

  case ANTLR3_MISMATCHED_SET_EXCEPTION:

  {
    ANTLR3_UINT32 count;
    ANTLR3_UINT32 bit;
    ANTLR3_UINT32 size;
    ANTLR3_UINT32 numbits;
    pANTLR3_BITSET errBits;

    // This means we were able to deal with one of a set of
    // possible tokens at this point, but we did not see any
    // member of that set.
    //
    ss << "Unexpected input: '" << tokenText((pANTLR3_COMMON_TOKEN)ex->token)
       << "'. Expected one of: ";

    // What tokens could we have accepted at this point in the
    // parse?
    //
    count = 0;
    errBits = antlr3BitsetLoad(ex->expectingSet);
    numbits = errBits->numBits(errBits);
    size = errBits->size(errBits);

    if(size > 0) {
      // However many tokens we could have dealt with here, it is usually
      // not useful to print ALL of the set here. I arbitrarily chose 8
      // here, but you should do whatever makes sense for you of course.
      // No token number 0, so look for bit 1 and on.
      //
      for(bit = 1; bit < numbits && count < 8 && count < size; bit++) {
        // TODO: This doesn;t look right - should be asking if the bit is set!!
        //
        if(tokenNames[bit]) {
          if( count++ > 0 ) {
            ss << ", ";
          }
          ss << tokenNames[bit];
        }
      }
    } else {
      Unreachable("Parse error with empty set of expected tokens.");
    }
  }
    break;

  case ANTLR3_EARLY_EXIT_EXCEPTION:

    // We entered a loop requiring a number of token sequences
    // but found a token that ended that sequence earlier than
    // we should have done.
    //
    ss << "Sequence terminated early by token: '"
       << tokenText((pANTLR3_COMMON_TOKEN)ex->token) << "'.";
    break;

  default:

    // We don't handle any other exceptions here, but you can
    // if you wish. If we get an exception that hits this point
    // then we are just going to report what we know about the
    // token.
    //
    Unhandled("Unexpected exception in parser.");
    break;
  }

  // Now get ready to throw an exception
  pANTLR3_PARSER parser = (pANTLR3_PARSER)(recognizer->super);
  AlwaysAssert(parser!=NULL);
  ParserState *parserState = (ParserState*)(parser->super);
  AlwaysAssert(parserState!=NULL);

  // Call the error display routine
  parserState->parseError(ss.str());
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
}

void AntlrInput::setParser(pANTLR3_PARSER pParser) {
  d_parser = pParser;
  // ANTLR isn't using super, AFAICT.
  // We could also use @parser::context to add a field to the generated parser, but then
  // it would have to be declared separately in every input's grammar and we'd have to
  // pass it in as an address anyway.
  d_parser->super = getParserState();
  d_parser->rec->reportError = &reportError;
  d_parser->rec->recoverFromMismatchedToken = &recoverFromMismatchedToken;
}


}/* CVC4::parser namespace */
}/* CVC4 namespace */

/*********************                                                        */
/*! \file antlr_input.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Kshitij Bansal, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A super-class for ANTLR-generated input language parsers.
 **
 ** A super-class for ANTLR-generated input language parsers
 **/

#include "parser/antlr_input.h"

#include <antlr3.h>
#include <limits.h>
#include <stdint.h>

#include "base/output.h"
#include "expr/type.h"
#include "parser/antlr_line_buffered_input.h"
#include "parser/bounded_token_buffer.h"
#include "parser/bounded_token_factory.h"
#include "parser/cvc/cvc_input.h"
#include "parser/input.h"
#include "parser/memory_mapped_input_buffer.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"
#include "parser/smt2/smt2_input.h"
#include "parser/smt2/sygus_input.h"
#include "parser/tptp/tptp_input.h"
#include "smt/command.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::kind;

namespace CVC4 {
namespace parser {

// These functions exactly wrap the antlr3 source inconsistencies.
// These are the only location CVC4_ANTLR3_OLD_INPUT_STREAM ifdefs appear.
// No other sanity checking happens;
pANTLR3_INPUT_STREAM newAntlr3BufferedStream(std::istream& input,
                                             const std::string& name,
                                             LineBuffer* line_buffer);
pANTLR3_INPUT_STREAM newAntlr3FileStream(const std::string& name);
pANTLR3_INPUT_STREAM newAntrl3InPlaceStream(pANTLR3_UINT8 basep,
                                            uint32_t size,
                                            const std::string& name);

pANTLR3_INPUT_STREAM newAntlr3BufferedStream(std::istream& input,
                                             const std::string& name,
                                             LineBuffer* line_buffer) {
  pANTLR3_INPUT_STREAM inputStream = NULL;
  pANTLR3_UINT8 name_duplicate = (pANTLR3_UINT8) strdup(name.c_str());

#ifdef CVC4_ANTLR3_OLD_INPUT_STREAM
  inputStream =
      antlr3LineBufferedStreamNew(input, 0, name_duplicate, line_buffer);
#else /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  inputStream = antlr3LineBufferedStreamNew(input, ANTLR3_ENC_8BIT,
                                            name_duplicate, line_buffer);
#endif /* CVC4_ANTLR3_OLD_INPUT_STREAM */

  free(name_duplicate);
  return inputStream;
}

pANTLR3_INPUT_STREAM newAntlr3FileStream(const std::string& name){
  pANTLR3_INPUT_STREAM input = NULL;
  pANTLR3_UINT8 name_duplicate = (pANTLR3_UINT8) strdup(name.c_str());

  // libantlr3c v3.2 isn't source-compatible with v3.4
#ifdef CVC4_ANTLR3_OLD_INPUT_STREAM
  input = antlr3AsciiFileStreamNew(name_duplicate);
#else /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  input = antlr3FileStreamNew(name_duplicate, ANTLR3_ENC_8BIT);
#endif /* CVC4_ANTLR3_OLD_INPUT_STREAM */

  free(name_duplicate);
  return input;
}


pANTLR3_INPUT_STREAM newAntrl3InPlaceStream(pANTLR3_UINT8 basep,
                                            uint32_t size,
                                            const std::string& name){
  pANTLR3_UINT8 name_duplicate = (pANTLR3_UINT8) strdup(name.c_str());
  pANTLR3_INPUT_STREAM inputStream = NULL;
  /* Create an ANTLR input backed by the buffer. */
#ifdef CVC4_ANTLR3_OLD_INPUT_STREAM
  inputStream =
    antlr3NewAsciiStringInPlaceStream(basep, size, name_duplicate);
#else /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  inputStream =
    antlr3StringStreamNew(basep, ANTLR3_ENC_8BIT, size,
                          name_duplicate);
#endif /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  free(name_duplicate);
  return inputStream;
}

AntlrInputStream::AntlrInputStream(std::string name, pANTLR3_INPUT_STREAM input,
                                   bool fileIsTemporary,
                                   pANTLR3_UINT8 inputString,
                                   LineBuffer* line_buffer)
    : InputStream(name, fileIsTemporary),
      d_input(input),
      d_inputString(inputString),
      d_line_buffer(line_buffer) {
  assert( input != NULL );
  input->fileName = input->strFactory->newStr8(input->strFactory, (pANTLR3_UINT8)name.c_str());
}

AntlrInputStream::~AntlrInputStream() {
  d_input->free(d_input);
  if(d_inputString != NULL){
    free(d_inputString);
  }
  if (d_line_buffer != NULL) {
    delete d_line_buffer;
  }
}

pANTLR3_INPUT_STREAM AntlrInputStream::getAntlr3InputStream() const {
  return d_input;
}



AntlrInputStream*
AntlrInputStream::newFileInputStream(const std::string& name,
                                     bool useMmap)
{
#ifdef _WIN32
  if(useMmap) {
    useMmap = false;
  }
#endif
  pANTLR3_INPUT_STREAM input = NULL;
  if(useMmap) {
    input = MemoryMappedInputBufferNew(name);
  } else {
    input = newAntlr3FileStream(name);
  }
  if(input == NULL) {
    throw InputStreamException("Couldn't open file: " + name);
  }
  return new AntlrInputStream(name, input, false, NULL, NULL);
}


AntlrInputStream*
AntlrInputStream::newStreamInputStream(std::istream& input,
                                       const std::string& name,
                                       bool lineBuffered)
{
  pANTLR3_INPUT_STREAM inputStream = NULL;
  pANTLR3_UINT8 inputStringCopy = NULL;
  LineBuffer* line_buffer = NULL;

  if(lineBuffered) {
    line_buffer = new LineBuffer(&input);
    inputStream = newAntlr3BufferedStream(input, name, line_buffer);
  } else {

    // Since these are all NULL on entry, realloc will be called
    char *basep = NULL, *boundp = NULL, *cp = NULL;
    /* 64KB seems like a reasonable default size. */
    size_t bufSize = 0x10000;

    /* Keep going until we can't go no more. */
    while( !input.eof() && !input.fail() ) {

      if( cp == boundp ) {
        /* We ran out of room in the buffer. Realloc at double the size. */
        ptrdiff_t offset = cp - basep;
        basep = (char *) realloc(basep, bufSize);
        if( basep == NULL ) {
          throw InputStreamException("Failed buffering input stream: " + name);
        }
        cp = basep + offset;
        boundp = basep + bufSize;
        bufSize *= 2;
      }

      /* Read as much as we have room for. */
      input.read( cp, boundp - cp );
      cp += input.gcount();
    }

    /* Make sure the fail bit didn't get set. */
    if( !input.eof() ) {
      throw InputStreamException("Stream input failed: " + name);
    }
    ptrdiff_t offset = cp - basep;
    assert(offset >= 0);
    assert(offset <= std::numeric_limits<uint32_t>::max());
    inputStringCopy = (pANTLR3_UINT8)basep;
    inputStream = newAntrl3InPlaceStream(inputStringCopy, (uint32_t) offset, name);
  }

  if( inputStream == NULL ) {
    throw InputStreamException("Couldn't initialize input: " + name);
  }

  return new AntlrInputStream(name, inputStream, false, inputStringCopy,
                              line_buffer);
}


AntlrInputStream*
AntlrInputStream::newStringInputStream(const std::string& input,
                                       const std::string& name)
{
  size_t input_size = input.size();
  assert(input_size <= std::numeric_limits<uint32_t>::max());

  // Ownership of input_duplicate  is transferred to the AntlrInputStream.
  pANTLR3_UINT8 input_duplicate = (pANTLR3_UINT8) strdup(input.c_str());

  if( input_duplicate == NULL ) {
    throw InputStreamException("Couldn't initialize string input: '" + input + "'");
  }

  pANTLR3_INPUT_STREAM inputStream = newAntrl3InPlaceStream(input_duplicate, (uint32_t)input_size, name);
  if( inputStream==NULL ) {
    throw InputStreamException("Couldn't initialize string input: '" + input + "'");
  }
  return new AntlrInputStream(name, inputStream, false, input_duplicate, NULL);
}

AntlrInput* AntlrInput::newInput(InputLanguage lang, AntlrInputStream& inputStream) {
  using namespace language::input;

  AntlrInput* input;

  switch(lang) {
  case LANG_CVC4: {
    input = new CvcInput(inputStream);
    break;
  }

  case LANG_SYGUS:
  case LANG_SYGUS_V2: input = new SygusInput(inputStream); break;

  case LANG_TPTP:
    input = new TptpInput(inputStream);
    break;

  default:
    if (language::isInputLang_smt2(lang))
    {
      input = new Smt2Input(inputStream);
    }
    else
    {
      std::stringstream ss;
      ss << "unable to detect input file format, try --lang ";
      throw InputStreamException(ss.str());
    }
  }

  return input;
}

AntlrInput::AntlrInput(AntlrInputStream& inputStream, unsigned int lookahead) :
    Input(inputStream),
    d_lookahead(lookahead),
    d_lexer(NULL),
    d_parser(NULL),
    d_antlr3InputStream( inputStream.getAntlr3InputStream() ),
    d_tokenBuffer(NULL) {
}

/*
AntlrParser::AntlrParser(ExprManager* exprManager, std::istream& input, const std::string& name, unsigned int lookahead)
  Parser(exprManager,name),
  d_lookahead(lookahead) {

}
*/

/*
AntlrInput::Input(ExprManager* exprManager, const std::string& input, const std::string& name, unsigned int lookahead) :
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
  d_inputStream = antlr3NewAsciiStringInPlaceStream((pANTLR3_UINT8)inputStr,input.size(),(pANTLR3_UINT8)nameStr);
  if( d_inputStream == NULL ) {
    throw ParserException("Couldn't create input stream for string: '" + input + "'");
  }

}
*/

AntlrInput::~AntlrInput() {
  BoundedTokenBufferFree(d_tokenBuffer);
}

pANTLR3_COMMON_TOKEN_STREAM AntlrInput::getTokenStream() {
  return d_tokenBuffer->commonTstream;
}

void AntlrInput::lexerError(pANTLR3_BASE_RECOGNIZER recognizer) {
  pANTLR3_LEXER lexer = (pANTLR3_LEXER)(recognizer->super);
  assert(lexer!=NULL);
  Parser *parser = (Parser*)(lexer->super);
  assert(parser!=NULL);
  AntlrInput *input = (AntlrInput*) parser->getInput();
  assert(input!=NULL);

  /* Call the error display routine *if* there's not already a 
   * parse error pending.  If a parser error is pending, this
   * error is probably less important, so we just drop it. */
  if( input->d_parser->rec->state->error == ANTLR3_FALSE ) {
    input->parseError("Error finding next token.");
  }
}

void AntlrInput::warning(const std::string& message) {
  Warning() << getInputStream()->getName() << ':' << d_lexer->getLine(d_lexer) << '.' << d_lexer->getCharPositionInLine(d_lexer) << ": " << message << endl;
}



/**
 * characters considered part of a simple symbol in SMTLIB.
 *
 * TODO: Ideally this code shouldn't be smtlib specific (should work
 * with CVC language too), but this per-language specialization has
 * been left for a later point.
 */
inline bool isSimpleChar(char ch) {
  return isalnum(ch) || (strchr("~!@$%^&*_-+=<>.?/", ch) != NULL);
}

size_t wholeWordMatch(string input, string pattern, bool (*isWordChar)(char)) {
  size_t st = 0;
  size_t N = input.size();
  while(st < N) {
    while( st < N && (*isWordChar)(input[st])  == false ) st++;
    size_t en = st;
    while(en + 1 < N && (*isWordChar)(input[en + 1]) == true) en++;
    if(en - st + 1 == pattern.size()) {
      bool match = true;
      for(size_t i = 0; match && i < pattern.size(); ++i) {
        match &= (pattern[i] == input[st+i]);
      }
      if(match == true) {
        return st;
      }
    }
    st = en + 1;
  }
  return string::npos;
}

/**
 * Gets part of original input and tries to visually hint where the
 * error might be.
 *
 * Something like:
 *
 *   ...nd (= alpha beta) (= beta delta))
 *                                ^
 *
 * Implementation (as on 2014/04/24):
 *
 * > if suggested pointer by lexer is under a "simple char", move to
 *   start of the word and print pointer there.
 *
 * > in the other case, it tries to find the nearest word in the error
 *   message passed along. if it can't find it, we don't add this
 *   visual hint, as experimentally position suggested by lexer was
 *   found to be totally unhelpful. (TODO: fix this upstream to
 *   improve)
 */
std::string parseErrorHelper(const char* lineStart, int charPositionInLine, const std::string& message)
{
  // Is it a multi-line message
  bool multilineMessage = (message.find('\n') != string::npos);
  // Useful only if it is a multi-line message
  int firstLineEnd = message.find('\n');

  std::ostringstream ss, slicess;

  // Keep first line of message
  if(multilineMessage) {
    ss << message.substr(0, firstLineEnd) << endl << endl;
  } else {
    ss << message << endl << endl;
  }

  int posSliceStart = (charPositionInLine - 50 <= 0) ? 0 : charPositionInLine - 50 + 5;
  int posSliceEnd = posSliceStart + 70;
  int caretPos = 0;
  int caretPosExtra = 0; // for inital intendation, epilipses etc.

  ss << "  "; caretPosExtra += 2;
  if(posSliceStart > 0) {
    ss << "..."; caretPosExtra += 3;
  }

  for(int i = posSliceStart; lineStart[i] != '\n'; ++i) {
    if(i == posSliceEnd) {
      ss << "...";
      break;
    }
    if(i < charPositionInLine) { caretPos++; }

    if(!isprint(lineStart[i])) {
      // non-printable character, something wrong, bail out
      return message;
    }

    ss << (lineStart[i]);
    slicess << (lineStart[i]);
  }

  // adjust position of caret, based on slice and message
  {
    int caretPosOrig = caretPos;
    string slice = slicess.str();
    if(isSimpleChar(slice[caretPos])) {
      // if alphanumeric, try to go to beginning of word/number
      while(caretPos > 0 && isSimpleChar(slice[caretPos - 1])) { --caretPos; }
      if(caretPos == 0 && posSliceStart > 0) {
        // reached start and this is not really the start? bail out
        return message;
      } else {
        // likely it is also in original message? if so, very likely
        // we found the right place
        string word = slice.substr(caretPos, (caretPosOrig - caretPos + 1));
        size_t matchLoc = wholeWordMatch(message, word, isSimpleChar);
        Debug("friendlyparser") << "[friendlyparser] matchLoc = " << matchLoc << endl;
        if( matchLoc != string::npos ) {
          Debug("friendlyparser") << "[friendlyparser] Feeling good." << std::endl;
        }
      }
    } else {
      bool foundCaretPos = false;

      for(int tries = 0; tries < 2 && caretPos > 0 && !foundCaretPos; ++tries) {
        // go to nearest alphanumeric string (before current position),
        // see if that word can be found in original message. If so,
        // point to that, else keep pointer where it was.
        int nearestWordEn = caretPos - 1;
        while(nearestWordEn > 0 && !isSimpleChar(slice[nearestWordEn])) {
          --nearestWordEn;
        }
        if(isSimpleChar(slice[nearestWordEn])) {
          int nearestWordSt = nearestWordEn;
          while(nearestWordSt > 0 && isSimpleChar(slice[nearestWordSt - 1])) {
            --nearestWordSt;
          }
          string word = slice.substr(nearestWordSt, (nearestWordEn - nearestWordSt + 1));
          size_t matchLoc = wholeWordMatch(message, word, isSimpleChar);
          Debug("friendlyparser") << "[friendlyparser] nearest word = " << word << std::endl;
          Debug("friendlyparser") << "[friendlyparser] matchLoc = " << matchLoc << endl;
          if( matchLoc != string::npos ) {
            Debug("friendlyparser") << "[friendlyparser] strong evidence that caret should be at "
                                    << nearestWordSt << std::endl;
            foundCaretPos = true;
          }
          caretPos = nearestWordSt;
        }
      }
      if( !foundCaretPos) {
        // this doesn't look good. caret generally getting printed
        // at unhelpful positions. improve upstream?
        return message;
      }
    }
    caretPos += caretPosExtra;
  }// end of caret position computation/heuristics

  ss << std::endl;
  while( caretPos-- > 0 ) {
    ss << ' ';
  }
  ss << '^' << endl;
  if(multilineMessage) {
     ss << message.substr(firstLineEnd, message.size() - firstLineEnd);;
  }
  return ss.str();
}

void AntlrInput::parseError(const std::string& message, bool eofException)
{
  string updatedMessage = parseErrorHelper((const char*)d_antlr3InputStream->getLineBuf(d_antlr3InputStream),
                                           d_lexer->getCharPositionInLine(d_lexer),
                                           message);

  Debug("parser") << "Throwing exception: "
      << (const char*)d_lexer->rec->state->tokSource->fileName->chars << ":"
      << d_lexer->getLine(d_lexer) << "."
      << d_lexer->getCharPositionInLine(d_lexer) << ": "
      << updatedMessage << endl;
  if(eofException) {
    throw ParserEndOfFileException(message,
                                   (const char*)d_lexer->rec->state->tokSource->fileName->chars,
                                   d_lexer->getLine(d_lexer),
                                   d_lexer->getCharPositionInLine(d_lexer));
  } else {
    throw ParserException(updatedMessage,
                          (const char*)d_lexer->rec->state->tokSource->fileName->chars,
                          d_lexer->getLine(d_lexer),
                          d_lexer->getCharPositionInLine(d_lexer));
  }
}


void AntlrInput::setAntlr3Lexer(pANTLR3_LEXER pLexer) {
  d_lexer = pLexer;

  pANTLR3_TOKEN_FACTORY pTokenFactory = d_lexer->rec->state->tokFactory;
  if( pTokenFactory != NULL ) {
    pTokenFactory->close(pTokenFactory);
  }

  /* 2*lookahead should be sufficient, but we give ourselves some breathing room. */
  pTokenFactory = BoundedTokenFactoryNew(d_antlr3InputStream, 2*d_lookahead);
  if( pTokenFactory == NULL ) {
    throw InputStreamException("Couldn't create token factory.");
  }
  d_lexer->rec->state->tokFactory = pTokenFactory;

  pBOUNDED_TOKEN_BUFFER buffer = BoundedTokenBufferSourceNew(d_lookahead, d_lexer->rec->state->tokSource);
  if( buffer == NULL ) {
    throw InputStreamException("Couldn't create token buffer.");
  }

  d_tokenBuffer = buffer;

  // Override default lexer error reporting
  d_lexer->rec->reportError = &lexerError;
  // Override default nextToken function, just to prevent exceptions escaping.
  d_lexer->rec->state->tokSource->nextToken = &nextToken;
}

void AntlrInput::setParser(Parser& parser) {
  // ANTLR isn't using super in the lexer or the parser, AFAICT.
  // We could also use @lexer/parser::context to add a field to the generated
  // objects, but then it would have to be declared separately in every
  // language's grammar and we'd have to in the address of the field anyway.
  d_lexer->super = &parser;
  d_parser->super = &parser;
}

void AntlrInput::setAntlr3Parser(pANTLR3_PARSER pParser) {
  d_parser = pParser;
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

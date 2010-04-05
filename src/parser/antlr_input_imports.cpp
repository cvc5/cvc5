/*
 * The functions in this file are based on implementations in libantlr3c,
 * with only minor CVC4-specific changes.
 */

// [The "BSD licence"]
// Copyright (c) 2005-2009 Jim Idle, Temporal Wave LLC
// http://www.temporal-wave.com
// http://www.linkedin.com/in/jimidle
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
// 3. The name of the author may not be used to endorse or promote products
//    derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
// IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
// OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
// IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
// NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
// THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#include <antlr3.h>
#include <sstream>

#include "antlr_input.h"
#include "parser_state.h"
#include "util/Assert.h"

using namespace std;

namespace CVC4 {
namespace parser {

/// Match current input symbol against ttype.  Upon error, do one token
/// insertion or deletion if possible.
/// To turn off single token insertion or deletion error
/// recovery, override mismatchRecover() and have it call
/// plain mismatch(), which does not recover.  Then any error
/// in a rule will cause an exception and immediate exit from
/// rule.  Rule would recover by resynchronizing to the set of
/// symbols that can follow rule ref.
///
/* *** CVC4 NOTE ***
 * This function is unchanged from its libantlr3c version. It is included
 * here to avoid an exception-handling bug caused by libantlr3c being compiled
 * without support for C++ exceptions by default.
 */
void *
AntlrInput::match(pANTLR3_BASE_RECOGNIZER recognizer, ANTLR3_UINT32 ttype,
      pANTLR3_BITSET_LIST follow) {
  pANTLR3_PARSER parser;
  pANTLR3_TREE_PARSER tparser;
  pANTLR3_INT_STREAM is;
  void * matchedSymbol;

  switch(recognizer->type) {
  case ANTLR3_TYPE_PARSER:

    parser = (pANTLR3_PARSER)(recognizer->super);
    tparser = NULL;
    is = parser->tstream->istream;

    break;

  case ANTLR3_TYPE_TREE_PARSER:

    tparser = (pANTLR3_TREE_PARSER)(recognizer->super);
    parser = NULL;
    is = tparser->ctnstream->tnstream->istream;

    break;

  default:

    ANTLR3_FPRINTF(
                   stderr,
                   "Base recognizer function 'match' called by unknown parser type - provide override for this function\n");
    return ANTLR3_FALSE;

    break;
  }

  // Pick up the current input token/node for assignment to labels
  //
  matchedSymbol = recognizer->getCurrentInputSymbol(recognizer, is);

  if(is->_LA(is, 1) == ttype) {
    // The token was the one we were told to expect
    //
    is->consume(is); // Consume that token from the stream
    recognizer->state->errorRecovery = ANTLR3_FALSE; // Not in error recovery now (if we were)
    recognizer->state->failed = ANTLR3_FALSE; // The match was a success
    return matchedSymbol; // We are done
  }

  // We did not find the expected token type, if we are backtracking then
  // we just set the failed flag and return.
  //
  if(recognizer->state->backtracking > 0) {
    // Backtracking is going on
    //
    recognizer->state->failed = ANTLR3_TRUE;
    return matchedSymbol;
  }

  // We did not find the expected token and there is no backtracking
  // going on, so we mismatch, which creates an exception in the recognizer exception
  // stack.
  //
  matchedSymbol = recognizer->recoverFromMismatchedToken(recognizer, ttype,
                                                         follow);
  return matchedSymbol;
}

/// Attempt to recover from a single missing or extra token.
///
/// EXTRA TOKEN
///
/// LA(1) is not what we are looking for.  If LA(2) has the right token,
/// however, then assume LA(1) is some extra spurious token.  Delete it
/// and LA(2) as if we were doing a normal match(), which advances the
/// input.
///
/// MISSING TOKEN
///
/// If current token is consistent with what could come after
/// ttype then it is ok to "insert" the missing token, else throw
/// exception For example, Input "i=(3;" is clearly missing the
/// ')'.  When the parser returns from the nested call to expr, it
/// will have call chain:
///
///    stat -> expr -> atom
///
/// and it will be trying to match the ')' at this point in the
/// derivation:
///
///       => ID '=' '(' INT ')' ('+' atom)* ';'
///                          ^
/// match() will see that ';' doesn't match ')' and report a
/// mismatched token error.  To recover, it sees that LA(1)==';'
/// is in the set of tokens that can follow the ')' token
/// reference in rule atom.  It can assume that you forgot the ')'.
///
/// The exception that was passed in, in the java implementation is
/// sorted in the recognizer exception stack in the C version. To 'throw' it we set the
/// error flag and rules cascade back when this is set.
///
/* *** CVC4 NOTE ***
 * This function has been basically gutted to remove any attempts to recover
 * from a syntax error.
 */
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


/// Report a recognition problem.
///
/// This method sets errorRecovery to indicate the parser is recovering
/// not parsing.  Once in recovery mode, no errors are generated.
/// To get out of recovery mode, the parser must successfully match
/// a token (after a resync).  So it will go:
///
///             1. error occurs
///             2. enter recovery mode, report error
///             3. consume until token found in resynch set
///             4. try to resume parsing
///             5. next match() will reset errorRecovery mode
///
/// If you override, make sure to update errorCount if you care about that.
///
/* *** CVC4 NOTE ***
 * This function is has been modified in not-completely-trivial ways from its
 * libantlr3c implementation to support more informative error messages and to
 * invoke the error reporting mechanism of the AntlrInput class instead of the
 * default error printer.
 */
void AntlrInput::reportError(pANTLR3_BASE_RECOGNIZER recognizer) {
  pANTLR3_EXCEPTION ex = recognizer->state->exception;
  pANTLR3_UINT8 * tokenNames = recognizer->state->tokenNames;
  stringstream ss;

  // Signal we are in error recovery now
  recognizer->state->errorRecovery = ANTLR3_TRUE;

  // Indicate this recognizer had an error while processing.
  recognizer->state->errorCount++;

  // Call the builtin error formatter
  // recognizer->displayRecognitionError(recognizer, recognizer->state->tokenNames);

  /* TODO: Make error messages more useful, maybe by including more expected tokens and information
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

} // namespace parser
} // namespace CVC4

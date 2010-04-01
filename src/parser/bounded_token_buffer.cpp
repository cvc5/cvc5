/// \file 
/// Default implementation of CommonTokenStream
///

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

#include <antlr3commontoken.h>
#include <antlr3lexer.h>
#include <antlr3tokenstream.h>

#include "parser/bounded_token_buffer.h"
#include "util/Assert.h"

namespace CVC4 {
namespace parser {

#ifdef	ANTLR3_WINDOWS
#pragma warning( disable : 4100 )
#endif

// COMMON_TOKEN_STREAM API
//
static void					setTokenTypeChannel	(pANTLR3_COMMON_TOKEN_STREAM cts, ANTLR3_UINT32 ttype, ANTLR3_UINT32 channel);
static void					discardTokenType	(pANTLR3_COMMON_TOKEN_STREAM cts, ANTLR3_INT32 ttype);
static void					discardOffChannel	(pANTLR3_COMMON_TOKEN_STREAM cts, ANTLR3_BOOLEAN discard);
static pANTLR3_VECTOR		getTokens			(pANTLR3_COMMON_TOKEN_STREAM cts);
static pANTLR3_LIST			getTokenRange		(pANTLR3_COMMON_TOKEN_STREAM cts, ANTLR3_UINT32 start, ANTLR3_UINT32 stop);
static pANTLR3_LIST			getTokensSet		(pANTLR3_COMMON_TOKEN_STREAM cts, ANTLR3_UINT32 start, ANTLR3_UINT32 stop, pANTLR3_BITSET types);
static pANTLR3_LIST			getTokensList		(pANTLR3_COMMON_TOKEN_STREAM cts, ANTLR3_UINT32 start, ANTLR3_UINT32 stop, pANTLR3_LIST list);
static pANTLR3_LIST			getTokensType		(pANTLR3_COMMON_TOKEN_STREAM cts, ANTLR3_UINT32 start, ANTLR3_UINT32 stop, ANTLR3_UINT32 type);

// TOKEN_STREAM API 
//
static pANTLR3_COMMON_TOKEN tokLT				(pANTLR3_TOKEN_STREAM ts, ANTLR3_INT32 k);
static pANTLR3_COMMON_TOKEN dbgTokLT			(pANTLR3_TOKEN_STREAM ts, ANTLR3_INT32 k);
static pANTLR3_COMMON_TOKEN get					(pANTLR3_TOKEN_STREAM ts, ANTLR3_UINT32 i);
static pANTLR3_TOKEN_SOURCE getTokenSource		(pANTLR3_TOKEN_STREAM ts);
static void					setTokenSource		(pANTLR3_TOKEN_STREAM ts, pANTLR3_TOKEN_SOURCE tokenSource);
static pANTLR3_STRING	    toString			(pANTLR3_TOKEN_STREAM ts);
static pANTLR3_STRING	    toStringSS			(pANTLR3_TOKEN_STREAM ts, ANTLR3_UINT32 start, ANTLR3_UINT32 stop);
static pANTLR3_STRING	    toStringTT			(pANTLR3_TOKEN_STREAM ts, pANTLR3_COMMON_TOKEN start, pANTLR3_COMMON_TOKEN stop);
static void					setDebugListener	(pANTLR3_TOKEN_STREAM ts, pANTLR3_DEBUG_EVENT_LISTENER debugger);

// INT STREAM API
//
static void					consume						(pANTLR3_INT_STREAM is);
static void					dbgConsume					(pANTLR3_INT_STREAM is);
static ANTLR3_UINT32	    _LA							(pANTLR3_INT_STREAM is, ANTLR3_INT32 i);
static ANTLR3_UINT32	    dbgLA						(pANTLR3_INT_STREAM is, ANTLR3_INT32 i);
static ANTLR3_MARKER	    mark						(pANTLR3_INT_STREAM is);
static ANTLR3_MARKER	    dbgMark						(pANTLR3_INT_STREAM is);
static void					release						(pANTLR3_INT_STREAM is, ANTLR3_MARKER mark);
static ANTLR3_UINT32	    size						(pANTLR3_INT_STREAM is);
static ANTLR3_MARKER		tindex						(pANTLR3_INT_STREAM is);
static void					rewindStream				(pANTLR3_INT_STREAM is, ANTLR3_MARKER marker);
static void					dbgRewindStream				(pANTLR3_INT_STREAM is, ANTLR3_MARKER marker);
static void					rewindLast					(pANTLR3_INT_STREAM is);
static void					dbgRewindLast				(pANTLR3_INT_STREAM is);
static void					seek						(pANTLR3_INT_STREAM is, ANTLR3_MARKER index);
static void					dbgSeek						(pANTLR3_INT_STREAM is, ANTLR3_MARKER index);
static pANTLR3_STRING		getSourceName				(pANTLR3_INT_STREAM is);
static pANTLR3_COMMON_TOKEN LB							(pANTLR3_COMMON_TOKEN_STREAM tokenStream, ANTLR3_INT32 i);

static pANTLR3_COMMON_TOKEN nextToken(pBOUNDED_TOKEN_BUFFER buffer);
static pANTLR3_COMMON_TOKEN simpleEmit        (pANTLR3_LEXER lexer);

void
BoundedTokenBufferFree(pBOUNDED_TOKEN_BUFFER buffer) {
  buffer->commonTstream->free(buffer->commonTstream);
  ANTLR3_FREE(buffer->tokenBuffer);
  ANTLR3_FREE(buffer);
}

/*ANTLR3_API pANTLR3_COMMON_TOKEN_STREAM
antlr3CommonTokenDebugStreamSourceNew(ANTLR3_UINT32 hint, pANTLR3_TOKEN_SOURCE source, pANTLR3_DEBUG_EVENT_LISTENER debugger)
{
    pANTLR3_COMMON_TOKEN_STREAM	stream;

	// Create a standard token stream
	//
	stream = antlr3CommonTokenStreamSourceNew(hint, source);

	// Install the debugger object
	//
	stream->tstream->debugger = debugger;

	// Override standard token stream methods with debugging versions
	//
	stream->tstream->initialStreamState	= ANTLR3_FALSE;

	stream->tstream->_LT				= dbgTokLT;

	stream->tstream->istream->consume		= dbgConsume;
	stream->tstream->istream->_LA			= dbgLA;
	stream->tstream->istream->mark			= dbgMark;
	stream->tstream->istream->rewind		= dbgRewindStream;
	stream->tstream->istream->rewindLast	= dbgRewindLast;
	stream->tstream->istream->seek			= dbgSeek;

	return stream;
}*/

pBOUNDED_TOKEN_BUFFER
BoundedTokenBufferSourceNew(ANTLR3_UINT32 k, pANTLR3_TOKEN_SOURCE source)
{
    pBOUNDED_TOKEN_BUFFER buffer;
    pANTLR3_COMMON_TOKEN_STREAM	stream;


    AlwaysAssert( k > 0 );

    /* Memory for the interface structure
     */
    buffer = (pBOUNDED_TOKEN_BUFFER) ANTLR3_MALLOC(sizeof(BOUNDED_TOKEN_BUFFER_struct));

    if	(buffer == NULL)
    {
	return	NULL;
    }

    buffer->tokenBuffer = (pANTLR3_COMMON_TOKEN*) ANTLR3_MALLOC(2*k*sizeof(pANTLR3_COMMON_TOKEN));
    buffer->currentIndex = 0;
    buffer->maxIndex = 0;
    buffer->k = k;
    buffer->bufferSize = 2*k;
    buffer->empty = ANTLR3_TRUE;
    buffer->done = ANTLR3_FALSE;

    stream = antlr3CommonTokenStreamSourceNew(k,source);
    if  (stream == NULL)
    {
        return  NULL;
    }

    stream->super = buffer;
    buffer->commonTstream = stream;

    /* Defaults
     */
    stream->p	    = -1;

    /* Install the token stream API
     */
    stream->tstream->_LT				=  tokLT;
    stream->tstream->get				=  get;
    stream->tstream->getTokenSource		=  getTokenSource;
    stream->tstream->setTokenSource		=  setTokenSource;
    stream->tstream->toString			=  toString;
    stream->tstream->toStringSS			=  toStringSS;
    stream->tstream->toStringTT			=  toStringTT;
	stream->tstream->setDebugListener	=  setDebugListener;

    /* Install INT_STREAM interface
     */
    stream->tstream->istream->_LA	=  _LA;
    stream->tstream->istream->mark	=  mark;
    stream->tstream->istream->release	=  release;
    stream->tstream->istream->size	=  size;
    stream->tstream->istream->index	=  tindex;
    stream->tstream->istream->rewind	=  rewindStream;
    stream->tstream->istream->rewindLast=  rewindLast;
    stream->tstream->istream->seek	=  seek;
    stream->tstream->istream->consume	=  consume;
    stream->tstream->istream->getSourceName = getSourceName;

    return  buffer;
}

// Install a debug listener adn switch to debug mode methods
//
static void					
setDebugListener	(pANTLR3_TOKEN_STREAM ts, pANTLR3_DEBUG_EVENT_LISTENER debugger)
{
		// Install the debugger object
	//
	ts->debugger = debugger;

	// Override standard token stream methods with debugging versions
	//
	ts->initialStreamState	= ANTLR3_FALSE;

	ts->_LT				= dbgTokLT;

	ts->istream->consume		= dbgConsume;
	ts->istream->_LA			= dbgLA;
	ts->istream->mark			= dbgMark;
	ts->istream->rewind			= dbgRewindStream;
	ts->istream->rewindLast		= dbgRewindLast;
	ts->istream->seek			= dbgSeek;
}

/** Get the ith token from the current position 1..n where k=1 is the
*  first symbol of lookahead.
*/
static pANTLR3_COMMON_TOKEN tokLT(pANTLR3_TOKEN_STREAM ts, ANTLR3_INT32 k) {
  pANTLR3_COMMON_TOKEN_STREAM cts;
  pBOUNDED_TOKEN_BUFFER buffer;

  cts = (pANTLR3_COMMON_TOKEN_STREAM) ts->super;
  buffer = (pBOUNDED_TOKEN_BUFFER) cts->super;

  /* k must be in the range [-buffer->k..buffer->k] */
  AlwaysAssert( k <= (ANTLR3_INT32)buffer->k 
                && -k <= (ANTLR3_INT32)buffer->k );

  if(k == 0) {
    return NULL;
  }

  /* Initialize the buffer on our first call. */
  if( EXPECT_FALSE(buffer->empty == ANTLR3_TRUE) ) {
    AlwaysAssert( buffer->tokenBuffer != NULL );
    buffer->tokenBuffer[ 0 ] = nextToken(buffer);
    buffer->maxIndex = 0;
    buffer->currentIndex = 0;
    buffer->empty = ANTLR3_FALSE;
  }

  ANTLR3_UINT32 kIndex;
  if( k > 0 ) {
    /* look-ahead token k is at offset k-1 */
    kIndex = buffer->currentIndex + k - 1;
  } else {
    /* Can't look behind more tokens than we've consumed. */
    AlwaysAssert( -k <= (ANTLR3_INT32)buffer->currentIndex );
    /* look-behind token k is at offset -k */
    kIndex = buffer->currentIndex + k;
  }

  while( kIndex > buffer->maxIndex ) {
    buffer->maxIndex++;
    buffer->tokenBuffer[ buffer->maxIndex % buffer->bufferSize ] = nextToken(buffer);
  }

  return buffer->tokenBuffer[ kIndex % buffer->bufferSize ];
}


/// As per the normal tokLT but sends information to the debugger
///
static pANTLR3_COMMON_TOKEN 
dbgTokLT  (pANTLR3_TOKEN_STREAM ts, ANTLR3_INT32 k)
{
	return tokLT(ts, k);
}

#ifdef	ANTLR3_WINDOWS
	/* When fully optimized VC7 complains about non reachable code.
	 * Not yet sure if this is an optimizer bug, or a bug in the flow analysis
	 */
#pragma warning( disable : 4702 )
#endif

static pANTLR3_COMMON_TOKEN
LB(pANTLR3_COMMON_TOKEN_STREAM cts, ANTLR3_INT32 k)
{
  AlwaysAssert(false);
}

static pANTLR3_COMMON_TOKEN 
get (pANTLR3_TOKEN_STREAM ts, ANTLR3_UINT32 i)
{
  AlwaysAssert(false);
}

static pANTLR3_TOKEN_SOURCE 
getTokenSource	(pANTLR3_TOKEN_STREAM ts)
{
    return  ts->tokenSource;
}

static void
setTokenSource	(   pANTLR3_TOKEN_STREAM ts,
		    pANTLR3_TOKEN_SOURCE tokenSource)
{
    ts->tokenSource	= tokenSource;
}

static pANTLR3_STRING	    
toString    (pANTLR3_TOKEN_STREAM ts)
{
  AlwaysAssert(false);
}

static pANTLR3_STRING
toStringSS(pANTLR3_TOKEN_STREAM ts, ANTLR3_UINT32 start, ANTLR3_UINT32 stop)
{
  AlwaysAssert(false);
}

static pANTLR3_STRING	    
toStringTT  (pANTLR3_TOKEN_STREAM ts, pANTLR3_COMMON_TOKEN start, pANTLR3_COMMON_TOKEN stop)
{
  AlwaysAssert(false);
}

/** Move the input pointer to the next incoming token.  The stream
 *  must become active with LT(1) available.  consume() simply
 *  moves the input pointer so that LT(1) points at the next
 *  input symbol. Consume at least one token.
 *
 *  Walk past any token not on the channel the parser is listening to.
 */
static void		    
consume	(pANTLR3_INT_STREAM is)
{
	pANTLR3_COMMON_TOKEN_STREAM cts;
	pANTLR3_TOKEN_STREAM	ts;
	pBOUNDED_TOKEN_BUFFER buffer;

	ts	    = (pANTLR3_TOKEN_STREAM)	    is->super;
	cts	    = (pANTLR3_COMMON_TOKEN_STREAM) ts->super;
	buffer      = (pBOUNDED_TOKEN_BUFFER)     cts->super;

	buffer->currentIndex++;
}


/// As per ordinary consume but notifies the debugger about hidden
/// tokens and so on.
///
static void
dbgConsume	(pANTLR3_INT_STREAM is)
{
    consume(is);
}

/** A simple filter mechanism whereby you can tell this token stream
 *  to force all tokens of type ttype to be on channel.  For example,
 *  when interpreting, we cannot execute actions so we need to tell
 *  the stream to force all WS and NEWLINE to be a different, ignored,
 *  channel.
 */
static void		    
setTokenTypeChannel (pANTLR3_COMMON_TOKEN_STREAM tokenStream, ANTLR3_UINT32 ttype, ANTLR3_UINT32 channel)
{
    if	(tokenStream->channelOverrides == NULL)
    {
	tokenStream->channelOverrides	= antlr3ListNew(10);
    }

    /* We add one to the channel so we can distinguish NULL as being no entry in the
     * table for a particular token type.
     */
    tokenStream->channelOverrides->put(tokenStream->channelOverrides, ttype, ANTLR3_FUNC_PTR((ANTLR3_UINT32)channel + 1), NULL);
}

static void		    
discardTokenType    (pANTLR3_COMMON_TOKEN_STREAM tokenStream, ANTLR3_INT32 ttype)
{
    if	(tokenStream->discardSet == NULL)
    {
	tokenStream->discardSet	= antlr3ListNew(31);
    }

    /* We add one to the channel so we can distinguish NULL as being no entry in the
     * table for a particular token type. We could use bitsets for this I suppose too.
     */
    tokenStream->discardSet->put(tokenStream->discardSet, ttype, ANTLR3_FUNC_PTR((ANTLR3_UINT32)ttype + 1), NULL);
}

static void		    
discardOffChannel   (pANTLR3_COMMON_TOKEN_STREAM tokenStream, ANTLR3_BOOLEAN discard)
{
    tokenStream->discardOffChannel  = discard;
}

static pANTLR3_VECTOR	    
getTokens   (pANTLR3_COMMON_TOKEN_STREAM tokenStream)
{
    AlwaysAssert(false);
}

static pANTLR3_LIST	    
getTokenRange	(pANTLR3_COMMON_TOKEN_STREAM tokenStream, ANTLR3_UINT32 start, ANTLR3_UINT32 stop)
{
  AlwaysAssert(false);
}                                                   
/** Given a start and stop index, return a List of all tokens in
 *  the token type BitSet.  Return null if no tokens were found.  This
 *  method looks at both on and off channel tokens.
 */
static pANTLR3_LIST	    
getTokensSet	(pANTLR3_COMMON_TOKEN_STREAM tokenStream, ANTLR3_UINT32 start, ANTLR3_UINT32 stop, pANTLR3_BITSET types)
{
  AlwaysAssert(false);
}

static pANTLR3_LIST	    
getTokensList	(pANTLR3_COMMON_TOKEN_STREAM tokenStream, ANTLR3_UINT32 start, ANTLR3_UINT32 stop, pANTLR3_LIST list)
{
  AlwaysAssert(false);
}

static pANTLR3_LIST	    
getTokensType	(pANTLR3_COMMON_TOKEN_STREAM tokenStream, ANTLR3_UINT32 start, ANTLR3_UINT32 stop, ANTLR3_UINT32 type)
{
  AlwaysAssert(false);
}

static ANTLR3_UINT32	    
_LA  (pANTLR3_INT_STREAM is, ANTLR3_INT32 i)
{
	pANTLR3_TOKEN_STREAM    ts;
	pANTLR3_COMMON_TOKEN    tok;

	ts	    = (pANTLR3_TOKEN_STREAM)	    is->super;

	tok	    =  ts->_LT(ts, i);

	if	(tok != NULL)
	{
		return	tok->getType(tok);
	}
	else
	{
		return	ANTLR3_TOKEN_INVALID;
	}
}

/// As per _LA() but for debug mode.
///
static ANTLR3_UINT32	    
dbgLA  (pANTLR3_INT_STREAM is, ANTLR3_INT32 i)
{
  AlwaysAssert(false);
}

static ANTLR3_MARKER
mark	(pANTLR3_INT_STREAM is)
{
  AlwaysAssert(false);
}

/// As per mark() but with a call to tell the debugger we are doing this
///
static ANTLR3_MARKER
dbgMark	(pANTLR3_INT_STREAM is)
{
  AlwaysAssert(false);
}

static void		    
release	(pANTLR3_INT_STREAM is, ANTLR3_MARKER mark)
{
    return;
}

static ANTLR3_UINT32	    
size	(pANTLR3_INT_STREAM is)
{
  AlwaysAssert(false);
}

static ANTLR3_MARKER   
tindex	(pANTLR3_INT_STREAM is)
{
  pANTLR3_COMMON_TOKEN_STREAM cts;
  pANTLR3_TOKEN_STREAM        ts;
  pBOUNDED_TOKEN_BUFFER buffer;

  ts      = (pANTLR3_TOKEN_STREAM)        is->super;
  cts     = (pANTLR3_COMMON_TOKEN_STREAM) ts->super;
  buffer      = (pBOUNDED_TOKEN_BUFFER)     cts->super;

  return  buffer->currentIndex;
}

static void		    
dbgRewindLast	(pANTLR3_INT_STREAM is)
{
  AlwaysAssert(false);
}
static void		    
rewindLast	(pANTLR3_INT_STREAM is)
{
  AlwaysAssert(false);
}
static void		    
rewindStream	(pANTLR3_INT_STREAM is, ANTLR3_MARKER marker)
{
  AlwaysAssert(false);
}
static void		    
dbgRewindStream	(pANTLR3_INT_STREAM is, ANTLR3_MARKER marker)
{
   AlwaysAssert(false);
}

static void		    
seek	(pANTLR3_INT_STREAM is, ANTLR3_MARKER index)
{
    AlwaysAssert(false);
}
static void		    
dbgSeek	(pANTLR3_INT_STREAM is, ANTLR3_MARKER index)
{
  AlwaysAssert(false);
}

static pANTLR3_COMMON_TOKEN nextToken(pBOUNDED_TOKEN_BUFFER buffer) {
  pANTLR3_COMMON_TOKEN_STREAM tokenStream;
  pANTLR3_COMMON_TOKEN tok;
  ANTLR3_BOOLEAN discard;
  void * channelI;

  tokenStream = buffer->commonTstream;

  if( buffer->done == ANTLR3_TRUE ) {
    return &(tokenStream->tstream->tokenSource->eofToken);
  }

  /* Pick out the next token from the token source
   * Remember we just get a pointer (reference if you like) here
   * and so if we store it anywhere, we don't set any pointers to auto free it.
   */
  do {
    tok
        = tokenStream->tstream->tokenSource->nextToken(
                                                       tokenStream->tstream->tokenSource);
    if(tok == NULL || tok->type == ANTLR3_TOKEN_EOF) {
      buffer->done = ANTLR3_TRUE;
      break;
    }

    discard = ANTLR3_FALSE; /* Assume we are not discarding	*/

    /* I employ a bit of a trick, or perhaps hack here. Rather than
     * store a pointer to a structure in the override map and discard set
     * we store the value + 1 cast to a void *. Hence on systems where NULL = (void *)0
     * we can distinguish "not being there" from "being channel or type 0"
     */

    if(tokenStream->discardSet != NULL
        && tokenStream->discardSet->get(tokenStream->discardSet,
                                        tok->getType(tok)) != NULL) {
      discard = ANTLR3_TRUE;
    } else if(tok->getChannel(tok) != tokenStream->channel) {
      discard = ANTLR3_TRUE;
    }

  } while(discard == ANTLR3_TRUE);

  return tok;
}


/// Return a string that represents the name assoicated with the input source
///
/// /param[in] is The ANTLR3_INT_STREAM interface that is representing this token stream.
///
/// /returns 
/// /implements ANTLR3_INT_STREAM_struct::getSourceName()
///
static pANTLR3_STRING		
getSourceName				(pANTLR3_INT_STREAM is)
{
	// Slightly convoluted as we must trace back to the lexer's input source
	// via the token source. The streamName that is here is not initialized
	// because this is a token stream, not a file or string stream, which are the
	// only things that have a context for a source name.
	//
	return ((pANTLR3_TOKEN_STREAM)(is->super))->tokenSource->fileName;
}

static pANTLR3_COMMON_TOKEN
simpleEmit        (pANTLR3_LEXER lexer)
{
    pANTLR3_COMMON_TOKEN        token;

    /* We could check pointers to token factories and so on, but
     * we are in code that we want to run as fast as possible
     * so we are not checking any errors. So make sure you have installed an input stream before
     * trying to emit a new token.
     */
    token   = antlr3CommonTokenNew( lexer->rec->state->type );
        // lexer->rec->state->tokFactory->newToken(lexer->rec->state->tokFactory);

    /* Install the supplied information, and some other bits we already know
     * get added automatically, such as the input stream it is associated with
     * (though it can all be overridden of course)
     */
    // token->type             = lexer->rec->state->type;
    token->channel          = lexer->rec->state->channel;
    token->start            = lexer->rec->state->tokenStartCharIndex;
    token->stop             = lexer->getCharIndex(lexer) - 1;
    token->line             = lexer->rec->state->tokenStartLine;
    token->charPosition = lexer->rec->state->tokenStartCharPositionInLine;

        if      (lexer->rec->state->text != NULL)
        {
                token->textState                = ANTLR3_TEXT_STRING;
                token->tokText.text         = lexer->rec->state->text;
        }
        else
        {
                token->textState        = ANTLR3_TEXT_NONE;
        }
    token->lineStart    = lexer->input->currentLine;
        token->user1            = lexer->rec->state->user1;
        token->user2            = lexer->rec->state->user2;
        token->user3            = lexer->rec->state->user3;
        token->custom           = lexer->rec->state->custom;

    lexer->rec->state->token        = token;

    return  token;
}


}
}

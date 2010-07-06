/*********************                                                        */
/*! \file bounded_token_buffer.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An ANTLR3 bounded token stream.
 **
 ** An ANTLR3 bounded token stream. The stream has a bounded
 ** lookahead/behind k. Calling LT(i) with i > k or i < -k will raise
 ** an exception. Only use this factory if you *know* that the grammar
 ** has bounded lookahead (e.g., if you've set the k parameter in the 
 ** parser.
 **/

#ifndef	__CVC4__PARSER__BOUNDED_TOKEN_BUFFER_H
#define	__CVC4__PARSER__BOUNDED_TOKEN_BUFFER_H

#include <antlr3defs.h>

namespace CVC4 {
namespace parser {

#ifdef __cplusplus
extern "C" {
#endif


/** A "super" structure for COMMON_TOKEN_STREAM. */
typedef struct BOUNDED_TOKEN_BUFFER_struct
{
    pANTLR3_COMMON_TOKEN_STREAM    commonTstream;
    pANTLR3_COMMON_TOKEN* tokenBuffer;
    // tokenNeg1, token1, token2;
    ANTLR3_UINT32 currentIndex, maxIndex, k, bufferSize;
    ANTLR3_BOOLEAN empty, done;
} BOUNDED_TOKEN_BUFFER, *pBOUNDED_TOKEN_BUFFER;

pBOUNDED_TOKEN_BUFFER
BoundedTokenBufferSourceNew(ANTLR3_UINT32 k, pANTLR3_TOKEN_SOURCE source);

void
BoundedTokenBufferFree(pBOUNDED_TOKEN_BUFFER buffer);

#ifdef __cplusplus
}/* extern "C" */
#endif

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__BOUNDED_TOKEN_BUFFER_H */

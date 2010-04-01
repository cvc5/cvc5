/*********************                                                        */
/** bounded_token_factory.h
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__BOUNDED_TOKEN_FACTORY_H
#define __CVC4__PARSER__BOUNDED_TOKEN_FACTORY_H

namespace CVC4 {
namespace parser {

#ifdef __cplusplus
extern "C" {
#endif

/** Create a token factory with a pool of exactly <code>size</code> tokens,
 * attached to the input stream <code>input</code>. <code>size</code> must be
 * greater than the maximum lookahead in the parser, or tokens will be prematurely re-used.
 *
 * We abuse <code>pANTLR3_TOKEN_FACTORY</code> fields for our own purposes:
 * <code>pANTLR3_COMMON_TOKEN    *pools</code>: a pointer to a single-element array, a single pool of tokens
 * <code>ANTLR3_INT32       thisPool</code>: the size of the pool
 * <code>ANTLR3_UINT32      nextToken</code>: the index of the next token to be returned
 * */
pANTLR3_TOKEN_FACTORY
BoundedTokenFactoryNew(pANTLR3_INPUT_STREAM input,ANTLR3_UINT32 size);

#ifdef __cplusplus
}/* extern "C" */
#endif

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__BOUNDED_TOKEN_FACTORY_H */

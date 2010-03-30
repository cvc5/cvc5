/*
 * bounded_token_factory.h
 *
 *  Created on: Mar 2, 2010
 *      Author: dejan
 */

#ifndef BOUNDED_TOKEN_FACTORY_H_
#define BOUNDED_TOKEN_FACTORY_H_

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
}
#endif

}
}


#endif /* BOUNDED_TOKEN_FACTORY_H_ */

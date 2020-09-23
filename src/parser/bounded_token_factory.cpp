/*********************                                                        */
/*! \file bounded_token_factory.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An ANTLR3 bounded token factory implementation.
 **
 ** An ANTLR3 bounded token factory implementation.
 **/

#include <antlr3input.h>
#include <antlr3commontoken.h>
#include <antlr3interfaces.h>
#include "parser/bounded_token_factory.h"

namespace CVC4 {
namespace parser {

static pANTLR3_COMMON_TOKEN
newPoolToken(pANTLR3_TOKEN_FACTORY factory);

static void
setInputStream  (pANTLR3_TOKEN_FACTORY factory, pANTLR3_INPUT_STREAM input);

static  void
factoryClose        (pANTLR3_TOKEN_FACTORY factory);

pANTLR3_TOKEN_FACTORY
BoundedTokenFactoryNew(pANTLR3_INPUT_STREAM input,ANTLR3_UINT32 size)
{
    pANTLR3_TOKEN_FACTORY   factory;
    pANTLR3_COMMON_TOKEN tok;
    ANTLR3_UINT32 i;

    /* allocate memory
     */
    factory     = (pANTLR3_TOKEN_FACTORY) ANTLR3_MALLOC(sizeof(ANTLR3_TOKEN_FACTORY));

    if  (factory == NULL)
    {
        return  NULL;
    }

    /* Install factory API
     */
    factory->newToken       =  newPoolToken;
    factory->close          =  factoryClose;
    factory->setInputStream = setInputStream;

    /* Allocate the initial pool
     */
    factory->thisPool   = size;
    factory->nextToken  = 0;
    factory->pools      = (pANTLR3_COMMON_TOKEN*) ANTLR3_MALLOC(sizeof(pANTLR3_COMMON_TOKEN));
    factory->pools[0]  =
        (pANTLR3_COMMON_TOKEN)
        ANTLR3_MALLOC((size_t)(sizeof(ANTLR3_COMMON_TOKEN) * size));

    /* Set up the tokens once and for all */
    for( i=0; i < size; i++ ) {
      tok = factory->pools[0] + i;
      antlr3SetTokenAPI(tok);

      /* It is factory made, and we need to copy the string factory pointer
       */
      tok->factoryMade  = ANTLR3_TRUE;
      tok->strFactory   = input == NULL ? NULL : input->strFactory;
      tok->input        = input;
    }

    /* Factory space is good, we now want to initialize our cheating token
     * which one it is initialized is the model for all tokens we manufacture
     */
    antlr3SetTokenAPI(&factory->unTruc);

    /* Set some initial variables for future copying
     */
    factory->unTruc.factoryMade = ANTLR3_TRUE;

    // Input stream
    //
    setInputStream(factory, input);

    return  factory;

}

static pANTLR3_COMMON_TOKEN
newPoolToken(pANTLR3_TOKEN_FACTORY factory)
{
  ANTLR3_UINT32 size = factory->thisPool;
  pANTLR3_COMMON_TOKEN tok = factory->pools[0] + (factory->nextToken % size);
  if(factory->nextToken >= size && tok->custom != NULL && tok->freeCustom != NULL) {
    tok->freeCustom(tok->custom);
    tok->custom = NULL;
  }
  factory->nextToken++;

  return tok;
}

static  void
factoryClose        (pANTLR3_TOKEN_FACTORY factory)
{
  ANTLR3_UINT32 i;
  ANTLR3_UINT32 size = factory->thisPool;
  pANTLR3_COMMON_TOKEN tok;

  for(i = 0; i < size && i < factory->nextToken; i++) {
    tok = factory->pools[0] + i;
    if(tok->custom != NULL && tok->freeCustom != NULL) {
      tok->freeCustom(tok->custom);
      tok->custom = NULL;
    }
  }
  ANTLR3_FREE(factory->pools[0]);
  ANTLR3_FREE(factory->pools);
  ANTLR3_FREE(factory);

}

static void
setInputStream  (pANTLR3_TOKEN_FACTORY factory, pANTLR3_INPUT_STREAM input)
{
    factory->input          =  input;
    factory->unTruc.input   =  input;
        if      (input != NULL)
        {
                factory->unTruc.strFactory      = input->strFactory;
        }
        else
        {
                factory->unTruc.strFactory = NULL;
    }
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

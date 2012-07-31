/*********************                                                        */
/*! \file proof.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Proof manager
 **
 ** Proof manager
 **/

#ifndef __CVC4__PROOF__PROOF_H
#define __CVC4__PROOF__PROOF_H

#include "options/options.h"

#ifdef CVC4_PROOF
#  define PROOF(x) if(options::proof()) { x; }
#  define NULLPROOF(x) (options::proof())? x : NULL
#  define PROOF_ON() options::proof()
#else /* CVC4_PROOF */
#  define PROOF(x)
#  define NULLPROOF(x) NULL
#  define PROOF_ON() false
#endif /* CVC4_PROOF */



#endif /* __CVC4__PROOF__PROOF_H */

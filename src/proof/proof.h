/*********************                                                        */
/*! \file proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Proof macros
 **
 ** Proof macros
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__PROOF_H
#define __CVC4__PROOF__PROOF_H

// FIXME: rename proof to unsat core and theory_proof to proof
#include "smt/options.h"
#ifdef CVC4_PROOF
#  define PROOF(x) if(CVC4::options::proof() || CVC4::options::unsatCores()) { x; }
#  define NULLPROOF(x) (CVC4::options::proof() || CVC4::options::unsatCores()) ? x : NULL
#  define PROOF_ON() (CVC4::options::proof() || CVC4::options::unsatCores())
#  define THEORY_PROOF(x) if(CVC4::options::proof()) { x; }
#  define THEORY_NULLPROOF(x) CVC4::options::proof() ? x : NULL
#  define THEORY_PROOF_ON() CVC4::options::proof()
#else /* CVC4_PROOF */
#  define PROOF(x)
#  define NULLPROOF(x) NULL
#  define PROOF_ON() false
#endif /* CVC4_PROOF */

#ifdef CVC4_PROOF_STATS /* CVC4_PROOF_STATS */
# define PSTATS(x) { x; }
#else
# define PSTATS(x)
#endif /* CVC4_PROOF_STATS */

#endif /* __CVC4__PROOF__PROOF_H */

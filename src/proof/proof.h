/*********************                                                        */
/*! \file proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof macros
 **
 ** Proof macros
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__PROOF_H
#define __CVC4__PROOF__PROOF_H

#include "options/smt_options.h"


/* Do NOT use #ifdef CVC4_PROOF to check if proofs are enabled.
 * We cannot assume users will use -DCVC4_PROOFS if they have a proofs build.
 * The preferred way of checking that proofs are enabled is to use:
 * #if IS_PROOFS_BUILD
 * ...
 * #endif
 *
 * The macro IS_PROOFS_BUILD is defined in base/configuration_private.h
 *
 * This has the effect of forcing that location to have included this header
 * *before* performing this test. This includes C preprocessing expansion.
 * This forces the inclusion of "cvc4_private.h". This is intentional!
 *
 * See bug 688 for more details:
 * https://github.com/CVC4/CVC4/issues/907
 *
 * If you want to check CVC4_PROOF, you should have a very good reason
 * and should list the exceptions here:
 * - Makefile.am
 * - proof/proofs.h
 * - base/configuration_private.h
 */

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
#  define THEORY_PROOF(x) 
#  define THEORY_NULLPROOF(x) NULL
#  define THEORY_PROOF_ON() false
#endif /* CVC4_PROOF */

#ifdef CVC4_PROOF_STATS /* CVC4_PROOF_STATS */
# define PSTATS(x) { x; }
#else
# define PSTATS(x)
#endif /* CVC4_PROOF_STATS */

#endif /* __CVC4__PROOF__PROOF_H */

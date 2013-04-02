/*********************                                                        */
/*! \file theory_rewriterules_params.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Parameters for the rewrite rules theory
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_PARAMS_H
#define __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_PARAMS_H

namespace CVC4 {
namespace theory {
namespace rewriterules {

/**
   Specify if the propagation is done by lemma or by real theory propagation
 */
static const bool propagate_as_lemma = true;

/**
   Cache the instantiation of rules in order to remove duplicate
 */
static const bool cache_match = true;

/**
   Compute when the rules are created which terms in the body can lead
   to new instantiation (try only single trigger). During propagation
   we check if the instantiation of these terms are known terms.
 */
static const bool compute_opt = true;

/**
   rewrite the matching found
 */
static const bool rewrite_instantiation = true;

/**
   use the representative for the matching found
 */
static const bool representative_instantiation = false;

/**
   Wait the specified number of check after a new propagation (a
   previous unknown guards becomes true) is found before verifying again the guards.

   Allow to break loop with other theories.
 */
static const size_t checkSlowdown = 0;

/**
   Use the current model to eliminate guard before asking for notification
 */
static const bool useCurrentModel = false;

/**
   Simulate rewriting by tagging rewritten terms.
 */
static const bool simulateRewritting = true;

/**
   Do narrowing at full effort
*/
static const bool narrowing_full_effort = false;

/**
   Direct rewrite: Add rewrite rules directly in the rewriter.
 */
static const bool direct_rewrite = false;

}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_PARAMS_H */

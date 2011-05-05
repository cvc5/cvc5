/*********************                                                        */
/*! \file substitutions.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A substitution mapping for theory simplification
 **
 ** A substitution mapping for theory simplification.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SUBSTITUTIONS_H
#define __CVC4__THEORY__SUBSTITUTIONS_H

#include <utility>
#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {

/**
 * The type for the Substitutions mapping output by
 * Theory::simplify(), TheoryEngine::simplify(), and
 * Valuation::simplify().  This is in its own header to avoid circular
 * dependences between those three.
 */
typedef std::vector< std::pair<Node, Node> > Substitutions;

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SUBSTITUTIONS_H */

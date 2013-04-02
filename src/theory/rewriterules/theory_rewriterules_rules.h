/*********************                                                        */
/*! \file theory_rewriterules_rules.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewrite Engine classes
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_RULES_H
#define __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_RULES_H

#include "theory/rewriterules/theory_rewriterules.h"
#include "theory/rewriterules/theory_rewriterules_params.h"

namespace CVC4 {
namespace theory {
namespace rewriterules {

inline std::ostream& operator <<(std::ostream& stream, const RewriteRule& r) {
  r.toStream(stream);
  return stream;
}

}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_RULES_H */

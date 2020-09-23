/*********************                                                        */
/*! \file theory_sep_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SEP__THEORY_SEP_REWRITER_H
#define CVC4__THEORY__SEP__THEORY_SEP_REWRITER_H

#include "theory/theory_rewriter.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace sep {

class TheorySepRewriter : public TheoryRewriter
{
 public:
  RewriteResponse postRewrite(TNode node) override;
  RewriteResponse preRewrite(TNode node) override
  {
    Trace("sep-prerewrite") << "Sep::preRewrite returning " << node << std::endl;
    return RewriteResponse(REWRITE_DONE, node);
  }

 private:
  static void getStarChildren(Node n,
                              std::vector<Node>& s_children,
                              std::vector<Node>& ns_children);
  static void getAndChildren(Node n,
                             std::vector<Node>& s_children,
                             std::vector<Node>& ns_children);
  static bool isSpatial(Node n, std::map<Node, bool>& visited);
}; /* class TheorySepRewriter */

}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__SEP__THEORY_SEP_REWRITER_H */

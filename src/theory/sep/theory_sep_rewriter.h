/*********************                                                        */
/*! \file theory_sep_rewriter.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SEP__THEORY_SEP_REWRITER_H
#define __CVC4__THEORY__SEP__THEORY_SEP_REWRITER_H

#include "theory/rewriter.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace sep {


class TheorySepRewriter {
private:
  static void getStarChildren( Node n, std::vector< Node >& s_children, std::vector< Node >& ns_children );
  static void getAndChildren( Node n, std::vector< Node >& s_children, std::vector< Node >& ns_children );
  static bool isSpatial( Node n, std::map< Node, bool >& visited );
public:

  static RewriteResponse postRewrite(TNode node);
  static inline RewriteResponse preRewrite(TNode node) {
    Trace("sep-prerewrite") << "Sep::preRewrite returning " << node << std::endl;
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline void init() {}
  static inline void shutdown() {}
private:
  static Node preSkolemEmp( Node n, bool pol, std::map< bool, std::map< Node, Node > >& visited );
public:
  static Node preprocess( Node n );
};/* class TheorySepRewriter */

}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SEP__THEORY_SEP_REWRITER_H */

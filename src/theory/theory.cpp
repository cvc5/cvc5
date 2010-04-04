/*********************                                                        */
/** theory.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Base for theory interface.
 **/

#include "theory/theory.h"
#include "util/Assert.h"

#include <vector>

using namespace std;

namespace CVC4 {
namespace theory {

Node Theory::get() {
  Assert( !d_facts.empty(),
          "Theory::get() called with assertion queue empty!" );

  Node fact = d_facts.front();
  d_facts.pop_front();

  Debug("theory") << "Theory::get() => " << fact
                  << "(" << d_facts.size() << " left)" << std::endl;

  if(! fact.getAttribute(RegisteredAttr())) {
    std::list<TNode> toReg;
    toReg.push_back(fact);

    Debug("theory") << "Theory::get(): registering new atom" << std::endl;

    /* Essentially this is doing a breadth-first numbering of
     * non-registered subterms with children.  Any non-registered
     * leaves are immediately registered. */
    for(std::list<TNode>::iterator workp = toReg.begin();
        workp != toReg.end();
        ++workp) {

      TNode n = *workp;

      if(n.hasOperator()) {
        TNode c = n.getOperator();

        if(! c.getAttribute(RegisteredAttr())) {
          if(c.getNumChildren() == 0) {
            c.setAttribute(RegisteredAttr(), true);
            registerTerm(c);
          } else {
            toReg.push_back(c);
          }
        }
      }

      for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
        TNode c = *i;

        if(! c.getAttribute(RegisteredAttr())) {
          if(c.getNumChildren() == 0) {
            c.setAttribute(RegisteredAttr(), true);
            registerTerm(c);
          } else {
            toReg.push_back(c);
          }
        }
      }
    }

    /* Now register the list of terms in reverse order.  Between this
     * and the above registration of leaves, this should ensure that
     * all subterms in the entire tree were registered in
     * reverse-topological order. */
    for(std::list<TNode>::reverse_iterator i = toReg.rbegin();
        i != toReg.rend();
        ++i) {

      TNode n = *i;

      /* Note that a shared TNode in the DAG rooted at "fact" could
       * appear twice on the list, so we have to avoid hitting it
       * twice. */
      // FIXME when ExprSets are online, use one of those to avoid
      // duplicates in the above?
      if(! n.getAttribute(RegisteredAttr())) {
        n.setAttribute(RegisteredAttr(), true);
        registerTerm(n);
      }
    }
  }

  return fact;
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

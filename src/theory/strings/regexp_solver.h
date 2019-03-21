/*********************                                                        */
/*! \file regexp_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory of strings
 **
 ** Theory of strings.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__STRINGS__REGEXP_SOLVER_H
#define __CVC4__THEORY__STRINGS__REGEXP_SOLVER_H

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "theory/strings/regexp_operation.h"

namespace CVC4 {
namespace theory {
namespace strings {
  
class TheoryStrings;

class RegExpSolver 
{
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  RegExpSolver(TheoryStrings& p, context::Context* c, context::UserContext* u);
  ~RegExpSolver(){}
  
  /** add membership
   * 
   * This informs this class that assertion is asserted in the current context.
   * We expect that assertion is a (possibly negated) regular expression
   * membership.
   */
  void addMembership(Node assertion);
  /** check
   * 
   * Tells this solver to check whether the regular expressions asserted to it
   * are consistent. If they are not, then this class will FIXME
   */
  void check();
private:
  // Constants
  Node d_emptyString;
  Node d_emptyRegexp;
  Node d_true;
  Node d_false;
  /** the parent of this object */
  TheoryStrings& d_parent;
  //--------------------------------for checkMemberships
  // check membership constraints
  Node mkAnd(Node c1, Node c2);
  bool checkPDerivative( Node x, Node r, Node atom, bool &addedLemma, std::vector< Node > &nf_exp);
  Node getMembership( Node n, bool isPos, unsigned i );
  unsigned getNumMemberships( Node n, bool isPos );
  CVC4::String getHeadConst( Node x );
  bool deriveRegExp( Node x, Node r, Node atom, std::vector< Node >& ant );
  Node getNormalSymRegExp(Node r, std::vector<Node> &nf_exp);
  //--------------------------------end for checkMemberships
  // regular expression memberships
  NodeList d_regexp_memberships;
  NodeSet d_regexp_ucached;
  NodeSet d_regexp_ccached;
  // stored assertions
  NodeIntMap d_pos_memberships;
  std::map< Node, std::vector< Node > > d_pos_memberships_data;
  NodeIntMap d_neg_memberships;
  std::map< Node, std::vector< Node > > d_neg_memberships_data;
  // semi normal forms for symbolic expression
  std::map< Node, Node > d_nf_regexps;
  std::map< Node, std::vector< Node > > d_nf_regexps_exp;
  // intersection
  NodeNodeMap d_inter_cache;
  NodeIntMap d_inter_index;
  // processed memberships
  NodeSet d_processed_memberships;
  /** regular expression operation module */
  RegExpOpr d_regexp_opr;
};/* class TheoryStrings */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__THEORY_STRINGS_H */

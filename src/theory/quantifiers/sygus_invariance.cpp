/*********************                                                        */
/*! \file sygus_invariance.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of techniques for sygus invariance tests.
 **/

#include "theory/quantifiers/sygus_invariance.h"

#include "theory/quantifiers/term_database_sygus.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool EvalSygusInvarianceTest::invariant( quantifiers::TermDbSygus * tds, Node nvn, Node x ){
  TNode tnvn = nvn;
  Node conj_subs = d_conj.substitute( d_var, tnvn );
  Node conj_subs_unfold = tds->evaluateWithUnfolding( conj_subs, d_visited );
  Trace("sygus-cref-eval2-debug") << "  ...check unfolding : " << conj_subs_unfold << std::endl;
  Trace("sygus-cref-eval2-debug") << "  ......from : " << conj_subs << std::endl;
  if( conj_subs_unfold==d_result ){
    Trace("sygus-cref-eval2") << "Evaluation min explain : " << conj_subs << " still evaluates to " << d_result << " regardless of ";
    Trace("sygus-cref-eval2") << x << std::endl;
    return true;
  }else{
    return false;
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

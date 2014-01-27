/*********************                                                        */
/*! \file bv_subtheory_bitblast.cpp
 ** \verbatim
 ** Original author: Liana Hadarean 
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "theory/bv/bv_subtheory_algebraic.h"
#include "theory/bv/bv_quick_check.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/lazy_bitblaster.h"
#include "theory/bv/options.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;


struct SubstitutionElement {
  TNode to;
  TNode reason;
  SubstitutionElement(TNode t, TNode r)
    : to(t)
    , reason(r)
  {}
};


typedef __gnu_cxx::hash_map<TNode, SubstitutionElement, TNodeHashFunction> Substitutions;

class SubstitutionEx {
  Substitutions d_substitutions;

public:
  SubstitutionEx()
    : d_substitutions()
  {}

  void addSubstitution(TNode from, TNode to, TNode reason) {
    Assert (from != to);
    Assert (d_substitutions.find(from) == d_substitutions.end());
    d_substitutions[from] = 
  }
};

bool AlgebraicSolver::check(Theory::Effort e) {
  if (!Theory::fullEffort(e))
    return true;

  
  Debug("bv-algebraic") << "AlgebraicSolver::check (" << e << ")\n";
  Assert(!options::bitvectorEagerBitblast()); 

  ++(d_statistics.d_numCallstoCheck);

  std::vector<TNode> facts;
  // Processing assertions from scratch
  for (AssertionQueue::const_iterator it = assertionsBegin(); it != assertionsEnd(); ++it) {
    facts.push_back(*it); 
  }

  

  return true;
}

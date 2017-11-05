/*********************                                                        */
/*! \file sygus_process_conj.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of techniqures for static preprocessing and analysis
 ** of sygus conjectures.
 **/
#include "theory/quantifiers/sygus_process_conj.h"

#include <stack>

#include "expr/datatype.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegConjectureProcess::CegConjectureProcess(QuantifiersEngine* qe) : d_qe(qe) {}
CegConjectureProcess::~CegConjectureProcess() {}
Node CegConjectureProcess::simplify(Node q)
{
  Trace("sygus-process") << "Simplify conjecture : " << q << std::endl;

  return q;
}

void CegConjectureProcess::initialize(Node n, std::vector<Node>& candidates)
{
  if (Trace.isOn("sygus-process"))
  {
    Trace("sygus-process") << "Process conjecture : " << n
                           << " with candidates: " << std::endl;
    for (unsigned i = 0; i < candidates.size(); i++)
    {
      Trace("sygus-process") << "  " << candidates[i] << std::endl;
    }
  }
  Node base;
  if (n.getKind() == NOT && n[0].getKind() == FORALL)
  {
    base = n[0][1];
  }
  else
  {
    base = n;
  }

  std::vector<Node> conj;
  if (base.getKind() == AND)
  {
    for (unsigned i = 0; i < base.getNumChildren(); i++)
    {
      conj.push_back(base[i]);
    }
  }
  else
  {
    conj.push_back(base);
  }

  // initialize the information for synth funs
  for (unsigned i = 0; i < candidates.size(); i++)
  {
    Node e = candidates[i];
    // d_sf_info[e].d_arg_independent
  }

  // process the conjunctions
  for (unsigned i = 0; i < conj.size(); i++)
  {
    processConjunct(conj[i]);
  }
}

void CegConjectureProcess::processConjunct(Node c) {}
Node CegConjectureProcess::getSymmetryBreakingPredicate(
    Node x, Node e, TypeNode tn, unsigned tindex, unsigned depth)
{
  return Node::null();
}

void CegConjectureProcess::debugPrint(const char* c) {}
} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

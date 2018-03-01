/*********************                                                        */
/*! \file cegis.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of cegis
 **/

#include "theory/quantifiers/sygus/cegis.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Cegis::Cegis(QuantifiersEngine* qe, CegConjecture* p) : SygusModule(qe, p) {}

bool Cegis::initialize(Node n,
                       const std::vector<Node>& candidates,
                       std::vector<Node>& lemmas)
{
  // initialize an enumerator for each candidate
  TermDbSygus* tds = d_qe->getTermDatabaseSygus();
  for (unsigned i = 0; i < candidates.size(); i++)
  {
    tds->registerEnumerator(candidates[i], candidates[i], d_parent);
  }
  return true;
}

void Cegis::getTermList(const std::vector<Node>& candidates,
                        std::vector<Node>& enums)
{
  enums.insert(enums.end(), candidates.begin(), candidates.end());
}

/** construct candidate */
bool Cegis::constructCandidates(const std::vector<Node>& enums,
                                const std::vector<Node>& enum_values,
                                const std::vector<Node>& candidates,
                                std::vector<Node>& candidate_values,
                                std::vector<Node>& lems)
{
  candidate_values.insert(
      candidate_values.end(), enum_values.begin(), enum_values.end());
  return true;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

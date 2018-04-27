/*********************                                                        */
/*! \file sygus_unif_rl.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_unif_rl
 **/

#include "theory/quantifiers/sygus/sygus_unif_rl.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusUnifRl::SygusUnifRl() {}

SygusUnifRl::~SygusUnifRl() {}

void SygusUnifRl::initialize(QuantifiersEngine* qe,
                             Node f,
                             std::vector<Node>& enums,
                             std::vector<Node>& lemmas)
{
  SygusUnif::initialize(qe, f, enums, lemmas);
}

void SygusUnifRl::notifyEnumeration(Node e, Node v, std::vector<Node>& lemmas)
{
}

void SygusUnifRl::addRefLemma(Node lemma) {}

void SygusUnifRl::initializeConstructSol() {}

Node SygusUnifRl::constructSol(Node e, NodeRole nrole, int ind)
{
  return Node::null();
}


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

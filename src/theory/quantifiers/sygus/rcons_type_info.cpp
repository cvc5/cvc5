/*********************                                                        */
/*! \file rcons_type_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Reconstruct Type Info class implementation
 **/

#include "theory/quantifiers/sygus/rcons_type_info.h"

#include "theory/datatypes/sygus_datatype_utils.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

void RConsTypeInfo::initialize(TermDbSygus* tds,
                               SygusStatistics& s,
                               TypeNode stn,
                               const std::vector<Node>& builtinVars)
{
  NodeManager* nm = NodeManager::currentNM();

  d_enumerator.reset(new SygusEnumerator(tds, nullptr, s, true));
  d_enumerator->initialize(nm->mkSkolem("sygus_rcons", stn));
  d_crd.reset(new CandidateRewriteDatabase(true, false, true, false));
  // since initial samples are not always useful for equivalence checks, set
  // their number to 0
  d_sygusSampler.initialize(stn, builtinVars, 0);
  d_crd->initialize(builtinVars, &d_sygusSampler);
}

Node RConsTypeInfo::nextEnum()
{
  if (!d_enumerator->increment())
  {
    Trace("sygus-rcons") << "no increment" << std::endl;
    return Node::null();
  }

  Node sz = d_enumerator->getCurrent();

  Trace("sygus-rcons") << (sz == Node::null()
                               ? sz
                               : datatypes::utils::sygusToBuiltin(sz))
                       << std::endl;

  return sz;
}

Node RConsTypeInfo::addTerm(Node n)
{
  std::stringstream out;
  return d_crd->addTerm(n, false, out);
}

void RConsTypeInfo::setBuiltinToOb(Node builtin, Node ob)
{
  d_ob[builtin] = ob;
}

Node RConsTypeInfo::builtinToOb(Node builtin) { return d_ob[builtin]; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

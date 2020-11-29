/*********************                                                        */
/*! \file sygus_enumerator_basic.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus basic enumerator
 **/
#include "theory/quantifiers/sygus/sygus_enumerator_basic.h"

#include "options/datatypes_options.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

EnumValGeneratorBasic::EnumValGeneratorBasic(TermDbSygus* tds, TypeNode tn)
    : d_tds(tds), d_te(tn)
{
}

bool EnumValGeneratorBasic::increment()
{
  ++d_te;
  if (d_te.isFinished())
  {
    d_currTerm = Node::null();
    return false;
  }
  d_currTerm = *d_te;
  if (options::sygusSymBreakDynamic())
  {
    Node nextb = d_tds->sygusToBuiltin(d_currTerm);
    nextb = d_tds->getExtRewriter()->extendedRewrite(nextb);
    if (d_cache.find(nextb) == d_cache.end())
    {
      d_cache.insert(nextb);
      // only return the current term if not unique
    }
    else
    {
      d_currTerm = Node::null();
    }
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */

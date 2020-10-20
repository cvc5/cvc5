/*********************                                                        */
/*! \file term_enumeration.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term enumeration utility
 **/

#include "theory/quantifiers/term_enumeration.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Node TermEnumeration::getEnumerateTerm(TypeNode tn, unsigned index)
{
  Trace("term-db-enum") << "Get enumerate term " << tn << " " << index
                        << std::endl;
  std::unordered_map<TypeNode, size_t, TypeNodeHashFunction>::iterator it =
      d_typ_enum_map.find(tn);
  size_t teIndex;
  if (it == d_typ_enum_map.end())
  {
    teIndex = d_typ_enum.size();
    d_typ_enum_map[tn] = teIndex;
    d_typ_enum.push_back(TypeEnumerator(tn));
  }
  else
  {
    teIndex = it->second;
  }
  while (index >= d_enum_terms[tn].size())
  {
    if (d_typ_enum[teIndex].isFinished())
    {
      return Node::null();
    }
    d_enum_terms[tn].push_back(*d_typ_enum[teIndex]);
    ++d_typ_enum[teIndex];
  }
  return d_enum_terms[tn][index];
}

bool TermEnumeration::mayComplete(TypeNode tn)
{
  std::unordered_map<TypeNode, bool, TypeNodeHashFunction>::iterator it =
      d_may_complete.find(tn);
  if (it == d_may_complete.end())
  {
    // cache
    bool mc = mayComplete(tn, options::fmfTypeCompletionThresh());
    d_may_complete[tn] = mc;
    return mc;
  }
  return it->second;
}

bool TermEnumeration::mayComplete(TypeNode tn, unsigned maxCard)
{
  bool mc = false;
  if (tn.isClosedEnumerable() && tn.isInterpretedFinite())
  {
    Cardinality c = tn.getCardinality();
    if (!c.isLargeFinite())
    {
      NodeManager* nm = NodeManager::currentNM();
      Node card = nm->mkConst(Rational(c.getFiniteCardinality()));
      // check if less than fixed upper bound
      Node oth = nm->mkConst(Rational(maxCard));
      Node eq = nm->mkNode(LEQ, card, oth);
      eq = Rewriter::rewrite(eq);
      mc = eq.isConst() && eq.getConst<bool>();
    }
  }
  return mc;
}

bool TermEnumeration::getDomain(TypeNode tn, std::vector<Node>& dom)
{
  if (!mayComplete(tn))
  {
    return false;
  }
  Node curre;
  unsigned counter = 0;
  do
  {
    curre = getEnumerateTerm(tn, counter);
    counter++;
    if (!curre.isNull())
    {
      dom.push_back(curre);
    }
  } while (!curre.isNull());
  return true;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

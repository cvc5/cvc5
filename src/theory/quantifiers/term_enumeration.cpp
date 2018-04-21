/*********************                                                        */
/*! \file term_enumeration.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term enumeration utility
 **/

#include "theory/quantifiers/term_enumeration.h"

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

bool TermEnumeration::isClosedEnumerableType(TypeNode tn)
{
  std::unordered_map<TypeNode, bool, TypeNodeHashFunction>::iterator it =
      d_typ_closed_enum.find(tn);
  if (it == d_typ_closed_enum.end())
  {
    d_typ_closed_enum[tn] = true;
    bool ret = true;
    if (tn.isArray() || tn.isSort() || tn.isCodatatype() || tn.isFunction())
    {
      ret = false;
    }
    else if (tn.isSet())
    {
      ret = isClosedEnumerableType(tn.getSetElementType());
    }
    else if (tn.isDatatype())
    {
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      for (unsigned i = 0; i < dt.getNumConstructors(); i++)
      {
        for (unsigned j = 0; j < dt[i].getNumArgs(); j++)
        {
          TypeNode ctn = TypeNode::fromType(dt[i][j].getRangeType());
          if (tn != ctn && !isClosedEnumerableType(ctn))
          {
            ret = false;
            break;
          }
        }
        if (!ret)
        {
          break;
        }
      }
    }
    
    // other parametric sorts go here
    
    d_typ_closed_enum[tn] = ret;
    return ret;
  }
  else
  {
    return it->second;
  }
}

// checks whether a type is closed enumerable and is reasonably small enough (<1000)
// such that all of its domain elements can be enumerated
bool TermEnumeration::mayComplete(TypeNode tn)
{
  std::unordered_map<TypeNode, bool, TypeNodeHashFunction>::iterator it =
      d_may_complete.find(tn);
  if (it == d_may_complete.end())
  {
    bool mc = false;
    if (isClosedEnumerableType(tn) && tn.getCardinality().isFinite()
        && !tn.getCardinality().isLargeFinite())
    {
      Node card = NodeManager::currentNM()->mkConst(
          Rational(tn.getCardinality().getFiniteCardinality()));
      Node oth = NodeManager::currentNM()->mkConst(Rational(1000));
      Node eq = NodeManager::currentNM()->mkNode(LEQ, card, oth);
      eq = Rewriter::rewrite(eq);
      mc = eq.isConst() && eq.getConst<bool>();
    }
    d_may_complete[tn] = mc;
    return mc;
  }
  else
  {
    return it->second;
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

/*********************                                                        */
/*! \file type_matcher.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a class representing a type matcher
 **/

#include "type_matcher.h"

namespace CVC4 {

TypeMatcher::TypeMatcher(TypeNode dt)
{
  Assert(dt.isDatatype());
  addTypesFromDatatype(dt);
}

void TypeMatcher::addTypesFromDatatype(TypeNode dt)
{
  std::vector<TypeNode> argTypes = dt.getParamTypes();
  addTypes(argTypes);
  Debug("typecheck-idt") << "instantiating matcher for " << dt << std::endl;
  for (unsigned i = 0, narg = argTypes.size(); i < narg; ++i)
  {
    if (dt.isParameterInstantiatedDatatype(i))
    {
      Debug("typecheck-idt")
          << "++ instantiate param " << i << " : " << d_types[i] << std::endl;
      d_match[i] = d_types[i];
    }
  }
}

void TypeMatcher::addType(TypeNode t)
{
  d_types.push_back(t);
  d_match.push_back(TypeNode::null());
}

void TypeMatcher::addTypes(const std::vector<TypeNode>& types)
{
  for (const TypeNode& t : types)
  {
    addType(t);
  }
}

bool TypeMatcher::doMatching(TypeNode pattern, TypeNode tn)
{
  Debug("typecheck-idt") << "doMatching() : " << pattern << " : " << tn
                         << std::endl;
  std::vector<TypeNode>::iterator i =
      std::find(d_types.begin(), d_types.end(), pattern);
  if (i != d_types.end())
  {
    size_t index = i - d_types.begin();
    if (!d_match[index].isNull())
    {
      Debug("typecheck-idt")
          << "check subtype " << tn << " " << d_match[index] << std::endl;
      TypeNode tnn = TypeNode::leastCommonTypeNode(tn, d_match[index]);
      // recognize subtype relation
      if (!tnn.isNull())
      {
        d_match[index] = tnn;
        return true;
      }
      return false;
    }
    d_match[index] = tn;
    return true;
  }
  else if (pattern == tn)
  {
    return true;
  }
  else if (pattern.getKind() != tn.getKind()
           || pattern.getNumChildren() != tn.getNumChildren())
  {
    return false;
  }
  else if (pattern.getNumChildren() == 0)
  {
    // fail if the type parameter or type constructors are different
    return pattern == tn;
  }
  for (size_t j = 0, nchild = pattern.getNumChildren(); j < nchild; j++)
  {
    if (!doMatching(pattern[j], tn[j]))
    {
      return false;
    }
  }
  return true;
}

void TypeMatcher::getTypes(std::vector<TypeNode>& types) const
{
  types.clear();
  for (const TypeNode& t : d_types)
  {
    types.push_back(t);
  }
}
void TypeMatcher::getMatches(std::vector<TypeNode>& types) const
{
  types.clear();
  for (size_t i = 0, nmatch = d_match.size(); i < nmatch; i++)
  {
    if (d_match[i].isNull())
    {
      types.push_back(d_types[i]);
    }
    else
    {
      types.push_back(d_match[i]);
    }
  }
}

}  // namespace CVC4

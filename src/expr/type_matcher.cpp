/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of a class representing a type matcher.
 */

#include "type_matcher.h"

#include "expr/dtype.h"

namespace cvc5::internal {

TypeMatcher::TypeMatcher(TypeNode dt)
{
  Assert(dt.isDatatype());
  addTypesFromDatatype(dt);
}

void TypeMatcher::addTypesFromDatatype(TypeNode dt)
{
  std::vector<TypeNode> argTypes;
  if (dt.isInstantiated())
  {
    argTypes = dt.getInstantiatedParamTypes();
  }
  else
  {
    argTypes = dt.getDType().getParameters();
  }
  addTypes(argTypes);
  Trace("typecheck-idt") << "instantiating matcher for " << dt << std::endl;
  for (unsigned i = 0, narg = argTypes.size(); i < narg; ++i)
  {
    if (dt.isParameterInstantiatedDatatype(i))
    {
      Trace("typecheck-idt")
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
  Trace("typecheck-idt") << "doMatching() : " << pattern << " : " << tn
                         << std::endl;
  std::vector<TypeNode>::iterator i =
      std::find(d_types.begin(), d_types.end(), pattern);
  if (i != d_types.end())
  {
    size_t index = i - d_types.begin();
    if (!d_match[index].isNull())
    {
      Trace("typecheck-idt")
          << "check types " << tn << " " << d_match[index] << std::endl;
      if (tn != d_match[index])
      {
        return false;
      }
      d_match[index] = tn;
      return true;
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

}  // namespace cvc5::internal

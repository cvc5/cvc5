/*********************                                                        */
/*! \file symbol_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The symbol manager
 **/

#include "parser/symbol_manager.h"

namespace CVC4 {
namespace parser {

SymbolManager::SymbolManager(api::Solver* s) : d_solver(s) {}

SymbolTable * SymbolManager::getSymbolTable()
{
  return &d_symtabAllocated;
}

void SymbolManager::setName(api::Term t,
                            const std::string& name,
                            bool isAssertion)
{
  if (d_names.find(t)!=d_names.end())
  {
    // already named assertion, or we are not naming an assertion
    if (!isAssertion || d_namedAsserts.find(t)!=d_namedAsserts.end())
    {
      return;
    }
  }
  d_namedAsserts.insert(t);
  d_names[t] = name;
}

bool SymbolManager::getName(api::Term t,
                            std::string& name,
                            bool isAssertion) const
{
  std::map<api::Term, std::string>::const_iterator it = d_names.find(t);
  if (it==d_names.end())
  {
    return false;
  }
  if (isAssertion)
  {
    // must be an assertion name
    if (d_namedAsserts.find(t)==d_namedAsserts.end())
    {
      return false;
    }
  }
  name = it->second;
  return true;
}

void SymbolManager::getNames(const std::vector<api::Term>& ts,
                             std::vector<std::string>& names,
                             bool areAssertions) const
{
  for (const api::Term& t : ts)
  {
    std::string name;
    if (getName(t, name, areAssertions))
    {
      names.push_back(name);
    }
  }
}

}  // namespace parser
}  // namespace CVC4

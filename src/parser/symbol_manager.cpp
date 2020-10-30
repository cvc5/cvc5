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

SymbolManager::SymbolManager(api::Solver* s) : d_solver(s){}
void SymbolManager::setName(api::Term t, const std::string& name, bool isAssertion )
{
}
bool SymbolManager::getName(api::Term t, std::string& name, bool isAssertion ) const
{
return false;
}
void SymbolManager::getNames(const std::vector<api::Term>& ts,
std::vector<std::string>& names,
bool areAssertions ) const
{
}

}  // namespace parser
}  // namespace CVC4

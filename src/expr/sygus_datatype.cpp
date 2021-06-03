/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of class for constructing SyGuS datatypes.
 */

#include "expr/sygus_datatype.h"

#include <sstream>
#include "expr/skolem_manager.h"

using namespace cvc5::kind;

namespace cvc5 {

SygusDatatype::SygusDatatype(const std::string& name) : d_dt(DType(name)) {}

std::string SygusDatatype::getName() const { return d_dt.getName(); }

void SygusDatatype::addConstructor(Node op,
                                   const std::string& name,
                                   const std::vector<TypeNode>& argTypes,
                                   int weight)
{
  d_cons.push_back(SygusDatatypeConstructor());
  d_cons.back().d_op = op;
  d_cons.back().d_name = name;
  d_cons.back().d_argTypes = argTypes;
  d_cons.back().d_weight = weight;
}

void SygusDatatype::addAnyConstantConstructor(TypeNode tn)
{
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  // add an "any constant" proxy variable
  Node av = sm->mkDummySkolem("_any_constant", tn);
  // mark that it represents any constant
  SygusAnyConstAttribute saca;
  av.setAttribute(saca, true);
  std::stringstream ss;
  ss << getName() << "_any_constant";
  std::string cname(ss.str());
  std::vector<TypeNode> builtinArg;
  builtinArg.push_back(tn);
  addConstructor(
      av, cname, builtinArg, 0);
}
void SygusDatatype::addConstructor(Kind k,
                                   const std::vector<TypeNode>& argTypes,
                                   int weight)
{
  NodeManager* nm = NodeManager::currentNM();
  addConstructor(nm->operatorOf(k), kindToString(k), argTypes, weight);
}

size_t SygusDatatype::getNumConstructors() const { return d_cons.size(); }

const SygusDatatypeConstructor& SygusDatatype::getConstructor(unsigned i) const
{
  Assert(i < d_cons.size());
  return d_cons[i];
}

void SygusDatatype::initializeDatatype(TypeNode sygusType,
                                       Node sygusVars,
                                       bool allowConst,
                                       bool allowAll)
{
  // should not have initialized (set sygus) yet
  Assert(!isInitialized());
  // should have added a constructor
  Assert(!d_cons.empty());
  /* Use the sygus type to not lose reference to the original types (Bool,
   * Int, etc) */
  d_dt.setSygus(sygusType, sygusVars, allowConst, allowAll);
  for (unsigned i = 0, ncons = d_cons.size(); i < ncons; ++i)
  {
    // add (sygus) constructor
    d_dt.addSygusConstructor(d_cons[i].d_op,
                             d_cons[i].d_name,
                             d_cons[i].d_argTypes,
                             d_cons[i].d_weight);
  }
  Trace("sygus-type-cons") << "...built datatype " << d_dt << " ";
}

const DType& SygusDatatype::getDatatype() const
{
  // should have initialized by this point
  Assert(isInitialized());
  return d_dt;
}

bool SygusDatatype::isInitialized() const { return d_dt.isSygus(); }

}  // namespace cvc5

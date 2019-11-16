/*********************                                                        */
/*! \file sygus_datatype.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of class for constructing SyGuS datatypes.
 **/

#include "expr/sygus_datatype.h"

#include "printer/sygus_print_callback.h"

using namespace CVC4::kind;

namespace CVC4 {

SygusDatatype::SygusDatatype(const std::string& name) : d_dt(Datatype(name)) {}

std::string SygusDatatype::getName() const { return d_dt.getName(); }

void SygusDatatype::addConstructor(Node op,
                                   const std::string& name,
                                   const std::vector<TypeNode>& consTypes,
                                   std::shared_ptr<SygusPrintCallback> spc,
                                   int weight)
{
  d_ops.push_back(op);
  d_cons_names.push_back(std::string(name));
  d_pc.push_back(spc);
  d_weight.push_back(weight);
  d_consArgs.push_back(consTypes);
}

void SygusDatatype::addAnyConstantConstructor(TypeNode tn)
{
  // add an "any constant" proxy variable
  Node av = NodeManager::currentNM()->mkSkolem("_any_constant", tn);
  // mark that it represents any constant
  SygusAnyConstAttribute saca;
  av.setAttribute(saca, true);
  std::stringstream ss;
  ss << getName() << "_any_constant";
  std::string cname(ss.str());
  std::vector<TypeNode> builtinArg;
  builtinArg.push_back(tn);
  addConstructor(
      av, cname, builtinArg, printer::SygusEmptyPrintCallback::getEmptyPC(), 0);
}
void SygusDatatype::addConstructor(Kind k,
                      const std::vector<TypeNode>& consTypes,
                      std::shared_ptr<SygusPrintCallback> spc,
                      int weight)
{
  NodeManager * nm = NodeManager::currentNM();
  addConstructor(nm->operatorOf(k), kindToString(k), consTypes, spc, weight);
}

size_t SygusDatatype::getNumConstructors() const { return d_ops.size(); }

void SygusDatatype::initializeDatatype(TypeNode sygusType,
                                       Node sygusVars,
                                       bool allowConst,
                                       bool allowAll)
{
  // should not have initialized (set sygus) yet
  Assert(!d_dt.isSygus());
  /* Use the sygus type to not lose reference to the original types (Bool,
   * Int, etc) */
  d_dt.setSygus(sygusType.toType(), sygusVars.toExpr(), allowConst, allowAll);
  for (unsigned i = 0, size_d_ops = d_ops.size(); i < size_d_ops; ++i)
  {
    // must convert to type now
    std::vector<Type> cargs;
    for (TypeNode& ct : d_consArgs[i])
    {
      cargs.push_back(ct.toType());
    }
    // add (sygus) constructor
    d_dt.addSygusConstructor(
        d_ops[i].toExpr(), d_cons_names[i], cargs, d_pc[i], d_weight[i]);
  }
  Trace("sygus-type-cons") << "...built datatype " << d_dt << " ";
}

const Datatype& SygusDatatype::getDatatype() const
{
  // should have initialized by this point
  Assert(d_dt.isSygus());
  return d_dt;
}

}  // namespace CVC4

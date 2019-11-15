/*********************                                                        */
/*! \file sygus_type_constructor.cpp
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

#include "theory/quantifiers/sygus/sygus_type_constructor.h"

#include "printer/sygus_print_callback.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusTypeConstructor::SygusTypeConstructor(const std::string& name)
    : d_dt(Datatype(name))
{
}

std::string SygusTypeConstructor::getName() const
{
  return d_dt.getName();
}

void SygusTypeConstructor::addConstructor(Node op,
                                       const std::string&  name,
                                       std::shared_ptr<SygusPrintCallback> spc,
                                       int weight,
                                       const std::vector<TypeNode>& consTypes)
{
  d_ops.push_back(op);
  d_cons_names.push_back(std::string(name));
  d_pc.push_back(spc);
  d_weight.push_back(weight);
  d_consArgs.push_back(consTypes);
}

void SygusTypeConstructor::addAnyConstantConstructor(TypeNode tn)
{
  // add an "any constant" proxy variable
  Node av = NodeManager::currentNM()->mkSkolem("_any_constant", tn);
  // mark that it represents any constant
  SygusAnyConstAttribute saca;
  av.setAttribute(saca, true);
  std::stringstream ss;
  ss << getName() << "_any_constant";
  std::string cname(ss.str());
  std::vector<TypeNode> builtin_arg;
  builtin_arg.push_back(tn);
  // we add this constructor first since we use left associative chains
  // and our symmetry breaking should group any constants together
  // beneath the same application
  // we set its weight to zero since it should be considered at the
  // same level as constants.
  d_ops.insert(d_ops.begin(), av.toExpr());
  d_cons_names.insert(d_cons_names.begin(), cname);
  d_consArgs.insert(d_consArgs.begin(), builtin_arg);
  d_pc.insert(d_pc.begin(), printer::SygusEmptyPrintCallback::getEmptyPC());
  d_weight.insert(d_weight.begin(), 0);
}

void SygusTypeConstructor::buildDatatype(TypeNode sygusType,
                                         Node sygusVars,
                                         bool allowConst,
                                         bool allowAll)
{
  /* Use the sygus type to not lose reference to the original types (Bool,
   * Int, etc) */
  d_dt.setSygus(sygusType.toType(),
                sygusVars.toExpr(),
                allowConst,
                allowAll);
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


const Datatype& SygusTypeConstructor::getDatatype() const
{
  return d_dt;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

/*********************                                                        */
/*! \file sygus_grammar_norm.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief implementation of class for for simplifying SyGuS grammars after they
 ** are encoded into datatypes.
 **/

#include "theory/quantifiers/sygus_grammar_norm.h"

#include "expr/datatype.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/ce_guided_conjecture.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

TypeObject::TypeObject(std::string type_name) : d_dt(Datatype(type_name))
{
  d_tn = TypeNode::null();
  /* Create an unresolved type */
  d_unres_t = NodeManager::currentNM()
                  ->mkSort(type_name, ExprManager::SORT_FLAG_PLACEHOLDER)
                  .toType();
}

TypeObject::TypeObject(TypeNode src_tn, std::string type_name)
    : d_dt(Datatype(type_name))
{
  d_tn = src_tn;
  d_t = src_tn.toType();
  /* Create an unresolved type */
  d_unres_t = NodeManager::currentNM()
                  ->mkSort(type_name, ExprManager::SORT_FLAG_PLACEHOLDER)
                  .toType();
}

SygusGrammarNorm::SygusGrammarNorm(QuantifiersEngine* qe, CegConjecture* p)
    : d_qe(qe), d_parent(p), d_tds(d_qe->getTermDatabaseSygus())
{
}

/* recursion depth is limited by the height of the types, which is small  */
void SygusGrammarNorm::collectInfoFor(TypeNode tn,
                                      std::vector<TypeObject>& tos,
                                      std::map<TypeNode, Type>& tn_to_unres,
                                      std::map<TypeNode, bool>& visited)
{
  if (visited.find(tn) != visited.end())
  {
    return;
  }
  visited[tn] = true;
  Assert(tn.isDatatype());
  /* Create new type name */
  std::stringstream ss;
  ss << tn << "_norm";
  std::string type_name = ss.str();
  /* Add to global accumulators */
  tos.push_back(TypeObject(tn, type_name));
  const Datatype& dt = static_cast<DatatypeType>(tos.back().d_t).getDatatype();
  tn_to_unres[tn] = tos.back().d_unres_t;
  /* Visit types of constructor arguments */
  for (const DatatypeConstructor& cons : dt)
  {
    for (const DatatypeConstructorArg& arg : cons)
    {
      collectInfoFor(
          TypeNode::fromType(
              static_cast<SelectorType>(arg.getType()).getRangeType()),
          tos,
          tn_to_unres,
          visited);
    }
  }
}

void SygusGrammarNorm::normalizeSygusInt(unsigned ind,
                                         std::vector<TypeObject>& tos,
                                         std::map<TypeNode, Type>& tn_to_unres,
                                         Node sygus_vars)
{
  const Datatype& dt =
      static_cast<DatatypeType>(tos[ind].d_t).getDatatype();
  Trace("sygus-grammar-normalize")
      << "Normalizing integer type " << tos[ind].d_tn << " from datatype\n"
      << dt << std::endl;
}

TypeNode SygusGrammarNorm::normalizeSygusType(TypeNode tn, Node sygus_vars)
{
  /* Make int_type and zero */
  NodeManager* nm = NodeManager::currentNM();
  /* Accumulates all typing information for normalization and reconstruction */
  std::vector<TypeObject> tos;
  /* Allows retrieving respective unresolved types for the sygus types of the
   * original type nodes */
  std::map<TypeNode, Type> tn_to_unres;
  std::map<TypeNode, bool> visited;
  collectInfoFor(tn, tos, tn_to_unres, visited);
  /* Build datatypes TODO and normalize accordingly #1304 */
  for (unsigned i = 0, size = tos.size(); i < size; ++i)
  {
    const Datatype& dt =
        static_cast<DatatypeType>(tos[i].d_t).getDatatype();
    Trace("sygus-grammar-normalize")
        << "Rebuild " << tos[i].d_tn << " from " << dt << std::endl;
    /* Collect information to rebuild constructors */
    for (const DatatypeConstructor& cons : dt)
    {
      Trace("sygus-grammar-normalize")
          << "...for " << cons.getName() << std::endl;
      /* Recover the sygus operator to not lose reference to the original
       * operator (NOT, ITE, etc) */
      tos[i].d_ops.push_back(cons.getSygusOp());
      tos[i].d_cons_names.push_back(cons.getName());
      tos[i].d_cons_args_t.push_back(std::vector<Type>());
      for (const DatatypeConstructorArg& arg : cons)
      {
        /* Collect unresolved types corresponding to the typenode of the
         * arguments */
        tos[i].d_cons_args_t.back().push_back(tn_to_unres[TypeNode::fromType(
            static_cast<SelectorType>(arg.getType()).getRangeType())]);
      }
    }
    /* Use the sygus type to not lose reference to the original types (Bool,
     * Int, etc) */
    tos[i].d_dt.setSygus(dt.getSygusType(),
                         sygus_vars.toExpr(),
                         dt.getSygusAllowConst(),
                         dt.getSygusAllowAll());
    for (unsigned j = 0, size_d_ops = tos[i].d_ops.size(); j < size_d_ops; ++j)
    {
      tos[i].d_dt.addSygusConstructor(
          tos[i].d_ops[j], tos[i].d_cons_names[j], tos[i].d_cons_args_t[j]);
    }
    Trace("sygus-grammar-normalize")
        << "...built datatype " << tos[i].d_dt << std::endl;
  }
  /* Resolve types */
  std::vector<Datatype> dts;
  std::set<Type> unres_all;
  for (TypeObject& to : tos)
  {
    dts.push_back(to.d_dt);
    unres_all.insert(to.d_unres_t);
  }
  std::vector<DatatypeType> types =
      nm->toExprManager()->mkMutualDatatypeTypes(dts, unres_all);
  Assert(types.size() == dts.size());
  /* By construction the normalized type node will be first one considered */
  return TypeNode::fromType(types[0]);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

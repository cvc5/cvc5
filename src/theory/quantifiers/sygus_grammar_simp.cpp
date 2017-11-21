/*********************                                                        */
/*! \file sygus_grammar_cons.cpp
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

#include "theory/quantifiers/sygus_grammar_simp.h"

#include <stack>

#include "expr/datatype.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/ce_guided_conjecture.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

TypeObject::TypeObject(TypeNode tn)
{
  d_tn = tn;
  /* Create new datatype */
  std::stringstream ss;
  ss << tn << "_norm";
  std::string dt_name = ss.str();
  Datatype* tmp_dt = new Datatype(dt_name);
  unres_dt = tmp_dt;
  /* Create an unresolved type */
  unres_t = NodeManager::currentNM()
                ->mkSort(dt_name, ExprManager::SORT_FLAG_PLACEHOLDER)
                .toType();
}

SygusGrammarSimplifier::SygusGrammarSimplifier(QuantifiersEngine* qe,
                                               CegConjecture* p)
    : d_qe(qe), d_parent(p), d_tds(d_qe->getTermDatabaseSygus())
{
}

void SygusGrammarSimplifier::collectInfoFor(
    TypeNode tn,
    std::vector<TypeObject>& tos,
    std::map<TypeNode, Type>& tn_to_unres,
    std::set<Type>& unres_all,
    std::map<TypeNode, bool>& visited)
{
  if (visited.find(tn) != visited.end())
  {
    return;
  }
  visited[tn] = true;
  Assert(tn.isDatatype());
  Trace("sygus-grammar-normalize")
      << "...will need to rebuild " << tn << std::endl;
  /* Add to global accumulators */
  tos.push_back(TypeObject(tn));
  tn_to_unres[tn] = tos.back().unres_t;
  unres_all.insert(tos.back().unres_t);
  /* Visit types of constructor arguments */
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  for (const DatatypeConstructor& cons : dt)
  {
    for (const DatatypeConstructorArg& arg : cons)
    {
      collectInfoFor(
          TypeNode::fromType(
              static_cast<SelectorType>(arg.getType()).getRangeType()),
          tos,
          tn_to_unres,
          unres_all,
          visited);
    }
  }
}

/* Make int_type and zero */
/* const Type& int_type = nm->integerType().toType(); */
/* Node zero = */
/*     d_qe->getTermUtil()->getTypeValue(TypeNode::fromType(int_type), 0); */

/* /\* Normalize integer type *\/ */
/* if (dt.getSygusType() == int_type) */
/* { */
/*   Trace("sygus-grammar-normalize") */
/*       << "Normalizing integer type " << tn << " from datatype\n" */
/*       << dt << std::endl; */
/*   /\* Initialize term database utilities for the given typenode and retrieve
 */
/*    * some stuff *\/ */
/*   d_tds->registerSygusType(type_nodes[i]); */
/*   /\* Build ITE if it has ITE *\/ */
/*   int ite_cons_pos = d_tds->getKindConsNum(type_nodes[i], ITE); */
/*   if (ite_cons_pos != -1) */
/*   { */
/*     Trace("sygus-grammar-normalize") << "...add for " << ITE << std::endl; */
/*     ops[i].push_back(nm->operatorOf(ITE).toExpr()); */
/*     cons_names.push_back(kindToString(ITE)); */
/*     cons_args.push_back(std::vector<Type>()); */
/*     cons_args.back().push_back(unres_bt); */
/*     cons_args.back().push_back(unres_t); */
/*     cons_args.back().push_back(unres_t); */
/*   } */
/*   unsigned name_count = 0; */
/*   /\* Build normalized minus if has 0 and minus *\/ */
/*   /\* std::vector<Node> consts = d_tds->getConstList(type_nodes[i]); *\/ */
/*   /\* std::vector<Node> vars = d_tds->getVarList(type_nodes[i]); *\/ */
/*   /\* Trace("sygus-grammar-normalize") *\/ */
/*   /\*     << "...have to add vars " << vars << std::endl; *\/ */
/*   /\* Trace("sygus-grammar-normalize") *\/ */
/*   /\*     << "...have to add consts " << consts << std::endl; *\/ */
/*   if (d_tds->hasKind(type_nodes[i], MINUS) */
/*       && d_tds->hasConst(type_nodes[i], zero)) */
/*   { */
/*     Trace("sygus-grammar-normalize") << "\tHas minus and 0\n"; */
/*     ops[i].push_back(nm->operatorOf(MINUS).toExpr()); */
/*     cons_names.push_back(kindToString(MINUS)); */
/*     cons_args.push_back(std::vector<Type>()); */
/*     /\* Create type of zero *\/ */
/*     std::stringstream ss; */
/*     ss << type_nodes[i] << "_zero"; */
/*     std::string name_zero = ss.str(); */
/*     Type unres_zero = */
/*         nm->mkSort(name_zero, ExprManager::SORT_FLAG_PLACEHOLDER).toType();
 */
/*     unres_types.push_back(unres_zero); */
/*     unres_all.insert(unres_zero); */

/*     /\* Adding type of zero and rest to minus *\/ */
/*     cons_args.back().push_back(unres_zero); */
/*     /\* For now have rest as int *\/ */
/*     cons_args.back().push_back(unres_t); */

/*     /\* std::stringstream ss; *\/ */
/*     /\* ss << type_nodes[i] << name_count++; *\/ */
/*     /\* std::string name_arg2 = ss.str(); *\/ */
/*     /\* Datatype dt_minus_arg2 = Datatype(name_arg2); *\/ */
/*     /\* /\\* Add placeholder for operators this datatype will have *\\/ *\/
 */
/*     /\* ops.push_back(std::vector<Expr>()); *\/ */
/*     /\* /\\* Create an unresolved type to stand for this datatype when */
/*      * resolved *\\/ *\/ */
/*     /\* Type unres_minus = *\/ */
/*     /\*     nm->mkSort(name, ExprManager::SORT_FLAG_PLACEHOLDER).toType();
 * *\/ */
/*     /\* unres_types.push_back(unres_minus); *\/ */
/*     /\* unres_all.insert(unres_t); *\/ */
/*   } */
/* } */

/* add this:     gr = Node::fromExpr(
 * smt::currentSmtEngine()->expandDefinitions( gr.toExpr() ) ); */

/* void SygusGrammarSimplifier::processTypeObject( */
/*     unsigned index, */
/*     Node sygus_vars, */
/*     std::vector<DatatypeConstructorArg> sels, */
/*     std::vector<TypeObject>& tos, */
/*     std::map<TypeNode, Type>& tn_to_unres, */
/*     std::set<Type>& unres_all) */
/* { */
/*   Trace("sygus-grammar-normalize") */
/*       << "Type " << tos[index].tn << " will be have the same structure as
 * before\n"; */
/*   for (const DatatypeConstructor& cons : tos[index].dt) */
/*   { */
/*     Trace("sygus-grammar-normalize") */
/*         << "...for " << cons.getName() << std::endl; */
/*     tos[index].ops.push_back(cons.getConstructor()); */
/*     tos[index].cons_names.push_back(cons.getName()); */
/*     for (const DatatypeConstructorArg& arg : cons) */
/*     { */
/*       tos[index].cons_args.push_back(tn_to_unres[TypeNode::fromType( */
/*           static_cast<SelectorType>(arg.getType()).getRangeType())]); */
/*     } */
/*   } */
/*   /\* Add for all selectors to this type *\/ */
/*   if (!sels.empty()) */
/*   { */
/*     Trace("sygus-grammar-normalize") << "...add for selectors" << std::endl;
 */
/*     for (const DatatypeConstructorArg& arg : sels) */
/*     { */
/*       Trace("sygus-grammar-normalize") */
/*           << "\t...for " << arg.getName() << std::endl; */
/*       tos[index].ops.push_back(arg.getSelector()); */
/*       tos[index].cons_names.push_back(arg.getName()); */
/*       tos[index].cons_args.push_back(tn_to_unres[TypeNode::fromType( */
/*           static_cast<SelectorType>(arg.getType()).getDomain())]); */
/*     } */
/*   } */
/*   Trace("sygus-grammar-normalize") */
/*       << "...make datatype " << tos[index].unres_dt << std::endl; */
/*   tos[index].unres_dt.setSygus(tos[index].t, sygus_vars.toExpr(), true,
 * true); */
/*   for (unsigned i = 0, size_ops = tos[index].ops.size(); i < size_ops; ++i)
 */
/*   { */
/*     tos[index].unres_dt.addSygusConstructor( */
/*         tos[index].ops[i], tos[index].cons_names[i],
 * tos[index].cons_args[i]); */
/*   } */
/*   Trace("sygus-grammar-normalize") */
/*       << "...result is " << tos[index].unres_dt << std::endl; */
/* } */

TypeNode SygusGrammarSimplifier::normalizeSygusType(TypeNode tn,
                                                    Node sygus_vars)
{
  /* Accumulates all typing information for normalization and reconstruction */
  std::vector<TypeObject> tos;
  /* Allows retrieving respective unresolved types for typenodes */
  std::map<TypeNode, Type> tn_to_unres;
  /* Accomulator of all unresolved types and datypes */
  std::set<Type> unres_all;
  std::map<TypeNode, bool> visited;
  collectInfoFor(tn, tos, tn_to_unres, unres_all, visited);
  /* Build datatypes TODO and normalize accordingly */
  for (unsigned i = 0, size = tos.size(); i < size; ++i)
  {
    /* processTypeObject(i, sygus_vars, tos, tn_to_unres,
     * unres_all);
     */
    const Datatype& dt =
        static_cast<DatatypeType>(tos[i].d_tn.toType()).getDatatype();
    Trace("sygus-grammar-normalize")
        << "Type " << tos[i].d_tn << " whose sygus type is "
        << dt.getSygusType() << " to be normalized with datatype " << dt
        << std::endl;
    for (const DatatypeConstructor& cons : dt)
    {
      Trace("sygus-grammar-normalize")
          << "...for " << cons.getName() << std::endl;
      tos[i].ops.push_back(cons.getConstructor());
      tos[i].cons_names.push_back(cons.getName());
      tos[i].cons_args.push_back(std::vector<Type>());
      for (const DatatypeConstructorArg& arg : cons)
      {
        tos[i].cons_args.back().push_back(tn_to_unres[TypeNode::fromType(
            static_cast<SelectorType>(arg.getType()).getRangeType())]);
      }
    }
    Trace("sygus-grammar-normalize")
        << "...make datatype " << *tos[i].unres_dt << std::endl;
    /* Use original type represented */
    tos[i].unres_dt->setSygus(
        tos[i].d_tn.toType(), sygus_vars.toExpr(), true, true);
    for (unsigned j = 0, size_ops = tos[i].ops.size(); j < size_ops; ++j)
    {
      tos[i].unres_dt->addSygusConstructor(
          tos[i].ops[j], tos[i].cons_names[j], tos[i].cons_args[j]);
    }
    Trace("sygus-grammar-normalize")
        << "...result is " << *tos[i].unres_dt << std::endl;
  }
  /* Resolve types */
  Trace("sygus-grammar-normalize")
      << "...made " << tos.size()
      << " datatypes, now make mutual datatype types..." << std::endl;
  std::vector<Datatype> dts;
  for (TypeObject& to : tos)
  {
    dts.push_back(*to.unres_dt);
  }
  std::vector<DatatypeType> types =
      NodeManager::currentNM()->toExprManager()->mkMutualDatatypeTypes(
          dts, unres_all);
  Assert(types.size() == dts.size());
  TypeNode tn_norm = TypeNode::fromType(types[0]);
  const Datatype& dt = static_cast<DatatypeType>(tn_norm.toType()).getDatatype();
  Trace("sygus-grammar-normalize")
      << "Made typenode " << tn_norm << " with datatype " << dt
      << " which has sygus type " << dt.getSygusType() << " while " << tn
      << " had sygus type "
      << static_cast<DatatypeType>(tn.toType()).getDatatype().getSygusType()
      << "\n";
  /* Make int_type and zero */
  NodeManager* nm = NodeManager::currentNM();
  const Type& int_type = nm->integerType().toType();
  Node zero =
      d_qe->getTermUtil()->getTypeValue(TypeNode::fromType(int_type), 0);
  d_tds->registerSygusType(tn_norm);
  d_tds->registerSygusType(tn);
  if (d_tds->hasKind(tn_norm, MINUS) && d_tds->hasConst(tn_norm, zero))
  {
    Trace("sygus-grammar-normalize") << tn_norm << " has minus and 0\n";
  }
  else if (d_tds->hasKind(tn, MINUS) && d_tds->hasConst(tn, zero))
  {
    Trace("sygus-grammar-normalize") << tn_norm << " does not have minus and 0 but " << tn << " does\n";
  }
  else
  {
    Trace("sygus-grammar-normalize") << tn_norm << " nor " << tn << " has minus and 0\n";
  }
  return tn_norm;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

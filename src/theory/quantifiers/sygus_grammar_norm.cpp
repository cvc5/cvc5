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
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
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
  /* Utilities */
  d_nm = NodeManager::currentNM();
  d_smte = smt::currentSmtEngine();
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
                                         const Datatype& dt,
                                         Node sygus_vars)
{
  Trace("sygus-grammar-normalize-int")
      << "Normalizing integer type " << tos[ind].d_tn << " from datatype\n"
      << dt << std::endl;
  /* Accumulators for variables and constants */
  std::vector<Node> vars, consts;
  /* Conditions for grammar recipe */
  bool has_minus = false, has_zero = false, has_plus = false, has_one = false;
  const Type& int_type = d_nm->integerType().toType();
  Node zero =
      d_qe->getTermUtil()->getTypeValue(TypeNode::fromType(int_type), 0);
  Node one =
      d_qe->getTermUtil()->getTypeValue(TypeNode::fromType(int_type), 1);
  /* Collect non-normalizable constructors and assert conditions */
  for (const DatatypeConstructor& cons : dt)
  {
    Expr sop = cons.getSygusOp();
    Kind sop_k = sop.getKind();
    /* Better way?? */
    Kind actual_sop_k = d_nm->operatorToKind(sop);
    /* Ignore + and - */
    if (sop_k == BUILTIN && actual_sop_k != ITE)
    {
      Trace("sygus-grammar-normalize-int")
          << "Operator " << cons.getSygusOp()
          << " is builtin and not an ITE and has actual kind " << actual_sop_k
          << "\n";
      if (actual_sop_k == PLUS)
      {
        has_plus = true;
      }
      else
      {
        AlwaysAssert(actual_sop_k == MINUS);
        has_minus = true;
      }
      continue;
    }
    /* How come ITE is constant?? */
    if (sop.isConst() && actual_sop_k != ITE)
    {
      Node sop_n = Node::fromExpr(sop);
      if (sop_n == zero)
      {
        Trace("sygus-grammar-normalize-int") << "Const " << sop << " is zero\n";
        has_zero = true;
      }
      else if (sop_n == one)
      {
        Trace("sygus-grammar-normalize-int") << "Const " << sop << " is one\n";
        has_one = true;
      }
      else
      {
        Trace("sygus-grammar-normalize-int")
            << "Collecting const " << sop << "\n";
        consts.push_back(sop_n);
      }
      continue;
    }
    if (sop_k == BOUND_VARIABLE)
    {
      Trace("sygus-grammar-normalize-int") << "Collecting var " << sop << "\n";
      vars.push_back(Node::fromExpr(sop));
      continue;
    }
    /* Collect constructor to rebuild */
    Node exp_sop_n = Node::fromExpr(d_smte->expandDefinitions(sop));
    tos[ind].d_ops.push_back(Rewriter::rewrite(exp_sop_n));
    Trace("sygus-grammar-normalize-defs")
        << "\tOriginal op: " << sop
        << "\n\tExpanded one: " << exp_sop_n
        << "\n\tRewritten one: " << tos[ind].d_ops.back() << "\n\n";
    tos[ind].d_cons_names.push_back(cons.getName());
    tos[ind].d_pcb.push_back(cons.getSygusPrintCallback());
    tos[ind].d_cons_args_t.push_back(std::vector<Type>());
    for (const DatatypeConstructorArg& arg : cons)
    {
      /* Collect unresolved types corresponding to the typenode of the
       * arguments */
      tos[ind].d_cons_args_t.back().push_back(tn_to_unres[TypeNode::fromType(
          static_cast<SelectorType>(arg.getType()).getRangeType())]);
    }
  }
  /* Initialize term database utilities for the given typenode and retrieve
   * some stuff */
  d_tds->registerSygusType(tos[ind].d_tn);

  /* Build normalized minus if has 0 and if has not */
  /* Build normalized + */

  /* extra constants?? */

  /* Building datatype */
  tos[ind].d_dt.setSygus(dt.getSygusType(),
                         sygus_vars.toExpr(),
                         dt.getSygusAllowConst(),
                         dt.getSygusAllowAll());
  for (unsigned i = 0, size_d_ops = tos[ind].d_ops.size(); i < size_d_ops; ++i)
  {
    tos[ind].d_dt.addSygusConstructor(tos[ind].d_ops[i].toExpr(),
                                      tos[ind].d_cons_names[i],
                                      tos[ind].d_cons_args_t[i],
                                      tos[ind].d_pcb[i]);
  }
  Trace("sygus-grammar-normalize")
      << "...built datatype " << tos[ind].d_dt << std::endl;
}

TypeNode SygusGrammarNorm::normalizeSygusType(TypeNode tn, Node sygus_vars)
{
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
    /* Whether type can be normalized */
    if (dt.getSygusType().isInteger())
    {
      normalizeSygusInt(i, tos, tn_to_unres, dt, sygus_vars);
      continue;
    }
    Trace("sygus-grammar-normalize")
        << "Rebuild " << tos[i].d_tn << " from " << dt << std::endl;
    /* Collect information to rebuild constructors */
    for (const DatatypeConstructor& cons : dt)
    {
      Trace("sygus-grammar-normalize")
          << "...for " << cons.getName() << std::endl;
      /* Recover the sygus operator to not lose reference to the original
       * operator (NOT, ITE, etc) */
      Node exp_sop_n =
          Node::fromExpr(d_smte->expandDefinitions(cons.getSygusOp()));
      tos[i].d_ops.push_back(Rewriter::rewrite(exp_sop_n));
      Trace("sygus-grammar-normalize-defs")
          << "\tOriginal op: " << cons.getSygusOp()
          << "\n\tExpanded one: " << exp_sop_n
          << "\n\tRewritten one: " << tos[i].d_ops.back() << "\n\n";
      tos[i].d_cons_names.push_back(cons.getName());
      tos[i].d_pcb.push_back(cons.getSygusPrintCallback());
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
      tos[i].d_dt.addSygusConstructor(tos[i].d_ops[j].toExpr(),
                                      tos[i].d_cons_names[j],
                                      tos[i].d_cons_args_t[j],
                                      tos[i].d_pcb[j]);
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
      d_nm->toExprManager()->mkMutualDatatypeTypes(dts, unres_all);
  Assert(types.size() == dts.size());
  /* By construction the normalized type node will be first one considered */
  return TypeNode::fromType(types[0]);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

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

SygusGrammarSimplifier::SygusGrammarSimplifier(QuantifiersEngine* qe,
                                               CegConjecture* p)
    : d_qe(qe),
      d_parent(p),
      d_tds(d_qe->getTermDatabaseSygus()),
      d_is_syntax_restricted(false),
      d_has_ite(true)
{
}

void SygusGrammarSimplifier::collectSygusGrammarVars(
    TypeNode tn,
    std::vector<Node>& vars,
    std::map<TypeNode, bool>& visited)
{
  if (visited.find(tn) != visited.end())
  {
    return;
  }
  visited[tn] = true;
  Assert(tn.isDatatype());
  /* Look for variables */
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  for (unsigned i = 0, size_dt = dt.getNumConstructors(); i < size_dt; ++i)
  {
    Node sygus_opn = Node::fromExpr(dt[i].getSygusOp());
    if (sygus_opn.getKind() == BOUND_VARIABLE)
    {
      vars.push_back(sygus_opn);
      continue;
    }
    /* if (sygus_opn.getKind() == BOUND_VARIABLE) */
    /* { */
    /*   vars.push_back(sygus_opn); */
    /*   continue; */
    /* } */
    for (unsigned j = 0, size_cons = dt[i].getNumArgs(); j < size_cons; ++j)
    {
      TypeNode cons_range = TypeNode::fromType(
          static_cast<SelectorType>(dt[i][j].getType()).getRangeType());
      collectSygusGrammarVars(cons_range, vars, visited);
    }
  }
}

void SygusGrammarSimplifier::collectSygusGrammarTypesFor(
    TypeNode range,
    std::vector<TypeNode>& types,
    std::map<TypeNode, std::vector<DatatypeConstructorArg>>& sels,
    TypeNode& bool_type)
{
  Assert(range.isDatatype());
  const Datatype& dt = static_cast<DatatypeType>(range.toType()).getDatatype();
  /* Whether there is a dependency on booleans */
  if (dt.getSygusType().isBoolean())
  {
    bool_type = range;
    return;
  }
  /* Dependencies already taken */
  if (std::find(types.begin(), types.end(), range) != types.end())
  {
    return;
  }
  Trace("sygus-grammar-normalize")
      << "...will need a grammar for " << range << std::endl;
  types.push_back(range);
  for (unsigned i = 0, size_dt = dt.getNumConstructors(); i < size_dt; ++i)
  {
    for (unsigned j = 0, size_cons = dt[i].getNumArgs(); j < size_cons; ++j)
    {
      TypeNode cons_range = TypeNode::fromType(
          static_cast<SelectorType>(dt[i][j].getType()).getRangeType());
      sels[cons_range].push_back(dt[i][j]);
      collectSygusGrammarTypesFor(cons_range, types, sels, bool_type);
    }
  }
}

TypeNode SygusGrammarSimplifier::normalizeSygusType(TypeNode tn)
{
  /* Accumulate types to be reconstructed. Bool is special? */
  TypeNode bool_type = TypeNode::null();
  std::vector<TypeNode> types;
  std::map<TypeNode, std::vector<DatatypeConstructorArg>> sels;
  collectSygusGrammarTypesFor(tn, types, sels, bool_type);
  /* Accumulates variables occurring in tn */
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> tn_vars;
  std::map<TypeNode, bool> visited;
  collectSygusGrammarVars(tn, tn_vars, visited);
  std::string bool_name;
  Type unres_bt;
  if (!bool_type.isNull())
  {
    Trace("sygus-grammar-normalize")
        << "Has bool type " << bool_type << std::endl;
    /* Create unresolved boolean type */
    std::stringstream ss;
    ss << bool_type;
    bool_name = ss.str();
    unres_bt =
        nm->mkSort(bool_name, ExprManager::SORT_FLAG_PLACEHOLDER).toType();
  }
  else
  {
    Trace("sygus-grammar-normalize") << "No previous boolean type\n";
  }
  /* Datatypes for each type */
  std::vector<Datatype> datatypes;
  /* Operators */
  std::vector<std::vector<Expr>> ops;
  /* Accomulator of all unresolved types */
  std::set<Type> unres_all;
  /* All unresolved types. This vector is "synced" with the types one */
  std::vector<Type> unres_types;
  /* Maintains the relation between types and their unresolved correspondents */
  std::map<TypeNode, Type> type_to_unres;
  for (unsigned i = 0, size = types.size(); i < size; ++i)
  {
    /* Create datatype */
    std::stringstream ss;
    ss << types[i];
    std::string dt_name = ss.str();
    datatypes.push_back(Datatype(dt_name));
    /* Add placeholder for operators this datatype will have */
    ops.push_back(std::vector<Expr>());
    /* Create an unresolved type to stand for this datatype when resolved */
    Type unres_t =
        nm->mkSort(dt_name, ExprManager::SORT_FLAG_PLACEHOLDER).toType();
    unres_types.push_back(unres_t);
    type_to_unres[types[i]] = unres_t;
    unres_all.insert(unres_t);
  }
  /* Make int_type and zero */
  const Type& int_type = nm->integerType().toType();
  Node zero =
      d_qe->getTermUtil()->getTypeValue(TypeNode::fromType(int_type), 0);
  /* Build datatypes TODO and normalize accordingly */
  for (unsigned i = 0, size = types.size(); i < size; ++i)
  {
    std::vector<std::string> cons_names;
    std::vector<std::vector<Type>> cons_args;
    Type unres_t = unres_types[i];
    /* Retrieve datatype encoding given typenode */
    const Datatype& dt =
        static_cast<DatatypeType>(types[i].toType()).getDatatype();
    /* Normalize integer type */
    if (dt.getSygusType() == int_type)
    {
      Trace("sygus-grammar-normalize")
          << "Normalizing integer type " << tn << " from datatype\n"
          << dt << std::endl;
      /* Initialize term database utilities for the given typenode and retrieve
       * some stuff */
      d_tds->registerSygusType(types[i]);
      /* Build ITE if it has ITE */
      if (d_tds->hasKind(types[i], ITE))
      {
        Trace("sygus-grammar-normalize") << "...add for " << ITE << std::endl;
        ops[i].push_back(nm->operatorOf(ITE).toExpr());
        cons_names.push_back(kindToString(ITE));
        cons_args.push_back(std::vector<Type>());
        cons_args.back().push_back(unres_bt);
        cons_args.back().push_back(unres_t);
        cons_args.back().push_back(unres_t);
      }
      unsigned name_count = 0;
      /* Build normalized minus if has 0 and minus */
      std::vector<Node> consts = d_tds->getConstList(types[i]);
      std::vector<Node> vars = d_tds->getVarList(types[i]);
      Trace("sygus-grammar-normalize")
          << "...have to add vars " << vars << std::endl;
      Trace("sygus-grammar-normalize")
          << "...have to add consts " << consts << std::endl;
      if (d_tds->hasKind(types[i], MINUS) && d_tds->hasConst(types[i], zero))
      {
        Trace("sygus-grammar-normalize") << "\tHas minus and 0\n";
        ops[i].push_back(nm->operatorOf(MINUS).toExpr());
        cons_names.push_back(kindToString(MINUS));
        cons_args.push_back(std::vector<Type>());
        /* Create type of zero */
        std::stringstream ss;
        ss << types[i] << "_zero";
        std::string name_zero = ss.str();
        Type unres_zero = nm->mkSort(name_zero, ExprManager::SORT_FLAG_PLACEHOLDER).toType();
        unres_types.push_back(unres_zero);
        unres_all.insert(unres_zero);

        /* Adding type of zero and rest to minus */
        cons_args.back().push_back(unres_zero);
        /* For now have rest as int */
        cons_args.back().push_back(unres_t);

        /* std::stringstream ss; */
        /* ss << types[i] << name_count++; */
        /* std::string name_arg2 = ss.str(); */
        /* Datatype dt_minus_arg2 = Datatype(name_arg2); */
        /* /\* Add placeholder for operators this datatype will have *\/ */
        /* ops.push_back(std::vector<Expr>()); */
        /* /\* Create an unresolved type to stand for this datatype when resolved *\/ */
        /* Type unres_minus = */
        /*     nm->mkSort(name, ExprManager::SORT_FLAG_PLACEHOLDER).toType(); */
        /* unres_types.push_back(unres_minus); */
        /* unres_all.insert(unres_t); */
      }
    }
    else /* Types that cannot be normalized are built normally */
    {
      Trace("sygus-grammar-normalize")
          << "Type " << types[i]
          << " will be have the same structure as before\n";
      for (unsigned j = 0, size_dt = dt.getNumConstructors(); j < size_dt; ++j)
      {
        Trace("sygus-grammar-normalize")
            << "...for " << dt[j].getName() << std::endl;
        ops[i].push_back(dt[j].getConstructor());
        cons_names.push_back(dt[j].getName());
        cons_args.push_back(std::vector<Type>());
        for (unsigned k = 0, size_cons = dt[j].getNumArgs(); k < size_cons; ++k)
        {
          TypeNode cons_range = TypeNode::fromType(
              static_cast<SelectorType>(dt[j][k].getType()).getRangeType());
          cons_args.back().push_back(type_to_unres[cons_range]);
        }
      }
      /* Add for all selectors to this type */
      if (!sels[types[i]].empty())
      {
        Trace("sygus-grammar-normalize") << "...add for selectors" << std::endl;
        for (unsigned j = 0, size_sels = sels[types[i]].size(); j < size_sels;
             ++j)
        {
          Trace("sygus-grammar-normalize")
              << "\t...for " << sels[types[i]][j].getName() << std::endl;
          TypeNode arg_tn = TypeNode::fromType(
              static_cast<SelectorType>(sels[types[i]][j].getType())
                  .getDomain());
          ops[i].push_back(sels[types[i]][j].getSelector());
          cons_names.push_back(sels[types[i]][j].getName());
          cons_args.push_back(std::vector<CVC4::Type>());
          cons_args.back().push_back(type_to_unres[arg_tn]);
        }
      }
    }
    Trace("sygus-grammar-normalize")
        << "...make datatype " << datatypes.back() << std::endl;
    datatypes[i].setSygus(types[i].toType(),
                          nm->mkNode(BOUND_VAR_LIST, tn_vars).toExpr(),
                          true,
                          true);
    for (unsigned j = 0, size_op = ops[i].size(); j < size_op; ++j)
    {
      datatypes[i].addSygusConstructor(ops[i][j], cons_names[j], cons_args[j]);
    }
    Trace("sygus-grammar-normalize")
        << "...result is " << datatypes.back() << std::endl;
  }
  /* Build boolean type */
  datatypes.push_back(Datatype(bool_name));
  ops.push_back(std::vector<Expr>());
  Trace("sygus-grammar-def") << "Make grammar for " << bool_type << " "
                             << datatypes.back() << std::endl;
  /* TODO take the vars */
  /* TODO take the constants */
  /* TODO recreate the operators */
  /* TODO recreate the predicates */

  /* Resolve types */

  return tn;
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

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
    unres_bt = NodeManager::currentNM()
                   ->mkSort(bool_name, ExprManager::SORT_FLAG_PLACEHOLDER)
                   .toType();
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
    Type unres_t = NodeManager::currentNM()
                          ->mkSort(dt_name, ExprManager::SORT_FLAG_PLACEHOLDER)
                          .toType();
    unres_types.push_back(unres_t);
    type_to_unres[types[i]] = unres_t;
    unres_all.insert(unres_t);
  }
  /* Make int_type */
  const Type& int_type = NodeManager::currentNM()->integerType().toType();
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
        ops[i].push_back(NodeManager::currentNM()->operatorOf(ITE).toExpr());
        cons_names.push_back(kindToString(ITE));
        cons_args.push_back(std::vector<Type>());
        cons_args.back().push_back(unres_bt);
        cons_args.back().push_back(unres_t);
        cons_args.back().push_back(unres_t);
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
    }
    /* Add for all selectors to this type */
    if (!sels[types[i]].empty())
    {
      Trace("sygus-grammar-normalize") << "...add for selectors" << std::endl;
      for (unsigned j = 0, size_sels = sels[types[i]].size(); j < ; ++j)
      {
        Trace("sygus-grammar-normalize")
            << "...for " << sels[types[i]][j].getName() << std::endl;
        TypeNode arg_type = TypeNode::fromType(
            static_cast<SelectorType>(sels[types[i]][j].getType()).getDomain());
        ops[i].push_back(sels[types[i]][j].getSelector());
        cnames.push_back(sels[types[i]][j].getName());
        cargs.push_back(std::vector<CVC4::Type>());
        cargs.back().push_back(type_to_unres[arg_type]);
      }
    }
    Trace("sygus-grammar-normalize")
        << "...make datatype " << datatypes.back() << std::endl;
    datatypes[i].setSygus(types[i].toType(), bvl.toExpr(), true, true);
    for (unsigned j = 0, size_op = ops[i].size(); j < size_op; ++j)
    {
      datatypes[i].addSygusConstructor(ops[i][j], cons_names[j], cons_args[j]);
    }
    if (types[i] == range)
    {
      startIndex = i;
    }
  }
  /* Build boolean type */
  datatypes.push_back(Datatype(bool_name));
  ops.push_back(std::vector<Expr>());
  Trace("sygus-grammar-def")
      << "Make grammar for " << bool_type << " " << datatypes.back() << std::endl;
  /* TODO take the vars */
  /* TODO take the constants */
  /* TODO recreate the operators */
  /* TODO recreate the predicates */

  /* Resolve types */





  /* const std::map<Kind, int>& tn_kinds = d_tds->getKindsMap(tn); */
  /* Assert(!tn_kinds.empty()); */
  /* /\* Trace("sygus-grammar-normalize") << "Ops " << dt.d_ops << std::endl; *\/ */
  /* std::map<Kind, int>::const_iterator it = tn_kinds.find(ITE); */
  /* if (it != tn_kinds.end()) */
  /* { */
  /*   Trace("sygus-grammar-normalize") */
  /*       << "Has ITE in position " << it->second << std::endl; */
  /* } */
  /* it = tn_kinds.find(PLUS); */
  /* if (it != tn_kinds.end()) */
  /* { */
  /*   Trace("sygus-grammar-normalize") */
  /*       << "Has PLUS in position " << it->second << std::endl; */
  /* } */
  /* it = tn_kinds.find(MINUS); */
  /* if (it != tn_kinds.end()) */
  /* { */
  /*   Trace("sygus-grammar-normalize") */
  /*       << "Has MINUS in position " << it->second << std::endl; */
  /* } */
  /* Trace("sygus-grammar-normalize") << "Vars " << dt.getSygusVarList() << std::endl; */
  /* Node zero = d_qe->getTermUtil()->getTypeValue( */
  /*     TypeNode::fromType(dt.getSygusType()), 0); */
  /* Trace("sygus-grammar-normalize") */
  /*     << "Type " << tn << " has const 0? " << d_tds->hasConst(tn, zero) */
  /*     << std::endl */
  /*     << "Type " << tn << " has +? " << d_tds->hasKind(tn, PLUS) << std::endl; */
  /* /\* Accumulate shallow elements and operators to normalize *\/ */
  /* std::vector<Node> ctes, vars; */
  /* /\* stores the positions of operators to be normalized. ZERO is in 0, ite in 1, */
  /*  * minus in 2, plus in 3, others in 4 and on. If operator not in grammar */
  /*  * position is set as -1 *\/ */
  /* std::vector<int> ops_positions(4); */
  /* std::fill(ops_positions.begin(), ops_positions.end(), -1); */
  /* for (i = 0; i < dt.getNumConstructors(); ++i) */
  /* { */
  /*   Expr sygus_op = dt[i].getSygusOp(); */
  /*   Node sygus_opn = Node::fromExpr(dt[i].getSygusOp()); */
  /*   /\* Trace("sygus-grammar-normalize") *\/ */
  /*   /\*     << "SygusOp " << opn << " has kind " << opn.getKind() << std::endl; *\/ */
  /*   /\* Trace("sygus-grammar-normalize") *\/ */
  /*   /\*     << "dt[" << i << "] = " << dt[i] << " has const 0? " *\/ */
  /*   /\*     << d_tds->hasConst(TypeNode::fromType(dt[i].getConstructor().getType()), *\/ */
  /*   /\*                        zero_int) *\/ */
  /*   /\*     << std::endl; *\/ */
  /*   if (sygus_op.isConst()) */
  /*   { */
  /*     ctes.push_back(sygus_opn); */
  /*     if (sygus_opn == zero) */
  /*     { */
  /*       Trace("sygus-grammar-normalize") */
  /*           << "\tOperator " << sygus_opn << " is zero\n"; */
  /*       ops_positions[0] = i; */
  /*     } */
  /*   } */
  /*   else if (sygus_opn.getKind() == BOUND_VARIABLE) */
  /*   { */
  /*     vars.push_back(sygus_opn); */
  /*   } */
  /*   else if (sygus_opn.getKind() == BUILTIN) */
  /*   { */
  /*     Kind op_actual_kind = NodeManager::operatorToKind(sygus_opn); */
  /*     if (op_actual_kind == ITE) */
  /*     { */
  /*       ops_positions[1] = i; */
  /*       Trace("sygus-grammar-normalize") */
  /*           << "SygusOp " << sygus_opn << " is ITE" << std::endl; */
  /*       for (j = 0; j < dt[i].getNumArgs(); j++) */
  /*       { */
  /*         TypeNode ct = TypeNode::fromType(dt[i][j].getRangeType()); */
  /*         Trace("sygus-grammar-normalize") */
  /*             << "   Child type " << j << " : " */
  /*             << static_cast<DatatypeType>(ct.toType()).getDatatype().getName() */
  /*             << std::endl; */
  /*       } */
  /*     } */
  /*     else if (op_actual_kind == MINUS) */
  /*     { */
  /*       ops_positions[2] = i; */
  /*       Trace("sygus-grammar-normalize") */
  /*           << "SygusOp " << sygus_opn << " is MINUS" << std::endl; */
  /*       for (j = 0; j < dt[i].getNumArgs(); ++j) */
  /*       { */
  /*         TypeNode ct = TypeNode::fromType(dt[i][j].getRangeType()); */
  /*         Trace("sygus-grammar-normalize") */
  /*             << "   Child type " << j << " : " */
  /*             << static_cast<DatatypeType>(ct.toType()).getDatatype().getName() */
  /*             << std::endl; */
  /*       } */
  /*     } */
  /*     else if (op_actual_kind == PLUS) */
  /*     { */
  /*       ops_positions[3] = i; */
  /*       Trace("sygus-grammar-normalize") */
  /*           << "SygusOp " << sygus_opn << " is PLUS" << std::endl; */
  /*       for (j = 0; j < dt[i].getNumArgs(); ++j) */
  /*       { */
  /*         TypeNode ct = TypeNode::fromType(dt[i][j].getRangeType()); */
  /*         Trace("sygus-grammar-normalize") */
  /*             << "   Child type " << j << " : " */
  /*             << static_cast<DatatypeType>(ct.toType()).getDatatype().getName() */
  /*             << std::endl; */
  /*       } */
  /*     } */
  /*     else */
  /*     { */
  /*       ops_positions.push_back(i); */
  /*       Trace("sygus-grammar-normalize") */
  /*           << "SygusOp " << sygus_opn << " is something else" << std::endl; */
  /*       for (j = 0; j < dt[i].getNumArgs(); ++j) */
  /*       { */
  /*         TypeNode ct = TypeNode::fromType(dt[i][j].getRangeType()); */
  /*         Trace("sygus-grammar-normalize") */
  /*             << "   Child type " << j << " : " */
  /*             << static_cast<DatatypeType>(ct.toType()).getDatatype().getName() */
  /*             << std::endl; */
  /*       } */
  /*     } */
  /*   } */
  /* } */
  /* /\* Build normalized grammar based on what is present in it *\/ */
  /* /\* Datatype norm_dt; *\/ */
  /* /\* Type unres_bt = NodeManager::currentNM()->mkSort( *\/ */
  /* /\*     dt.getName(), ExprManager::SORT_FLAG_PLACEHOLDER); *\/ */



  return tn;
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

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
#include "expr/node_manager_attributes.h"  // for VarNameAttr
#include "options/quantifiers_options.h"
#include "printer/sygus_print_callback.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/quantifiers/ce_guided_conjecture.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

#include <numeric>  // for std::iota

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

TypeObject::TypeObject(TypeNode src_tn, TypeNode unres_tn, Type unres_t)
    : d_dt(Datatype(unres_tn.getAttribute(expr::VarNameAttr())))
{
  d_tn = src_tn;
  /* Create an unresolved type */
  d_unres_tn = unres_tn;
  d_unres_t = unres_t;
}

bool TypeOpTrie::getOrMakeType(TypeNode tn,
                               TypeNode& unres_tn,
                               std::vector<bool> op_flags,
                               unsigned ind)
{
  Assert(ind != op_flags.size() || d_children.empty());
  if (ind == op_flags.size())
  {
    /* Found type */
    if (!d_unres_tn.isNull())
    {
      Trace("sygus-grammar-normalize-trie")
          << "\tFound type " << d_unres_tn << "\n";
      unres_tn = d_unres_tn;
      return true;
    }
    /* Creating unresolved type */
    std::stringstream ss;
    ss << tn << "_";
    for (const bool& flag : op_flags)
    {
      ss << "_" << std::to_string(flag);
    }
    d_unres_tn = NodeManager::currentNM()->mkSort(
        ss.str(), ExprManager::SORT_FLAG_PLACEHOLDER);
    Trace("sygus-grammar-normalize-trie")
        << "\tCreating type " << d_unres_tn << "\n";
    unres_tn = d_unres_tn;
    return false;
  }
  /* Go to next node */
  return d_children[op_flags[ind]].getOrMakeType(
      tn, unres_tn, op_flags, ind + 1);
}

SygusGrammarNorm::SygusGrammarNorm(QuantifiersEngine* qe)
    : d_qe(qe), d_tds(d_qe->getTermDatabaseSygus())
{
  /* Utilities */
  d_nm = NodeManager::currentNM();
  d_smte = smt::currentSmtEngine();
}

#if 0

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
  Node zero =
      d_qe->getTermUtil()->getTypeValue(TypeNode::fromType(d_int_type), 0);
  Node one = d_qe->getTermUtil()->getTypeValue(TypeNode::fromType(d_int_type), 1);
  /* TODO fix this */
  std::shared_ptr<printer::SygusEmptyPrintCallback> empty_pc =
      std::make_shared<printer::SygusEmptyPrintCallback>();
  /* Build integer identity operator */
  vars.push_back(d_nm->mkBoundVar(TypeNode::fromType(d_int_type)));
  Node iden_op = d_nm->mkNode(LAMBDA, d_nm->mkNode(BOUND_VAR_LIST, vars), vars.back());
  vars.clear();
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
      Trace("sygus-grammar-normalize-int2")
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
        Trace("sygus-grammar-normalize-int2")
            << "Const " << sop << " is zero\n";
        has_zero = true;
      }
      else if (sop_n == one)
      {
        Trace("sygus-grammar-normalize-int2") << "Const " << sop << " is one\n";
        has_one = true;
      }
      else
      {
        Trace("sygus-grammar-normalize-int2")
            << "Collecting const " << sop << "\n";
        consts.push_back(sop_n);
      }
      continue;
    }
    if (sop_k == BOUND_VARIABLE)
    {
      Trace("sygus-grammar-normalize-int2") << "Collecting var " << sop << "\n";
      vars.push_back(Node::fromExpr(sop));
      continue;
    }
    Trace("sygus-grammar-normalize-int2") << "Rebuilding cons " << sop << "\n";
    /* Collect constructor to rebuild */
    Node exp_sop_n = Node::fromExpr(d_smte->expandDefinitions(sop));
    tos[ind].d_ops.push_back(Rewriter::rewrite(exp_sop_n));
    Trace("sygus-grammar-normalize-defs")
        << "\tOriginal op: " << sop << "\n\tExpanded one: " << exp_sop_n
        << "\n\tRewritten one: " << tos[ind].d_ops.back() << "\n\n";
    tos[ind].d_cons_names.push_back(cons.getName());
    tos[ind].d_pc.push_back(cons.getSygusPrintCallback());
    tos[ind].d_cons_args_t.push_back(std::vector<Type>());
    for (const DatatypeConstructorArg& arg : cons)
    {
      /* Collect unresolved types corresponding to the typenode of the
       * arguments */
      tos[ind].d_cons_args_t.back().push_back(tn_to_unres[TypeNode::fromType(
          static_cast<SelectorType>(arg.getType()).getRangeType())]);
    }
  }
  Trace("sygus-grammar-normalize-int") << "Starting normalization\n";
  /* Common normalization: Int -> ... | IntNext */
  unsigned r_pos, first, counter = 0;
  /* Create primal type name */
  std::stringstream type_name;
  type_name << tos[ind].d_tn << "_norm_" << counter++;
  /* Save position where started adding new types */
  first = tos.size();
  /* Add to global accumulators */
  tos.push_back(TypeObject(tos[ind].d_tn, tos[ind].d_t, type_name.str()));
  /* Add to integer type */
  tos[ind].d_ops.push_back(iden_op);
  tos[ind].d_cons_names.push_back("id_next");
  tos[ind].d_pc.push_back(empty_pc);
  tos[ind].d_cons_args_t.push_back(std::vector<Type>());
  tos[ind].d_cons_args_t.back().push_back(tos.back().d_unres_t);
  /* Assign next root position */
  r_pos = tos.size() - 1;
  /* Root -> IntNext | Int0 | Int0 - IntNext */
  if (has_minus && has_zero && has_plus && has_one)
  {
    /* Creates and defines Int0 */
    type_name.str("");
    type_name << tos[ind].d_tn << "_norm_zero";
    tos.push_back(TypeObject(tos[ind].d_tn, tos[ind].d_t, type_name.str()));
    Trace("sygus-grammar-normalize-int") << "\tCreating 0\n";
    tos.back().d_ops.push_back(zero);
    tos.back().d_cons_names.push_back("zero");
    tos.back().d_pc.push_back(nullptr);
    tos.back().d_cons_args_t.push_back(std::vector<Type>());
    /* adds Int0 to Root */
    tos[r_pos].d_ops.push_back(iden_op);
    Trace("sygus-grammar-normalize-int")
        << "\tAdding Int0 to " << tos[r_pos].d_unres_t << " with op "
        << tos[r_pos].d_ops.back() << "\n";
    tos[r_pos].d_cons_names.push_back("id_zero");
    tos[r_pos].d_pc.push_back(empty_pc);
    tos[r_pos].d_cons_args_t.push_back(std::vector<Type>());
    tos[r_pos].d_cons_args_t.back().push_back(tos.back().d_unres_t);
    /* Creates IntNext */
    type_name.str("");
    type_name << tos[ind].d_tn << "_norm_" << counter++;
    tos.push_back(TypeObject(tos[ind].d_tn, tos[ind].d_t, type_name.str()));
    Trace("sygus-grammar-normalize-int")
        << "\tCreating type " << tos.back().d_unres_t << " for next entry\n";
    /* adds IntNext to Root */
    tos[r_pos].d_ops.push_back(iden_op);
    tos[r_pos].d_cons_names.push_back("id_next");
    tos[r_pos].d_pc.push_back(empty_pc);
    tos[r_pos].d_cons_args_t.push_back(std::vector<Type>());
    tos[r_pos].d_cons_args_t.back().push_back(tos.back().d_unres_t);
    Trace("sygus-grammar-normalize-int")
        << "\tAdding " << tos.back().d_unres_t << " to " << tos[r_pos].d_unres_t
        << " with op " << tos[r_pos].d_ops.back() << "\n";
    /* Adds Int0 - IntNext to Root */
    tos[r_pos].d_ops.push_back(d_nm->operatorOf(MINUS));
    tos[r_pos].d_cons_names.push_back(kindToString(MINUS));
    tos[r_pos].d_pc.push_back(nullptr);
    tos[r_pos].d_cons_args_t.push_back(std::vector<Type>());
    tos[r_pos].d_cons_args_t.back().push_back(tos[r_pos + 1].d_unres_t);
    tos[r_pos].d_cons_args_t.back().push_back(tos[r_pos + 2].d_unres_t);
    Trace("sygus-grammar-normalize-int")
        << "\tAdding MINUS to " << tos[r_pos].d_unres_t << " with arg types "
        << tos[r_pos + 1].d_unres_t << " and " << tos[r_pos + 2].d_unres_t
        << "\n";
    /* Updates root position */
    r_pos = tos.size() - 1;
    Trace("sygus-grammar-normalize-int") << "Creating types for variables\n";
    /* Iterates through variables for defining IntNext:
     * Root -> IntV | IntV + Root | IntNext; IntV -> v */
    for (unsigned i = 0, size = vars.size(); i < size; ++i)
    {
      Trace("sygus-grammar-normalize-int") << "\tVariable" << i << "\n";
      /* Creates and defines IntV */
      type_name.str("");
      type_name << tos[ind].d_tn << "_norm_v" << i;
      tos.push_back(TypeObject(tos[ind].d_tn, tos[ind].d_t, type_name.str()));
      tos.back().d_ops.push_back(vars[i]);
      tos.back().d_cons_names.push_back(vars[i].toString());
      tos.back().d_pc.push_back(nullptr);
      tos.back().d_cons_args_t.push_back(std::vector<Type>());
      tos.back().d_cons_args_t.back().push_back(tos.back().d_unres_t);
      /* Adds to Root: IntV */
      tos[r_pos].d_ops.push_back(iden_op);
      tos[r_pos].d_cons_names.push_back("id_v");
      tos[r_pos].d_pc.push_back(empty_pc);
      tos[r_pos].d_cons_args_t.push_back(std::vector<Type>());
      tos[r_pos].d_cons_args_t.back().push_back(tos.back().d_unres_t);
      /* Adds to Root: IntV + Root */
      tos[r_pos].d_ops.push_back(d_nm->operatorOf(PLUS));
      tos[r_pos].d_cons_names.push_back(kindToString(PLUS));
      tos[r_pos].d_pc.push_back(nullptr);
      tos[r_pos].d_cons_args_t.push_back(std::vector<Type>());
      tos[r_pos].d_cons_args_t.back().push_back(tos[r_pos + 1].d_unres_t);
      tos[r_pos].d_cons_args_t.back().push_back(tos[r_pos].d_unres_t);
      /* Creates IntNext and adds to Root */
      type_name.str("");
      type_name << tos[ind].d_tn << "_norm_" << counter++;
      tos.push_back(TypeObject(tos[ind].d_tn, tos[ind].d_t, type_name.str()));
      tos[r_pos].d_ops.push_back(iden_op);
      tos[r_pos].d_cons_names.push_back("id_next");
      tos[r_pos].d_pc.push_back(empty_pc);
      tos[r_pos].d_cons_args_t.push_back(std::vector<Type>());
      tos[r_pos].d_cons_args_t.back().push_back(tos.back().d_unres_t);
      /* Updates root position */
      r_pos = tos.size() - 1;
    }
    Trace("sygus-grammar-normalize-int") << "Creating types for constants\n";
    /* IntNext -> Int1 | Int1 + IntNext | IntC; Int1 -> 1; IntC -> c1|...|cn */
    if (!consts.empty())
    {
      /* Creates and defines Int1 */
      type_name.str("");
      type_name << tos[ind].d_tn << "_norm_one";
      tos.push_back(TypeObject(tos[ind].d_tn, tos[ind].d_t, type_name.str()));
      tos.back().d_ops.push_back(one);
      tos.back().d_cons_names.push_back("one");
      tos.back().d_pc.push_back(nullptr);
      tos.back().d_cons_args_t.push_back(std::vector<Type>());
      Trace("sygus-grammar-normalize-int") << "\tCreating and defining 1\n";
      /* adds to Root: Int1 */
      tos[r_pos].d_ops.push_back(iden_op);
      tos[r_pos].d_cons_names.push_back("id_one");
      tos[r_pos].d_pc.push_back(empty_pc);
      tos[r_pos].d_cons_args_t.push_back(std::vector<Type>());
      tos[r_pos].d_cons_args_t.back().push_back(tos.back().d_unres_t);
      Trace("sygus-grammar-normalize-int")
          << "\tAdding Int1 to " << tos[r_pos].d_unres_t << " with op "
          << tos[r_pos].d_ops.back() << "\n";
      /* Adds to Root: Int1 + Root */
      tos[r_pos].d_ops.push_back(d_nm->operatorOf(PLUS));
      tos[r_pos].d_cons_names.push_back(kindToString(PLUS));
      tos[r_pos].d_pc.push_back(nullptr);
      tos[r_pos].d_cons_args_t.push_back(std::vector<Type>());
      tos[r_pos].d_cons_args_t.back().push_back(tos[r_pos + 1].d_unres_t);
      tos[r_pos].d_cons_args_t.back().push_back(tos[r_pos].d_unres_t);
      Trace("sygus-grammar-normalize-int")
          << "\tAdding PLUS to " << tos[r_pos].d_unres_t << " with arg types "
          << tos[r_pos + 1].d_unres_t << " and " << tos[r_pos].d_unres_t
          << "\n";
      /* Creats IntC */
      type_name.str("");
      type_name << tos[ind].d_tn << "_norm_" << counter++;
      tos.push_back(TypeObject(tos[ind].d_tn, tos[ind].d_t, type_name.str()));
      /* Adds to Root: IntC */
      tos[r_pos].d_ops.push_back(iden_op);
      tos[r_pos].d_cons_names.push_back("id_C");
      tos[r_pos].d_pc.push_back(empty_pc);
      tos[r_pos].d_cons_args_t.push_back(std::vector<Type>());
      tos[r_pos].d_cons_args_t.back().push_back(tos.back().d_unres_t);
      Trace("sygus-grammar-normalize-int")
          << "\tAdding " << tos[r_pos].d_unres_t << " op "
          << tos[r_pos].d_ops.back() << " and arg types "
          << tos.back().d_unres_t << "\n";
      /* Defines IntC */
      r_pos = tos.size() - 1;
      for (unsigned i = 0, size = consts.size(); i < size; ++i)
      {
        tos[r_pos].d_ops.push_back(consts[i]);
        tos[r_pos].d_cons_names.push_back(consts[i].toString());
        tos[r_pos].d_pc.push_back(nullptr);
        tos[r_pos].d_cons_args_t.push_back(std::vector<Type>());
        Trace("sygus-grammar-normalize-int")
            << "\tAdding " << tos[r_pos].d_unres_t << " constant "
            << consts[i].toString() << "\n";
      }
    }
    else /* IntNext -> 1 */
    {
      Trace("sygus-grammar-normalize-int") << "\tNo other consts, just add 1\n";
      tos[r_pos].d_ops.push_back(one);
      tos[r_pos].d_cons_names.push_back("one");
      tos[r_pos].d_pc.push_back(nullptr);
      tos[r_pos].d_cons_args_t.push_back(std::vector<Type>());
    }
    /* Bulding new datatypes */
    for (unsigned i = first, size = tos.size(); i < size; ++i)
    {
      tos[i].d_dt.setSygus(dt.getSygusType(),
                           sygus_vars.toExpr(),
                           dt.getSygusAllowConst(),
                           dt.getSygusAllowAll());
      for (unsigned j = 0, size_ops = tos[i].d_ops.size(); j < size_ops; ++j)
      {
        tos[i].d_dt.addSygusConstructor(tos[i].d_ops[j].toExpr(),
                                        tos[i].d_cons_names[j],
                                        tos[i].d_cons_args_t[j],
                                        tos[i].d_pc[j]);
      }
      Trace("sygus-grammar-normalize-int")
          << "...built new datatype " << tos[i].d_dt << std::endl;
    }
  }
  /* Building normalized integer datatype */
  tos[ind].d_dt.setSygus(dt.getSygusType(),
                         sygus_vars.toExpr(),
                         dt.getSygusAllowConst(),
                         dt.getSygusAllowAll());
  for (unsigned i = 0, size = tos[ind].d_ops.size(); i < size; ++i)
  {
    tos[ind].d_dt.addSygusConstructor(tos[ind].d_ops[i].toExpr(),
                                      tos[ind].d_cons_names[i],
                                      tos[ind].d_cons_args_t[i],
                                      tos[ind].d_pc[i]);
  }
  Trace("sygus-grammar-normalize-int")
      << "...built datatype " << tos[ind].d_dt << std::endl;
}

#endif

std::vector<bool> SygusGrammarNorm::get_op_flags(std::vector<unsigned> op_pos,
                                                 unsigned num_cons)
{
  std::vector<bool> op_flags(num_cons);
  std::fill(op_flags.begin(), op_flags.end(), false);
  for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
  {
    Assert(op_pos[i] < op_flags.size());
    op_flags[op_pos[i]] = true;
  }
  Trace("sygus-grammar-normalize-trie") << "get_op_flags for op_pos ";
  for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
  {
    Trace("sygus-grammar-normalize-trie") << op_pos[i] << " ";
  }
  Trace("sygus-grammar-normalize-trie") << " yields ";
  for (unsigned i = 0, size = op_flags.size(); i < size; ++i)
  {
    Trace("sygus-grammar-normalize-trie") << op_flags[i] << " ";
  }
  Trace("sygus-grammar-normalize-trie") << "\n";
  return op_flags;
}

void SygusGrammarNorm::addConsInfo(TypeObject& to,
                                   const DatatypeConstructor& cons,
                                   Node sygus_vars)
{
  Trace("sygus-grammar-normalize") << "...for " << cons.getName() << std::endl;
  /* Recover the sygus operator to not lose reference to the original
   * operator (NOT, ITE, etc) */
  Node exp_sop_n = Node::fromExpr(d_smte->expandDefinitions(cons.getSygusOp()));
  to.d_ops.push_back(Rewriter::rewrite(exp_sop_n));
  Trace("sygus-grammar-normalize-defs")
      << "\tOriginal op: " << cons.getSygusOp()
      << "\n\tExpanded one: " << exp_sop_n
      << "\n\tRewritten one: " << to.d_ops.back() << "\n\n";
  to.d_cons_names.push_back(cons.getName());
  to.d_pc.push_back(cons.getSygusPrintCallback());
  to.d_cons_args_t.push_back(std::vector<Type>());
  for (const DatatypeConstructorArg& arg : cons)
  {
    /* Collect unresolved type nodes corresponding to the typenode of the
     * arguments */
    to.d_cons_args_t.back().push_back(
        normalizeSygusRec(
            TypeNode::fromType(
                static_cast<SelectorType>(arg.getType()).getRangeType()),
            sygus_vars)
            .toType());
  }
}

void SygusGrammarNorm::buildDatatype(TypeObject& to,
                                     const Datatype& dt,
                                     Node sygus_vars)
{
  /* Use the sygus type to not lose reference to the original types (Bool,
   * Int, etc) */
  to.d_dt.setSygus(dt.getSygusType(),
                   sygus_vars.toExpr(),
                   dt.getSygusAllowConst(),
                   dt.getSygusAllowAll());
  for (unsigned i = 0, size_d_ops = to.d_ops.size(); i < size_d_ops; ++i)
  {
    to.d_dt.addSygusConstructor(to.d_ops[i].toExpr(),
                                to.d_cons_names[i],
                                to.d_cons_args_t[i],
                                to.d_pc[i]);
  }
  Trace("sygus-grammar-normalize")
      << "...built datatype " << to.d_dt << std::endl;
  /* Add to global accumulators */
  d_dt_all.push_back(to.d_dt);
  d_unres_t_all.insert(to.d_unres_t);
}

/* Traverse the constructors of dt according to the positions in op_pos. Collect
 * those that fit the kinds established by to_collect. Remove collected operator
 * positions from op_pos. Accumulate collected positions in collected
 *
 * returns true if collected anything
 */
bool SygusGrammarNorm::collect(const Datatype& dt,
                               std::vector<unsigned>& op_pos,
                               std::vector<unsigned> to_collect,
                               std::vector<unsigned>& collected)
{
  /* TODO cache */
  Node zero =
      d_qe->getTermUtil()->getTypeValue(TypeNode::fromType(d_int_type), 0);
  Node one =
      d_qe->getTermUtil()->getTypeValue(TypeNode::fromType(d_int_type), 1);
  /* TODO do all this properly */
  /* Collect */
  for (unsigned group : to_collect)
  {
    switch (group)
    {
      case OP_PLUS:
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.getKind() == BUILTIN && d_nm->operatorToKind(sop) == PLUS)
          {
            Trace("sygus-grammar-normalize-collect")
                << "For OP_PLUS collecting sop " << sop << " in position "
                << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
          }
        }
        break;
      case OP_MINUS:
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.getKind() == BUILTIN && d_nm->operatorToKind(sop) == MINUS)
          {
            Trace("sygus-grammar-normalize-collect")
                << "For OP_MINUS collecting sop " << sop << " in position "
                << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
          }
        }
        break;
      case VARS:
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.getKind() == BOUND_VARIABLE)
          {
            Trace("sygus-grammar-normalize-collect")
                << "For VARS collecting sop " << sop << " in position "
                << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
          }
        }
        break;
      case A_VAR:
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.getKind() == BOUND_VARIABLE)
          {
            Trace("sygus-grammar-normalize-collect")
                << "For A_VAR collecting sop " << sop << " in position "
                << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
            break;
          }
        }
        break;
      case CONST_ZERO:
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.isConst() && Node::fromExpr(sop) == zero)
          {
            Trace("sygus-grammar-normalize-collect")
                << "For CONST_ZERO collecting sop " << sop << " in position "
                << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
          }
        }
        break;
      case CONST_ONE:
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.isConst() && Node::fromExpr(sop) == one)
          {
            Trace("sygus-grammar-normalize-collect")
                << "For CONST_ONE collecting sop " << sop << " in position "
                << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
          }
        }
        break;
      case NON_ZERO_CONSTS:  // Includes ITEs
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.isConst() && Node::fromExpr(sop) != zero)
          {
            Trace("sygus-grammar-normalize-collect")
                << "For NON_ZERO_CONSTS collecting sop " << sop
                << " in position " << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
          }
        }
        break;
      case A_NON_ZERO_CONST:  // Includes ITEs
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.isConst() && Node::fromExpr(sop) != zero)
          {
            Trace("sygus-grammar-normalize-collect")
                << "For A_NON_ZERO_CONST collecting sop " << sop
                << " in position " << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
            break;
          }
        }
        break;
    }
  }
  /* TODO do this properly */
  /* Remove from op_pos what has been colleced */
  std::sort(op_pos.begin(), op_pos.end());
  std::sort(collected.begin(), collected.end());
  std::vector<unsigned> difference;
  std::set_difference(op_pos.begin(),
                      op_pos.end(),
                      collected.begin(),
                      collected.end(),
                      std::back_inserter(difference));
  op_pos = difference;
  Trace("sygus-grammar-normalize-collect") << "Remaining op_pos ";
  for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
  {
    Trace("sygus-grammar-normalize-rec") << op_pos[i] << " ";
  }
  Trace("sygus-grammar-normalize-rec") << "\n";
  return !collected.empty();
}

TypeNode SygusGrammarNorm::normalizeSygusRec(TypeNode tn,
                                             const Datatype& dt,
                                             std::vector<unsigned> op_pos,
                                             Node sygus_vars)
{
  Trace("sygus-grammar-normalize-rec")
      << "\tRecursing on " << tn << " with op_positions ";
  for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
  {
    Trace("sygus-grammar-normalize-rec") << op_pos[i] << " ";
  }
  Trace("sygus-grammar-normalize-rec") << "\n";
  Type t;
  TypeNode unres_tn;
  std::map<TypeNode, Type>::iterator it = d_tn_to_t.find(tn);
  /* New type node */
  if (it == d_tn_to_t.end())
  {
    Trace("sygus-grammar-normalize-rec") << "\tTypenode " << tn << " is new\n";
    t = tn.toType();
    d_tn_to_t[tn] = t;
    Trace("sygus-grammar-normalize-trie") << "\tSetting tn to ops to pos map\n";
    /* If new type then op_pos contains positions of all constructors of tn */
    Assert(op_pos.size() == dt.getNumConstructors());
    /* Set positions of operators */
    std::map<Node, unsigned> op_to_pos;
    std::vector<bool> op_flags;
    for (unsigned i = 0, size = dt.getNumConstructors(); i < size; ++i)
    {
      Trace("sygus-grammar-normalize-trie")
          << "\t\tAdding op " << Node::fromExpr(dt[i].getSygusOp());
      op_to_pos[Node::fromExpr(dt[i].getSygusOp())] = i;
      Trace("sygus-grammar-normalize-trie") << " to position " << i;
      op_flags.push_back(true);
      Trace("sygus-grammar-normalize-trie") << " and set it to true\n";
    }
    Assert(d_tn_to_op_to_pos.find(tn) == d_tn_to_op_to_pos.end());
    d_tn_to_op_to_pos[tn] = op_to_pos;
    /* Set trie */
    Trace("sygus-grammar-normalize-trie")
        << "\tSetting trie for " << tn << "\n";
    Assert(d_tries.find(tn) == d_tries.end());
    d_tries[tn].getOrMakeType(tn, unres_tn, op_flags);
    Trace("sygus-grammar-normalize-rec")
        << "\tCreating tn " << unres_tn << "\n";
  }
  else
  {
    Trace("sygus-grammar-normalize-rec")
        << "\tTypenode " << tn << " is not new.\n";
    t = it->second;
    Assert(d_tries.find(tn) != d_tries.end());
    Assert(d_tn_to_op_to_pos.find(tn) != d_tn_to_op_to_pos.end());
    /* Checks if unresolved type already created (and returns) or creates it
     * (and then proceeds to definition) */
    if (d_tries[tn].getOrMakeType(
            tn, unres_tn, get_op_flags(op_pos, dt.getNumConstructors())))
    {
      Trace("sygus-grammar-normalize-rec")
          << "\tTypenode " << tn << " has already been normalized with op_pos ";
      for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
      {
        Trace("sygus-grammar-normalize-rec") << op_pos[i] << " ";
      }
      Trace("sygus-grammar-normalize-rec") << " with tn " << unres_tn << "\n";
      return unres_tn;
    }
  }
  Trace("sygus-grammar-normalize-rec")
      << "\tTypenode " << tn << " not yet normalized with op_pos ";
  for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
  {
    Trace("sygus-grammar-normalize-rec") << op_pos[i] << " ";
  }
  Trace("sygus-grammar-normalize-rec") << "\n";
  /* Creates type object for normalization */
  TypeObject to(tn, unres_tn, unres_tn.toType());
  /* Determine normalization based on sygus type and given operators */
  /* Non-normalizable type */
  if (!dt.getSygusType().isInteger())
  {
    Trace("sygus-grammar-normalize")
        << "Rebuild " << to.d_tn << " from " << dt << std::endl;
    /* If non-normalizable then ops contains all constructors of tn */
    Assert(op_pos.size() == dt.getNumConstructors());
    /* Collect information to rebuild constructors */
    for (const DatatypeConstructor& cons : dt)
    {
      addConsInfo(to, cons, sygus_vars);
    }
    buildDatatype(to, dt, sygus_vars);
    return to.d_unres_tn;
  }
  /* If has +, vars and constants, get those and leave the rest as is */
  std::vector<unsigned> collected;
  /* go recursive with plus, vars and non zero constants */
  if (collect(dt, op_pos, {PLUS, VARS, NON_ZERO_CONSTS}, collected))
  {
    /* TODO cache */
    /* Build integer identity operator */
    std::vector<Node> vars = {d_nm->mkBoundVar(TypeNode::fromType(d_int_type))};
    Node iden_op =
        d_nm->mkNode(LAMBDA, d_nm->mkNode(BOUND_VAR_LIST, vars), vars.back());
    std::shared_ptr<printer::SygusEmptyPrintCallback> empty_pc =
        std::make_shared<printer::SygusEmptyPrintCallback>();
    /* If everything collected, create chain of monomials */
    if (op_pos.empty())
    {
      std::vector<unsigned> recollected;
      /* Add var monomial */
      if (collect(dt, collected, {A_VAR}, recollected))
      {
        Assert(recollected.size() == 1);
        /* Only plus remains, so this is the last monomial */
        if (collected.size() == 1)
        {
          /* TODO function for creating singleton */
          /* Adds to Root: IntV */
          to.d_ops.push_back(iden_op);
          to.d_cons_names.push_back("id_V");
          to.d_pc.push_back(empty_pc);
          to.d_cons_args_t.push_back(std::vector<Type>());
          to.d_cons_args_t.back().push_back(
              normalizeSygusRec(tn, dt, recollected, sygus_vars).toType());
          buildDatatype(to, dt, sygus_vars);
          return to.d_unres_tn;
        }
        /* TODO function for creating monomial */
        /* Creates type node for variable */
        TypeNode var_tn = normalizeSygusRec(tn, dt, recollected, sygus_vars);
        Assert(d_tn_to_t.find(var_tn) != d_tn_to_t.end());
        Type var_t = d_tn_to_t[var_tn];
        /* adds to Root: IntV */
        to.d_ops.push_back(iden_op);
        to.d_cons_names.push_back("id_V");
        to.d_pc.push_back(empty_pc);
        to.d_cons_args_t.push_back(std::vector<Type>());
        to.d_cons_args_t.back().push_back(var_t);
        Trace("sygus-grammar-normalize-int")
            << "\tAdding  " << var_tn << " to " << to.d_unres_t << "\n";
        /* Adds to Root: IntV + Root */
        to.d_ops.push_back(d_nm->operatorOf(PLUS));
        to.d_cons_names.push_back(kindToString(PLUS));
        to.d_pc.push_back(nullptr);
        to.d_cons_args_t.push_back(std::vector<Type>());
        to.d_cons_args_t.back().push_back(var_t);
        to.d_cons_args_t.back().push_back(to.d_unres_t);
        Trace("sygus-grammar-normalize-int")
            << "\tAdding PLUS to " << to.d_unres_t << " with arg types "
            << to.d_unres_t << " and " << var_tn << "\n";
      }
      else /* Add const monomial */
      {
        collect(dt, collected, {A_NON_ZERO_CONST}, recollected);
        Assert(recollected.size() == 1);
        /* Only plus remains, so this is the last monomial */
        if (collected.size() == 1)
        {
          /* Adds to Root: IntC */
          to.d_ops.push_back(iden_op);
          to.d_cons_names.push_back("id_C");
          to.d_pc.push_back(empty_pc);
          to.d_cons_args_t.push_back(std::vector<Type>());
          to.d_cons_args_t.back().push_back(
              normalizeSygusRec(tn, dt, recollected, sygus_vars).toType());
          buildDatatype(to, dt, sygus_vars);
          return to.d_unres_tn;
        }
        /* Creates type node for constant */
        TypeNode const_tn = normalizeSygusRec(tn, dt, recollected, sygus_vars);
        Assert(d_tn_to_t.find(const_tn) != d_tn_to_t.end());
        Type const_t = d_tn_to_t[const_tn];
        /* adds to Root: IntC */
        to.d_ops.push_back(iden_op);
        to.d_cons_names.push_back("id_const");
        to.d_pc.push_back(empty_pc);
        to.d_cons_args_t.push_back(std::vector<Type>());
        to.d_cons_args_t.back().push_back(const_t);
        Trace("sygus-grammar-normalize-int")
            << "\tAdding  " << const_tn << " to " << to.d_unres_t << "\n";
        /* Adds to Root: IntC + Root */
        to.d_ops.push_back(d_nm->operatorOf(PLUS));
        to.d_cons_names.push_back(kindToString(PLUS));
        to.d_pc.push_back(nullptr);
        to.d_cons_args_t.push_back(std::vector<Type>());
        to.d_cons_args_t.back().push_back(const_t);
        to.d_cons_args_t.back().push_back(to.d_unres_t);
        Trace("sygus-grammar-normalize-int")
            << "\tAdding PLUS to " << to.d_unres_t << " with arg types "
            << to.d_unres_t << " and " << const_tn << "\n";
      }
    }
    /* if had other operators, create a next type for the normalization */
    /* Creates IntNext */
    Trace("sygus-grammar-normalize-int")
        << "\tCreating type for next entry with operators ";
    for (unsigned i = 0, size = collected.size(); i < size; ++i)
    {
      Trace("sygus-grammar-normalize-int") << dt[collected[i]] << " ";
    }
    Trace("sygus-grammar-normalize-int") << "\n";
    /* adds to Root: IntNext */
    to.d_ops.push_back(iden_op);
    to.d_cons_names.push_back("id_next");
    to.d_pc.push_back(empty_pc);
    to.d_cons_args_t.push_back(std::vector<Type>());
    to.d_cons_args_t.back().push_back(
        normalizeSygusRec(tn, dt, collected, sygus_vars).toType());
  }
  /* Build not normalized ops as they are */
  for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
  {
    Assert(op_pos[i] < dt.getNumConstructors());
    addConsInfo(to, dt[op_pos[i]], sygus_vars);
  }
  buildDatatype(to, dt, sygus_vars);
  return to.d_unres_tn;
}

TypeNode SygusGrammarNorm::normalizeSygusRec(TypeNode tn, Node sygus_vars)
{
  /* Collect all operators for normalization */
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  std::vector<unsigned> op_pos(dt.getNumConstructors());
  std::iota(op_pos.begin(), op_pos.end(), 0);
  return normalizeSygusRec(tn, dt, op_pos, sygus_vars);
}

TypeNode SygusGrammarNorm::normalizeSygusType(TypeNode tn, Node sygus_vars)
{
  Trace("sygus-grammar-normalize-build")
      << "Will normalize " << tn << " with datatype "
      << static_cast<DatatypeType>(tn.toType()).getDatatype() << "\n";
  /* Normalize all types in tn */
  normalizeSygusRec(tn, sygus_vars);
  /* Resolve created types */
  Assert(!d_dt_all.empty() && !d_unres_t_all.empty());
  Trace("sygus-grammar-normalize-build")
      << "making mutual datatyes with datatypes \n";
  for (unsigned i = 0, size = d_dt_all.size(); i < size; ++i)
  {
    Trace("sygus-grammar-normalize-build") << d_dt_all[i];
  }
  Trace("sygus-grammar-normalize-build") << " and unresolved types\n";
  for (const Type& unres_t : d_unres_t_all)
  {
    Trace("sygus-grammar-normalize-build") << unres_t << " ";
  }
  Trace("sygus-grammar-normalize-build") << "\n";
  Assert(d_dt_all.size() == d_unres_t_all.size());
  std::vector<DatatypeType> types =
      d_nm->toExprManager()->mkMutualDatatypeTypes(d_dt_all, d_unres_t_all);
  Assert(types.size() == d_dt_all.size());
  /* Clear accumulators */
  d_dt_all.clear();
  d_unres_t_all.clear();
  /* By construction the normalized type node will be the last one considered */
  return TypeNode::fromType(types.back());
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

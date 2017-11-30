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

TypeObject::TypeObject(TypeNode src_tn, TypeNode unres_tn)
    : d_dt(Datatype(unres_tn.getAttribute(expr::VarNameAttr())))
{
  d_tn = src_tn;
  /* Create an unresolved type */
  d_unres_tn = unres_tn;
}

bool OpPosTrie::getOrMakeType(TypeNode tn,
                              TypeNode& unres_tn,
                              std::vector<unsigned> op_pos,
                              unsigned ind)
{
  Assert(ind != op_pos.size() || d_children.empty());
  if (ind == op_pos.size())
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
    for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
    {
      ss << "_" << std::to_string(op_pos[i]);
    }
    d_unres_tn = NodeManager::currentNM()->mkSort(
        ss.str(), ExprManager::SORT_FLAG_PLACEHOLDER);
    Trace("sygus-grammar-normalize-trie")
        << "\tCreating type " << d_unres_tn << "\n";
    unres_tn = d_unres_tn;
    return false;
  }
  /* Go to next node */
  return d_children[op_pos[ind]].getOrMakeType(tn, unres_tn, op_pos, ind + 1);
}

std::map<TypeNode, std::map<StratChain::Block, Node>> StratChain::d_assoc = {};

void StratChain::buildType(SygusGrammarNorm* sygus_norm,
                           TypeObject& to,
                           const Datatype& dt,
                           std::vector<unsigned>& op_pos)
{
  std::vector<unsigned> claimed(d_elem_pos);
  claimed.push_back(d_chain_op_pos);
  unsigned nb_op_pos = op_pos.size();
  /* TODO do this properly */
  /* Remove from op_pos the positions claimed by the strategy */
  std::sort(op_pos.begin(), op_pos.end());
  std::sort(claimed.begin(), claimed.end());
  std::vector<unsigned> difference;
  std::set_difference(op_pos.begin(),
                      op_pos.end(),
                      claimed.begin(),
                      claimed.end(),
                      std::back_inserter(difference));
  op_pos = difference;
  if (Trace.isOn("sygus-grammar-normalize-chain"))
  {
    Trace("sygus-grammar-normalize-chain")
        << "OP at " << d_chain_op_pos << "\n"
        << d_elem_pos.size() << " d_elem_pos: ";
    for (unsigned i = 0, size = d_elem_pos.size(); i < size; ++i)
    {
      Trace("sygus-grammar-normalize-chain") << d_elem_pos[i] << " ";
    }
    Trace("sygus-grammar-normalize-chain")
        << "\n"
        << op_pos.size() << " remaining op_pos: ";
    for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
    {
      Trace("sygus-grammar-normalize-chain") << op_pos[i] << " ";
    }
    Trace("sygus-grammar-normalize-chain") << "\n";
  }
  /* TODO cache */
  /* Build identity operator and empty callback */
  std::vector<Node> vars = {
      sygus_norm->d_nm->mkBoundVar(TypeNode::fromType(dt.getSygusType()))};
  Node iden_op = sygus_norm->d_nm->mkNode(
      LAMBDA, sygus_norm->d_nm->mkNode(BOUND_VAR_LIST, vars), vars.back());
  std::shared_ptr<printer::SygusEmptyPrintCallback> empty_pc =
      std::make_shared<printer::SygusEmptyPrintCallback>();
  /* If all operators are claimed, create a monomial */
  if (nb_op_pos == d_elem_pos.size() + 1)
  {
    /* creates type for element */
    Type t = sygus_norm->normalizeSygusRec(to.d_tn, dt, {d_elem_pos.back()})
                 .toType();
    /* consumes element */
    d_elem_pos.pop_back();
    /* adds to Root: "type" */
    to.d_ops.push_back(iden_op);
    to.d_cons_names.push_back("id");
    to.d_pc.push_back(empty_pc);
    to.d_cons_args_t.push_back(std::vector<Type>());
    to.d_cons_args_t.back().push_back(t);
    Trace("sygus-grammar-normalize-chain")
        << "\tAdding  " << t << " to " << to.d_unres_tn << "\n";
    /* adds to Root: "type + Root" */
    to.d_ops.push_back(sygus_norm->d_nm->operatorOf(PLUS));
    to.d_cons_names.push_back(kindToString(PLUS));
    to.d_pc.push_back(nullptr);
    to.d_cons_args_t.push_back(std::vector<Type>());
    to.d_cons_args_t.back().push_back(t);
    to.d_cons_args_t.back().push_back(to.d_unres_tn.toType());
    Trace("sygus-grammar-normalize-chain")
        << "\tAdding PLUS to " << to.d_unres_tn << " with arg types "
        << to.d_unres_tn << " and " << t << "\n";
  }
  /* In the initial case if not all operators claimed always creates a next */
  Assert(nb_op_pos != d_elem_pos.size() + 1 || d_elem_pos.size() > 1);
  /* Creates a type do be added to root representing the next step in the chain
   */
  if (d_elem_pos.size() > 0)
  {
    /* Add + to elems */
    d_elem_pos.push_back(d_chain_op_pos);
    if (Trace.isOn("sygus-grammar-normalize-chain"))
    {
      Trace("sygus-grammar-normalize-chain")
          << "\tCreating type for next entry with sygus_ops ";
      for (unsigned i = 0, size = d_elem_pos.size(); i < size; ++i)
      {
        Trace("sygus-grammar-normalize-chain") << dt[d_elem_pos[i]].getSygusOp() << " ";
      }
      Trace("sygus-grammar-normalize-chain") << "\n";
    }
    /* adds to Root: (\lambda x. x ) Next */
    to.d_ops.push_back(iden_op);
    to.d_cons_names.push_back("id_next");
    to.d_pc.push_back(empty_pc);
    to.d_cons_args_t.push_back(std::vector<Type>());
    to.d_cons_args_t.back().push_back(
        sygus_norm->normalizeSygusRec(to.d_tn, dt, d_elem_pos).toType());
  }
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
  Node one =
      d_qe->getTermUtil()->getTypeValue(TypeNode::fromType(d_int_type), 1);
  /* TODO fix this */
  std::shared_ptr<printer::SygusEmptyPrintCallback> empty_pc =
      std::make_shared<printer::SygusEmptyPrintCallback>();
  /* Build integer identity operator */
  vars.push_back(d_nm->mkBoundVar(TypeNode::fromType(d_int_type)));
  Node iden_op =
      d_nm->mkNode(LAMBDA, d_nm->mkNode(BOUND_VAR_LIST, vars), vars.back());
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

void SygusGrammarNorm::addConsInfo(TypeObject& to,
                                   const DatatypeConstructor& cons)
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
                static_cast<SelectorType>(arg.getType()).getRangeType()))
            .toType());
  }
}

void SygusGrammarNorm::buildDatatype(TypeObject& to,
                                     const Datatype& dt)
{
  /* Use the sygus type to not lose reference to the original types (Bool,
   * Int, etc) */
  to.d_dt.setSygus(dt.getSygusType(),
                   d_sygus_vars.toExpr(),
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
  d_unres_t_all.insert(to.d_unres_tn.toType());
}

/* Traverse the constructors of dt according to the positions in op_pos. Collect
 * those that fit the kinds established by to_collect. Remove collected operator
 * positions from op_pos. Accumulate collected positions in collected
 *
 * returns true if collected anything
 */
Strat* SygusGrammarNorm::inferStrategy(const Datatype& dt,
                                       std::vector<unsigned>& op_pos)
{
  TypeNode tn = TypeNode::fromType(dt.getSygusType());
  /* TODO fix */
  if (tn.isInteger())
  {
    StratChain::addType(
        tn,
        {{StratChain::OP, d_nm->operatorOf(PLUS)},
         {StratChain::ELEMS_ID, d_qe->getTermUtil()->getTypeValue(tn, 0)}});
  }
  /* TODO step 0: look for singleton */
  /* step 1: look for chain */
  std::map<StratChain::Block, Node> assoc;
  auto it = StratChain::d_assoc.find(tn);
  if (it == StratChain::d_assoc.end())
  {
    return nullptr;
  }
  assoc = it->second;
  unsigned chain_op_pos = dt.getNumConstructors();
  std::vector<unsigned> elem_pos;
  Node id = assoc[StratChain::ELEMS_ID];
  Kind op = d_nm->operatorToKind(assoc[StratChain::OP].toExpr());
  Trace("sygus-grammar-normalize-infer")
      << "Looking for op " << op << " and elems diff from " << id << "\n";
  for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
  {
    Assert(op_pos[i] < dt.getNumConstructors());
    Expr sop = dt[op_pos[i]].getSygusOp();
    /* Collects a chainable operator such as PLUS */
    if (sop.getKind() == BUILTIN && d_nm->operatorToKind(sop) == op)
    {
      Assert(chain_op_pos == dt.getNumConstructors());
      Trace("sygus-grammar-normalize-infer")
          << "\tFor OP " << op << " collecting sop " << sop << " in position "
          << op_pos[i] << "\n";
      chain_op_pos = op_pos[i];
      continue;
    }
    /* Collects elements different from the identity (e.g. zero) */
    Kind actual_sop_k = d_nm->operatorToKind(sop);
    if (sop.getKind() == BOUND_VARIABLE
        || ((sop.getKind() != BUILTIN || actual_sop_k == ITE) && sop.isConst()
            && Node::fromExpr(sop) != id))
    {
      Trace("sygus-grammar-normalize-infer")
          << "\tFor NON_ID_ELEMS collecting sop " << sop << " in position "
          << op_pos[i] << "\n";
      elem_pos.push_back(op_pos[i]);
    }
  }
  /* Typenode admits a chain strategy for normalization */
  if (chain_op_pos != dt.getNumConstructors() && !elem_pos.empty())
  {
    Trace("sygus-grammar-normalize-infer") << "\tInfering chain strategy\n";
    return new StratChain(chain_op_pos, elem_pos);
  }
  return nullptr;
}

#if 0
{
  /* TODO cache */
  Node zero = d_qe->getTermUtil()->getTypeValue(
      TypeNode::fromType(dt.getSygusType()), 0);
  Node zero_int = d_qe->getTermUtil()->getTypeValue(
      TypeNode::fromType(d_int_type), 0);
  Node one = d_qe->getTermUtil()->getTypeValue(
      TypeNode::fromType(dt.getSygusType()), 1);
  /* TODO do all this properly */
  /* Collect */
  for (unsigned group : to_collect)
  {
    switch (group)
    {
      case OP_PLUS:
        Trace("sygus-grammar-normalize-collect2") << "Collecting for OP_PLUS\n";
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.getKind() == BUILTIN && d_nm->operatorToKind(sop) == PLUS)
          {
            Trace("sygus-grammar-normalize-collect2")
                << "\tFor OP_PLUS collecting sop " << sop << " in position "
                << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
          }
        }
        break;
      case OP_MINUS:
        Trace("sygus-grammar-normalize-collect2") << "Collecting for OP_MINUS\n";
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.getKind() == BUILTIN && d_nm->operatorToKind(sop) == MINUS)
          {
            Trace("sygus-grammar-normalize-collect2")
                << "\tFor OP_MINUS collecting sop " << sop << " in position "
                << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
          }
        }
        break;
      case VARS:
        Trace("sygus-grammar-normalize-collect2") << "Collecting for VARS\n";
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.getKind() == BOUND_VARIABLE)
          {
            Trace("sygus-grammar-normalize-collect2")
                << "\tFor VARS collecting sop " << sop << " in position "
                << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
          }
        }
        break;
      case A_VAR:
        Trace("sygus-grammar-normalize-collect2") << "Collecting for A_VAR\n";
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.getKind() == BOUND_VARIABLE)
          {
            Trace("sygus-grammar-normalize-collect2")
                << "\tFor A_VAR collecting sop " << sop << " in position "
                << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
            break;
          }
        }
        break;
      case CONST_ZERO:
        Trace("sygus-grammar-normalize-collect2")
            << "Collecting for CONST_ZERO\n";
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.isConst() && Node::fromExpr(sop) == zero)
          {
            Trace("sygus-grammar-normalize-collect2")
                << "\tFor CONST_ZERO collecting sop " << sop << " in position "
                << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
          }
        }
        break;
      case CONST_ONE:
        Trace("sygus-grammar-normalize-collect2")
            << "Collecting for CONST_ONE\n";
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          if (sop.isConst() && Node::fromExpr(sop) == one)
          {
            Trace("sygus-grammar-normalize-collect2")
                << "\tFor CONST_ONE collecting sop " << sop << " in position "
                << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
          }
        }
        break;
      case NON_ZERO_CONSTS:  // Includes ITEs
        Trace("sygus-grammar-normalize-collect2")
            << "Collecting for NON_ZERO_CONSTS\n";
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          /* Better way?? */
          Kind actual_sop_k = d_nm->operatorToKind(sop);
          if ((sop.getKind() != BUILTIN || actual_sop_k == ITE) && sop.isConst()
              && Node::fromExpr(sop) != zero)
          {
            Trace("sygus-grammar-normalize-collect2")
                << "\tFor NON_ZERO_CONSTS collecting sop " << sop
                << " in position " << op_pos[i] << "\n";
            collected.push_back(op_pos[i]);
          }
        }
        break;
      case A_NON_ZERO_CONST:  // Includes ITEs
        Trace("sygus-grammar-normalize-collect2")
            << "Collecting for A_NON_ZERO_CONST\n";
        for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
        {
          Assert(op_pos[i] < dt.getNumConstructors());
          Expr sop = dt[op_pos[i]].getSygusOp();
          /* Better way?? */
          Kind actual_sop_k = d_nm->operatorToKind(sop);
          if ((sop.getKind() != BUILTIN || actual_sop_k == ITE) && sop.isConst()
              && Node::fromExpr(sop) != zero)
          {
            Trace("sygus-grammar-normalize-collect2")
                << "\tFor A_NON_ZERO_CONST collecting sop " << sop
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
  Trace("sygus-grammar-normalize-collect") << collected.size() << " collected: ";
  for (unsigned i = 0, size = collected.size(); i < size; ++i)
  {
    Trace("sygus-grammar-normalize-collect") << collected[i] << " ";
  }
  Trace("sygus-grammar-normalize-collect")
      << "\n"
      << op_pos.size() << " remaining op_pos: ";
  for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
  {
    Trace("sygus-grammar-normalize-collect") << op_pos[i] << " ";
  }
  Trace("sygus-grammar-normalize-collect") << "\n";
  return !collected.empty();
}
#endif

TypeNode SygusGrammarNorm::normalizeSygusRec(TypeNode tn,
                                             const Datatype& dt,
                                             std::vector<unsigned> op_pos)
{
  /* Corresponding type node to tn with the given operator positions. To be
   * retrieved (if cached) or defined (otherwise) */
  TypeNode unres_tn;
  if (Trace.isOn("sygus-grammar-normalize-trie"))
  {
    Trace("sygus-grammar-normalize-trie")
        << "\tRecursing on " << tn << " with op_positions ";
    for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
    {
      Trace("sygus-grammar-normalize-trie") << op_pos[i] << " ";
    }
    Trace("sygus-grammar-normalize-trie") << "\n";
  }
  /* Checks if unresolved type already created (and returns) or creates it
   * (and then proceeds to definition) */
  std::sort(op_pos.begin(), op_pos.end());
  if (d_tries[tn].getOrMakeType(tn, unres_tn, op_pos))
  {
    if (Trace.isOn("sygus-grammar-normalize-trie"))
    {
      Trace("sygus-grammar-normalize-trie")
          << "\tTypenode " << tn << " has already been normalized with op_pos ";
      for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
      {
        Trace("sygus-grammar-normalize-trie") << op_pos[i] << " ";
      }
      Trace("sygus-grammar-normalize-trie") << " with tn " << unres_tn << "\n";
    }
    return unres_tn;
  }
  if (Trace.isOn("sygus-grammar-normalize-trie"))
  {
    Trace("sygus-grammar-normalize-trie")
        << "\tTypenode " << tn << " not yet normalized with op_pos ";
    for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
    {
      Trace("sygus-grammar-normalize-trie") << op_pos[i] << " ";
    }
    Trace("sygus-grammar-normalize-trie") << "\n";
  }
  /* Creates type object for normalization */
  TypeObject to(tn, unres_tn);
  /* Determine normalization strategy based on sygus type and given operators */
  Strat* strategy = inferStrategy(dt, op_pos);
  /* If a strategy was selected, apply it */
  if (strategy != nullptr)
  {
    strategy->buildType(this, to, dt, op_pos);
  }
  /* Remaining operators are rebuilt as they are */
  for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
  {
    Assert(op_pos[i] < dt.getNumConstructors());
    addConsInfo(to, dt[op_pos[i]]);
  }
  /* Build normalize datatype */
  buildDatatype(to, dt);
  return to.d_unres_tn;
}

TypeNode SygusGrammarNorm::normalizeSygusRec(TypeNode tn)
{
  /* Collect all operators for normalization */
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  std::vector<unsigned> op_pos(dt.getNumConstructors());
  std::iota(op_pos.begin(), op_pos.end(), 0);
  return normalizeSygusRec(tn, dt, op_pos);
}

TypeNode SygusGrammarNorm::normalizeSygusType(TypeNode tn, Node sygus_vars)
{
  Trace("sygus-grammar-normalize-build")
      << "Will normalize " << tn << " with datatype "
      << static_cast<DatatypeType>(tn.toType()).getDatatype() << "\n";
  /* Normalize all types in tn */
  d_sygus_vars = sygus_vars;
  normalizeSygusRec(tn);
  /* Resolve created types */
  Assert(!d_dt_all.empty() && !d_unres_t_all.empty());
  if (Trace.isOn("sygus-grammar-normalize-build"))
  {
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
  }
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

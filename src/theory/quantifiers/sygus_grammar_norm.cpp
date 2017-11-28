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
#include "printer/sygus_print_callback.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/quantifiers/ce_guided_conjecture.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

TypeObject::TypeObject(TypeNode src_tn, Type src_t, std::string type_name)
    : d_dt(Datatype(type_name))
{
  d_tn = src_tn;
  d_t = src_t;
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
  /* TODO improve this so the names are not duplicated */
  /* Create new type name */
  std::stringstream ss;
  ss << tn << "_norm";
  std::string type_name = ss.str();
  /* Add to global accumulators */
  tos.push_back(TypeObject(tn, tn.toType(), type_name));
  tn_to_unres[tn] = tos.back().d_unres_t;
  /* Visit types of constructor arguments */
  const Datatype& dt = static_cast<DatatypeType>(tos.back().d_t).getDatatype();
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
  Node one = d_qe->getTermUtil()->getTypeValue(TypeNode::fromType(int_type), 1);
  /* TODO fix this */
  /* SygusEmptyPrintCallback empty_pc; */
  /* Build integer identity operator */
  vars.push_back(d_nm->mkBoundVar(TypeNode::fromType(int_type)));
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
  tos[ind].d_pc.push_back(nullptr);
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
    tos[r_pos].d_pc.push_back(nullptr);
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
    tos[r_pos].d_pc.push_back(nullptr);
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
      tos[r_pos].d_pc.push_back(nullptr);
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
      tos[r_pos].d_pc.push_back(nullptr);
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
      tos[r_pos].d_pc.push_back(nullptr);
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
      tos[r_pos].d_pc.push_back(nullptr);
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
      tos[i].d_pc.push_back(cons.getSygusPrintCallback());
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
                                      tos[i].d_pc[j]);
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

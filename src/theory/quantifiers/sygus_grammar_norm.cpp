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
#include "theory/quantifiers/sygus_grammar_red.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

#include <numeric>  // for std::iota

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool OpPosTrie::getOrMakeType(TypeNode tn,
                              TypeNode& unres_tn,
                              const std::vector<unsigned>& op_pos,
                              unsigned ind)
{
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

void SygusGrammarNorm::TypeObject::addConsInfo(SygusGrammarNorm* sygus_norm,
                                               const DatatypeConstructor& cons)
{
  Trace("sygus-grammar-normalize") << "...for " << cons.getName() << "\n";
  /* Recover the sygus operator to not lose reference to the original
   * operator (NOT, ITE, etc) */
  Node exp_sop_n = Node::fromExpr(
      smt::currentSmtEngine()->expandDefinitions(cons.getSygusOp()));
  d_ops.push_back(Rewriter::rewrite(exp_sop_n));
  Trace("sygus-grammar-normalize-defs")
      << "\tOriginal op: " << cons.getSygusOp()
      << "\n\tExpanded one: " << exp_sop_n
      << "\n\tRewritten one: " << d_ops.back() << "\n\n";
  d_cons_names.push_back(cons.getName());
  d_pc.push_back(cons.getSygusPrintCallback());
  d_weight.push_back(cons.getWeight());
  d_cons_args_t.push_back(std::vector<Type>());
  for (const DatatypeConstructorArg& arg : cons)
  {
    /* Collect unresolved type nodes corresponding to the typenode of the
     * arguments */
    d_cons_args_t.back().push_back(
        sygus_norm
            ->normalizeSygusRec(TypeNode::fromType(
                static_cast<SelectorType>(arg.getType()).getRangeType()))
            .toType());
  }
}

void SygusGrammarNorm::TypeObject::buildDatatype(SygusGrammarNorm* sygus_norm,
                                                 const Datatype& dt)
{
  /* Use the sygus type to not lose reference to the original types (Bool,
   * Int, etc) */
  d_dt.setSygus(dt.getSygusType(),
                sygus_norm->d_sygus_vars.toExpr(),
                dt.getSygusAllowConst(),
                dt.getSygusAllowAll());
  for (unsigned i = 0, size_d_ops = d_ops.size(); i < size_d_ops; ++i)
  {
    d_dt.addSygusConstructor(d_ops[i].toExpr(),
                             d_cons_names[i],
                             d_cons_args_t[i],
                             d_pc[i],
                             d_weight[i]);
  }
  Trace("sygus-grammar-normalize") << "...built datatype " << d_dt << " ";
  /* Add to global accumulators */
  sygus_norm->d_dt_all.push_back(d_dt);
  sygus_norm->d_unres_t_all.insert(d_unres_tn.toType());
  Trace("sygus-grammar-normalize") << "---------------------------------\n";
}

void SygusGrammarNorm::TransfDrop::buildType(SygusGrammarNorm* sygus_norm,
                                             TypeObject& to,
                                             const Datatype& dt,
                                             std::vector<unsigned>& op_pos)
{
  std::vector<unsigned> difference;
  std::set_difference(op_pos.begin(),
                      op_pos.end(),
                      d_drop_indices.begin(),
                      d_drop_indices.end(),
                      std::back_inserter(difference));
  op_pos = difference;
}

/* TODO #1304: have more operators and types. Moreover, have more general ways
   of finding kind of operator, e.g. if op is (\lambda xy. x + y) this
   function should realize that it is chainable for integers */
bool SygusGrammarNorm::TransfChain::isChainable(TypeNode tn, Node op)
{
  /* Checks whether operator occurs chainable for its type */
  if (tn.isInteger() && NodeManager::currentNM()->operatorToKind(op) == PLUS)
  {
    return true;
  }
  return false;
}

/* TODO #1304: have more operators and types. Moreover, have more general ways
   of finding kind of operator, e.g. if op is (\lambda xy. x + y) this
   function should realize that it is chainable for integers */
bool SygusGrammarNorm::TransfChain::isId(TypeNode tn, Node op, Node n)
{
  if (tn.isInteger() && NodeManager::currentNM()->operatorToKind(op) == PLUS
      && n == TermUtil::mkTypeValue(tn, 0))
  {
    return true;
  }
  return false;
}

void SygusGrammarNorm::TransfChain::buildType(SygusGrammarNorm* sygus_norm,
                                              TypeObject& to,
                                              const Datatype& dt,
                                              std::vector<unsigned>& op_pos)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<unsigned> claimed(d_elem_pos);
  claimed.push_back(d_chain_op_pos);
  unsigned nb_op_pos = op_pos.size();
  /* TODO do this properly */
  /* Remove from op_pos the positions claimed by the transformation */
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
  /* Build identity operator and empty callback */
  Node iden_op =
      SygusGrammarNorm::getIdOp(TypeNode::fromType(dt.getSygusType()));
  /* If all operators are claimed, create a monomial */
  if (nb_op_pos == d_elem_pos.size() + 1)
  {
    Trace("sygus-grammar-normalize-chain")
        << "\tCreating id type for " << d_elem_pos.back() << "\n";
    /* creates type for element */
    std::vector<unsigned> tmp;
    tmp.push_back(d_elem_pos.back());
    Type t = sygus_norm->normalizeSygusRec(to.d_tn, dt, tmp).toType();
    /* consumes element */
    d_elem_pos.pop_back();
    /* adds to Root: "type" */
    to.d_ops.push_back(iden_op);
    to.d_cons_names.push_back("id");
    to.d_pc.push_back(printer::SygusEmptyPrintCallback::getEmptyPC());
    /* Identity operators should not increase the size of terms */
    to.d_weight.push_back(0);
    to.d_cons_args_t.push_back(std::vector<Type>());
    to.d_cons_args_t.back().push_back(t);
    Trace("sygus-grammar-normalize-chain")
        << "\tAdding  " << t << " to " << to.d_unres_tn << "\n";
    /* adds to Root: "type + Root" */
    to.d_ops.push_back(nm->operatorOf(PLUS));
    to.d_cons_names.push_back(kindToString(PLUS));
    to.d_pc.push_back(nullptr);
    to.d_weight.push_back(-1);
    to.d_cons_args_t.push_back(std::vector<Type>());
    to.d_cons_args_t.back().push_back(t);
    to.d_cons_args_t.back().push_back(to.d_unres_tn.toType());
    Trace("sygus-grammar-normalize-chain")
        << "\tAdding PLUS to " << to.d_unres_tn << " with arg types "
        << to.d_unres_tn << " and " << t << "\n";
  }
  /* In the initial case if not all operators claimed always creates a next */
  Assert(nb_op_pos != d_elem_pos.size() + 1 || d_elem_pos.size() > 1);
  /* TODO #1304: consider case in which CHAIN op has different types than
     to.d_tn */
  /* If no more elements to chain, finish */
  if (d_elem_pos.size() == 0)
  {
    return;
  }
  /* Creates a type do be added to root representing next step in the chain */
  /* Add + to elems */
  d_elem_pos.push_back(d_chain_op_pos);
  if (Trace.isOn("sygus-grammar-normalize-chain"))
  {
    Trace("sygus-grammar-normalize-chain")
        << "\tCreating type for next entry with sygus_ops ";
    for (unsigned i = 0, size = d_elem_pos.size(); i < size; ++i)
    {
      Trace("sygus-grammar-normalize-chain")
          << dt[d_elem_pos[i]].getSygusOp() << " ";
    }
    Trace("sygus-grammar-normalize-chain") << "\n";
  }
  /* adds to Root: (\lambda x. x ) Next */
  to.d_ops.push_back(iden_op);
  to.d_cons_names.push_back("id_next");
  to.d_pc.push_back(printer::SygusEmptyPrintCallback::getEmptyPC());
  to.d_weight.push_back(0);
  to.d_cons_args_t.push_back(std::vector<Type>());
  to.d_cons_args_t.back().push_back(
      sygus_norm->normalizeSygusRec(to.d_tn, dt, d_elem_pos).toType());
}

std::map<TypeNode, Node> SygusGrammarNorm::d_tn_to_id = {};

/* Traverse the constructors of dt according to the positions in op_pos. Collect
 * those that fit the kinds established by to_collect. Remove collected operator
 * positions from op_pos. Accumulate collected positions in collected
 *
 * returns true if collected anything
 */
std::unique_ptr<SygusGrammarNorm::Transf> SygusGrammarNorm::inferTransf(
    TypeNode tn, const Datatype& dt, const std::vector<unsigned>& op_pos)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode sygus_tn = TypeNode::fromType(dt.getSygusType());
  Trace("sygus-gnorm") << "Infer transf for " << dt.getName() << "..."
                       << std::endl;
  Trace("sygus-gnorm") << "  #cons = " << op_pos.size() << " / "
                       << dt.getNumConstructors() << std::endl;
  // look for redundant constructors to drop
  if (options::sygusMinGrammar() && dt.getNumConstructors() == op_pos.size())
  {
    SygusRedundantCons src;
    src.initialize(d_qe, tn);
    std::vector<unsigned> rindices;
    src.getRedundant(rindices);
    if (!rindices.empty())
    {
      Trace("sygus-gnorm") << "...drop transf, " << rindices.size() << "/"
                           << op_pos.size() << " constructors." << std::endl;
      Assert(rindices.size() < op_pos.size());
      return std::unique_ptr<Transf>(new TransfDrop(rindices));
    }
  }

  // if normalization option is not enabled, we do not infer the transformations
  // below
  if (!options::sygusGrammarNorm())
  {
    return nullptr;
  }

  /* TODO #1304: step 1: look for singleton */
  /* step 2: look for chain */
  unsigned chain_op_pos = dt.getNumConstructors();
  std::vector<unsigned> elem_pos;
  for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
  {
    Assert(op_pos[i] < dt.getNumConstructors());
    Expr sop = dt[op_pos[i]].getSygusOp();
    /* Collects a chainable operator such as PLUS */
    if (sop.getKind() == BUILTIN
        && TransfChain::isChainable(sygus_tn, Node::fromExpr(sop)))
    {
      Assert(nm->operatorToKind(Node::fromExpr(sop)) == PLUS);
      /* TODO #1304: be robust for this case */
      /* For now only transforms applications whose arguments have the same type
       * as the root */
      bool same_type_plus = true;
      for (const DatatypeConstructorArg& arg : dt[op_pos[i]])
      {
        if (TypeNode::fromType(
                static_cast<SelectorType>(arg.getType()).getRangeType())
            != tn)
        {
          same_type_plus = false;
          break;
        }
      }
      if (!same_type_plus)
      {
        Trace("sygus-grammar-normalize-infer")
            << "\tFor OP " << PLUS << " did not collecting sop " << sop
            << " in position " << op_pos[i] << "\n";
        continue;
      }
      Assert(chain_op_pos == dt.getNumConstructors());
      Trace("sygus-grammar-normalize-infer")
          << "\tCollecting chainable OP " << sop << " in position " << op_pos[i]
          << "\n";
      chain_op_pos = op_pos[i];
      continue;
    }
    /* TODO #1304: check this for each operator */
    /* Collects elements that are not the identity (e.g. 0 is the id of PLUS) */
    if (!TransfChain::isId(sygus_tn, nm->operatorOf(PLUS), Node::fromExpr(sop)))
    {
      Trace("sygus-grammar-normalize-infer")
          << "\tCollecting for NON_ID_ELEMS the sop " << sop
          << " in position " << op_pos[i] << "\n";
      elem_pos.push_back(op_pos[i]);
    }
  }
  /* Typenode admits a chain transformation for normalization */
  if (chain_op_pos != dt.getNumConstructors() && !elem_pos.empty())
  {
    Trace("sygus-gnorm") << "...chain transf." << std::endl;
    Trace("sygus-grammar-normalize-infer")
        << "\tInfering chain transformation\n";
    return std::unique_ptr<Transf>(new TransfChain(chain_op_pos, elem_pos));
  }
  return nullptr;
}

TypeNode SygusGrammarNorm::normalizeSygusRec(TypeNode tn,
                                             const Datatype& dt,
                                             std::vector<unsigned>& op_pos)
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

  /* Determine normalization transformation based on sygus type and given
    * operators */
  std::unique_ptr<Transf> transformation = inferTransf(tn, dt, op_pos);
  /* If a transformation was selected, apply it */
  if (transformation != nullptr)
  {
    transformation->buildType(this, to, dt, op_pos);
  }

  /* Remaining operators are rebuilt as they are */
  for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
  {
    Assert(op_pos[i] < dt.getNumConstructors());
    to.addConsInfo(this, dt[op_pos[i]]);
  }
  /* Build normalize datatype */
  if (Trace.isOn("sygus-grammar-normalize"))
  {
    Trace("sygus-grammar-normalize") << "\nFor positions ";
    for (unsigned i = 0, size = op_pos.size(); i < size; ++i)
    {
      Trace("sygus-grammar-normalize") << op_pos[i] << " ";
    }
    Trace("sygus-grammar-normalize") << " and datatype " << dt << " \n";
  }
  to.buildDatatype(this, dt);
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
      NodeManager::currentNM()->toExprManager()->mkMutualDatatypeTypes(
          d_dt_all, d_unres_t_all);
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

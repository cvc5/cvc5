/*********************                                                        */
/*! \file sygus_simple_sym.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of simple symmetry breaking for sygus
 **/

#include "theory/datatypes/sygus_simple_sym.h"

#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace datatypes {

SygusSimpleSymBreak::SygusSimpleSymBreak(QuantifiersEngine* qe)
    : d_tds(qe->getTermDatabaseSygus()), d_tutil(qe->getTermUtil())
{
}

/** Requirement trie
 *
 * This class is used to make queries about sygus grammars, including what
 * constructors they contain, and their types.
 *
 * As a simple example, consider the trie:
 * root:
 *   d_req_kind = PLUS
 *   d_children[0]:
 *     d_req_type = A
 *   d_children[1]:
 *     d_req_type = A
 * This trie is satisfied by sygus types that have a constructor whose builtin
 * kind is PLUS and whose argument types are both A.
 */
class ReqTrie
{
 public:
  ReqTrie() : d_req_kind(UNDEFINED_KIND) {}
  /** the children of this node */
  std::map<unsigned, ReqTrie> d_children;
  /** the (builtin) kind required by this node */
  Kind d_req_kind;
  /** the type that this node is required to be */
  TypeNode d_req_type;
  /** the constant required by this node */
  Node d_req_const;
  /** print this trie */
  void print(const char* c, int indent = 0)
  {
    if (d_req_kind != UNDEFINED_KIND)
    {
      Trace(c) << d_req_kind << " ";
    }
    else if (!d_req_type.isNull())
    {
      Trace(c) << d_req_type;
    }
    else if (!d_req_const.isNull())
    {
      Trace(c) << d_req_const;
    }
    else
    {
      Trace(c) << "_";
    }
    Trace(c) << std::endl;
    for (std::map<unsigned, ReqTrie>::iterator it = d_children.begin();
         it != d_children.end();
         ++it)
    {
      for (int i = 0; i <= indent; i++)
      {
        Trace(c) << "  ";
      }
      Trace(c) << it->first << " : ";
      it->second.print(c, indent + 1);
    }
  }
  /**
   * Are the requirements of this trie satisfied by sygus type tn?
   * tdb is a reference to the sygus term database.
   */
  bool satisfiedBy(quantifiers::TermDbSygus* tdb, TypeNode tn)
  {
    if (!d_req_const.isNull())
    {
      quantifiers::SygusTypeInfo& sti = tdb->getTypeInfo(tn);
      if (!sti.hasConst(d_req_const))
      {
        return false;
      }
    }
    if (!d_req_type.isNull())
    {
      Trace("sygus-sb-debug")
          << "- check if " << tn << " is type " << d_req_type << std::endl;
      if (tn != d_req_type)
      {
        return false;
      }
    }
    if (d_req_kind != UNDEFINED_KIND)
    {
      Trace("sygus-sb-debug")
          << "- check if " << tn << " has " << d_req_kind << std::endl;
      std::vector<TypeNode> argts;
      if (tdb->canConstructKind(tn, d_req_kind, argts))
      {
        for (std::map<unsigned, ReqTrie>::iterator it = d_children.begin();
             it != d_children.end();
             ++it)
        {
          if (it->first < argts.size())
          {
            TypeNode tnc = argts[it->first];
            if (!it->second.satisfiedBy(tdb, tnc))
            {
              return false;
            }
          }
          else
          {
            return false;
          }
        }
      }
      else
      {
        return false;
      }
    }
    return true;
  }
  /** is this the empty (trivially satisfied) trie? */
  bool empty()
  {
    return d_req_kind == UNDEFINED_KIND && d_req_const.isNull()
           && d_req_type.isNull() && d_children.empty();
  }
};

bool SygusSimpleSymBreak::considerArgKind(
    TypeNode tn, TypeNode tnp, Kind k, Kind pk, int arg)
{
  const DType& pdt = tnp.getDType();
  const DType& dt = tn.getDType();
  quantifiers::SygusTypeInfo& ti = d_tds->getTypeInfo(tn);
  quantifiers::SygusTypeInfo& pti = d_tds->getTypeInfo(tnp);
  Assert(ti.hasKind(k));
  Assert(pti.hasKind(pk));
  Trace("sygus-sb-debug") << "Consider sygus arg kind " << k << ", pk = " << pk
                          << ", arg = " << arg << " in " << tnp << "?"
                          << std::endl;
  int c = ti.getKindConsNum(k);
  int pc = pti.getKindConsNum(pk);
  // check for associativity
  if (k == pk && quantifiers::TermUtil::isAssoc(k))
  {
    // if the operator is associative, then a repeated occurrence should only
    // occur in the leftmost argument position
    int firstArg = getFirstArgOccurrence(pdt[pc], tn);
    Assert(firstArg != -1);
    if (arg == firstArg)
    {
      return true;
    }
    // the argument types of the child must be the parent's type
    for (unsigned i = 0, nargs = dt[c].getNumArgs(); i < nargs; i++)
    {
      TypeNode type = dt[c].getArgType(i);
      if (type != tnp)
      {
        return true;
      }
    }
    Trace("sygus-sb-simple")
        << "  sb-simple : do not consider " << k << " at child arg " << arg
        << " of " << k
        << " since it is associative, with first arg = " << firstArg
        << std::endl;
    return false;
  }
  // describes the shape of an alternate term to construct
  //  we check whether this term is in the sygus grammar below
  ReqTrie rt;
  Assert(rt.empty());

  // construct rt by cases
  if (pk == NOT || pk == BITVECTOR_NOT || pk == UMINUS || pk == BITVECTOR_NEG)
  {
    // negation normal form
    if (pk == k)
    {
      rt.d_req_type = dt[c].getArgType(0);
    }
    else
    {
      Kind reqk = UNDEFINED_KIND;      // required kind for all children
      std::map<unsigned, Kind> reqkc;  // required kind for some children
      if (pk == NOT)
      {
        if (k == AND)
        {
          rt.d_req_kind = OR;
          reqk = NOT;
        }
        else if (k == OR)
        {
          rt.d_req_kind = AND;
          reqk = NOT;
        }
        else if (k == EQUAL)
        {
          rt.d_req_kind = XOR;
        }
        else if (k == XOR)
        {
          rt.d_req_kind = EQUAL;
        }
        else if (k == ITE)
        {
          rt.d_req_kind = ITE;
          reqkc[1] = NOT;
          reqkc[2] = NOT;
          rt.d_children[0].d_req_type = dt[c].getArgType(0);
        }
        else if (k == LEQ || k == GT)
        {
          //  (not (~ x y)) ----->  (~ (+ y 1) x)
          rt.d_req_kind = k;
          rt.d_children[0].d_req_kind = PLUS;
          rt.d_children[0].d_children[0].d_req_type = dt[c].getArgType(1);
          rt.d_children[0].d_children[1].d_req_const =
              NodeManager::currentNM()->mkConst(Rational(1));
          rt.d_children[1].d_req_type = dt[c].getArgType(0);
        }
        else if (k == LT || k == GEQ)
        {
          //  (not (~ x y)) ----->  (~ y (+ x 1))
          rt.d_req_kind = k;
          rt.d_children[0].d_req_type = dt[c].getArgType(1);
          rt.d_children[1].d_req_kind = PLUS;
          rt.d_children[1].d_children[0].d_req_type = dt[c].getArgType(0);
          rt.d_children[1].d_children[1].d_req_const =
              NodeManager::currentNM()->mkConst(Rational(1));
        }
      }
      else if (pk == BITVECTOR_NOT)
      {
        if (k == BITVECTOR_AND)
        {
          rt.d_req_kind = BITVECTOR_OR;
          reqk = BITVECTOR_NOT;
        }
        else if (k == BITVECTOR_OR)
        {
          rt.d_req_kind = BITVECTOR_AND;
          reqk = BITVECTOR_NOT;
        }
        else if (k == BITVECTOR_XNOR)
        {
          rt.d_req_kind = BITVECTOR_XOR;
        }
        else if (k == BITVECTOR_XOR)
        {
          rt.d_req_kind = BITVECTOR_XNOR;
        }
      }
      else if (pk == UMINUS)
      {
        if (k == PLUS)
        {
          rt.d_req_kind = PLUS;
          reqk = UMINUS;
        }
      }
      else if (pk == BITVECTOR_NEG)
      {
        if (k == PLUS)
        {
          rt.d_req_kind = PLUS;
          reqk = BITVECTOR_NEG;
        }
      }
      if (!rt.empty() && (reqk != UNDEFINED_KIND || !reqkc.empty()))
      {
        int pcr = pti.getKindConsNum(rt.d_req_kind);
        if (pcr != -1)
        {
          Assert(pcr < static_cast<int>(pdt.getNumConstructors()));
          // must have same number of arguments
          if (pdt[pcr].getNumArgs() == dt[c].getNumArgs())
          {
            for (unsigned i = 0, nargs = pdt[pcr].getNumArgs(); i < nargs; i++)
            {
              Kind rk = reqk;
              if (reqk == UNDEFINED_KIND)
              {
                std::map<unsigned, Kind>::iterator itr = reqkc.find(i);
                if (itr != reqkc.end())
                {
                  rk = itr->second;
                }
              }
              if (rk != UNDEFINED_KIND)
              {
                rt.d_children[i].d_req_kind = rk;
                rt.d_children[i].d_children[0].d_req_type = dt[c].getArgType(i);
              }
            }
          }
        }
      }
    }
  }
  else if (k == MINUS || k == BITVECTOR_SUB)
  {
    if (pk == EQUAL || pk == MINUS || pk == BITVECTOR_SUB || pk == LEQ
        || pk == LT || pk == GEQ || pk == GT)
    {
      int oarg = arg == 0 ? 1 : 0;
      //  (~ x (- y z))  ---->  (~ (+ x z) y)
      //  (~ (- y z) x)  ---->  (~ y (+ x z))
      rt.d_req_kind = pk;
      rt.d_children[arg].d_req_type = dt[c].getArgType(0);
      rt.d_children[oarg].d_req_kind = k == MINUS ? PLUS : BITVECTOR_PLUS;
      rt.d_children[oarg].d_children[0].d_req_type = pdt[pc].getArgType(oarg);
      rt.d_children[oarg].d_children[1].d_req_type = dt[c].getArgType(1);
    }
    else if (pk == PLUS || pk == BITVECTOR_PLUS)
    {
      //  (+ x (- y z))  -----> (- (+ x y) z)
      //  (+ (- y z) x)  -----> (- (+ x y) z)
      rt.d_req_kind = pk == PLUS ? MINUS : BITVECTOR_SUB;
      int oarg = arg == 0 ? 1 : 0;
      rt.d_children[0].d_req_kind = pk;
      rt.d_children[0].d_children[0].d_req_type = pdt[pc].getArgType(oarg);
      rt.d_children[0].d_children[1].d_req_type = dt[c].getArgType(0);
      rt.d_children[1].d_req_type = dt[c].getArgType(1);
    }
  }
  else if (k == ITE)
  {
    if (pk != ITE)
    {
      //  (o X (ite y z w) X')  -----> (ite y (o X z X') (o X w X'))
      rt.d_req_kind = ITE;
      rt.d_children[0].d_req_type = dt[c].getArgType(0);
      unsigned n_args = pdt[pc].getNumArgs();
      for (unsigned r = 1; r <= 2; r++)
      {
        rt.d_children[r].d_req_kind = pk;
        for (unsigned q = 0; q < n_args; q++)
        {
          if ((int)q == arg)
          {
            rt.d_children[r].d_children[q].d_req_type = dt[c].getArgType(r);
          }
          else
          {
            rt.d_children[r].d_children[q].d_req_type = pdt[pc].getArgType(q);
          }
        }
      }
      // this increases term size but is probably a good idea
    }
  }
  else if (k == NOT)
  {
    if (pk == ITE)
    {
      //  (ite (not y) z w)  -----> (ite y w z)
      rt.d_req_kind = ITE;
      rt.d_children[0].d_req_type = dt[c].getArgType(0);
      rt.d_children[1].d_req_type = pdt[pc].getArgType(2);
      rt.d_children[2].d_req_type = pdt[pc].getArgType(1);
    }
  }
  Trace("sygus-sb-debug") << "Consider sygus arg kind " << k << ", pk = " << pk
                          << ", arg = " << arg << "?" << std::endl;
  if (!rt.empty())
  {
    rt.print("sygus-sb-debug");
    // check if it meets the requirements
    if (rt.satisfiedBy(d_tds, tnp))
    {
      Trace("sygus-sb-debug") << "...success!" << std::endl;
      Trace("sygus-sb-simple")
          << "  sb-simple : do not consider " << k << " as arg " << arg
          << " of " << pk << std::endl;
      // do not need to consider the kind in the search since there are ways to
      // construct equivalent terms
      return false;
    }
    else
    {
      Trace("sygus-sb-debug") << "...failed." << std::endl;
    }
    Trace("sygus-sb-debug") << std::endl;
  }
  // must consider this kind in the search
  return true;
}

bool SygusSimpleSymBreak::considerConst(
    TypeNode tn, TypeNode tnp, Node c, Kind pk, int arg)
{
  const DType& pdt = tnp.getDType();
  // child grammar-independent
  if (!considerConst(pdt, tnp, c, pk, arg))
  {
    return false;
  }
  // this can probably be made child grammar independent
  quantifiers::SygusTypeInfo& ti = d_tds->getTypeInfo(tn);
  quantifiers::SygusTypeInfo& pti = d_tds->getTypeInfo(tnp);
  int pc = pti.getKindConsNum(pk);
  if (pdt[pc].getNumArgs() == 2)
  {
    Kind ok;
    int offset;
    if (d_tutil->hasOffsetArg(pk, arg, offset, ok))
    {
      Trace("sygus-sb-simple-debug")
          << pk << " has offset arg " << ok << " " << offset << std::endl;
      int ok_arg = pti.getKindConsNum(ok);
      if (ok_arg != -1)
      {
        Trace("sygus-sb-simple-debug")
            << "...at argument " << ok_arg << std::endl;
        // other operator be the same type
        if (d_tds->isTypeMatch(pdt[ok_arg], pdt[arg]))
        {
          int status;
          Node co = d_tutil->getTypeValueOffset(c.getType(), c, offset, status);
          Trace("sygus-sb-simple-debug")
              << c << " with offset " << offset << " is " << co
              << ", status=" << status << std::endl;
          if (status == 0 && !co.isNull())
          {
            if (ti.hasConst(co))
            {
              Trace("sygus-sb-simple")
                  << "  sb-simple : by offset reasoning, do not consider const "
                  << c;
              Trace("sygus-sb-simple")
                  << " as arg " << arg << " of " << pk << " since we can use "
                  << co << " under " << ok << " " << std::endl;
              return false;
            }
          }
        }
      }
    }
  }
  return true;
}

bool SygusSimpleSymBreak::considerConst(
    const DType& pdt, TypeNode tnp, Node c, Kind pk, int arg)
{
  quantifiers::SygusTypeInfo& pti = d_tds->getTypeInfo(tnp);
  Assert(pti.hasKind(pk));
  int pc = pti.getKindConsNum(pk);
  bool ret = true;
  Trace("sygus-sb-debug") << "Consider sygus const " << c << ", parent = " << pk
                          << ", arg = " << arg << "?" << std::endl;
  if (d_tutil->isIdempotentArg(c, pk, arg))
  {
    if (pdt[pc].getNumArgs() == 2)
    {
      int oarg = arg == 0 ? 1 : 0;
      TypeNode otn = pdt[pc].getArgType(oarg);
      if (otn == tnp)
      {
        Trace("sygus-sb-simple")
            << "  sb-simple : " << c << " is idempotent arg " << arg << " of "
            << pk << "..." << std::endl;
        ret = false;
      }
    }
  }
  else
  {
    Node sc = d_tutil->isSingularArg(c, pk, arg);
    if (!sc.isNull())
    {
      if (pti.hasConst(sc))
      {
        Trace("sygus-sb-simple")
            << "  sb-simple : " << c << " is singular arg " << arg << " of "
            << pk << ", evaluating to " << sc << "..." << std::endl;
        ret = false;
      }
    }
  }
  if (ret)
  {
    ReqTrie rt;
    Assert(rt.empty());
    Node max_c = d_tutil->getTypeMaxValue(c.getType());
    Node zero_c = d_tutil->getTypeValue(c.getType(), 0);
    Node one_c = d_tutil->getTypeValue(c.getType(), 1);
    if (pk == XOR || pk == BITVECTOR_XOR)
    {
      if (c == max_c)
      {
        rt.d_req_kind = pk == XOR ? NOT : BITVECTOR_NOT;
      }
    }
    else if (pk == ITE)
    {
      if (arg == 0)
      {
        if (c == max_c)
        {
          rt.d_children[1].d_req_type = tnp;
        }
        else if (c == zero_c)
        {
          rt.d_children[2].d_req_type = tnp;
        }
      }
    }
    else if (pk == STRING_SUBSTR)
    {
      if (c == one_c && arg == 2)
      {
        rt.d_req_kind = STRING_CHARAT;
        rt.d_children[0].d_req_type = pdt[pc].getArgType(0);
        rt.d_children[1].d_req_type = pdt[pc].getArgType(1);
      }
    }
    if (!rt.empty())
    {
      // check if satisfied
      if (rt.satisfiedBy(d_tds, tnp))
      {
        Trace("sygus-sb-simple") << "  sb-simple : do not consider const " << c
                                 << " as arg " << arg << " of " << pk;
        Trace("sygus-sb-simple") << " in " << pdt.getName() << std::endl;
        // do not need to consider the constant in the search since there are
        // ways to construct equivalent terms
        ret = false;
      }
    }
  }
  return ret;
}

int SygusSimpleSymBreak::solveForArgument(TypeNode tn,
                                          unsigned cindex,
                                          unsigned arg)
{
  // we currently do not solve for arguments
  return -1;
}

int SygusSimpleSymBreak::getFirstArgOccurrence(const DTypeConstructor& c,
                                               TypeNode tn)
{
  for (unsigned i = 0, nargs = c.getNumArgs(); i < nargs; i++)
  {
    if (c.getArgType(i) == tn)
    {
      return i;
    }
  }
  return -1;
}

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4

/*********************                                                        */
/*! \file type_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus type info class
 **/

#include "theory/quantifiers/sygus/type_info.h"

#include "base/check.h"
#include "expr/dtype.h"
#include "expr/sygus_datatype.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusTypeInfo::SygusTypeInfo()
    : d_hasIte(false),
      d_min_term_size(0),
      d_sym_cons_any_constant(-1),
      d_has_subterm_sym_cons(false)
{
}

void SygusTypeInfo::initialize(TermDbSygus* tds, TypeNode tn)
{
  d_this = tn;
  Assert(tn.isDatatype());
  const DType& dt = tn.getDType();
  Assert(dt.isSygus());
  Trace("sygus-db") << "Register type " << dt.getName() << "..." << std::endl;
  TypeNode btn = dt.getSygusType();
  d_btype = btn;
  Assert(!d_btype.isNull());
  // get the sygus variable list
  Node var_list = dt.getSygusVarList();
  if (!var_list.isNull())
  {
    for (unsigned j = 0; j < var_list.getNumChildren(); j++)
    {
      Node sv = var_list[j];
      SygusVarNumAttribute svna;
      sv.setAttribute(svna, j);
      d_var_list.push_back(sv);
    }
  }
  else
  {
    // no arguments to synthesis functions
    d_var_list.clear();
  }

  // compute min term size information: this must be computed before registering
  // subfield types
  d_min_term_size = 1;
  for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    if (dt[i].getNumArgs() == 0)
    {
      d_min_term_size = 0;
    }
  }

  // register connected types
  for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
    {
      TypeNode ctn = dt[i].getArgType(j);
      Trace("sygus-db") << "  register subfield type " << ctn << std::endl;
      if (tds->registerSygusType(ctn))
      {
        SygusTypeInfo& stic = tds->getTypeInfo(ctn);
        // carry type attributes
        if (stic.d_has_subterm_sym_cons)
        {
          d_has_subterm_sym_cons = true;
        }
      }
    }
  }
  // iterate over constructors
  for (unsigned i = 0; i < dt.getNumConstructors(); i++)
  {
    Node sop = dt[i].getSygusOp();
    Assert(!sop.isNull());
    Trace("sygus-db") << "  Operator #" << i << " : " << sop;
    Kind builtinKind = UNDEFINED_KIND;
    if (sop.getKind() == kind::BUILTIN)
    {
      builtinKind = NodeManager::operatorToKind(sop);
      Trace("sygus-db") << ", kind = " << builtinKind;
    }
    else if (sop.isConst() && dt[i].getNumArgs() == 0)
    {
      Trace("sygus-db") << ", constant";
      d_consts[sop] = i;
      d_arg_const[i] = sop;
    }
    else if (sop.getKind() == LAMBDA)
    {
      // do type checking
      Assert(sop[0].getNumChildren() == dt[i].getNumArgs());
      for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
      {
        TypeNode ct = dt[i].getArgType(j);
        TypeNode cbt = tds->sygusToBuiltinType(ct);
        TypeNode lat = sop[0][j].getType();
        AlwaysAssert(cbt.isSubtypeOf(lat))
            << "In sygus datatype " << dt.getName()
            << ", argument to a lambda constructor is not " << lat << std::endl;
      }
      // See if it is a builtin kind, possible if the operator is of the form:
      // lambda x1 ... xn. f( x1, ..., xn ) and f is not a parameterized kind
      // (e.g. APPLY_UF is a parameterized kind).
      if (sop[1].getMetaKind() != kind::metakind::PARAMETERIZED)
      {
        size_t nchild = sop[0].getNumChildren();
        if (nchild == sop[1].getNumChildren())
        {
          builtinKind = sop[1].getKind();
          for (size_t j = 0; j < nchild; j++)
          {
            if (sop[0][j] != sop[1][j])
            {
              // arguments not in order
              builtinKind = UNDEFINED_KIND;
              break;
            }
          }
        }
      }
    }
    if (builtinKind != UNDEFINED_KIND)
    {
      d_kinds[builtinKind] = i;
      d_arg_kind[i] = builtinKind;
      if (builtinKind == ITE)
      {
        // mark that this type has an ITE
        d_hasIte = true;
      }
    }
    // symbolic constructors
    if (sop.getAttribute(SygusAnyConstAttribute()))
    {
      d_sym_cons_any_constant = i;
      d_has_subterm_sym_cons = true;
    }
    d_ops[sop] = i;
    d_arg_ops[i] = sop;
    Trace("sygus-db") << std::endl;
    // We must properly catch type errors in sygus grammars for arguments of
    // builtin operators. The challenge is that we easily ask for expected
    // argument types of builtin operators e.g. PLUS. Hence we use a call to
    // mkGeneric below. This ensures that terms that this constructor encodes
    // are of the type specified in the datatype. This will fail if
    // e.g. bitvector-and is a constructor of an integer grammar. Our (version
    // 2) SyGuS parser ensures that sygus constructors are built from well-typed
    // terms, so the term created by mkGeneric will also be well-typed here.
    Node g = tds->mkGeneric(dt, i);
    TypeNode gtn = g.getType();
    AlwaysAssert(gtn.isSubtypeOf(btn))
        << "Sygus datatype " << dt.getName()
        << " encodes terms that are not of type " << btn << std::endl;
    Trace("sygus-db") << "...done register Operator #" << i << std::endl;
  }
  // compute minimum type depth information
  computeMinTypeDepthInternal(tn, 0);
  // compute minimum term size information
  d_min_term_size = 1;
  for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    unsigned csize = 0;
    if (dt[i].getNumArgs() > 0)
    {
      csize = 1;
      for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
      {
        TypeNode ct = dt[i].getArgType(j);
        if (ct == tn)
        {
          csize += d_min_term_size;
        }
        else if (tds->isRegistered(ct))
        {
          SygusTypeInfo& stic = tds->getTypeInfo(ct);
          csize += stic.getMinTermSize();
        }
        else
        {
          Assert(!ct.isDatatype() || !ct.getDType().isSygus());
        }
      }
    }
    d_min_cons_term_size[i] = csize;
  }
  Trace("sygus-db") << "Register type " << dt.getName() << " finished"
                    << std::endl;
}

void SygusTypeInfo::initializeVarSubclasses()
{
  if (d_var_list.empty())
  {
    // no variables
    return;
  }
  if (!d_var_subclass_id.empty())
  {
    // already computed
    return;
  }
  // compute variable subclasses
  std::vector<TypeNode> sf_types;
  getSubfieldTypes(sf_types);
  // maps variables to the list of subfield types they occur in
  std::map<Node, std::vector<TypeNode> > type_occurs;
  for (const Node& v : d_var_list)
  {
    type_occurs[v].clear();
  }
  // for each type of subfield type of this enumerator
  for (unsigned i = 0, ntypes = sf_types.size(); i < ntypes; i++)
  {
    std::vector<unsigned> rm_indices;
    TypeNode stn = sf_types[i];
    Assert(stn.isDatatype());
    const DType& dt = stn.getDType();
    for (unsigned j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
    {
      Node sopn = dt[j].getSygusOp();
      Assert(!sopn.isNull());
      if (type_occurs.find(sopn) != type_occurs.end())
      {
        // if it is a variable, store that it occurs in stn
        type_occurs[sopn].push_back(stn);
      }
    }
  }
  TypeNodeIdTrie tnit;
  for (std::pair<const Node, std::vector<TypeNode> >& to : type_occurs)
  {
    tnit.add(to.first, to.second);
  }
  // 0 is reserved for "no type class id"
  unsigned typeIdCount = 1;
  tnit.assignIds(d_var_subclass_id, typeIdCount);
  // assign the list and reverse map to index
  for (std::pair<const Node, std::vector<TypeNode> >& to : type_occurs)
  {
    Node v = to.first;
    unsigned sc = d_var_subclass_id[v];
    Trace("sygus-db") << v << " has subclass id " << sc << std::endl;
    d_var_subclass_list_index[v] = d_var_subclass_list[sc].size();
    d_var_subclass_list[sc].push_back(v);
  }
}

TypeNode SygusTypeInfo::getBuiltinType() const { return d_btype; }

const std::vector<Node>& SygusTypeInfo::getVarList() const
{
  return d_var_list;
}

void SygusTypeInfo::computeMinTypeDepthInternal(TypeNode tn,
                                                unsigned type_depth)
{
  std::map<TypeNode, unsigned>::iterator it = d_min_type_depth.find(tn);
  if (it != d_min_type_depth.end() && type_depth >= it->second)
  {
    // no new information
    return;
  }
  if (!tn.isDatatype())
  {
    // do not recurse to non-datatype types
    return;
  }
  const DType& dt = tn.getDType();
  if (!dt.isSygus())
  {
    // do not recurse to non-sygus datatype types
    return;
  }
  d_min_type_depth[tn] = type_depth;
  // compute for connected types
  for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
    {
      TypeNode at = dt[i].getArgType(j);
      computeMinTypeDepthInternal(at, type_depth + 1);
    }
  }
}

unsigned SygusTypeInfo::getMinTypeDepth(TypeNode tn) const
{
  std::map<TypeNode, unsigned>::const_iterator it = d_min_type_depth.find(tn);
  if (it != d_min_type_depth.end())
  {
    Assert(false);
    return 0;
  }
  return it->second;
}

unsigned SygusTypeInfo::getMinTermSize() const { return d_min_term_size; }

unsigned SygusTypeInfo::getMinConsTermSize(unsigned cindex)
{
  std::map<unsigned, unsigned>::iterator it = d_min_cons_term_size.find(cindex);
  if (it != d_min_cons_term_size.end())
  {
    return it->second;
  }
  Assert(false);
  return 0;
}

void SygusTypeInfo::getSubfieldTypes(std::vector<TypeNode>& sf_types) const
{
  for (const std::pair<const TypeNode, unsigned>& st : d_min_type_depth)
  {
    sf_types.push_back(st.first);
  }
}

int SygusTypeInfo::getKindConsNum(Kind k) const
{
  std::map<Kind, unsigned>::const_iterator it = d_kinds.find(k);
  if (it != d_kinds.end())
  {
    return static_cast<int>(it->second);
  }
  return -1;
}

int SygusTypeInfo::getConstConsNum(Node n) const
{
  std::map<Node, unsigned>::const_iterator it = d_consts.find(n);
  if (it != d_consts.end())
  {
    return static_cast<int>(it->second);
  }
  return -1;
}

int SygusTypeInfo::getOpConsNum(Node n) const
{
  std::map<Node, unsigned>::const_iterator it = d_ops.find(n);
  if (it != d_ops.end())
  {
    return static_cast<int>(it->second);
  }
  return -1;
}

bool SygusTypeInfo::hasKind(Kind k) const { return getKindConsNum(k) != -1; }
bool SygusTypeInfo::hasIte() const { return d_hasIte; }
bool SygusTypeInfo::hasConst(Node n) const { return getConstConsNum(n) != -1; }
bool SygusTypeInfo::hasOp(Node n) const { return getOpConsNum(n) != -1; }

Node SygusTypeInfo::getConsNumOp(unsigned i) const
{
  std::map<unsigned, Node>::const_iterator itn = d_arg_ops.find(i);
  if (itn != d_arg_ops.end())
  {
    return itn->second;
  }
  return Node::null();
}

Node SygusTypeInfo::getConsNumConst(unsigned i) const
{
  std::map<unsigned, Node>::const_iterator itn = d_arg_const.find(i);
  if (itn != d_arg_const.end())
  {
    return itn->second;
  }
  return Node::null();
}

Kind SygusTypeInfo::getConsNumKind(unsigned i) const
{
  std::map<unsigned, Kind>::const_iterator itk = d_arg_kind.find(i);
  if (itk != d_arg_kind.end())
  {
    return itk->second;
  }
  return UNDEFINED_KIND;
}

bool SygusTypeInfo::isKindArg(unsigned i) const
{
  return getConsNumKind(i) != UNDEFINED_KIND;
}

bool SygusTypeInfo::isConstArg(unsigned i) const
{
  return d_arg_const.find(i) != d_arg_const.end();
}

int SygusTypeInfo::getAnyConstantConsNum() const
{
  return d_sym_cons_any_constant;
}

bool SygusTypeInfo::hasSubtermSymbolicCons() const
{
  return d_has_subterm_sym_cons;
}

unsigned SygusTypeInfo::getSubclassForVar(Node n) const
{
  std::map<Node, unsigned>::const_iterator itcc = d_var_subclass_id.find(n);
  if (itcc == d_var_subclass_id.end())
  {
    Assert(false);
    return 0;
  }
  return itcc->second;
}

unsigned SygusTypeInfo::getNumSubclassVars(unsigned sc) const
{
  std::map<unsigned, std::vector<Node> >::const_iterator itvv =
      d_var_subclass_list.find(sc);
  if (itvv == d_var_subclass_list.end())
  {
    Assert(false);
    return 0;
  }
  return itvv->second.size();
}
Node SygusTypeInfo::getVarSubclassIndex(unsigned sc, unsigned i) const
{
  std::map<unsigned, std::vector<Node> >::const_iterator itvv =
      d_var_subclass_list.find(sc);
  if (itvv == d_var_subclass_list.end() || i >= itvv->second.size())
  {
    Assert(false);
    return Node::null();
  }
  return itvv->second[i];
}

bool SygusTypeInfo::getIndexInSubclassForVar(Node v, unsigned& index) const
{
  std::map<Node, unsigned>::const_iterator itvv =
      d_var_subclass_list_index.find(v);
  if (itvv == d_var_subclass_list_index.end())
  {
    return false;
  }
  index = itvv->second;
  return true;
}

bool SygusTypeInfo::isSubclassVarTrivial() const
{
  for (const std::pair<const unsigned, std::vector<Node> >& p :
       d_var_subclass_list)
  {
    if (p.second.size() > 1)
    {
      return false;
    }
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

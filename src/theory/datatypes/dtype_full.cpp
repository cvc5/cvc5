/*********************                                                        */
/*! \file dtype.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class representing a datatype definition
 **/
#include "theory/datatypes/dtype.h"

#include <sstream>
#include <string>

#include "base/check.h"
#include "expr/attribute.h"
#include "expr/expr_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/matcher.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "expr/type.h"
#include "options/datatypes_options.h"
#include "options/set_language.h"
#include "theory/type_enumerator.h"

// FIXME : remove
using namespace std;
using namespace CVC4::kind;

namespace CVC4 {

struct DTypeIndexTag
{
};
struct DTypeConsIndexTag
{
};
struct DTypeFiniteTag
{
};
struct DTypeFiniteComputedTag
{
};
struct DTypeUFiniteTag
{
};
struct DTypeUFiniteComputedTag
{
};

typedef expr::Attribute<DTypeIndexTag, uint64_t> DTypeIndexAttr;
typedef expr::Attribute<DTypeConsIndexTag, uint64_t> DTypeConsIndexAttr;
typedef expr::Attribute<DTypeFiniteTag, bool> DTypeFiniteAttr;
typedef expr::Attribute<DTypeFiniteComputedTag, bool> DTypeFiniteComputedAttr;
typedef expr::Attribute<DTypeUFiniteTag, bool> DTypeUFiniteAttr;
typedef expr::Attribute<DTypeUFiniteComputedTag, bool> DTypeUFiniteComputedAttr;

DType::~DType() {}

const DType& DType::datatypeOf(Node item)
{
  TypeNode t = item.getType();
  switch (t.getKind())
  {
    case kind::CONSTRUCTOR_TYPE: return t[t.getNumChildren() - 1].getDType();
    case kind::SELECTOR_TYPE:
    case kind::TESTER_TYPE: return t[0].getDType();
    default:
      Unhandled() << "arg must be a datatype constructor, selector, or tester";
  }
}

size_t DType::indexOf(Node item)
{
  PrettyCheckArgument(
      item.getType().isConstructor() || item.getType().isTester()
          || item.getType().isSelector(),
      item,
      "arg must be a datatype constructor, selector, or tester");
  return indexOfInternal(item);
}

size_t DType::indexOfInternal(Node item)
{
  if (item.getKind() == kind::APPLY_TYPE_ASCRIPTION)
  {
    return indexOf(item[0]);
  }
  else
  {
    Assert(item.hasAttribute(DTypeIndexAttr()));
    return item.getAttribute(DTypeIndexAttr());
  }
}

size_t DType::cindexOf(Node item)
{
  PrettyCheckArgument(
      item.getType().isSelector(), item, "arg must be a datatype selector");
  return cindexOfInternal(item);
}
size_t DType::cindexOfInternal(Node item)
{
  if (item.getKind() == kind::APPLY_TYPE_ASCRIPTION)
  {
    return cindexOf(item[0]);
  }
  else
  {
    Assert(item.hasAttribute(DTypeConsIndexAttr()));
    return item.getAttribute(DTypeConsIndexAttr());
  }
}

void DType::resolve(NodeManager* em,
                    const std::map<std::string, DTypeType>& resolutions,
                    const std::vector<TypeNode>& placeholders,
                    const std::vector<TypeNode>& replacements,
                    const std::vector<SortConstructorType>& paramTypes,
                    const std::vector<DTypeType>& paramReplacements)
{
  PrettyCheckArgument(
      em != NULL, em, "cannot resolve a DType with a NULL expression manager");
  PrettyCheckArgument(!d_resolved, this, "cannot resolve a DTypeNode twice");
  PrettyCheckArgument(resolutions.find(d_name) != resolutions.end(),
                      resolutions,
                      "DType::resolve(): resolutions doesn't contain me!");
  PrettyCheckArgument(placeholders.size() == replacements.size(),
                      placeholders,
                      "placeholders and replacements must be the same size");
  PrettyCheckArgument(paramTypes.size() == paramReplacements.size(),
                      paramTypes,
                      "paramTypes and paramReplacements must be the same size");
  PrettyCheckArgument(getNumConstructors() > 0,
                      *this,
                      "cannot resolve a DTypeNode that has no constructors");
  DTypeType self = (*resolutions.find(d_name)).second;
  PrettyCheckArgument(&self.getDType() == this,
                      resolutions,
                      "DType::resolve(): resolutions doesn't contain me!");
  d_resolved = true;
  size_t index = 0;
  for (std::vector<DTypeConstructor>::iterator i = d_constructors.begin(),
                                               i_end = d_constructors.end();
       i != i_end;
       ++i)
  {
    (*i).resolve(em,
                 self,
                 resolutions,
                 placeholders,
                 replacements,
                 paramTypes,
                 paramReplacements,
                 index);
    (*i).d_constructor.setAttribute(DTypeIndexAttr(), index);
    (*i).d_tester.setAttribute(DTypeIndexAttr(), index++);
  }
  d_self = self;

  d_involvesExt = false;
  d_involvesUt = false;
  for (const_iterator i = begin(); i != end(); ++i)
  {
    if ((*i).involvesExternalType())
    {
      d_involvesExt = true;
    }
    if ((*i).involvesUninterpretedType())
    {
      d_involvesUt = true;
    }
  }

  if (isSygus())
  {
    // all datatype constructors should be sygus and have sygus operators whose
    // free variables are subsets of sygus bound var list.
    std::unordered_set<Node, NodeHashFunction> svs;
    for (const Node& sv : d_sygus_bvl)
    {
      svs.insert(sv);
    }
    for (unsigned i = 0, ncons = d_constructors.size(); i < ncons; i++)
    {
      Node sop = d_constructors[i].getSygusOp();
      PrettyCheckArgument(!sop.isNull(),
                          this,
                          "Sygus datatype contains a non-sygus constructor");
      std::unordered_set<Node, NodeHashFunction> fvs;
      expr::getFreeVariables(sop, fvs);
      for (const Node& v : fvs)
      {
        PrettyCheckArgument(
            svs.find(v) != svs.end(),
            this,
            "Sygus constructor has an operator with a free variable that is "
            "not in the formal argument list of the function-to-synthesize");
      }
    }
  }
}

void DType::addConstructor(const DTypeConstructor& c)
{
  PrettyCheckArgument(
      !d_resolved, this, "cannot add a constructor to a finalized DType");
  d_constructors.push_back(c);
}

void DType::setSygus(TypeNode st, Node bvl, bool allow_const, bool allow_all)
{
  PrettyCheckArgument(
      !d_resolved, this, "cannot set sygus type to a finalized DType");
  d_sygus_type = st;
  d_sygus_bvl = bvl;
  d_sygus_allow_const = allow_const || allow_all;
  d_sygus_allow_all = allow_all;
}

void DType::addSygusConstructor(Node op,
                                const std::string& cname,
                                const std::vector<TypeNode>& cargs,
                                std::shared_ptr<SygusPrintCallbackInternal> spc,
                                int weight)
{
  Debug("dt-sygus") << "--> Add constructor " << cname << " to " << getName()
                    << std::endl;
  Debug("dt-sygus") << "    sygus op : " << op << std::endl;
  // avoid name clashes
  std::stringstream ss;
  ss << getName() << "_" << getNumConstructors() << "_" << cname;
  std::string name = ss.str();
  std::string testerId("is-");
  testerId.append(name);
  unsigned cweight = weight >= 0 ? weight : (cargs.empty() ? 0 : 1);
  DTypeConstructor c(name, testerId, cweight);
  c.setSygus(op, spc);
  for (unsigned j = 0; j < cargs.size(); j++)
  {
    Debug("parser-sygus-debug")
        << "  arg " << j << " : " << cargs[j] << std::endl;
    std::stringstream sname;
    sname << name << "_" << j;
    c.addArg(sname.str(), cargs[j]);
  }
  addConstructor(c);
}

void DType::setTuple()
{
  PrettyCheckArgument(
      !d_resolved, this, "cannot set tuple to a finalized DType");
  d_isTuple = true;
}

Cardinality DType::getCardinality(TypeNode t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && t.getDType() == *this);
  std::vector<TypeNode> processing;
  computeCardinality(t, processing);
  return d_card;
}

Cardinality DType::getCardinality() const
{
  PrettyCheckArgument(!isParametric(),
                      this,
                      "for getCardinality, this datatype cannot be parametric");
  return getCardinality(d_self);
}

Cardinality DType::computeCardinality(TypeNode t,
                                      std::vector<TypeNode>& processing) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  if (std::find(processing.begin(), processing.end(), d_self)
      != processing.end())
  {
    d_card = Cardinality::INTEGERS;
  }
  else
  {
    processing.push_back(d_self);
    Cardinality c = 0;
    for (const_iterator i = begin(), i_end = end(); i != i_end; ++i)
    {
      c += (*i).computeCardinality(t, processing);
    }
    d_card = c;
    processing.pop_back();
  }
  return d_card;
}

bool DType::isRecursiveSingleton(TypeNode t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && t.getDType() == *this);
  if (d_card_rec_singleton.find(t) == d_card_rec_singleton.end())
  {
    if (isCodatatype())
    {
      Assert(d_card_u_assume[t].empty());
      std::vector<TypeNode> processing;
      if (computeCardinalityRecSingleton(t, processing, d_card_u_assume[t]))
      {
        d_card_rec_singleton[t] = 1;
      }
      else
      {
        d_card_rec_singleton[t] = -1;
      }
      if (d_card_rec_singleton[t] == 1)
      {
        Trace("dt-card") << "DType " << getName()
                         << " is recursive singleton, dependent upon "
                         << d_card_u_assume[t].size()
                         << " uninterpreted sorts: " << std::endl;
        for (unsigned i = 0; i < d_card_u_assume[t].size(); i++)
        {
          Trace("dt-card") << "  " << d_card_u_assume[t][i] << std::endl;
        }
        Trace("dt-card") << std::endl;
      }
    }
    else
    {
      d_card_rec_singleton[t] = -1;
    }
  }
  return d_card_rec_singleton[t] == 1;
}

bool DType::isRecursiveSingleton() const
{
  PrettyCheckArgument(
      !isParametric(),
      this,
      "for isRecursiveSingleton, this datatype cannot be parametric");
  return isRecursiveSingleton(d_self);
}

unsigned DType::getNumRecursiveSingletonArgTypes(TypeNode t) const
{
  Assert(d_card_rec_singleton.find(t) != d_card_rec_singleton.end());
  Assert(isRecursiveSingleton(t));
  return d_card_u_assume[t].size();
}

unsigned DType::getNumRecursiveSingletonArgTypes() const
{
  PrettyCheckArgument(!isParametric(),
                      this,
                      "for getNumRecursiveSingletonArgTypes, this datatype "
                      "cannot be parametric");
  return getNumRecursiveSingletonArgTypes(d_self);
}

TypeNode DType::getRecursiveSingletonArgType(TypeNode t, unsigned i) const
{
  Assert(d_card_rec_singleton.find(t) != d_card_rec_singleton.end());
  Assert(isRecursiveSingleton(t));
  return d_card_u_assume[t][i];
}

TypeNode DType::getRecursiveSingletonArgType(unsigned i) const
{
  PrettyCheckArgument(
      !isParametric(),
      this,
      "for getRecursiveSingletonArgType, this datatype cannot be parametric");
  return getRecursiveSingletonArgType(d_self, i);
}

bool DType::computeCardinalityRecSingleton(
    TypeNode t,
    std::vector<TypeNode>& processing,
    std::vector<TypeNode>& u_assume) const
{
  if (std::find(processing.begin(), processing.end(), d_self)
      != processing.end())
  {
    return true;
  }
  if (d_card_rec_singleton[t] == 0)
  {
    // if not yet computed
    if (d_constructors.size() != 1)
    {
      return false;
    }
    bool success = false;
    processing.push_back(d_self);
    for (unsigned i = 0; i < d_constructors[0].getNumArgs(); i++)
    {
      TypeNode tc = d_constructors[0].getArgType(i);
      // if it is an uninterpreted sort, then we depend on it having cardinality
      // one
      if (tc.isSort())
      {
        if (std::find(u_assume.begin(), u_assume.end(), tc) == u_assume.end())
        {
          u_assume.push_back(tc);
        }
        // if it is a datatype, recurse
      }
      else if (tc.isDatatype())
      {
        const DType& dt = tc.getDType();
        if (!dt.computeCardinalityRecSingleton(t, processing, u_assume))
        {
          return false;
        }
        else
        {
          success = true;
        }
        // if it is a builtin type, it must have cardinality one
      }
      else if (!tc.getCardinality().isOne())
      {
        return false;
      }
    }
    processing.pop_back();
    return success;
  }
  else if (d_card_rec_singleton[t] == -1)
  {
    return false;
  }
  for (unsigned i = 0; i < d_card_u_assume[t].size(); i++)
  {
    if (std::find(u_assume.begin(), u_assume.end(), d_card_u_assume[t][i])
        == u_assume.end())
    {
      u_assume.push_back(d_card_u_assume[t][i]);
    }
  }
  return true;
}

bool DType::isFinite(TypeNode t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && t.getDType() == *this);

  // is this already in the cache ?
  if (d_self.getAttribute(DTypeFiniteComputedAttr()))
  {
    return d_self.getAttribute(DTypeFiniteAttr());
  }
  for (const_iterator i = begin(), i_end = end(); i != i_end; ++i)
  {
    if (!(*i).isFinite(t))
    {
      d_self.setAttribute(DTypeFiniteComputedAttr(), true);
      d_self.setAttribute(DTypeFiniteAttr(), false);
      return false;
    }
  }
  d_self.setAttribute(DTypeFiniteComputedAttr(), true);
  d_self.setAttribute(DTypeFiniteAttr(), true);
  return true;
}
bool DType::isFinite() const
{
  PrettyCheckArgument(isResolved() && !isParametric(),
                      this,
                      "this datatype must be resolved and not parametric");
  return isFinite(d_self);
}

bool DType::isInterpretedFinite(TypeNode t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && t.getDType() == *this);
  // is this already in the cache ?
  if (d_self.getAttribute(DTypeUFiniteComputedAttr()))
  {
    return d_self.getAttribute(DTypeUFiniteAttr());
  }
  // start by assuming it is not
  d_self.setAttribute(DTypeUFiniteComputedAttr(), true);
  d_self.setAttribute(DTypeUFiniteAttr(), false);
  for (const_iterator i = begin(), i_end = end(); i != i_end; ++i)
  {
    if (!(*i).isInterpretedFinite(t))
    {
      return false;
    }
  }
  d_self.setAttribute(DTypeUFiniteComputedAttr(), true);
  d_self.setAttribute(DTypeUFiniteAttr(), true);
  return true;
}
bool DType::isInterpretedFinite() const
{
  PrettyCheckArgument(isResolved() && !isParametric(),
                      this,
                      "this datatype must be resolved and not parametric");
  return isInterpretedFinite(d_self);
}

bool DType::isWellFounded() const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  if (d_well_founded == 0)
  {
    std::vector<TypeNode> processing;
    if (computeWellFounded(processing))
    {
      d_well_founded = 1;
    }
    else
    {
      d_well_founded = -1;
    }
  }
  return d_well_founded == 1;
}

bool DType::computeWellFounded(std::vector<TypeNode>& processing) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  if (std::find(processing.begin(), processing.end(), d_self)
      != processing.end())
  {
    return d_isCo;
  }
  else
  {
    processing.push_back(d_self);
    for (const_iterator i = begin(), i_end = end(); i != i_end; ++i)
    {
      if ((*i).computeWellFounded(processing))
      {
        processing.pop_back();
        return true;
      }
      else
      {
        Trace("dt-wf") << "Constructor " << (*i).getName()
                       << " is not well-founded." << std::endl;
      }
    }
    processing.pop_back();
    Trace("dt-wf") << "DType " << getName() << " is not well-founded."
                   << std::endl;
    return false;
  }
}

Node DType::mkGroundTerm(TypeNode t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  return mkGroundTermInternal(t, false);
}

Node DType::mkGroundValue(TypeNode t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  return mkGroundTermInternal(t, true);
}

Node DType::mkGroundTermInternal(TypeNode t, bool isValue) const
{
  Debug("datatypes") << "mkGroundTerm of type " << t
                     << ", isValue = " << isValue << std::endl;
  // is this already in the cache ?
  std::map<TypeNode, Node>& cache = isValue ? d_ground_value : d_ground_term;
  std::map<TypeNode, Node>::iterator it = cache.find(t);
  if (it != cache.end())
  {
    Debug("datatypes") << "\nin cache: " << d_self << " => " << it->second
                       << std::endl;
    return it->second;
  }
  std::vector<TypeNode> processing;
  Node groundTerm = computeGroundTerm(t, processing, isValue);
  if (!groundTerm.isNull())
  {
    // we found a ground-term-constructing constructor!
    cache[t] = groundTerm;
    Debug("datatypes") << "constructed: " << getName() << " => " << groundTerm
                       << std::endl;
  }
  if (groundTerm.isNull())
  {
    if (!d_isCo)
    {
      // if we get all the way here, we aren't well-founded
      IllegalArgument(
          *this,
          "datatype is not well-founded, cannot construct a ground term!");
    }
  }
  return groundTerm;
}

Node getSubtermWithType(Node e, TypeNode t, bool isTop)
{
  if (!isTop && e.getType() == t)
  {
    return e;
  }
  else
  {
    for (unsigned i = 0; i < e.getNumChildren(); i++)
    {
      Node se = getSubtermWithType(e[i], t, false);
      if (!se.isNull())
      {
        return se;
      }
    }
    return Node();
  }
}

Node DType::computeGroundTerm(TypeNode t,
                              std::vector<TypeNode>& processing,
                              bool isValue) const
{
  if (std::find(processing.begin(), processing.end(), t) == processing.end())
  {
    processing.push_back(t);
    for (unsigned r = 0; r < 2; r++)
    {
      for (const_iterator i = begin(), i_end = end(); i != i_end; ++i)
      {
        // do nullary constructors first
        if (((*i).getNumArgs() == 0) == (r == 0))
        {
          Debug("datatypes")
              << "Try constructing for " << (*i).getName()
              << ", processing = " << processing.size() << std::endl;
          Node e =
              (*i).computeGroundTerm(t, processing, d_ground_term, isValue);
          if (!e.isNull())
          {
            // must check subterms for the same type to avoid infinite loops in
            // type enumeration
            Node se = getSubtermWithType(e, t, true);
            if (!se.isNull())
            {
              Debug("datatypes") << "Take subterm " << se << std::endl;
              e = se;
            }
            processing.pop_back();
            return e;
          }
          else
          {
            Debug("datatypes") << "...failed." << std::endl;
          }
        }
      }
    }
    processing.pop_back();
  }
  else
  {
    Debug("datatypes") << "...already processing " << t << " " << d_self
                       << std::endl;
  }
  return Node();
}

DTypeType DType::getDTypeType() const
{
  PrettyCheckArgument(
      isResolved(), *this, "DType must be resolved to get its DTypeType");
  PrettyCheckArgument(!d_self.isNull(), *this);
  return DTypeType(d_self);
}

DTypeType DType::getDTypeType(const std::vector<TypeNode>& params) const
{
  PrettyCheckArgument(
      isResolved(), *this, "DType must be resolved to get its DTypeType");
  PrettyCheckArgument(!d_self.isNull() && DTypeType(d_self).isParametric(),
                      this);
  return DTypeType(d_self).instantiate(params);
}

bool DType::operator==(const DType& other) const
{
  // two datatypes are == iff the name is the same and they have
  // exactly matching constructors (in the same order)

  if (this == &other)
  {
    return true;
  }

  if (isResolved() != other.isResolved())
  {
    return false;
  }

  if (d_name != other.d_name
      || getNumConstructors() != other.getNumConstructors())
  {
    return false;
  }
  for (const_iterator i = begin(), j = other.begin(); i != end(); ++i, ++j)
  {
    Assert(j != other.end());
    // two constructors are == iff they have the same name, their
    // constructors and testers are equal and they have exactly
    // matching args (in the same order)
    if ((*i).getName() != (*j).getName()
        || (*i).getNumArgs() != (*j).getNumArgs())
    {
      return false;
    }
    // testing equivalence of constructors and testers is harder b/c
    // this constructor might not be resolved yet; only compare them
    // if they are both resolved
    Assert(isResolved() == !(*i).d_constructor.isNull()
           && isResolved() == !(*i).d_tester.isNull()
           && (*i).d_constructor.isNull() == (*j).d_constructor.isNull()
           && (*i).d_tester.isNull() == (*j).d_tester.isNull());
    if (!(*i).d_constructor.isNull()
        && (*i).d_constructor != (*j).d_constructor)
    {
      return false;
    }
    if (!(*i).d_tester.isNull() && (*i).d_tester != (*j).d_tester)
    {
      return false;
    }
    for (DTypeConstructor::const_iterator k = (*i).begin(), l = (*j).begin();
         k != (*i).end();
         ++k, ++l)
    {
      Assert(l != (*j).end());
      if ((*k).getName() != (*l).getName())
      {
        return false;
      }
      // testing equivalence of selectors is harder b/c args might not
      // be resolved yet
      Assert(isResolved() == (*k).isResolved()
             && (*k).isResolved() == (*l).isResolved());
      if ((*k).isResolved())
      {
        // both are resolved, so simply compare the selectors directly
        if ((*k).d_selector != (*l).d_selector)
        {
          return false;
        }
      }
      else
      {
        // neither is resolved, so compare their (possibly unresolved)
        // types; we don't know if they'll be resolved the same way,
        // so we can't ever say unresolved types are equal
        if (!(*k).d_selector.isNull() && !(*l).d_selector.isNull())
        {
          if ((*k).d_selector.getType() != (*l).d_selector.getType())
          {
            return false;
          }
        }
        else
        {
          if ((*k).isUnresolvedSelf() && (*l).isUnresolvedSelf())
          {
            // Fine, the selectors are equal if the rest of the
            // enclosing datatypes are equal...
          }
          else
          {
            return false;
          }
        }
      }
    }
  }
  return true;
}

const DTypeConstructor& DType::operator[](size_t index) const
{
  PrettyCheckArgument(
      index < getNumConstructors(), index, "index out of bounds");
  return d_constructors[index];
}

const DTypeConstructor& DType::operator[](std::string name) const
{
  for (const_iterator i = begin(); i != end(); ++i)
  {
    if ((*i).getName() == name)
    {
      return *i;
    }
  }
  IllegalArgument(name,
                  "No such constructor `%s' of datatype `%s'",
                  name.c_str(),
                  d_name.c_str());
}

Node DType::getSharedSelector(Type dtt, TypeNode t, unsigned index) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  std::map<Type, std::map<Type, std::map<unsigned, Node> > >::iterator itd =
      d_shared_sel.find(dtt);
  if (itd != d_shared_sel.end())
  {
    std::map<Type, std::map<unsigned, Node> >::iterator its =
        itd->second.find(t);
    if (its != itd->second.end())
    {
      std::map<unsigned, Node>::iterator it = its->second.find(index);
      if (it != its->second.end())
      {
        return it->second;
      }
    }
  }
  // make the shared selector
  Node s;
  NodeManager* nm = NodeManager::fromNodeManager(d_self.getNodeManager());
  std::stringstream ss;
  ss << "sel_" << index;
  s = nm->mkSkolem(ss.str(),
                   nm->mkSelectorType(dtt, t),
                   "is a shared selector",
                   NodeManager::SKOLEM_NO_NOTIFY)
          .toNode();
  d_shared_sel[dtt][t][index] = s;
  Trace("dt-shared-sel") << "Made " << s << " of type " << dtt << " -> " << t
                         << std::endl;
  return s;
}

Node DType::getConstructor(std::string name) const
{
  return (*this)[name].getConstructor();
}

Type DType::getSygusType() const { return d_sygus_type; }

Node DType::getSygusVarList() const { return d_sygus_bvl; }

bool DType::getSygusAllowConst() const { return d_sygus_allow_const; }

bool DType::getSygusAllowAll() const { return d_sygus_allow_all; }

bool DType::involvesExternalType() const { return d_involvesExt; }

bool DType::involvesUninterpretedType() const { return d_involvesUt; }

const std::vector<DTypeConstructor>* DType::getConstructors() const
{
  return &d_constructors;
}

void DTypeConstructor::resolve(
    NodeManager* em,
    DTypeType self,
    const std::map<std::string, DTypeType>& resolutions,
    const std::vector<TypeNode>& placeholders,
    const std::vector<TypeNode>& replacements,
    const std::vector<SortConstructorType>& paramTypes,
    const std::vector<DTypeType>& paramReplacements,
    size_t cindex)
{
  PrettyCheckArgument(
      em != NULL, em, "cannot resolve a DType with a NULL expression manager");
  PrettyCheckArgument(!isResolved(),
                      "cannot resolve a DType constructor twice; "
                      "perhaps the same constructor was added twice, "
                      "or to two datatypes?");

  NodeManager* nm = NodeManager::fromNodeManager(em);
  size_t index = 0;
  for (std::vector<DTypeConstructorArg>::iterator i = d_args.begin(),
                                                  i_end = d_args.end();
       i != i_end;
       ++i)
  {
    if ((*i).d_selector.isNull())
    {
      // the unresolved type wasn't created here; do name resolution
      string typeName = (*i).d_name.substr((*i).d_name.find('\0') + 1);
      (*i).d_name.resize((*i).d_name.find('\0'));
      if (typeName == "")
      {
        (*i).d_selector = nm->mkSkolem((*i).d_name,
                                       nm->mkSelectorType(self, self),
                                       "is a selector",
                                       NodeManager::SKOLEM_EXACT_NAME
                                           | NodeManager::SKOLEM_NO_NOTIFY)
                              .toNode();
      }
      else
      {
        map<string, DTypeType>::const_iterator j = resolutions.find(typeName);
        if (j == resolutions.end())
        {
          stringstream msg;
          msg << "cannot resolve type \"" << typeName << "\" "
              << "in selector \"" << (*i).d_name << "\" "
              << "of constructor \"" << d_name << "\"";
          throw DTypeResolutionException(msg.str());
        }
        else
        {
          (*i).d_selector = nm->mkSkolem((*i).d_name,
                                         nm->mkSelectorType(self, (*j).second),
                                         "is a selector",
                                         NodeManager::SKOLEM_EXACT_NAME
                                             | NodeManager::SKOLEM_NO_NOTIFY)
                                .toNode();
        }
      }
    }
    else
    {
      // the type for the selector already exists; may need
      // complex-type substitution
      Type range = (*i).d_selector.getType();
      if (!placeholders.empty())
      {
        range = range.substitute(placeholders, replacements);
      }
      if (!paramTypes.empty())
      {
        range = doParametricSubstitution(range, paramTypes, paramReplacements);
      }
      (*i).d_selector = nm->mkSkolem((*i).d_name,
                                     nm->mkSelectorType(self, range),
                                     "is a selector",
                                     NodeManager::SKOLEM_EXACT_NAME
                                         | NodeManager::SKOLEM_NO_NOTIFY)
                            .toNode();
    }
    (*i).d_selector.setAttribute(DTypeConsIndexAttr(), cindex);
    (*i).d_selector.setAttribute(DTypeIndexAttr(), index++);
    (*i).d_resolved = true;
  }

  Assert(index == getNumArgs());

  // Set constructor/tester last, since DTypeConstructor::isResolved()
  // returns true when d_tester is not the null Node.  If something
  // fails above, we want Constuctor::isResolved() to remain "false".
  // Further, mkConstructorType() iterates over the selectors, so
  // should get the results of any resolutions we did above.
  d_tester = nm->mkSkolem(getTesterName(),
                          nm->mkTesterType(selfTypeNode),
                          "is a tester",
                          NodeManager::SKOLEM_EXACT_NAME
                              | NodeManager::SKOLEM_NO_NOTIFY)
                 .toNode();
  d_constructor = nm->mkSkolem(getName(),
                               nm->mkConstructorType(*this, selfTypeNode),
                               "is a constructor",
                               NodeManager::SKOLEM_EXACT_NAME
                                   | NodeManager::SKOLEM_NO_NOTIFY)
                      .toNode();
  // associate constructor with all selectors
  for (std::vector<DTypeConstructorArg>::iterator i = d_args.begin(),
                                                  i_end = d_args.end();
       i != i_end;
       ++i)
  {
    (*i).d_constructor = d_constructor;
  }
}

Type DTypeConstructor::doParametricSubstitution(
    Type range,
    const std::vector<SortConstructorType>& paramTypes,
    const std::vector<DTypeType>& paramReplacements)
{
  if (range.getNumChildren() == 0)
  {
    return range;
  }
  else
  {
    std::vector<TypeNode> origChildren;
    std::vector<TypeNode> children;
    for (TypeNode::const_iterator i = range.begin(), iend = range.end();
         i != iend;
         ++i)
    {
      origChildren.push_back((*i));
      children.push_back(
          doParametricSubstitution((*i), paramTypes, paramReplacements));
    }
    for (unsigned i = 0; i < paramTypes.size(); ++i)
    {
      if (paramTypes[i].getArity() == origChildren.size())
      {
        TypeNode tn = paramTypes[i].instantiate(origChildren);
        if (range == tn)
        {
          return paramReplacements[i].instantiate(children);
        }
      }
    }
    NodeBuilder<> nb(range.getKind());
    for (unsigned i = 0; i < children.size(); ++i)
    {
      nb << children[i];
    }
    return nb.constructTypeNode();
  }
}

DTypeConstructor::DTypeConstructor(std::string name)
    :  // We don't want to introduce a new data member, because eventually
       // we're going to be a constant stuffed inside a node.  So we stow
       // the tester name away inside the constructor name until
       // resolution.
      d_name(name + '\0' + "is_" + name),  // default tester name is "is_FOO"
      d_tester(),
      d_args(),
      d_sygus_pc(nullptr),
      d_weight(1)
{
  PrettyCheckArgument(name != "",
                      name,
                      "cannot construct a datatype constructor without a name");
}

DTypeConstructor::DTypeConstructor(std::string name,
                                   std::string tester,
                                   unsigned weight)
    :  // We don't want to introduce a new data member, because eventually
       // we're going to be a constant stuffed inside a node.  So we stow
       // the tester name away inside the constructor name until
       // resolution.
      d_name(name + '\0' + tester),
      d_tester(),
      d_args(),
      d_sygus_pc(nullptr),
      d_weight(weight)
{
  PrettyCheckArgument(name != "",
                      name,
                      "cannot construct a datatype constructor without a name");
  PrettyCheckArgument(
      !tester.empty(),
      tester,
      "cannot construct a datatype constructor without a tester");
}

void DTypeConstructor::setSygus(Node op,
                                std::shared_ptr<SygusPrintCallbackInternal> spc)
{
  PrettyCheckArgument(
      !isResolved(), this, "cannot modify a finalized DType constructor");
  d_sygus_op = op;
  d_sygus_pc = spc;
}

const std::vector<DTypeConstructorArg>* DTypeConstructor::getArgs() const
{
  return &d_args;
}

void DTypeConstructor::addArg(std::string selectorName, Type selectorType)
{
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away inside a var until resolution (when we can
  // create the proper selector type)
  PrettyCheckArgument(
      !isResolved(), this, "cannot modify a finalized DType constructor");
  PrettyCheckArgument(
      !selectorType.isNull(), selectorType, "cannot add a null selector type");

  Node type = NodeManager::currentNM()
                  ->mkSkolem("unresolved_" + selectorName,
                             selectorType,
                             "is an unresolved selector type placeholder",
                             NodeManager::SKOLEM_EXACT_NAME
                                 | NodeManager::SKOLEM_NO_NOTIFY)
                  .toNode();
  Debug("datatypes") << type << endl;
  d_args.push_back(DTypeConstructorArg(selectorName, type));
}

void DTypeConstructor::addArg(std::string selectorName,
                              DTypeUnresolvedType selectorType)
{
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away after a NUL in the name string until
  // resolution (when we can create the proper selector type)
  PrettyCheckArgument(
      !isResolved(), this, "cannot modify a finalized DType constructor");
  PrettyCheckArgument(selectorType.getName() != "",
                      selectorType,
                      "cannot add a null selector type");
  d_args.push_back(DTypeConstructorArg(
      selectorName + '\0' + selectorType.getName(), Node()));
}

void DTypeConstructor::addArg(std::string selectorName, DTypeSelfType)
{
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we mark
  // the name string with a NUL to indicate that we have a
  // self-selecting selector until resolution (when we can create the
  // proper selector type)
  PrettyCheckArgument(
      !isResolved(), this, "cannot modify a finalized DType constructor");
  d_args.push_back(DTypeConstructorArg(selectorName + '\0', Node()));
}

std::string DTypeConstructor::getName() const
{
  return d_name.substr(0, d_name.find('\0'));
}

std::string DTypeConstructor::getTesterName() const
{
  return d_name.substr(d_name.find('\0') + 1);
}

Node DTypeConstructor::getConstructor() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return d_constructor;
}

Type DTypeConstructor::getSpecializedConstructorType(Type returnType) const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  PrettyCheckArgument(
      returnType.isDatatype(),
      this,
      "cannot get specialized constructor type for non-datatype type");
  const DType& dt = DType::datatypeOf(d_constructor);
  PrettyCheckArgument(
      dt.isParametric(), this, "this datatype constructor is not parametric");
  DTypeType dtt = dt.getDTypeType();
  Matcher m(dtt);
  m.doMatching(dtt, returnType);
  std::vector<TypeNode> subst;
  m.getMatches(subst);
  std::vector<TypeNode> params = dt.getParameters();
  return d_constructor.getType().substitute(params, subst);
}

Node DTypeConstructor::getTester() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return d_tester;
}

Node DTypeConstructor::getSygusOp() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return d_sygus_op;
}

bool DTypeConstructor::isSygusIdFunc() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return (d_sygus_op.getKind() == kind::LAMBDA
          && d_sygus_op[0].getNumChildren() == 1
          && d_sygus_op[0][0] == d_sygus_op[1]);
}

unsigned DTypeConstructor::getWeight() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return d_weight;
}

std::shared_ptr<SygusPrintCallbackInternal>
DTypeConstructor::getSygusPrintCallbackInternal() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return d_sygus_pc;
}

Cardinality DTypeConstructor::getCardinality(TypeNode t) const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");

  Cardinality c = 1;

  for (unsigned i = 0, nargs = d_args.size(); i < nargs; i++)
  {
    c *= getArgType(i).getCardinality();
  }

  return c;
}

/** compute the cardinality of this datatype */
Cardinality DTypeConstructor::computeCardinality(
    TypeNode t, std::vector<TypeNode>& processing) const
{
  Cardinality c = 1;
  std::vector<TypeNode> instTypes;
  std::vector<TypeNode> paramTypes;
  bool isParam = t.isParametricDatatype();
  if (isParam)
  {
    paramTypes = t.getDType().getParameters();
    instTypes = t.getParamTypes();
  }
  for (unsigned i = 0, nargs = d_args.size(); i < nargs; i++)
  {
    TypeNode tc = getArgType(i);
    if (isParam)
    {
      tc = tc.substitute(paramTypes, instTypes);
    }
    if (tc.isDatatype())
    {
      const DType& dt = tc.getDType();
      c *= dt.computeCardinality(t, processing);
    }
    else
    {
      c *= tc.getCardinality();
    }
  }
  return c;
}

bool DTypeConstructor::computeWellFounded(
    std::vector<TypeNode>& processing) const
{
  for (const_iterator i = begin(), i_end = end(); i != i_end; ++i)
  {
    TypeNode t = SelectorType((*i).getSelector().getType()).getRangeType();
    if (t.isDatatype())
    {
      const DType& dt = t.getDType();
      if (!dt.computeWellFounded(processing))
      {
        return false;
      }
    }
  }
  return true;
}

bool DTypeConstructor::isFinite(TypeNode t) const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");

  TNode self = d_constructor;
  // is this already in the cache ?
  if (self.getAttribute(DTypeFiniteComputedAttr()))
  {
    return self.getAttribute(DTypeFiniteAttr());
  }
  std::vector<TypeNode> instTypes;
  std::vector<TypeNode> paramTypes;
  bool isParam = t.isParametricDatatype();
  if (isParam)
  {
    paramTypes = t.getDType().getParameters();
    instTypes = DTypeType(t).getParamTypes();
  }
  for (const_iterator i = begin(), i_end = end(); i != i_end; ++i)
  {
    TypeNode tc = (*i).getRangeType();
    if (isParam)
    {
      tc = tc.substitute(paramTypes, instTypes);
    }
    if (!tc.isFinite())
    {
      self.setAttribute(DTypeFiniteComputedAttr(), true);
      self.setAttribute(DTypeFiniteAttr(), false);
      return false;
    }
  }
  self.setAttribute(DTypeFiniteComputedAttr(), true);
  self.setAttribute(DTypeFiniteAttr(), true);
  return true;
}

bool DTypeConstructor::isInterpretedFinite(TypeNode t) const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  TNode self = d_constructor;
  // is this already in the cache ?
  if (self.getAttribute(DTypeUFiniteComputedAttr()))
  {
    return self.getAttribute(DTypeUFiniteAttr());
  }
  std::vector<TypeNode> instTypes;
  std::vector<TypeNode> paramTypes;
  bool isParam = t.isParametricDatatype();
  if (isParam)
  {
    paramTypes = t.getDType().getParameters();
    instTypes = DTypeType(t).getParamTypes();
  }
  for (const_iterator i = begin(), i_end = end(); i != i_end; ++i)
  {
    TypeNode tc = (*i).getRangeType();
    if (isParam)
    {
      tc = tc.substitute(paramTypes, instTypes);
    }
    if (!tc.isInterpretedFinite())
    {
      self.setAttribute(DTypeUFiniteComputedAttr(), true);
      self.setAttribute(DTypeUFiniteAttr(), false);
      return false;
    }
  }
  self.setAttribute(DTypeUFiniteComputedAttr(), true);
  self.setAttribute(DTypeUFiniteAttr(), true);
  return true;
}

Node DTypeConstructor::computeGroundTerm(TypeNode t,
                                         std::vector<TypeNode>& processing,
                                         std::map<TypeNode, Node>& gt,
                                         bool isValue) const
{
  std::vector<Node> groundTerms;
  groundTerms.push_back(getConstructor());

  // for each selector, get a ground term
  std::vector<TypeNode> instTypes;
  std::vector<TypeNode> paramTypes;
  bool isParam = t.isParametricDatatype();
  if (isParam)
  {
    paramTypes = t.getDType().getParameters();
    instTypes = DTypeType(t).getParamTypes();
  }
  for (const_iterator i = begin(), i_end = end(); i != i_end; ++i)
  {
    Type selType = SelectorType((*i).getSelector().getType()).getRangeType();
    if (isParam)
    {
      selType = selType.substitute(paramTypes, instTypes);
    }
    Node arg;
    if (selType.isDatatype())
    {
      std::map<Type, Node>::iterator itgt = gt.find(selType);
      if (itgt != gt.end())
      {
        arg = itgt->second;
      }
      else
      {
        const DType& dt = selType.getDType();
        arg = dt.computeGroundTerm(selType, processing, isValue);
      }
    }
    else
    {
      // call mkGroundValue or mkGroundTerm based on isValue
      arg = isValue ? selType.mkGroundValue() : selType.mkGroundTerm();
    }
    if (arg.isNull())
    {
      Debug("datatypes") << "...unable to construct arg of " << (*i).getName()
                         << std::endl;
      return Node();
    }
    else
    {
      Debug("datatypes") << "...constructed arg " << arg.getType() << std::endl;
      groundTerms.push_back(arg);
    }
  }

  Node groundTerm = getConstructor().getNodeManager()->mkNode(
      kind::APPLY_CONSTRUCTOR, groundTerms);
  if (isParam)
  {
    Assert(DType::datatypeOf(d_constructor).isParametric());
    // type is parametric, must apply type ascription
    Debug("datatypes-gt") << "ambiguous type for " << groundTerm
                          << ", ascribe to " << t << std::endl;
    groundTerms[0] = getConstructor().getNodeManager()->mkNode(
        kind::APPLY_TYPE_ASCRIPTION,
        getConstructor().getNodeManager()->mkConst(
            AscriptionType(getSpecializedConstructorType(t))),
        groundTerms[0]);
    groundTerm = getConstructor().getNodeManager()->mkNode(
        kind::APPLY_CONSTRUCTOR, groundTerms);
  }
  return groundTerm;
}

void DTypeConstructor::computeSharedSelectors(Type domainType) const
{
  if (d_shared_selectors[domainType].size() < getNumArgs())
  {
    TypeNode ctype;
    if (domainType.isParametricDatatype())
    {
      ctype = getSpecializedConstructorType(domainType);
    }
    else
    {
      ctype = d_constructor.getType();
    }
    Assert(ctype.isConstructor());
    Assert(ctype.getNumChildren() - 1 == getNumArgs());
    // compute the shared selectors
    const DType& dt = DType::datatypeOf(d_constructor);
    std::map<TypeNode, unsigned> counter;
    for (unsigned j = 0; j < ctype.getNumChildren() - 1; j++)
    {
      TypeNode t = ctype[j];
      Node ss = dt.getSharedSelector(domainType, t, counter[t]);
      d_shared_selectors[domainType].push_back(ss);
      Assert(d_shared_selector_index[domainType].find(ss)
             == d_shared_selector_index[domainType].end());
      d_shared_selector_index[domainType][ss] = j;
      counter[t]++;
    }
  }
}

const DTypeConstructorArg& DTypeConstructor::operator[](size_t index) const
{
  PrettyCheckArgument(index < getNumArgs(), index, "index out of bounds");
  return d_args[index];
}

const DTypeConstructorArg& DTypeConstructor::operator[](std::string name) const
{
  for (const_iterator i = begin(); i != end(); ++i)
  {
    if ((*i).getName() == name)
    {
      return *i;
    }
  }
  IllegalArgument(name,
                  "No such arg `%s' of constructor `%s'",
                  name.c_str(),
                  d_name.c_str());
}

Node DTypeConstructor::getSelector(std::string name) const
{
  return (*this)[name].getSelector();
}

Type DTypeConstructor::getArgType(unsigned index) const
{
  PrettyCheckArgument(index < getNumArgs(), index, "index out of bounds");
  return static_cast<SelectorType>((*this)[index].getType()).getRangeType();
}

bool DTypeConstructor::involvesExternalType() const
{
  for (const_iterator i = begin(); i != end(); ++i)
  {
    if (!SelectorType((*i).getSelector().getType()).getRangeType().isDatatype())
    {
      return true;
    }
  }
  return false;
}

bool DTypeConstructor::involvesUninterpretedType() const
{
  for (const_iterator i = begin(); i != end(); ++i)
  {
    if (SelectorType((*i).getSelector().getType()).getRangeType().isSort())
    {
      return true;
    }
  }
  return false;
}

DTypeConstructorArg::DTypeConstructorArg(std::string name, Node selector)
    : d_name(name), d_selector(selector), d_resolved(false)
{
  PrettyCheckArgument(
      name != "",
      name,
      "cannot construct a datatype constructor arg without a name");
}

std::string DTypeConstructorArg::getName() const
{
  string name = d_name;
  const size_t nul = name.find('\0');
  if (nul != string::npos)
  {
    name.resize(nul);
  }
  return name;
}

Node DTypeConstructorArg::getSelector() const
{
  PrettyCheckArgument(
      isResolved(),
      this,
      "cannot get a selector for an unresolved datatype constructor");
  return d_selector;
}

Node DTypeConstructor::getSelectorInternal(Type domainType, size_t index) const
{
  PrettyCheckArgument(
      isResolved(),
      this,
      "cannot get an internal selector for an unresolved datatype constructor");
  PrettyCheckArgument(index < getNumArgs(), index, "index out of bounds");
  if (options::dtSharedSelectors())
  {
    computeSharedSelectors(domainType);
    Assert(d_shared_selectors[domainType].size() == getNumArgs());
    return d_shared_selectors[domainType][index];
  }
  else
  {
    return d_args[index].getSelector();
  }
}

int DTypeConstructor::getSelectorIndexInternal(Node sel) const
{
  PrettyCheckArgument(isResolved(),
                      this,
                      "cannot get an internal selector index for an unresolved "
                      "datatype constructor");
  if (options::dtSharedSelectors())
  {
    Assert(sel.getType().isSelector());
    TypeNode domainType = ((SelectorType)sel.getType()).getDomain();
    computeSharedSelectors(domainType);
    std::map<Node, unsigned>::iterator its =
        d_shared_selector_index[domainType].find(sel);
    if (its != d_shared_selector_index[domainType].end())
    {
      return (int)its->second;
    }
  }
  else
  {
    unsigned sindex = DType::indexOf(sel);
    if (getNumArgs() > sindex && d_args[sindex].getSelector() == sel)
    {
      return (int)sindex;
    }
  }
  return -1;
}

Node DTypeConstructorArg::getConstructor() const
{
  PrettyCheckArgument(isResolved(),
                      this,
                      "cannot get a associated constructor for argument of an "
                      "unresolved datatype constructor");
  return d_constructor;
}

TypeNode DTypeConstructorArg::getType() const
{
  return getSelector().getType();
}

TypeNode DTypeConstructorArg::getRangeType() const
{
  return getType().getRangeType();
}

bool DTypeConstructorArg::isUnresolvedSelf() const
{
  return d_selector.isNull() && d_name.size() == d_name.find('\0') + 1;
}

std::ostream& operator<<(std::ostream& os, const DType& dt)
{
  // can only output datatypes in the CVC4 native language
  language::SetLanguage::Scope ls(os, language::output::LANG_CVC4);
  dt.toStream(os);
  return os;
}

void DType::toStream(std::ostream& out) const
{
  out << "DATATYPE " << getName();
  if (isParametric())
  {
    out << '[';
    for (size_t i = 0; i < getNumParameters(); ++i)
    {
      if (i > 0)
      {
        out << ',';
      }
      out << getParameter(i);
    }
    out << ']';
  }
  out << " =" << endl;
  DType::const_iterator i = begin(), i_end = end();
  if (i != i_end)
  {
    out << "  ";
    do
    {
      out << *i << endl;
      if (++i != i_end)
      {
        out << "| ";
      }
    } while (i != i_end);
  }
  out << "END;" << endl;
}

std::ostream& operator<<(std::ostream& os, const DTypeConstructor& ctor)
{
  // can only output datatypes in the CVC4 native language
  language::SetLanguage::Scope ls(os, language::output::LANG_CVC4);
  ctor.toStream(os);
  return os;
}

void DTypeConstructor::toStream(std::ostream& out) const
{
  out << getName();

  DTypeConstructor::const_iterator i = begin(), i_end = end();
  if (i != i_end)
  {
    out << "(";
    do
    {
      out << *i;
      if (++i != i_end)
      {
        out << ", ";
      }
    } while (i != i_end);
    out << ")";
  }
}

std::ostream& operator<<(std::ostream& os, const DTypeConstructorArg& arg)
{
  // can only output datatypes in the CVC4 native language
  language::SetLanguage::Scope ls(os, language::output::LANG_CVC4);
  arg.toStream(os);
  return os;
}

void DTypeConstructorArg::toStream(std::ostream& out) const
{
  out << getName() << ": ";

  TypeNode t;
  if (isResolved())
  {
    t = getRangeType();
  }
  else if (d_selector.isNull())
  {
    string typeName = d_name.substr(d_name.find('\0') + 1);
    out << ((typeName == "") ? "[self]" : typeName);
    return;
  }
  else
  {
    t = d_selector.getType();
  }
  out << t;
}

DTypeIndexConstant::DTypeIndexConstant(unsigned index) : d_index(index) {}
std::ostream& operator<<(std::ostream& out, const DTypeIndexConstant& dic)
{
  return out << "index_" << dic.getIndex();
}

}  // namespace CVC4

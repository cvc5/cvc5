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

#include "expr/node_algorithm.h"
#include "theory/datatypes/theory_datatypes_utils.h"

using namespace CVC4::kind;

namespace CVC4 {

DType::DType(std::string name, bool isCo)
    : d_name(name),
      d_params(),
      d_isCo(isCo),
      d_isTuple(false),
      d_constructors(),
      d_resolved(false),
      d_self(),
      d_involvesExt(false),
      d_involvesUt(false),
      d_sygus_allow_const(false),
      d_sygus_allow_all(false),
      d_card(CardinalityUnknown()),
      d_well_founded(0)
{
}

DType::DType(std::string name, const std::vector<TypeNode>& params, bool isCo)
    : d_name(name),
      d_params(params),
      d_isCo(isCo),
      d_isTuple(false),
      d_constructors(),
      d_resolved(false),
      d_self(),
      d_involvesExt(false),
      d_involvesUt(false),
      d_sygus_allow_const(false),
      d_sygus_allow_all(false),
      d_card(CardinalityUnknown()),
      d_well_founded(0)
{
}

std::string DType::getName() const { return d_name; }
size_t DType::getNumConstructors() const { return d_constructors.size(); }

bool DType::isParametric() const { return d_params.size() > 0; }
size_t DType::getNumParameters() const { return d_params.size(); }
TypeNode DType::getParameter(unsigned int i) const
{
  CheckArgument(isParametric(),
                this,
                "Cannot get type parameter of a non-parametric datatype.");
  CheckArgument(i < d_params.size(),
                i,
                "Type parameter index out of range for datatype.");
  return d_params[i];
}

std::vector<TypeNode> DType::getParameters() const
{
  CheckArgument(isParametric(),
                this,
                "Cannot get type parameters of a non-parametric datatype.");
  return d_params;
}

bool DType::isCodatatype() const { return d_isCo; }

bool DType::isSygus() const { return !d_sygus_type.isNull(); }

bool DType::isTuple() const { return d_isTuple; }

bool DType::isResolved() const { return d_resolved; }

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

void DType::resolve(const std::map<std::string, TypeNode>& resolutions,
                    const std::vector<TypeNode>& placeholders,
                    const std::vector<TypeNode>& replacements,
                    const std::vector<TypeNode>& paramTypes,
                    const std::vector<TypeNode>& paramReplacements)
{
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
  TypeNode self = (*resolutions.find(d_name)).second;
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
    (*i).resolve(self,
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
  for (const DTypeConstructor& ctor : d_constructors)
  {
    if (ctor.involvesExternalType())
    {
      d_involvesExt = true;
    }
    if (ctor.involvesUninterpretedType())
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
  Assert(t.isDatatype() && t.getDType().getTypeNode() == d_self);
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
    for (const DTypeConstructor& ctor : d_constructors)
    {
      c += ctor.computeCardinality(t, processing);
    }
    d_card = c;
    processing.pop_back();
  }
  return d_card;
}

bool DType::isRecursiveSingleton(TypeNode t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && t.getDType().getTypeNode() == d_self);
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
  Assert(t.isDatatype() && t.getDType().getTypeNode() == d_self);

  // is this already in the cache ?
  if (d_self.getAttribute(DTypeFiniteComputedAttr()))
  {
    return d_self.getAttribute(DTypeFiniteAttr());
  }
  for (const DTypeConstructor& ctor : d_constructors)
  {
    if (!ctor.isFinite(t))
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
  Assert(t.isDatatype() && t.getDType().getTypeNode() == d_self);
  // is this already in the cache ?
  if (d_self.getAttribute(DTypeUFiniteComputedAttr()))
  {
    return d_self.getAttribute(DTypeUFiniteAttr());
  }
  // start by assuming it is not
  d_self.setAttribute(DTypeUFiniteComputedAttr(), true);
  d_self.setAttribute(DTypeUFiniteAttr(), false);
  for (const DTypeConstructor& ctor : d_constructors)
  {
    if (!ctor.isInterpretedFinite(t))
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
    for (const DTypeConstructor& ctor : d_constructors)
    {
      if (ctor.computeWellFounded(processing))
      {
        processing.pop_back();
        return true;
      }
      else
      {
        Trace("dt-wf") << "Constructor " << ctor.getName()
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
      for (const DTypeConstructor& ctor : d_constructors)
      {
        // do nullary constructors first
        if ((ctor.getNumArgs() == 0) == (r == 0))
        {
          Debug("datatypes")
              << "Try constructing for " << ctor.getName()
              << ", processing = " << processing.size() << std::endl;
          Node e =
              ctor.computeGroundTerm(t, processing, d_ground_term, isValue);
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

TypeNode DType::getTypeNode() const
{
  PrettyCheckArgument(
      isResolved(), *this, "DType must be resolved to get its TypeNode");
  PrettyCheckArgument(!d_self.isNull(), *this);
  return d_self;
}

TypeNode DType::getTypeNode(const std::vector<TypeNode>& params) const
{
  PrettyCheckArgument(
      isResolved(), *this, "DType must be resolved to get its TypeNode");
  PrettyCheckArgument(!d_self.isNull() && d_self.isParametricDatatype(), this);
  return d_self.instantiateParametricDatatype(params);
}

const DTypeConstructor& DType::operator[](size_t index) const
{
  PrettyCheckArgument(
      index < getNumConstructors(), index, "index out of bounds");
  return d_constructors[index];
}

const DTypeConstructor& DType::operator[](std::string name) const
{
  for (const DTypeConstructor& ctor : d_constructors)
  {
    if (ctor.getName() == name)
    {
      return ctor;
    }
  }
  IllegalArgument(name,
                  "No such constructor `%s' of datatype `%s'",
                  name.c_str(),
                  d_name.c_str());
}

Node DType::getSharedSelector(TypeNode dtt, TypeNode t, unsigned index) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  std::map<TypeNode, std::map<TypeNode, std::map<unsigned, Node> > >::iterator
      itd = d_shared_sel.find(dtt);
  if (itd != d_shared_sel.end())
  {
    std::map<TypeNode, std::map<unsigned, Node> >::iterator its =
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
  NodeManager* nm = NodeManager::currentNM();
  std::stringstream ss;
  ss << "sel_" << index;
  s = nm->mkSkolem(ss.str(),
                   nm->mkSelectorType(dtt, t),
                   "is a shared selector",
                   NodeManager::SKOLEM_NO_NOTIFY);
  d_shared_sel[dtt][t][index] = s;
  Trace("dt-shared-sel") << "Made " << s << " of type " << dtt << " -> " << t
                         << std::endl;
  return s;
}

Node DType::getConstructor(std::string name) const
{
  return (*this)[name].getConstructor();
}

TypeNode DType::getSygusType() const { return d_sygus_type; }

Node DType::getSygusVarList() const { return d_sygus_bvl; }

bool DType::getSygusAllowConst() const { return d_sygus_allow_const; }

bool DType::getSygusAllowAll() const { return d_sygus_allow_all; }

bool DType::involvesExternalType() const { return d_involvesExt; }

bool DType::involvesUninterpretedType() const { return d_involvesUt; }

const std::vector<DTypeConstructor>* DType::getConstructors() const
{
  return &d_constructors;
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
  out << " = " << std::endl;
  bool firstTime = true;
  for (const DTypeConstructor& ctor : d_constructors)
  {
    if (!firstTime)
    {
      out << " | ";
    }
    firstTime = false;
    out << ctor;
  }
  out << " END;" << std::endl;
}

DTypeIndexConstant::DTypeIndexConstant(unsigned index) : d_index(index) {}
std::ostream& operator<<(std::ostream& out, const DTypeIndexConstant& dic)
{
  return out << "index_" << dic.getIndex();
}

}  // namespace CVC4

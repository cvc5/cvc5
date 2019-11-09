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
#include "theory/datatypes/dtype_cons.h"

#include "expr/node_manager.h"
#include "expr/type_matcher.h"
#include "options/datatypes_options.h"
#include "theory/datatypes/dtype.h"
#include "theory/datatypes/theory_datatypes_utils.h"

using namespace CVC4::kind;

namespace CVC4 {

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
  Trace("ajr-temp") << "DTypeConstructor::DTypeConstructor 1" << std::endl;
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
  Trace("ajr-temp") << "DTypeConstructor::DTypeConstructor 2" << std::endl;
  PrettyCheckArgument(name != "",
                      name,
                      "cannot construct a datatype constructor without a name");
  PrettyCheckArgument(
      !tester.empty(),
      tester,
      "cannot construct a datatype constructor without a tester");
  Trace("ajr-temp") << "DTypeConstructor::DTypeConstructor 2 finished" << std::endl;
}

void DTypeConstructor::addArg(std::string selectorName, TypeNode selectorType)
{
  Trace("ajr-temp") << "DTypeConstructor::addArg" << std::endl;
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away inside a var until resolution (when we can
  // create the proper selector type)
  PrettyCheckArgument(
      !isResolved(), this, "cannot modify a finalized DType constructor");
  PrettyCheckArgument(
      !selectorType.isNull(), selectorType, "cannot add a null selector type");

  Node type = NodeManager::currentNM()->mkSkolem(
      "unresolved_" + selectorName,
      selectorType,
      "is an unresolved selector type placeholder",
      NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY);
  Debug("datatypes") << type << std::endl;
  DTypeConstructorArg * a = new DTypeConstructorArg(selectorName, type);
  addArg(a);
}

void DTypeConstructor::addArg(DTypeConstructorArg* a)
{
  d_args.push_back(a);
}

std::string DTypeConstructor::getName() const
{
  return d_name;
}

Node DTypeConstructor::getConstructor() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return d_constructor;
}

Node DTypeConstructor::getTester() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return d_tester;
}

std::string DTypeConstructor::getTesterName() const
{
  return d_name.substr(d_name.find('\0') + 1);
}

void DTypeConstructor::setSygus(Node op,
                                std::shared_ptr<SygusPrintCallbackInternal> spc)
{
  PrettyCheckArgument(
      !isResolved(), this, "cannot modify a finalized DType constructor");
  d_sygus_op = op;
  d_sygus_pc = spc;
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
  return (d_sygus_op.getKind() == LAMBDA && d_sygus_op[0].getNumChildren() == 1
          && d_sygus_op[0][0] == d_sygus_op[1]);
}

std::shared_ptr<SygusPrintCallbackInternal>
DTypeConstructor::getSygusPrintCallbackInternal() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return d_sygus_pc;
}

unsigned DTypeConstructor::getWeight() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return d_weight;
}

size_t DTypeConstructor::getNumArgs() const { return d_args.size(); }

TypeNode DTypeConstructor::getSpecializedConstructorType(
    TypeNode returnType) const
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
  TypeNode dtt = dt.getTypeNode();
  TypeMatcher m(dtt);
  m.doMatching(dtt, returnType);
  std::vector<TypeNode> subst;
  m.getMatches(subst);
  std::vector<TypeNode> params = dt.getParameters();
  return d_constructor.getType().substitute(
      params.begin(), params.end(), subst.begin(), subst.end());
}

const std::vector<DTypeConstructorArg*>& DTypeConstructor::getArgs() const
{
  return d_args;
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
    instTypes = TypeNode(t).getParamTypes();
  }
  for (unsigned i = 0, nargs = getNumArgs(); i < nargs; i++)
  {
    TypeNode tc = getArgType(i);
    if (isParam)
    {
      tc = tc.substitute(paramTypes.begin(),
                         paramTypes.end(),
                         instTypes.begin(),
                         instTypes.end());
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
    instTypes = TypeNode(t).getParamTypes();
  }
  for (unsigned i = 0, nargs = getNumArgs(); i < nargs; i++)
  {
    TypeNode tc = getArgType(i);
    if (isParam)
    {
      tc = tc.substitute(paramTypes.begin(),
                         paramTypes.end(),
                         instTypes.begin(),
                         instTypes.end());
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

bool DTypeConstructor::isResolved() const { return !d_tester.isNull(); }

const DTypeConstructorArg& DTypeConstructor::operator[](size_t index) const
{
  PrettyCheckArgument(index < getNumArgs(), index, "index out of bounds");
  return *d_args[index];
}

TypeNode DTypeConstructor::getArgType(unsigned index) const
{
  PrettyCheckArgument(index < getNumArgs(), index, "index out of bounds");
  return (*this)[index].getType().getSelectorRangeType();
}

Node DTypeConstructor::getSelectorInternal(TypeNode domainType,
                                           size_t index) const
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
    return d_args[index]->getSelector();
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
    TypeNode domainType = sel.getType().getSelectorDomainType();
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
    if (getNumArgs() > sindex && d_args[sindex]->getSelector() == sel)
    {
      return (int)sindex;
    }
  }
  return -1;
}

bool DTypeConstructor::involvesExternalType() const
{
  for (unsigned i = 0, nargs = getNumArgs(); i < nargs; i++)
  {
    if (!getArgType(i).isDatatype())
    {
      return true;
    }
  }
  return false;
}

bool DTypeConstructor::involvesUninterpretedType() const
{
  for (unsigned i = 0, nargs = getNumArgs(); i < nargs; i++)
  {
    if (!getArgType(i).isSort())
    {
      return true;
    }
  }
  return false;
}

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
      tc = tc.substitute(paramTypes.begin(),
                         paramTypes.end(),
                         instTypes.begin(),
                         instTypes.end());
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
  for (unsigned i = 0, nargs = getNumArgs(); i < nargs; i++)
  {
    TypeNode t = getArgType(i);
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

Node DTypeConstructor::computeGroundTerm(TypeNode t,
                                         std::vector<TypeNode>& processing,
                                         std::map<TypeNode, Node>& gt,
                                         bool isValue) const
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> groundTerms;
  groundTerms.push_back(getConstructor());

  // for each selector, get a ground term
  std::vector<TypeNode> instTypes;
  std::vector<TypeNode> paramTypes;
  bool isParam = t.isParametricDatatype();
  if (isParam)
  {
    paramTypes = t.getDType().getParameters();
    instTypes = TypeNode(t).getParamTypes();
  }
  for (unsigned i = 0, nargs = getNumArgs(); i < nargs; i++)
  {
    TypeNode selType = getArgType(i);
    if (isParam)
    {
      selType = selType.substitute(paramTypes.begin(),
                                   paramTypes.end(),
                                   instTypes.begin(),
                                   instTypes.end());
    }
    Node arg;
    if (selType.isDatatype())
    {
      std::map<TypeNode, Node>::iterator itgt = gt.find(selType);
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
      Debug("datatypes") << "...unable to construct arg of "
                         << d_args[i]->getName() << std::endl;
      return Node();
    }
    else
    {
      Debug("datatypes") << "...constructed arg " << arg.getType() << std::endl;
      groundTerms.push_back(arg);
    }
  }

  Node groundTerm = nm->mkNode(APPLY_CONSTRUCTOR, groundTerms);
  if (isParam)
  {
    Assert(DType::datatypeOf(d_constructor).isParametric());
    // type is parametric, must apply type ascription
    Debug("datatypes-gt") << "ambiguous type for " << groundTerm
                          << ", ascribe to " << t << std::endl;
    groundTerms[0] = nm->mkNode(
        APPLY_TYPE_ASCRIPTION,
        nm->mkConst(AscriptionType(getSpecializedConstructorType(t).toType())),
        groundTerms[0]);
    groundTerm = nm->mkNode(APPLY_CONSTRUCTOR, groundTerms);
  }
  return groundTerm;
}

void DTypeConstructor::computeSharedSelectors(TypeNode domainType) const
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

bool DTypeConstructor::resolve(
    TypeNode self,
    const std::map<std::string, TypeNode>& resolutions,
    const std::vector<TypeNode>& placeholders,
    const std::vector<TypeNode>& replacements,
    const std::vector<TypeNode>& paramTypes,
    const std::vector<TypeNode>& paramReplacements,
    size_t cindex)
{
  Trace("ajr-temp") << "DTypeConstructor::resolve" << std::endl;
  PrettyCheckArgument(!isResolved(),
                      "cannot resolve a DType constructor twice; "
                      "perhaps the same constructor was added twice, "
                      "or to two datatypes?");

  NodeManager* nm = NodeManager::currentNM();
  size_t index = 0;
  for (std::vector<DTypeConstructorArg*>::iterator i = d_args.begin(),
                                                  i_end = d_args.end();
       i != i_end;
       ++i)
  {
    DTypeConstructorArg& arg = **i;
    std::string argName = arg.d_name;
    if (arg.d_selector.isNull())
    {
      // the unresolved type wasn't created here; do name resolution
      std::string typeName = argName.substr(argName.find('\0') + 1);
      argName.resize(argName.find('\0'));
      if (typeName == "")
      {
        arg.d_selector = nm->mkSkolem(
            argName,
            nm->mkSelectorType(self, self),
            "is a selector",
            NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY);
      }
      else
      {
        std::map<std::string, TypeNode>::const_iterator j =
            resolutions.find(typeName);
        if (j == resolutions.end())
        {
          // failed to resolve selector
          return false;
        }
        else
        {
          arg.d_selector = nm->mkSkolem(
              argName,
              nm->mkSelectorType(self, (*j).second),
              "is a selector",
              NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY);
        }
      }
    }
    else
    {
      // the type for the selector already exists; may need
      // complex-type substitution
      TypeNode range = arg.d_selector.getType();
      if (!placeholders.empty())
      {
        range = range.substitute(placeholders.begin(),
                                 placeholders.end(),
                                 replacements.begin(),
                                 replacements.end());
      }
      if (!paramTypes.empty())
      {
        range = doParametricSubstitution(range, paramTypes, paramReplacements);
      }
      arg.d_selector = nm->mkSkolem(
          argName,
          nm->mkSelectorType(self, range),
          "is a selector",
          NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY);
    }
    arg.d_selector.setAttribute(DTypeConsIndexAttr(), cindex);
    arg.d_selector.setAttribute(DTypeIndexAttr(), index++);
    arg.d_resolved = true;
  }

  Assert(index == getNumArgs());

  // Set constructor/tester last, since DTypeConstructor::isResolved()
  // returns true when d_tester is not the null Node.  If something
  // fails above, we want Constuctor::isResolved() to remain "false".
  // Further, mkConstructorType() iterates over the selectors, so
  // should get the results of any resolutions we did above.
  d_tester = nm->mkSkolem(
      getTesterName(),
      nm->mkTesterType(self),
      "is a tester",
      NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY);
  d_constructor = nm->mkSkolem(
      getName(),
      nm->mkConstructorType(*this, self),
      "is a constructor",
      NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY);
  Trace("ajr-temp") << "Type of constructor is " << d_constructor.getType() << std::endl;
  Assert( d_constructor.getType().isConstructor());
  // associate constructor with all selectors
  for (std::vector<DTypeConstructorArg*>::iterator i = d_args.begin(),
                                                  i_end = d_args.end();
       i != i_end;
       ++i)
  {
    (*i)->d_constructor = d_constructor;
  }
  Trace("ajr-temp") << "DTypeConstructor::resolve: " << this << " is resolved?" << std::endl;
  AlwaysAssert(isResolved());
  return true;
}

TypeNode DTypeConstructor::doParametricSubstitution(
    TypeNode range,
    const std::vector<TypeNode>& paramTypes,
    const std::vector<TypeNode>& paramReplacements)
{
  if (range.getNumChildren() == 0)
  {
    return range;
  }
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
    // the arity a parameterized type is the number of its children minus one.
    if (paramTypes[i].getNumChildren() == origChildren.size() + 1)
    {
      TypeNode tn = paramTypes[i].instantiateParametricDatatype(origChildren);
      if (range == tn)
      {
        return paramReplacements[i].instantiateParametricDatatype(children);
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

void DTypeConstructor::toStream(std::ostream& out) const
{
  Trace("ajr-temp") << "DTypeConstructor::toStream" << std::endl;
  out << getName();

  unsigned nargs = getNumArgs();
  if (nargs == 0)
  {
    return;
  }
  out << "(";
  for (unsigned i = 0; i < nargs; i++)
  {
    out << *d_args[i];
    if (i + 1 < nargs)
    {
      out << ", ";
    }
  }
  out << ")";
}

std::ostream& operator<<(std::ostream& os, const DTypeConstructor& ctor)
{
  // can only output datatypes in the CVC4 native language
  language::SetLanguage::Scope ls(os, language::output::LANG_CVC4);
  ctor.toStream(os);
  return os;
}

}  // namespace CVC4

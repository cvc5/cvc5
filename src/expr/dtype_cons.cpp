/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class representing a datatype definition.
 */
#include "expr/dtype_cons.h"

#include "expr/ascription_type.h"
#include "expr/dtype.h"
#include "expr/node_manager.h"
#include "expr/skolem_manager.h"
#include "expr/type_matcher.h"
#include "options/datatypes_options.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {

/** Attribute true for variables that represent any constant */
struct SygusAnyConstAttributeId
{
};
typedef expr::Attribute<SygusAnyConstAttributeId, bool> SygusAnyConstAttribute;

DTypeConstructor::DTypeConstructor(std::string name,
                                   unsigned weight)
    :  // We don't want to introduce a new data member, because eventually
       // we're going to be a constant stuffed inside a node.  So we stow
       // the tester name away inside the constructor name until
       // resolution.
      d_name(name),
      d_tester(),
      d_args(),
      d_weight(weight)
{
  Assert(name != "");
}

void DTypeConstructor::addArg(std::string selectorName, TypeNode rangeType)
{
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away inside a var until resolution (when we can
  // create the proper selector type)
  Assert(!isResolved());
  Assert(!rangeType.isNull());
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  Node sel = sm->mkDummySkolem("unresolved_" + selectorName,
                               rangeType,
                               "is an unresolved selector type placeholder",
                               SkolemManager::SKOLEM_EXACT_NAME);
  // can use null updater for now
  Node nullNode;
  Trace("datatypes") << "DTypeConstructor::addArg: " << sel << std::endl;
  std::shared_ptr<DTypeSelector> a =
      std::make_shared<DTypeSelector>(selectorName, sel, nullNode);
  addArg(a);
}

void DTypeConstructor::addArg(std::shared_ptr<DTypeSelector> a)
{
  d_args.push_back(a);
}

void DTypeConstructor::addArgSelf(std::string selectorName)
{
  Trace("datatypes") << "DTypeConstructor::addArgSelf" << std::endl;
  Node nullNode;
  std::shared_ptr<DTypeSelector> a =
      std::make_shared<DTypeSelector>(selectorName + '\0', nullNode, nullNode);
  addArg(a);
}

const std::string& DTypeConstructor::getName() const { return d_name; }

Node DTypeConstructor::getConstructor() const
{
  Assert(isResolved());
  return d_constructor;
}

Node DTypeConstructor::getInstantiatedConstructor(TypeNode returnType) const
{
  Assert(isResolved());
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(
      kind::APPLY_TYPE_ASCRIPTION,
      nm->mkConst(AscriptionType(getInstantiatedConstructorType(returnType))),
      d_constructor);
}

Node DTypeConstructor::getTester() const
{
  Assert(isResolved());
  return d_tester;
}

void DTypeConstructor::setSygus(Node op)
{
  Assert(!isResolved());
  d_sygusOp = op;
  if (op.getKind() == SKOLEM)
  {
    // check if stands for the "any constant" constructor
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    if (sm->getId(op) == SkolemFunId::SYGUS_ANY_CONSTANT)
    {
      // mark with attribute, which is a faster lookup
      SygusAnyConstAttribute saca;
      op.setAttribute(saca, true);
    }
  }
}

Node DTypeConstructor::getSygusOp() const
{
  Assert(isResolved());
  return d_sygusOp;
}

bool DTypeConstructor::isSygusIdFunc() const
{
  Assert(isResolved());
  Assert(!d_sygusOp.isNull());
  return (d_sygusOp.getKind() == LAMBDA && d_sygusOp[0].getNumChildren() == 1
          && d_sygusOp[0][0] == d_sygusOp[1]);
}

bool DTypeConstructor::isSygusAnyConstant() const
{
  Assert(isResolved());
  Assert(!d_sygusOp.isNull());
  return d_sygusOp.getAttribute(SygusAnyConstAttribute());
}

unsigned DTypeConstructor::getWeight() const
{
  Assert(isResolved());
  return d_weight;
}

size_t DTypeConstructor::getNumArgs() const { return d_args.size(); }

TypeNode DTypeConstructor::getInstantiatedConstructorType(
    TypeNode returnType) const
{
  Assert(isResolved());
  Assert(returnType.isDatatype())
      << "DTypeConstructor::getInstantiatedConstructorType: expected datatype, "
         "got "
      << returnType;
  TypeNode ctn = d_constructor.getType();
  const DType& dt = DType::datatypeOf(d_constructor);
  if (!dt.isParametric())
  {
    // if the datatype is not parametric, then no specialization is needed
    return ctn;
  }
  TypeNode dtt = dt.getTypeNode();
  TypeMatcher m(dtt);
  m.doMatching(dtt, returnType);
  std::vector<TypeNode> subst;
  m.getMatches(subst);
  std::vector<TypeNode> params = dt.getParameters();
  return ctn.substitute(
      params.begin(), params.end(), subst.begin(), subst.end());
}

const std::vector<std::shared_ptr<DTypeSelector> >& DTypeConstructor::getArgs()
    const
{
  return d_args;
}

Cardinality DTypeConstructor::getCardinality(TypeNode t) const
{
  Assert(isResolved());

  Cardinality c = 1;

  for (size_t i = 0, nargs = d_args.size(); i < nargs; i++)
  {
    c *= getArgType(i).getCardinality();
  }

  return c;
}

CardinalityClass DTypeConstructor::getCardinalityClass(TypeNode t) const
{
  std::pair<CardinalityClass, bool> cinfo = computeCardinalityInfo(t);
  return cinfo.first;
}

bool DTypeConstructor::hasFiniteExternalArgType(TypeNode t) const
{
  std::pair<CardinalityClass, bool> cinfo = computeCardinalityInfo(t);
  return cinfo.second;
}

std::pair<CardinalityClass, bool> DTypeConstructor::computeCardinalityInfo(
    TypeNode t) const
{
  std::map<TypeNode, std::pair<CardinalityClass, bool> >::iterator it =
      d_cardInfo.find(t);
  if (it != d_cardInfo.end())
  {
    return it->second;
  }
  std::pair<CardinalityClass, bool> ret(CardinalityClass::ONE, false);
  std::vector<TypeNode> instTypes;
  std::vector<TypeNode> paramTypes;
  bool isParam = t.isParametricDatatype();
  if (isParam)
  {
    paramTypes = t.getDType().getParameters();
    instTypes = t.getInstantiatedParamTypes();
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
    // get the current cardinality class
    CardinalityClass cctc = tc.getCardinalityClass();
    // update ret.first to the max cardinality class
    ret.first = maxCardinalityClass(ret.first, cctc);
    if (cctc != CardinalityClass::INFINITE)
    {
      // if the argument is (interpreted) finite and external, set the flag
      // for indicating it has a finite external argument
      ret.second = ret.second || !tc.isDatatype();
    }
  }
  d_cardInfo[t] = ret;
  return ret;
}

bool DTypeConstructor::isResolved() const { return !d_tester.isNull(); }

const DTypeSelector& DTypeConstructor::operator[](size_t index) const
{
  Assert(index < getNumArgs());
  return *d_args[index];
}

TypeNode DTypeConstructor::getArgType(size_t index) const
{
  Assert(index < getNumArgs());
  return (*this)[index].getType().getDatatypeSelectorRangeType();
}

Node DTypeConstructor::getSelector(size_t index) const
{
  Assert(isResolved());
  Assert(index < getNumArgs());
  return d_args[index]->getSelector();
}

Node DTypeConstructor::getSharedSelector(TypeNode domainType,
                                         size_t index) const
{
  Assert(isResolved());
  Assert(index < getNumArgs());
  computeSharedSelectors(domainType);
  Assert(d_sharedSelectors[domainType].size() == getNumArgs());
  return d_sharedSelectors[domainType][index];
}

int DTypeConstructor::getSelectorIndexInternal(Node sel) const
{
  Assert(isResolved());
  Assert(sel.getType().isDatatypeSelector());
  // might be a builtin selector
  if (sel.hasAttribute(DTypeIndexAttr()))
  {
    size_t sindex = DType::indexOf(sel);
    if (getNumArgs() > sindex && d_args[sindex]->getSelector() == sel)
    {
      return static_cast<int>(sindex);
    }
  }
  // otherwise, check shared selector
  TypeNode domainType = sel.getType().getDatatypeSelectorDomainType();
  computeSharedSelectors(domainType);
  std::map<Node, unsigned>::iterator its =
      d_sharedSelectorIndex[domainType].find(sel);
  if (its != d_sharedSelectorIndex[domainType].end())
  {
    return (int)its->second;
  }
  return -1;
}

int DTypeConstructor::getSelectorIndexForName(const std::string& name) const
{
  for (size_t i = 0, nargs = getNumArgs(); i < nargs; i++)
  {
    if (d_args[i]->getName() == name)
    {
      return i;
    }
  }
  return -1;
}

bool DTypeConstructor::involvesExternalType() const
{
  for (size_t i = 0, nargs = getNumArgs(); i < nargs; i++)
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
  for (size_t i = 0, nargs = getNumArgs(); i < nargs; i++)
  {
    if (!getArgType(i).isUninterpretedSort())
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
    instTypes = t.getInstantiatedParamTypes();
  }
  for (size_t i = 0, nargs = d_args.size(); i < nargs; i++)
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
  for (size_t i = 0, nargs = getNumArgs(); i < nargs; i++)
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
  Trace("datatypes-init") << "cons " << d_constructor
                          << " computeGroundTerm, isValue = " << isValue
                          << std::endl;

  // for each selector, get a ground term
  std::vector<TypeNode> instTypes;
  std::vector<TypeNode> paramTypes;
  bool isParam = t.isParametricDatatype();
  if (isParam)
  {
    paramTypes = t.getDType().getParameters();
    instTypes = TypeNode(t).getInstantiatedParamTypes();
  }
  for (size_t i = 0, nargs = getNumArgs(); i < nargs; i++)
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
      arg = isValue ? nm->mkGroundValue(selType) : nm->mkGroundTerm(selType);
    }
    if (arg.isNull())
    {
      Trace("datatypes-init") << "...unable to construct arg of "
                              << d_args[i]->getName() << std::endl;
      return Node();
    }
    else
    {
      Trace("datatypes-init")
          << "...constructed arg " << arg << " of type " << arg.getType()
          << ", isConst = " << arg.isConst() << std::endl;
      Assert(!isValue || arg.isConst())
          << "Expected non-constant constructor argument : " << arg
          << " of type " << arg.getType();
      groundTerms.push_back(arg);
    }
  }

  Node groundTerm = nm->mkNode(APPLY_CONSTRUCTOR, groundTerms);
  if (isParam)
  {
    Assert(DType::datatypeOf(d_constructor).isParametric());
    // type is parametric, must apply type ascription
    Trace("datatypes-init") << "ambiguous type for " << groundTerm
                            << ", ascribe to " << t << std::endl;
    groundTerms[0] = nm->mkNode(
        APPLY_TYPE_ASCRIPTION,
        nm->mkConst(AscriptionType(getInstantiatedConstructorType(t))),
        groundTerms[0]);
    groundTerm = nm->mkNode(APPLY_CONSTRUCTOR, groundTerms);
  }
  Trace("datatypes-init") << "...return " << groundTerm << std::endl;
  Assert(!isValue || groundTerm.isConst()) << "Non-constant term " << groundTerm
                                           << " returned for computeGroundTerm";
  return groundTerm;
}

void DTypeConstructor::computeSharedSelectors(TypeNode domainType) const
{
  if (d_sharedSelectors[domainType].size() < getNumArgs())
  {
    TypeNode ctype;
    if (domainType.isParametricDatatype())
    {
      ctype = getInstantiatedConstructorType(domainType);
    }
    else
    {
      ctype = d_constructor.getType();
    }
    Assert(ctype.isDatatypeConstructor());
    Assert(ctype.getNumChildren() - 1 == getNumArgs());
    // compute the shared selectors
    const DType& dt = DType::datatypeOf(d_constructor);
    std::map<TypeNode, unsigned> counter;
    for (size_t j = 0, jend = ctype.getNumChildren() - 1; j < jend; j++)
    {
      TypeNode t = ctype[j];
      Node ss = dt.getSharedSelector(domainType, t, counter[t]);
      d_sharedSelectors[domainType].push_back(ss);
      Assert(d_sharedSelectorIndex[domainType].find(ss)
             == d_sharedSelectorIndex[domainType].end());
      d_sharedSelectorIndex[domainType][ss] = j;
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
  if (isResolved())
  {
    // already resolved, fail
    return false;
  }
  Trace("datatypes") << "DTypeConstructor::resolve, self type is " << self
                     << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  size_t index = 0;
  std::vector<TypeNode> argTypes;
  Trace("datatypes-init") << "Initialize constructor " << d_name << std::endl;
  for (std::shared_ptr<DTypeSelector> arg : d_args)
  {
    std::string argName = arg->d_name;
    TypeNode range;
    if (arg->d_selector.isNull())
    {
      // the unresolved type wasn't created here; do name resolution
      std::string typeName = argName.substr(argName.find('\0') + 1);
      Trace("datatypes-init")
          << "  - selector, typeName is " << typeName << std::endl;
      argName.resize(argName.find('\0'));
      if (typeName == "")
      {
        Trace("datatypes-init") << "  ...self selector" << std::endl;
        range = self;
      }
      else
      {
        std::map<std::string, TypeNode>::const_iterator j =
            resolutions.find(typeName);
        if (j == resolutions.end())
        {
          Trace("datatypes-init")
              << "  ...failed to resolve selector" << std::endl;
          // failed to resolve selector
          return false;
        }
        else
        {
          Trace("datatypes-init") << "  ...resolved selector" << std::endl;
          range = (*j).second;
        }
      }
    }
    else
    {
      // the type for the selector already exists; may need
      // complex-type substitution
      range = arg->d_selector.getType();
      Trace("datatypes-init")
          << "  - null selector, range = " << range << std::endl;
      if (!placeholders.empty())
      {
        range = range.substitute(placeholders.begin(),
                                 placeholders.end(),
                                 replacements.begin(),
                                 replacements.end());
      }
      Trace("datatypes-init")
          << "  ...range after placeholder replacement " << range << std::endl;
      if (!paramTypes.empty())
      {
        range = doParametricSubstitution(range, paramTypes, paramReplacements);
      }
      Trace("datatypes-init")
          << "  ...range after parametric substitution " << range << std::endl;
    }
    // Internally, selectors (and updaters) are fresh internal skolems which
    // we constructor via mkDummySkolem.
    arg->d_selector = sm->mkDummySkolem(argName,
                                        nm->mkSelectorType(self, range),
                                        "is a selector",
                                        SkolemManager::SKOLEM_EXACT_NAME);
    std::string updateName("update_" + argName);
    arg->d_updater = sm->mkDummySkolem(updateName,
                                       nm->mkDatatypeUpdateType(self, range),
                                       "is a selector",
                                       SkolemManager::SKOLEM_EXACT_NAME);
    // must set indices to ensure datatypes::utils::indexOf works
    arg->d_selector.setAttribute(DTypeConsIndexAttr(), cindex);
    arg->d_selector.setAttribute(DTypeIndexAttr(), index);
    arg->d_updater.setAttribute(DTypeConsIndexAttr(), cindex);
    arg->d_updater.setAttribute(DTypeIndexAttr(), index);
    index = index + 1;
    arg->d_resolved = true;
    argTypes.push_back(range);
    // We use \0 as a distinguished marker for unresolved selectors for doing
    // name resolutions. We now can remove \0 from name if necessary.
    const size_t nul = arg->d_name.find('\0');
    if (nul != std::string::npos)
    {
      arg->d_name.resize(nul);
    }
  }

  Assert(index == getNumArgs());

  // Set constructor/tester last, since DTypeConstructor::isResolved()
  // returns true when d_tester is not the null Node.  If something
  // fails above, we want Constuctor::isResolved() to remain "false".
  // Further, mkConstructorType() iterates over the selectors, so
  // should get the results of any resolutions we did above.
  // The name of the tester variable does not matter, it is only used
  // internally.
  std::string testerName("is_" + d_name);
  d_tester = sm->mkDummySkolem(testerName,
                               nm->mkTesterType(self),
                               "is a tester",
                               SkolemManager::SKOLEM_EXACT_NAME);
  d_constructor = sm->mkDummySkolem(getName(),
                                    nm->mkConstructorType(argTypes, self),
                                    "is a constructor",
                                    SkolemManager::SKOLEM_EXACT_NAME);
  Assert(d_constructor.getType().isDatatypeConstructor());
  // associate constructor with all selectors
  for (std::shared_ptr<DTypeSelector> sel : d_args)
  {
    sel->d_constructor = d_constructor;
  }
  Assert(isResolved());
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
  if (range.getKind() == INSTANTIATED_SORT_TYPE)
  {
    // paramTypes contains a list of uninterpreted sort constructors.
    // paramReplacements contains a list of instantiated parametric datatypes.
    // If range is (INSTANTIATED_SORT_TYPE c T1 ... Tn), and
    //    paramTypes[i] is c
    //    paramReplacements[i] is (PARAMETRIC_DATATYPE d S1 ... Sn)
    // then we return (PARAMETRIC_DATATYPE d T'1 ... T'n) where T'1 ...T'n
    // is the result of recursively processing T1 ... Tn.
    for (size_t i = 0, psize = paramTypes.size(); i < psize; ++i)
    {
      if (paramTypes[i] == origChildren[0])
      {
        std::vector<TypeNode> params(children.begin() + 1, children.end());
        TypeNode tret = paramReplacements[i].instantiate(params);
        return tret;
      }
    }
  }
  NodeBuilder nb(range.getKind());
  for (size_t i = 0, csize = children.size(); i < csize; ++i)
  {
    nb << children[i];
  }
  TypeNode tn = nb.constructTypeNode();
  return tn;
}

void DTypeConstructor::toStream(std::ostream& out) const
{
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
  ctor.toStream(os);
  return os;
}

}  // namespace cvc5::internal

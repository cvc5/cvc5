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
#include "expr/dtype.h"

#include <sstream>

#include "expr/dtype_cons.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/type_matcher.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

DType::DType(std::string name, bool isCo)
    : d_name(name),
      d_params(),
      d_isCo(isCo),
      d_isTuple(false),
      d_isRecord(false),
      d_constructors(),
      d_resolved(false),
      d_self(),
      d_involvesExt(false),
      d_involvesUt(false),
      d_sygusAllowConst(false),
      d_sygusAllowAll(false),
      d_card(CardinalityUnknown()),
      d_wellFounded(0),
      d_nestedRecursion(0)
{
}

DType::DType(std::string name, const std::vector<TypeNode>& params, bool isCo)
    : d_name(name),
      d_params(params),
      d_isCo(isCo),
      d_isTuple(false),
      d_isRecord(false),
      d_constructors(),
      d_resolved(false),
      d_self(),
      d_involvesExt(false),
      d_involvesUt(false),
      d_sygusAllowConst(false),
      d_sygusAllowAll(false),
      d_card(CardinalityUnknown()),
      d_wellFounded(0),
      d_nestedRecursion(0)
{
}

DType::~DType() {}

std::string DType::getName() const { return d_name; }
size_t DType::getNumConstructors() const { return d_constructors.size(); }

bool DType::isParametric() const { return d_params.size() > 0; }
size_t DType::getNumParameters() const { return d_params.size(); }
TypeNode DType::getParameter(size_t i) const
{
  Assert(isParametric());
  Assert(i < d_params.size());
  return d_params[i];
}

std::vector<TypeNode> DType::getParameters() const
{
  Assert(isParametric());
  return d_params;
}

bool DType::isCodatatype() const { return d_isCo; }

bool DType::isSygus() const { return !d_sygusType.isNull(); }

bool DType::isTuple() const { return d_isTuple; }

bool DType::isRecord() const { return d_isRecord; }

bool DType::isResolved() const { return d_resolved; }

const DType& DType::datatypeOf(Node item)
{
  TypeNode t = item.getType();
  switch (t.getKind())
  {
    case CONSTRUCTOR_TYPE: return t[t.getNumChildren() - 1].getDType();
    case SELECTOR_TYPE:
    case TESTER_TYPE:
    case UPDATER_TYPE: return t[0].getDType();
    default:
      Unhandled() << "arg must be a datatype constructor, selector, or tester";
  }
}

size_t DType::indexOf(Node item)
{
  Assert(item.getType().isDatatypeConstructor()
         || item.getType().isDatatypeTester()
         || item.getType().isDatatypeSelector()
         || item.getType().isDatatypeUpdater());
  return indexOfInternal(item);
}

size_t DType::indexOfInternal(Node item)
{
  if (item.getKind() == APPLY_TYPE_ASCRIPTION)
  {
    return indexOf(item[0]);
  }
  Assert(item.hasAttribute(DTypeIndexAttr()));
  return item.getAttribute(DTypeIndexAttr());
}

size_t DType::cindexOf(Node item)
{
  Assert(item.getType().isDatatypeSelector()
         || item.getType().isDatatypeUpdater());
  return cindexOfInternal(item);
}
size_t DType::cindexOfInternal(Node item)
{
  if (item.getKind() == APPLY_TYPE_ASCRIPTION)
  {
    return cindexOf(item[0]);
  }
  Assert(item.hasAttribute(DTypeConsIndexAttr()));
  return item.getAttribute(DTypeConsIndexAttr());
}

void DType::collectUnresolvedDatatypeTypes(std::set<TypeNode>& unresTypes) const
{
  // Scan the arguments of all constructors and collect their types. To be
  // robust to datatypes with nested recursion, we collect the *component*
  // types of all subfield types and store them in csfTypes. In other words, we
  // search for unresolved datatypes that occur possibly as parameters to
  // other parametric types.
  std::unordered_set<TypeNode> csfTypes;
  for (const std::shared_ptr<DTypeConstructor>& ctor : d_constructors)
  {
    for (size_t i = 0, nargs = ctor->getNumArgs(); i < nargs; i++)
    {
      Node sel = (*ctor)[i].d_selector;
      if (sel.isNull())
      {
        // we currently permit null selector for representing self selectors,
        // skip these.
        continue;
      }
      // The selector has *not* been initialized to a variable of selector type,
      // which is done during resolve. Instead, we get the raw type of sel
      // and compute its component types.
      expr::getComponentTypes(sel.getType(), csfTypes);
    }
  }
  // Now, process each component type
  for (const TypeNode& arg : csfTypes)
  {
    if (arg.isUnresolvedDatatype())
    {
      // it is an unresolved datatype
      unresTypes.insert(arg);
    }
    else if (arg.isInstantiatedUninterpretedSort())
    {
      // it might be an instantiated sort constructor corresponding to a
      // unresolved parametric datatype, in which case we extract its operator
      TypeNode argc = arg.getUninterpretedSortConstructor();
      if (argc.isUnresolvedDatatype())
      {
        unresTypes.insert(argc);
      }
    }
  }
}

bool DType::resolve(const std::map<std::string, TypeNode>& resolutions,
                    const std::vector<TypeNode>& placeholders,
                    const std::vector<TypeNode>& replacements,
                    const std::vector<TypeNode>& paramTypes,
                    const std::vector<TypeNode>& paramReplacements)
{
  Trace("datatypes-init") << "DType::resolve: " << std::endl;
  Assert(!d_resolved);
  Assert(resolutions.find(d_name) != resolutions.end());
  Assert(placeholders.size() == replacements.size());
  Assert(paramTypes.size() == paramReplacements.size());
  Assert(getNumConstructors() > 0);
  TypeNode self = (*resolutions.find(d_name)).second;
  Assert(&self.getDType() == this);
  d_resolved = true;
  size_t index = 0;
  for (std::shared_ptr<DTypeConstructor> ctor : d_constructors)
  {
    Trace("datatypes-init") << "DType::resolve ctor " << std::endl;
    if (!ctor->resolve(self,
                       resolutions,
                       placeholders,
                       replacements,
                       paramTypes,
                       paramReplacements,
                       index))
    {
      return false;
    }
    ctor->d_constructor.setAttribute(DTypeIndexAttr(), index);
    ctor->d_tester.setAttribute(DTypeIndexAttr(), index++);
    Assert(ctor->isResolved());
    Trace("datatypes-init") << "DType::resolve ctor finished" << std::endl;
  }
  d_self = self;

  d_involvesExt = false;
  d_involvesUt = false;
  for (const std::shared_ptr<DTypeConstructor>& ctor : d_constructors)
  {
    if (ctor->involvesExternalType())
    {
      d_involvesExt = true;
    }
    if (ctor->involvesUninterpretedType())
    {
      d_involvesUt = true;
    }
  }

  if (isSygus())
  {
    // all datatype constructors should be sygus and have sygus operators whose
    // free variables are subsets of sygus bound var list.
    std::unordered_set<Node> svs;
    for (const Node& sv : d_sygusBvl)
    {
      svs.insert(sv);
    }
    for (size_t i = 0, ncons = d_constructors.size(); i < ncons; i++)
    {
      Node sop = d_constructors[i]->getSygusOp();
      Assert(!sop.isNull())
          << "Sygus datatype contains a non-sygus constructor";
      std::unordered_set<Node> fvs;
      expr::getFreeVariables(sop, fvs);
      for (const Node& v : fvs)
      {
        if (svs.find(v) == svs.end())
        {
          // return false, indicating we should abort, since this datatype is
          // not well formed.
          return false;
        }
      }
    }
  }
  Trace("datatypes-init") << "DType::resolve: finished" << std::endl;
  return true;
}

void DType::addConstructor(std::shared_ptr<DTypeConstructor> c)
{
  Assert(!d_resolved);
  d_constructors.push_back(c);
}

void DType::addSygusConstructor(Node op,
                                const std::string& cname,
                                const std::vector<TypeNode>& cargs,
                                int weight)
{
  // avoid name clashes
  std::stringstream ss;
  ss << getName() << "_" << getNumConstructors() << "_" << cname;
  std::string name = ss.str();
  unsigned cweight = weight >= 0 ? weight : (cargs.empty() ? 0 : 1);
  std::shared_ptr<DTypeConstructor> c =
      std::make_shared<DTypeConstructor>(name, cweight);
  c->setSygus(op);
  for (size_t j = 0, nargs = cargs.size(); j < nargs; j++)
  {
    std::stringstream sname;
    sname << name << "_" << j;
    c->addArg(sname.str(), cargs[j]);
  }
  addConstructor(c);
}

void DType::setSygus(TypeNode st, Node bvl, bool allowConst, bool allowAll)
{
  Assert(!d_resolved);
  // We can be in a case where the only rule specified was
  // (Constant T), in which case we have not yet added a constructor. We
  // ensure an arbitrary constant is added in this case. We additionally
  // add a constant if the grammar has only non-nullary constructors, since this
  // ensures the datatype is well-founded (see 3423).
  // Notice we only want to do this for sygus datatypes that are user-provided.
  // At the moment, the condition !allow_all implies the grammar is
  // user-provided and hence may require a default constant.
  // For the SyGuS API, we could consider requiring the user to explicitly add
  // the "any constant" constructor with a call instead of passing a flag. This
  // would make the block of code unnecessary.
  if (allowConst && !allowAll)
  {
    // if I don't already have a constant (0-ary constructor)
    bool hasConstant = false;
    for (size_t i = 0, ncons = getNumConstructors(); i < ncons; i++)
    {
      if ((*this)[i].getNumArgs() == 0)
      {
        hasConstant = true;
        break;
      }
    }
    if (!hasConstant)
    {
      // add an arbitrary one
      NodeManager* nm = NodeManager::currentNM();
      Node op = nm->mkGroundTerm(st);
      // use same naming convention as SygusDatatype
      std::stringstream ss;
      ss << getName() << "_" << getNumConstructors() << "_" << op;
      // it has zero weight
      std::shared_ptr<DTypeConstructor> c =
          std::make_shared<DTypeConstructor>(ss.str(), 0);
      c->setSygus(op);
      addConstructor(c);
    }
  }

  d_sygusType = st;
  d_sygusBvl = bvl;
  d_sygusAllowConst = allowConst || allowAll;
  d_sygusAllowAll = allowAll;
}

void DType::setTuple()
{
  Assert(!d_resolved);
  d_isTuple = true;
}

void DType::setRecord()
{
  Assert(!d_resolved);
  d_isRecord = true;
}

Cardinality DType::getCardinality(TypeNode t) const
{
  Trace("datatypes-init") << "DType::getCardinality " << std::endl;
  Assert(isResolved());
  Assert(t.isDatatype() && t.getDType().getTypeNode() == d_self);
  std::vector<TypeNode> processing;
  computeCardinality(t, processing);
  return d_card;
}

Cardinality DType::getCardinality() const
{
  Assert(!isParametric());
  return getCardinality(d_self);
}

Cardinality DType::computeCardinality(TypeNode t,
                                      std::vector<TypeNode>& processing) const
{
  Trace("datatypes-init") << "DType::computeCardinality " << std::endl;
  Assert(isResolved());
  if (std::find(processing.begin(), processing.end(), d_self)
      != processing.end())
  {
    d_card = Cardinality::INTEGERS;
    return d_card;
  }
  processing.push_back(d_self);
  Cardinality c = 0;
  for (std::shared_ptr<DTypeConstructor> ctor : d_constructors)
  {
    c += ctor->computeCardinality(t, processing);
  }
  d_card = c;
  processing.pop_back();
  return d_card;
}

bool DType::isRecursiveSingleton(TypeNode t) const
{
  Trace("datatypes-init") << "DType::isRecursiveSingleton " << std::endl;
  Assert(isResolved());
  Assert(t.isDatatype() && t.getDType().getTypeNode() == d_self);
  if (d_cardRecSingleton.find(t) != d_cardRecSingleton.end())
  {
    return d_cardRecSingleton[t] == 1;
  }
  if (isCodatatype())
  {
    Assert(d_cardUAssume[t].empty());
    std::vector<TypeNode> processing;
    if (computeCardinalityRecSingleton(t, processing, d_cardUAssume[t]))
    {
      d_cardRecSingleton[t] = 1;
      if (TraceIsOn("dt-card"))
      {
        Trace("dt-card") << "DType " << getName()
                         << " is recursive singleton, dependent upon "
                         << d_cardUAssume[t].size()
                         << " uninterpreted sorts: " << std::endl;
        for (size_t i = 0; i < d_cardUAssume[t].size(); i++)
        {
          Trace("dt-card") << "  " << d_cardUAssume[t][i] << std::endl;
        }
        Trace("dt-card") << std::endl;
      }
    }
    else
    {
      d_cardRecSingleton[t] = -1;
    }
  }
  else
  {
    d_cardRecSingleton[t] = -1;
  }
  return d_cardRecSingleton[t] == 1;
}

bool DType::isRecursiveSingleton() const
{
  Assert(!isParametric());
  return isRecursiveSingleton(d_self);
}

unsigned DType::getNumRecursiveSingletonArgTypes(TypeNode t) const
{
  Assert(d_cardRecSingleton.find(t) != d_cardRecSingleton.end());
  Assert(isRecursiveSingleton(t));
  return d_cardUAssume[t].size();
}

unsigned DType::getNumRecursiveSingletonArgTypes() const
{
  Assert(!isParametric());
  return getNumRecursiveSingletonArgTypes(d_self);
}

TypeNode DType::getRecursiveSingletonArgType(TypeNode t, size_t i) const
{
  Assert(d_cardRecSingleton.find(t) != d_cardRecSingleton.end());
  Assert(isRecursiveSingleton(t));
  return d_cardUAssume[t][i];
}

TypeNode DType::getRecursiveSingletonArgType(size_t i) const
{
  Assert(!isParametric());
  return getRecursiveSingletonArgType(d_self, i);
}

bool DType::computeCardinalityRecSingleton(
    TypeNode t,
    std::vector<TypeNode>& processing,
    std::vector<TypeNode>& u_assume) const
{
  Trace("datatypes-init") << "DType::computeCardinalityRecSingleton "
                          << std::endl;
  if (std::find(processing.begin(), processing.end(), d_self)
      != processing.end())
  {
    return true;
  }
  if (d_cardRecSingleton[t] == 0)
  {
    // if not yet computed
    if (d_constructors.size() != 1)
    {
      return false;
    }
    bool success = false;
    processing.push_back(d_self);
    for (size_t i = 0, nargs = d_constructors[0]->getNumArgs(); i < nargs; i++)
    {
      TypeNode tc = d_constructors[0]->getArgType(i);
      // if it is an uninterpreted sort, then we depend on it having cardinality
      // one
      if (tc.isUninterpretedSort())
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
  else if (d_cardRecSingleton[t] == -1)
  {
    return false;
  }
  for (size_t i = 0, csize = d_cardUAssume[t].size(); i < csize; i++)
  {
    if (std::find(u_assume.begin(), u_assume.end(), d_cardUAssume[t][i])
        == u_assume.end())
    {
      u_assume.push_back(d_cardUAssume[t][i]);
    }
  }
  return true;
}

CardinalityClass DType::getCardinalityClass(TypeNode t) const
{
  Trace("datatypes-init") << "DType::isFinite " << std::endl;
  Assert(isResolved());
  Assert(t.isDatatype() && t.getDType().getTypeNode() == d_self);

  // is this already in the cache ?
  std::map<TypeNode, CardinalityClass>::const_iterator it = d_cardClass.find(t);
  if (it != d_cardClass.end())
  {
    return it->second;
  }
  // it is the max cardinality class of a constructor, with base case ONE
  // if we have one constructor and FINITE otherwise.
  CardinalityClass c = d_constructors.size() == 1 ? CardinalityClass::ONE
                                                  : CardinalityClass::FINITE;
  for (std::shared_ptr<DTypeConstructor> ctor : d_constructors)
  {
    CardinalityClass cc = ctor->getCardinalityClass(t);
    c = maxCardinalityClass(c, cc);
  }
  d_cardClass[t] = c;
  return c;
}
CardinalityClass DType::getCardinalityClass() const
{
  Assert(isResolved() && !isParametric());
  return getCardinalityClass(d_self);
}

bool DType::isFinite(TypeNode t, bool fmfEnabled) const
{
  return isCardinalityClassFinite(getCardinalityClass(t), fmfEnabled);
}

bool DType::isFinite(bool fmfEnabled) const
{
  return isFinite(d_self, fmfEnabled);
}

bool DType::isWellFounded() const
{
  Assert(isResolved());
  if (d_wellFounded != 0)
  {
    // already computed
    return d_wellFounded == 1;
  }
  Trace("datatypes-init") << "DType::isWellFounded " << getName() << std::endl;
  std::vector<TypeNode> processing;
  if (!computeWellFounded(processing))
  {
    // not well-founded since no ground term can be constructed
    Trace("datatypes-init") << "DType::isWellFounded: false for " << getName()
                            << " due to no ground terms." << std::endl;
    d_wellFounded = -1;
    return false;
  }
  Trace("datatypes-init") << "DType::isWellFounded: true for " << getName()
                          << std::endl;
  d_wellFounded = 1;
  return true;
}

bool DType::computeWellFounded(std::vector<TypeNode>& processing) const
{
  Trace("datatypes-init") << "DType::computeWellFounded " << std::endl;
  Assert(isResolved());
  if (std::find(processing.begin(), processing.end(), d_self)
      != processing.end())
  {
    return d_isCo;
  }
  processing.push_back(d_self);
  for (std::shared_ptr<DTypeConstructor> ctor : d_constructors)
  {
    if (ctor->computeWellFounded(processing))
    {
      processing.pop_back();
      return true;
    }
    else
    {
      Trace("dt-wf") << "Constructor " << ctor->getName()
                     << " is not well-founded." << std::endl;
    }
  }
  processing.pop_back();
  Trace("dt-wf") << "DType " << getName() << " is not well-founded."
                 << std::endl;
  return false;
}

Node DType::mkGroundTerm(TypeNode t) const
{
  Trace("datatypes-init") << "DType::mkGroundTerm of type " << t << std::endl;
  Assert(isResolved());
  return mkGroundTermInternal(t, false);
}

Node DType::mkGroundValue(TypeNode t) const
{
  Assert(isResolved());
  Trace("datatypes-init") << "DType::mkGroundValue of type " << t << std::endl;
  Node v = mkGroundTermInternal(t, true);
  return v;
}

Node DType::mkGroundTermInternal(TypeNode t, bool isValue) const
{
  Trace("datatypes-init") << "DType::mkGroundTerm of type " << t
                          << ", isValue = " << isValue << std::endl;
  // is this already in the cache ?
  std::map<TypeNode, Node>& cache = isValue ? d_groundValue : d_groundTerm;
  std::map<TypeNode, Node>::iterator it = cache.find(t);
  if (it != cache.end())
  {
    Trace("datatypes-init")
        << "\nin cache: " << d_self << " => " << it->second << std::endl;
    return it->second;
  }
  std::vector<TypeNode> processing;
  Node groundTerm = computeGroundTerm(t, processing, isValue);
  if (!groundTerm.isNull())
  {
    // we found a ground-term-constructing constructor!
    cache[t] = groundTerm;
    Trace("datatypes-init")
        << "constructed: " << getName() << " => " << groundTerm << std::endl;
  }
  // if ground term is null, we are not well-founded
  Trace("datatypes-init") << "DType::mkGroundTerm for " << t
                          << ", isValue=" << isValue << " returns "
                          << groundTerm << std::endl;
  return groundTerm;
}

void DType::getAlienSubfieldTypes(std::unordered_set<TypeNode>& types,
                                  std::map<TypeNode, bool>& processed,
                                  bool isAlienPos) const
{
  std::map<TypeNode, bool>::iterator it = processed.find(d_self);
  if (it != processed.end())
  {
    if (it->second || (!isAlienPos && !it->second))
    {
      // already processed as an alien subfield type, or already processed
      // as a non-alien subfield type and isAlienPos is false.
      return;
    }
  }
  processed[d_self] = isAlienPos;
  for (std::shared_ptr<DTypeConstructor> ctor : d_constructors)
  {
    for (unsigned j = 0, nargs = ctor->getNumArgs(); j < nargs; ++j)
    {
      TypeNode tn = ctor->getArgType(j);
      if (tn.isDatatype())
      {
        // special case for datatypes, we must recurse to collect subfield types
        if (!isAlienPos)
        {
          // since we aren't adding it to types below, we add its alien
          // subfield types here.
          const DType& dt = tn.getDType();
          dt.getAlienSubfieldTypes(types, processed, false);
        }
        if (tn.isParametricDatatype() && !isAlienPos)
        {
          // (instantiated) parametric datatypes have an AST structure:
          //  (PARAMETRIC_DATATYPE D T1 ... Tn)
          // where D is the uninstantiated datatype type.  We should not view D
          // as an alien subfield type of tn. Thus, we need a special case here
          // which ignores the first child, when isAlienPos is false.
          for (unsigned i = 1, nchild = tn.getNumChildren(); i < nchild; i++)
          {
            expr::getComponentTypes(tn[i], types);
          }
          continue;
        }
      }
      // we are in a case where tn is not a datatype, we add all (alien)
      // component types to types below.
      bool hasTn = types.find(tn) != types.end();
      Trace("datatypes-init")
          << "Collect subfield types " << tn << ", hasTn=" << hasTn
          << ", isAlienPos=" << isAlienPos << std::endl;
      expr::getComponentTypes(tn, types);
      if (!isAlienPos && !hasTn)
      {
        // the top-level type is added by getComponentTypes, so remove it if it
        // was not already listed in types
        Assert(types.find(tn) != types.end());
        types.erase(tn);
      }
    }
  }
  // Now, go back and add all alien subfield types from datatypes if
  // not done so already. This is because getComponentTypes does not
  // recurse into subfield types of datatypes.
  for (const TypeNode& sstn : types)
  {
    if (sstn.isDatatype())
    {
      const DType& dt = sstn.getDType();
      dt.getAlienSubfieldTypes(types, processed, true);
    }
  }
}

bool DType::hasNestedRecursion() const
{
  if (d_nestedRecursion != 0)
  {
    return d_nestedRecursion == 1;
  }
  Trace("datatypes-init") << "Compute simply recursive for " << getName()
                          << std::endl;
  // get the alien subfield types of this datatype
  std::unordered_set<TypeNode> types;
  std::map<TypeNode, bool> processed;
  getAlienSubfieldTypes(types, processed, false);
  if (TraceIsOn("datatypes-init"))
  {
    Trace("datatypes-init") << "Alien subfield types: " << std::endl;
    for (const TypeNode& t : types)
    {
      Trace("datatypes-init") << "- " << t << std::endl;
    }
  }
  // does types contain self?
  if (types.find(d_self) != types.end())
  {
    Trace("datatypes-init")
        << "DType::hasNestedRecursion: true for " << getName()
        << " due to alien subfield type" << std::endl;
    // has nested recursion since it has itself as an alien subfield type.
    d_nestedRecursion = 1;
    return true;
  }
  // If it is parametric, this type may match with an alien subfield type (e.g.
  // we may have a field (T Int) for parametric datatype (T x) where x
  // is a type parameter). Thus, we check whether the self type matches any
  // alien subfield type using the TypeMatcher utility.
  if (isParametric())
  {
    for (const TypeNode& t : types)
    {
      TypeMatcher m(d_self);
      Trace("datatypes-init") << "  " << t << std::endl;
      if (m.doMatching(d_self, t))
      {
        Trace("datatypes-init")
            << "DType::hasNestedRecursion: true for " << getName()
            << " due to parametric strict component type, " << d_self
            << " matching " << t << std::endl;
        d_nestedRecursion = 1;
        return true;
      }
    }
  }
  Trace("datatypes-init") << "DType::hasNestedRecursion: false for "
                          << getName() << std::endl;
  d_nestedRecursion = -1;
  return false;
}

Node getSubtermWithType(Node e, TypeNode t, bool isTop)
{
  if (!isTop && e.getType() == t)
  {
    return e;
  }
  for (const Node& ei : e)
  {
    Node se = getSubtermWithType(ei, t, false);
    if (!se.isNull())
    {
      return se;
    }
  }
  return Node();
}

Node DType::computeGroundTerm(TypeNode t,
                              std::vector<TypeNode>& processing,
                              bool isValue) const
{
  if (std::find(processing.begin(), processing.end(), t) != processing.end())
  {
    Trace("datatypes-init")
        << "...already processing " << t << " " << d_self << std::endl;
    return Node();
  }
  processing.push_back(t);
  std::map<TypeNode, Node>& gtCache = isValue ? d_groundValue : d_groundTerm;
  for (unsigned r = 0; r < 2; r++)
  {
    for (std::shared_ptr<DTypeConstructor> ctor : d_constructors)
    {
      // do nullary constructors first
      if ((ctor->getNumArgs() == 0) != (r == 0))
      {
        continue;
      }
      Trace("datatypes-init") << "Try constructing for " << ctor->getName()
                              << ", processing = " << processing.size()
                              << ", isValue=" << isValue << std::endl;
      Node e = ctor->computeGroundTerm(t, processing, gtCache, isValue);
      if (!e.isNull())
      {
        // must check subterms for the same type to avoid infinite loops in
        // type enumeration
        Node se = getSubtermWithType(e, t, true);
        if (!se.isNull())
        {
          Trace("datatypes-init") << "Take subterm " << se << std::endl;
          e = se;
        }
        processing.pop_back();
        return e;
      }
      else
      {
        Trace("datatypes-init") << "...failed." << std::endl;
      }
    }
  }
  processing.pop_back();
  return Node();
}

TypeNode DType::getTypeNode() const
{
  Assert(isResolved());
  Assert(!d_self.isNull());
  return d_self;
}

TypeNode DType::getTypeNode(const std::vector<TypeNode>& params) const
{
  Assert(isResolved());
  Assert(!d_self.isNull() && d_self.isParametricDatatype());
  return d_self.instantiate(params);
}

const DTypeConstructor& DType::operator[](size_t index) const
{
  Assert(index < getNumConstructors());
  return *d_constructors[index];
}

Node DType::getSharedSelector(TypeNode dtt, TypeNode t, size_t index) const
{
  Assert(isResolved());
  std::map<TypeNode, std::map<TypeNode, std::map<unsigned, Node> > >::iterator
      itd = d_sharedSel.find(dtt);
  if (itd != d_sharedSel.end())
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
  SkolemManager* sm = nm->getSkolemManager();
  TypeNode stype = nm->mkSelectorType(dtt, t);
  Node nindex = nm->mkConstInt(Rational(index));
  s = sm->mkSkolemFunction(SkolemFunId::SHARED_SELECTOR, stype, nindex);
  d_sharedSel[dtt][t][index] = s;
  Trace("dt-shared-sel") << "Made " << s << " of type " << dtt << " -> " << t
                         << std::endl;
  return s;
}

TypeNode DType::getSygusType() const { return d_sygusType; }

Node DType::getSygusVarList() const { return d_sygusBvl; }

bool DType::getSygusAllowConst() const { return d_sygusAllowConst; }

bool DType::getSygusAllowAll() const { return d_sygusAllowAll; }

bool DType::involvesExternalType() const { return d_involvesExt; }

bool DType::involvesUninterpretedType() const { return d_involvesUt; }

const std::vector<std::shared_ptr<DTypeConstructor> >& DType::getConstructors()
    const
{
  return d_constructors;
}

std::unordered_set<TypeNode> DType::getSubfieldTypes() const
{
  std::unordered_set<TypeNode> subFieldTypes;
  for (std::shared_ptr<DTypeConstructor> ctor : d_constructors)
  {
    for (size_t i = 0, nargs = ctor->getNumArgs(); i < nargs; i++)
    {
      subFieldTypes.insert(ctor->getArgType(i));
    }
  }
  return subFieldTypes;
}

std::ostream& operator<<(std::ostream& os, const DType& dt)
{
  dt.toStream(os);
  return os;
}

void DType::toStream(std::ostream& out) const
{
  out << "DATATYPE " << getName();
  if (isParametric())
  {
    out << '[';
    for (size_t i = 0, nparams = getNumParameters(); i < nparams; ++i)
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
  for (std::shared_ptr<DTypeConstructor> ctor : d_constructors)
  {
    if (!firstTime)
    {
      out << " | ";
    }
    firstTime = false;
    out << *ctor;
  }
  out << " END;" << std::endl;
}

}  // namespace cvc5::internal

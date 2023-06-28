/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A manager for Nodes.
 */
#include <algorithm>
#include <sstream>
#include <stack>
#include <utility>

#include "base/check.h"
#include "base/listener.h"
#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/metakind.h"
#include "expr/node_manager.h"
#include "expr/node_manager_attributes.h"
#include "expr/oracle.h"
#include "expr/skolem_manager.h"
#include "expr/type_checker.h"
#include "expr/type_properties.h"
#include "theory/builtin/abstract_type.h"
#include "util/bitvector.h"
#include "util/finite_field_value.h"
#include "util/integer.h"
#include "util/poly_util.h"
#include "util/rational.h"
#include "util/resource_manager.h"
#include "util/uninterpreted_sort_value.h"

// clang-format off
${metakind_includes}
// clang-format off

using namespace std;
using namespace cvc5::internal::expr;

namespace cvc5::internal {

namespace {

/**
 * This class sets it reference argument to true and ensures that it gets set
 * to false on destruction. This can be used to make sure a flag gets toggled
 * in a function even on exceptional exit (e.g., see reclaimZombies()).
 */
struct ScopedBool {
  bool& d_value;

  ScopedBool(bool& value) :
    d_value(value) {

    Trace("gc") << ">> setting ScopedBool\n";
    d_value = true;
  }

  ~ScopedBool() {
    Trace("gc") << "<< clearing ScopedBool\n";
    d_value = false;
  }
};

/**
 * Similarly, ensure d_nodeUnderDeletion gets set to NULL even on
 * exceptional exit from NodeManager::reclaimZombies().
 */
struct NVReclaim {
  NodeValue*& d_deletionField;

  NVReclaim(NodeValue*& deletionField) :
    d_deletionField(deletionField) {

    Trace("gc") << ">> setting NVRECLAIM field\n";
  }

  ~NVReclaim() {
    Trace("gc") << "<< clearing NVRECLAIM field\n";
    d_deletionField = nullptr;
  }
};

} // namespace

// clang-format off
${metakind_mkConst}
// clang-format on

namespace attr {
struct LambdaBoundVarListTag
{
};
}  // namespace attr

// attribute that stores the canonical bound variable list for function types
typedef expr::Attribute<attr::LambdaBoundVarListTag, Node>
    LambdaBoundVarListAttr;

NodeManager::NodeManager()
    : d_skManager(new SkolemManager),
      d_bvManager(new BoundVarManager),
      d_nextId(0),
      d_attrManager(new expr::attr::AttributeManager()),
      d_nodeUnderDeletion(nullptr),
      d_inReclaimZombies(false)
{
  poolInsert(&expr::NodeValue::null());

  for (uint32_t i = 0; i < uint32_t (kind::LAST_KIND); ++i)
  {
    Kind k = Kind(i);

    if (hasOperator(k))
    {
      d_operators[i] = mkConst(Kind(k));
    }
  }
}

NodeManager* NodeManager::currentNM()
{
  thread_local static NodeManager nm;
  return &nm;
}

bool NodeManager::isNAryKind(Kind k)
{
  return kind::metakind::getMaxArityForKind(k) == expr::NodeValue::MAX_CHILDREN;
}

TypeNode NodeManager::booleanType()
{
  return mkConstInternal<TypeNode, TypeConstant>(kind::TYPE_CONSTANT,
                                                 BOOLEAN_TYPE);
}

TypeNode NodeManager::integerType()
{
  return mkConstInternal<TypeNode, TypeConstant>(kind::TYPE_CONSTANT,
                                                 INTEGER_TYPE);
}

TypeNode NodeManager::realType()
{
  return mkConstInternal<TypeNode, TypeConstant>(kind::TYPE_CONSTANT,
                                                 REAL_TYPE);
}

TypeNode NodeManager::stringType()
{
  return mkConstInternal<TypeNode, TypeConstant>(kind::TYPE_CONSTANT,
                                                 STRING_TYPE);
}

TypeNode NodeManager::regExpType()
{
  return mkConstInternal<TypeNode, TypeConstant>(kind::TYPE_CONSTANT,
                                                 REGEXP_TYPE);
}

TypeNode NodeManager::roundingModeType()
{
  return mkConstInternal<TypeNode, TypeConstant>(kind::TYPE_CONSTANT,
                                                 ROUNDINGMODE_TYPE);
}

TypeNode NodeManager::boundVarListType()
{
  return mkConstInternal<TypeNode, TypeConstant>(kind::TYPE_CONSTANT,
                                                 BOUND_VAR_LIST_TYPE);
}

TypeNode NodeManager::instPatternType()
{
  return mkConstInternal<TypeNode, TypeConstant>(kind::TYPE_CONSTANT,
                                                 INST_PATTERN_TYPE);
}

TypeNode NodeManager::instPatternListType()
{
  return mkConstInternal<TypeNode, TypeConstant>(kind::TYPE_CONSTANT,
                                                 INST_PATTERN_LIST_TYPE);
}

TypeNode NodeManager::builtinOperatorType()
{
  return mkConstInternal<TypeNode, TypeConstant>(kind::TYPE_CONSTANT,
                                                 BUILTIN_OPERATOR_TYPE);
}

TypeNode NodeManager::mkBitVectorType(unsigned size)
{
  return mkConstInternal<TypeNode, BitVectorSize>(kind::BITVECTOR_TYPE,
                                                  BitVectorSize(size));
}

TypeNode NodeManager::mkFiniteFieldType(const Integer& modulus)
{
  return mkConstInternal<TypeNode, FfSize>(kind::FINITE_FIELD_TYPE,
                                           FfSize(modulus));
}

TypeNode NodeManager::sExprType()
{
  return mkConstInternal<TypeNode, TypeConstant>(kind::TYPE_CONSTANT,
                                                 SEXPR_TYPE);
}

TypeNode NodeManager::mkFloatingPointType(unsigned exp, unsigned sig)
{
  return mkConstInternal<TypeNode, FloatingPointSize>(
      kind::FLOATINGPOINT_TYPE, FloatingPointSize(exp, sig));
}

TypeNode NodeManager::mkFloatingPointType(FloatingPointSize fs)
{
  return mkConstInternal<TypeNode, FloatingPointSize>(kind::FLOATINGPOINT_TYPE,
                                                      fs);
}

NodeManager::~NodeManager()
{
  // Destroy skolem and bound var manager before cleaning up attributes and
  // zombies
  d_skManager = nullptr;
  d_bvManager = nullptr;

  {
    ScopedBool dontGC(d_inReclaimZombies);
    // By this point, all SolverEngines should have been deleted, along with
    // all their attributes
    d_attrManager->deleteAllAttributes();
  }

  for (unsigned i = 0; i < unsigned(kind::LAST_KIND); ++i)
  {
    d_operators[i] = Node::null();
  }

  d_unique_vars.clear();

  TypeNode dummy;
  d_tt_cache.d_children.clear();
  d_tt_cache.d_data = dummy;
  d_rt_cache.d_children.clear();
  d_rt_cache.d_data = dummy;

  // clear the datatypes and oracles
  d_dtypes.clear();
  d_oracles.clear();

  Assert(!d_attrManager->inGarbageCollection());

  std::vector<NodeValue*> order = TopologicalSort(d_maxedOut);
  d_maxedOut.clear();

  while (!d_zombies.empty() || !order.empty())
  {
    if (d_zombies.empty())
    {
      // Delete the maxed out nodes in toplogical order once we know
      // there are no additional zombies, or other nodes to worry about.
      Assert(!order.empty());
      // We process these in reverse to reverse the topological order.
      NodeValue* greatest_maxed_out = order.back();
      order.pop_back();
      Assert(greatest_maxed_out->HasMaximizedReferenceCount());
      Trace("gc") << "Force zombify " << greatest_maxed_out << std::endl;
      greatest_maxed_out->d_rc = 0;
      markForDeletion(greatest_maxed_out);
    }
    else
    {
      reclaimZombies();
    }
  }

  poolRemove(&expr::NodeValue::null());

  if (TraceIsOn("gc:leaks"))
  {
    Trace("gc:leaks") << "still in pool:" << endl;
    for (NodeValuePool::const_iterator i = d_nodeValuePool.begin(),
                                       iend = d_nodeValuePool.end();
         i != iend;
         ++i)
    {
      Trace("gc:leaks") << "  " << *i << " id=" << (*i)->d_id
                        << " rc=" << (*i)->d_rc << " " << **i << endl;
    }
    Trace("gc:leaks") << ":end:" << endl;
  }

  // defensive coding, in case destruction-order issues pop up (they often do)
  delete d_attrManager;
  d_attrManager = NULL;
}

const DType& NodeManager::getDTypeFor(TypeNode tn) const
{
  Kind k = tn.getKind();
  if (k == kind::DATATYPE_TYPE)
  {
    size_t index = tn.getAttribute(DatatypeIndexAttr());
    return getDTypeForIndex(index);
  }
  else if (k == kind::TUPLE_TYPE)
  {
    // lookup its datatype encoding
    TypeNode dtt = getAttribute(tn, expr::TupleDatatypeAttr());
    Assert(!dtt.isNull());
    return getDTypeFor(dtt);
  }
  Assert(k == kind::PARAMETRIC_DATATYPE);
  return getDTypeFor(tn[0]);
}

const DType& NodeManager::getDTypeFor(Node n) const
{
  return getDTypeFor(TypeNode(n.d_nv));
}

const DType& NodeManager::getDTypeForIndex(size_t index) const
{
  // if this assertion fails, it is likely due to not managing datatypes
  // properly w.r.t. multiple NodeManagers.
  Assert(index < d_dtypes.size());
  return *d_dtypes[index];
}

void NodeManager::reclaimZombies()
{
  // FIXME multithreading
  Assert(!d_attrManager->inGarbageCollection());

  Trace("gc") << "reclaiming " << d_zombies.size() << " zombie(s)!\n";

  // during reclamation, reclaimZombies() is never supposed to be called
  Assert(!d_inReclaimZombies)
      << "NodeManager::reclaimZombies() not re-entrant!";

  // whether exit is normal or exceptional, the Reclaim dtor is called
  // and ensures that d_inReclaimZombies is set back to false.
  ScopedBool r(d_inReclaimZombies);

  // We copy the set away and clear the NodeManager's set of zombies.
  // This is because reclaimZombie() decrements the RC of the
  // NodeValue's children, which may (recursively) reclaim them.
  //
  // Let's say we're reclaiming zombie NodeValue "A" and its child "B"
  // then becomes a zombie (NodeManager::markForDeletion(B) is called).
  //
  // One way to handle B's zombification would be simply to put it
  // into d_zombies.  This is what we do.  However, if we were to
  // concurrently process d_zombies in the loop below, such addition
  // may be invisible to us (B is leaked) or even invalidate our
  // iterator, causing a crash.  So we need to copy the set away.

  vector<NodeValue*> zombies;
  zombies.reserve(d_zombies.size());
  remove_copy_if(d_zombies.begin(),
                 d_zombies.end(),
                 back_inserter(zombies),
                 NodeValueReferenceCountNonZero());
  d_zombies.clear();

#ifdef _LIBCPP_VERSION
  NodeValue* last = NULL;
#endif
  for (vector<NodeValue*>::iterator i = zombies.begin(); i != zombies.end();
       ++i)
  {
    NodeValue* nv = *i;
#ifdef _LIBCPP_VERSION
    // Work around an apparent bug in libc++'s hash_set<> which can
    // (very occasionally) have an element repeated.
    if (nv == last)
    {
      continue;
    }
    last = nv;
#endif

    // collect ONLY IF still zero
    if (nv->d_rc == 0)
    {
      if (TraceIsOn("gc"))
      {
        Trace("gc") << "deleting node value " << nv << " [" << nv->d_id
                    << "]: ";
        nv->printAst(Trace("gc"));
        Trace("gc") << endl;
      }

      // remove from the pool
      kind::MetaKind mk = nv->getMetaKind();
      if (mk != kind::metakind::VARIABLE
          && mk != kind::metakind::NULLARY_OPERATOR)
      {
        poolRemove(nv);
      }

      // whether exit is normal or exceptional, the NVReclaim dtor is
      // called and ensures that d_nodeUnderDeletion is set back to
      // NULL.
      NVReclaim rc(d_nodeUnderDeletion);
      d_nodeUnderDeletion = nv;

      // remove attributes
      {  // notify listeners of deleted node
        TNode n;
        n.d_nv = nv;
        nv->d_rc = 1;  // so that TNode doesn't assert-fail
        // this would mean that one of the listeners stowed away
        // a reference to this node!
        Assert(nv->d_rc == 1);
      }
      nv->d_rc = 0;
      d_attrManager->deleteAllAttributes(nv);

      // decr ref counts of children
      nv->decrRefCounts();
      if (mk == kind::metakind::CONSTANT)
      {
        // Destroy (call the destructor for) the C++ type representing
        // the constant in this NodeValue.  This is needed for
        // e.g. cvc5::internal::Rational, since it has a gmp internal
        // representation that mallocs memory and should be cleaned
        // up.  (This won't delete a pointer value if used as a
        // constant, but then, you should probably use a smart-pointer
        // type for a constant payload.)
        kind::metakind::deleteNodeValueConstant(nv);
      }
      free(nv);
    }
  }
} /* NodeManager::reclaimZombies() */

std::vector<NodeValue*> NodeManager::TopologicalSort(
    const std::vector<NodeValue*>& roots)
{
  std::vector<NodeValue*> order;
  // The stack of nodes to visit. The Boolean value is false when visiting the
  // node in preorder and true when visiting it in postorder.
  std::vector<std::pair<bool, NodeValue*> > stack;
  // Nodes that have been visited in both pre- and postorder
  NodeValueIDSet visited;
  const NodeValueIDSet root_set(roots.begin(), roots.end());

  for (size_t index = 0; index < roots.size(); index++)
  {
    NodeValue* root = roots[index];
    if (visited.find(root) == visited.end())
    {
      stack.push_back(std::make_pair(false, root));
    }
    while (!stack.empty())
    {
      NodeValue* current = stack.back().second;
      const bool visited_children = stack.back().first;
      Trace("gc") << "Topological sort " << current << " " << visited_children
                  << std::endl;
      if (visited_children)
      {
        if (root_set.find(current) != root_set.end())
        {
          order.push_back(current);
        }
        stack.pop_back();
      }
      else if (visited.find(current) == visited.end())
      {
        stack.back().first = true;
        visited.insert(current);
        for (unsigned i = 0; i < current->getNumChildren(); ++i)
        {
          expr::NodeValue* child = current->getChild(i);
          stack.push_back(std::make_pair(false, child));
        }
      }
      else
      {
        stack.pop_back();
      }
    }
  }
  Assert(order.size() == roots.size());
  return order;
} /* NodeManager::TopologicalSort() */

TypeNode NodeManager::getType(TNode n, bool check, std::ostream* errOut)
{
  TypeNode typeNode;
  TypeAttr ta;
  TypeCheckedAttr tca;
  bool hasType = getAttribute(n, ta, typeNode);
  bool needsCheck = check && !getAttribute(n, tca);
  if (hasType && !needsCheck)
  {
    return typeNode;
  }
  std::unordered_map<TNode, bool> visited;
  std::unordered_map<TNode, bool>::const_iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    // already computed (and checked, if necessary) this type
    if (!getAttribute(cur, ta).isNull() && (!check || getAttribute(cur, tca)))
    {
      continue;
    }
    it = visited.find(cur);
    // we have yet to visit children
    if (it == visited.end())
    {
      // See if it has a type inferrable at pre traversal. We only do this
      // if we are not checking, since preComputeType by design does not
      // check the children types.
      if (!check)
      {
        typeNode = TypeChecker::preComputeType(this, cur);
        if (!typeNode.isNull())
        {
          visited[cur] = true;
          setAttribute(cur, ta, typeNode);
          // note that the result of preComputeType is not cached
          continue;
        }
      }
      // we are checking, or pre-compute type is not available
      visited[cur] = false;
      visit.push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (!it->second)
    {
      visited[cur] = true;
      // children now have types assigned
      typeNode = TypeChecker::computeType(this, cur, check, errOut);
      // if null, immediately return without further caching
      if (typeNode.isNull())
      {
        return typeNode;
      }
      setAttribute(cur, ta, typeNode);
      setAttribute(cur, tca, check || getAttribute(cur, tca));
    }
  } while (!visit.empty());

  /* The type should be have been computed and stored. */
  Assert(hasAttribute(n, ta));
  /* The check should have happened, if we asked for it. */
  Assert(!check || getAttribute(n, tca));
  // should be the last type computed in the above loop
  return typeNode;
}

TypeNode NodeManager::mkBagType(TypeNode elementType)
{
  Assert(!elementType.isNull()) << "unexpected NULL element type";
  Trace("bags") << "making bags type " << elementType << std::endl;
  return mkTypeNode(kind::BAG_TYPE, elementType);
}

TypeNode NodeManager::mkSequenceType(TypeNode elementType)
{
  Assert(!elementType.isNull()) << "unexpected NULL element type";
  return mkTypeNode(kind::SEQUENCE_TYPE, elementType);
}

bool NodeManager::isSortKindAbstractable(Kind k)
{
  return k == kind::ABSTRACT_TYPE || k == kind::ARRAY_TYPE
         || k == kind::BAG_TYPE || k == kind::BITVECTOR_TYPE
         || k == kind::TUPLE_TYPE || k == kind::FINITE_FIELD_TYPE
         || k == kind::FLOATINGPOINT_TYPE || k == kind::FUNCTION_TYPE
         || k == kind::SEQUENCE_TYPE || k == kind::SET_TYPE;
}

TypeNode NodeManager::mkAbstractType(Kind k)
{
  if (!isSortKindAbstractable(k))
  {
    std::stringstream ss;
    ss << "Cannot construct abstract type for kind " << k;
    throw Exception(ss.str());
  }
  if (k == kind::ARRAY_TYPE)
  {
    // ?Array -> (Array ? ?)
    TypeNode a = mkAbstractType(kind::ABSTRACT_TYPE);
    return mkArrayType(a, a);
  }
  if (k == kind::SET_TYPE)
  {
    // ?Set -> (Set ?)
    TypeNode a = mkAbstractType(kind::ABSTRACT_TYPE);
    return mkSetType(a);
  }
  if (k == kind::BAG_TYPE)
  {
    // ?Bag -> (Bag ?)
    TypeNode a = mkAbstractType(kind::ABSTRACT_TYPE);
    return mkBagType(a);
  }
  if (k == kind::SEQUENCE_TYPE)
  {
    // ?Seq -> (Seq ?)
    TypeNode a = mkAbstractType(kind::ABSTRACT_TYPE);
    return mkSequenceType(a);
  }
  return mkConstInternal<TypeNode, AbstractType>(kind::ABSTRACT_TYPE,
                                                 AbstractType(k));
}

TypeNode NodeManager::mkDatatypeType(DType& datatype)
{
  // Not worth a special implementation; this doesn't need to be fast
  // code anyway.
  std::vector<DType> datatypes;
  datatypes.push_back(datatype);
  std::vector<TypeNode> result = mkMutualDatatypeTypes(datatypes);
  Assert(result.size() == 1);
  return result.front();
}

std::vector<TypeNode> NodeManager::mkMutualDatatypeTypes(
    const std::vector<DType>& datatypes)
{
  std::set<TypeNode> unresolvedTypes;
  // scan the list of datatypes to find unresolved datatypes
  for (const DType& dt : datatypes)
  {
    dt.collectUnresolvedDatatypeTypes(unresolvedTypes);
  }
  return mkMutualDatatypeTypesInternal(datatypes, unresolvedTypes);
}

std::vector<TypeNode> NodeManager::mkMutualDatatypeTypesInternal(
    const std::vector<DType>& datatypes,
    const std::set<TypeNode>& unresolvedTypes)
{
  std::map<std::string, TypeNode> nameResolutions;
  std::vector<TypeNode> dtts;

  // First do some sanity checks, set up the final Type to be used for
  // each datatype, and set up the "named resolutions" used to handle
  // simple self- and mutual-recursion, for example in the definition
  // "nat = succ(pred:nat) | zero", a named resolution can handle the
  // pred selector.
  DatatypeIndexAttr dia;
  for (const DType& dt : datatypes)
  {
    Assert(!dt.isResolved()) << "datatype is already resolved";
    uint32_t index = d_dtypes.size();
    d_dtypes.push_back(std::unique_ptr<DType>(new DType(dt)));
    DType* dtp = d_dtypes.back().get();

    NodeBuilder dtnb(this, kind::DATATYPE_TYPE);
    TypeNode typeNode = dtnb.constructTypeNode();
    typeNode.setAttribute(dia, index);
    if (dtp->getNumParameters() == 0)
    {
      // if the datatype is a tuple, the type will be (TUPLE_TYPE ...)
      if (dt.isTuple())
      {
        TypeNode dtt = typeNode;
        const DTypeConstructor& dc = dt[0];
        std::vector<TypeNode> tupleTypes;
        for (size_t i = 0, nargs = dc.getNumArgs(); i < nargs; i++)
        {
          // selector should be initialized to the range type, it is not null
          // or unresolved since tuples are not recursive
          tupleTypes.push_back(dc[i].getType());
        }
        // Set its datatype representation
        typeNode = mkTypeNode(kind::TUPLE_TYPE, tupleTypes);
        typeNode.setAttribute(expr::TupleDatatypeAttr(), dtt);
      }
    }
    else
    {
      TypeNode cons = typeNode;
      std::vector<TypeNode> params;
      params.push_back(cons);
      for (uint32_t ip = 0; ip < dtp->getNumParameters(); ++ip)
      {
        params.push_back(dtp->getParameter(ip));
      }
      typeNode = mkTypeNode(kind::PARAMETRIC_DATATYPE, params);
    }
    if (nameResolutions.find(dtp->getName()) != nameResolutions.end())
    {
      std::stringstream ss;
      ss << "cannot construct two datatypes at the same time with the same "
            "name ("
         << dtp->getName() << ")";
      throw Exception(ss.str());
    }
    nameResolutions.insert(std::make_pair(dtp->getName(), typeNode));
    dtts.push_back(typeNode);
  }

  // Second, set up the type substitution map for complex type
  // resolution (e.g. if "list" is the type we're defining, and it has
  // a selector of type "ARRAY INT OF list", this can't be taken care
  // of using the named resolutions that we set up above.  A
  // preliminary array type was set up, and now needs to have "list"
  // substituted in it for the correct type.
  //
  // @TODO get rid of named resolutions altogether and handle
  // everything with these resolutions?
  std::vector<TypeNode> paramTypes;
  std::vector<TypeNode> paramReplacements;
  std::vector<TypeNode> placeholders;  // to hold the "unresolved placeholders"
  std::vector<TypeNode> replacements;  // to hold our final, resolved types
  for (const TypeNode& ut : unresolvedTypes)
  {
    std::string name = ut.getName();
    std::map<std::string, TypeNode>::const_iterator resolver =
        nameResolutions.find(name);
    if (resolver == nameResolutions.end())
    {
      throw Exception("cannot resolve type " + name
                      + "; it's not among the datatypes being defined");
    }
    // We will instruct the Datatype to substitute "ut" (the
    // unresolved SortType used as a placeholder in complex types)
    // with "(*resolver).second" (the TypeNode we created in the
    // first step, above).
    if (ut.isUninterpretedSort())
    {
      placeholders.push_back(ut);
      replacements.push_back((*resolver).second);
    }
    else
    {
      Assert(ut.isUninterpretedSortConstructor());
      paramTypes.push_back(ut);
      paramReplacements.push_back((*resolver).second);
    }
  }

  // Lastly, perform the final resolutions and checks.
  for (const TypeNode& ut : dtts)
  {
    const DType& dt = ut.getDType();
    if (!dt.isResolved())
    {
      const_cast<DType&>(dt).resolve(nameResolutions,
                                     placeholders,
                                     replacements,
                                     paramTypes,
                                     paramReplacements);
    }
    // Check the datatype has been resolved properly.
    for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      const DTypeConstructor& c = dt[i];
      TypeNode testerType CVC5_UNUSED = c.getTester().getType();
      Assert(c.isResolved()) << "constructor not resolved";
      Assert(testerType.isDatatypeTester())
          << "malformed tester in datatype post-resolution";
      Assert(testerType[0] == ut)
          << "mismatched tester in datatype post-resolution";
      TypeNode ctorType CVC5_UNUSED = c.getConstructor().getType();
      Assert(ctorType.isDatatypeConstructor()
             && ctorType.getNumChildren() == c.getNumArgs() + 1
             && ctorType.getRangeType() == ut)
          << "malformed constructor in datatype post-resolution";
      // for all selectors...
      for (size_t j = 0, nargs = c.getNumArgs(); j < nargs; j++)
      {
        const DTypeSelector& a = c[j];
        TypeNode selectorType = a.getType();
        Assert(a.isResolved() && selectorType.isDatatypeSelector()
               && selectorType[0] == ut)
            << "malformed selector in datatype post-resolution";
        // This next one's a "hard" check, performed in non-debug builds
        // as well; the other ones should all be guaranteed by the
        // cvc5::internal::DType class, but this actually needs to be checked.
        if (!selectorType.getRangeType().isFirstClass())
        {
          throw Exception(
              "cannot use fields in datatypes that are not first class types");
        }
      }
    }
  }

  return dtts;
}

TypeNode NodeManager::mkConstructorType(const std::vector<TypeNode>& args,
                                        TypeNode range)
{
  std::vector<TypeNode> sorts = args;
  sorts.push_back(range);
  return mkTypeNode(kind::CONSTRUCTOR_TYPE, sorts);
}

TypeNode NodeManager::mkSelectorType(TypeNode domain, TypeNode range)
{
  Assert(domain.isDatatype()) << "cannot create non-datatype selector type";
  return mkTypeNode(kind::SELECTOR_TYPE, domain, range);
}

TypeNode NodeManager::mkTesterType(TypeNode domain)
{
  Assert(domain.isDatatype()) << "cannot create non-datatype tester";
  return mkTypeNode(kind::TESTER_TYPE, domain);
}

TypeNode NodeManager::mkDatatypeUpdateType(TypeNode domain, TypeNode range)
{
  Assert(domain.isDatatype()) << "cannot create non-datatype updater type";
  // It is a function type domain x range -> domain, we store only the
  // arguments
  return mkTypeNode(kind::UPDATER_TYPE, domain, range);
}

TypeNode NodeManager::TupleTypeCache::getTupleType(
    NodeManager* nm, const std::vector<TypeNode>& types, unsigned index)
{
  if (index == types.size())
  {
    if (d_data.isNull())
    {
      std::stringstream sst;
      sst << "__cvc5_tuple";
      size_t ntypes = types.size();
      for (size_t i = 0; i < ntypes; ++i)
      {
        sst << "_" << types[i];
      }
      DType dt(sst.str());
      dt.setTuple();
      std::stringstream ssc;
      ssc << sst.str() << "_ctor";
      std::shared_ptr<DTypeConstructor> c =
          std::make_shared<DTypeConstructor>(ssc.str());
      for (size_t i = 0; i < ntypes; ++i)
      {
        std::stringstream ss;
        ss << sst.str() << "_stor_" << i;
        c->addArg(ss.str().c_str(), types[i]);
      }
      dt.addConstructor(c);
      d_data = nm->mkDatatypeType(dt);
      Assert(d_data.isTuple());
      Trace("tuprec-debug") << "Return type : " << d_data << std::endl;
    }
    return d_data;
  }
  else
  {
    return d_children[types[index]].getTupleType(nm, types, index + 1);
  }
}

TypeNode NodeManager::RecTypeCache::getRecordType(NodeManager* nm,
                                                  const Record& rec,
                                                  unsigned index)
{
  if (index == rec.size())
  {
    if (d_data.isNull())
    {
      std::stringstream sst;
      sst << "__cvc5_record";
      for (const std::pair<std::string, TypeNode>& i : rec)
      {
        sst << "_" << i.first << "_" << i.second;
      }
      DType dt(sst.str());
      dt.setRecord();
      std::stringstream ssc;
      ssc << sst.str() << "_ctor";
      std::shared_ptr<DTypeConstructor> c =
          std::make_shared<DTypeConstructor>(ssc.str());
      for (const std::pair<std::string, TypeNode>& i : rec)
      {
        c->addArg(i.first, i.second);
      }
      dt.addConstructor(c);
      d_data = nm->mkDatatypeType(dt);
      Assert(d_data.isRecord());
      Trace("tuprec-debug") << "Return type : " << d_data << std::endl;
    }
    return d_data;
  }
  return d_children[rec[index].second][rec[index].first].getRecordType(
      nm, rec, index + 1);
}

TypeNode NodeManager::mkFunctionType(const std::vector<TypeNode>& sorts)
{
  Assert(sorts.size() >= 2);
  return mkTypeNode(kind::FUNCTION_TYPE, sorts);
}

TypeNode NodeManager::mkPredicateType(const std::vector<TypeNode>& sorts)
{
  Assert(sorts.size() >= 1);
  std::vector<TypeNode> sortNodes;
  sortNodes.insert(sortNodes.end(), sorts.begin(), sorts.end());
  sortNodes.push_back(booleanType());
  return mkFunctionType(sortNodes);
}

TypeNode NodeManager::mkFunctionType(const TypeNode& domain,
                                     const TypeNode& range)
{
  std::vector<TypeNode> sorts;
  sorts.push_back(domain);
  sorts.push_back(range);
  return mkFunctionType(sorts);
}

TypeNode NodeManager::mkFunctionType(const std::vector<TypeNode>& argTypes,
                                     const TypeNode& range)
{
  Assert(argTypes.size() >= 1);
  std::vector<TypeNode> sorts(argTypes);
  sorts.push_back(range);
  return mkFunctionType(sorts);
}

TypeNode NodeManager::mkTupleType(const std::vector<TypeNode>& types)
{
  return d_tt_cache.getTupleType(this, types);
}

TypeNode NodeManager::mkRecordType(const Record& rec)
{
  return d_rt_cache.getRecordType(this, rec);
}

TypeNode NodeManager::mkSort()
{
  NodeBuilder nb(this, kind::SORT_TYPE);
  return nb.constructTypeNode();
}

TypeNode NodeManager::mkSort(const std::string& name)
{
  NodeBuilder nb(this, kind::SORT_TYPE);
  TypeNode tn = nb.constructTypeNode();
  setAttribute(tn, expr::VarNameAttr(), name);
  return tn;
}

TypeNode NodeManager::mkSort(TypeNode constructor,
                             const std::vector<TypeNode>& children)
{
  Assert(constructor.getKind() == kind::SORT_TYPE
         && constructor.getNumChildren() == 0)
      << "expected a sort constructor";
  Assert(children.size() > 0) << "expected non-zero # of children";
  Assert(hasAttribute(constructor.d_nv, expr::SortArityAttr())
         && hasAttribute(constructor.d_nv, expr::VarNameAttr()))
      << "expected a sort constructor";
  Assert(getAttribute(constructor.d_nv, expr::SortArityAttr())
         == children.size())
      << "arity mismatch in application of sort constructor";
  NodeBuilder nb(this, kind::INSTANTIATED_SORT_TYPE);
  nb << constructor;
  nb.append(children);
  return nb.constructTypeNode();
}

TypeNode NodeManager::mkSortConstructor(const std::string& name, size_t arity)
{
  Assert(arity > 0);
  NodeBuilder nb(this, kind::SORT_TYPE);
  TypeNode type = nb.constructTypeNode();
  setAttribute(type, expr::VarNameAttr(), name);
  setAttribute(type, expr::SortArityAttr(), arity);
  return type;
}

TypeNode NodeManager::mkUnresolvedDatatypeSort(const std::string& name,
                                               size_t arity)
{
  TypeNode usort = arity > 0 ? mkSortConstructor(name, arity) : mkSort(name);
  // mark that it is an unresolved sort
  setAttribute(usort, expr::UnresolvedDatatypeAttr(), true);
  return usort;
}

Node NodeManager::mkOracle(Oracle& o)
{
  Node n = NodeBuilder(this, kind::ORACLE);
  n.setAttribute(TypeAttr(), builtinOperatorType());
  n.setAttribute(TypeCheckedAttr(), true);
  n.setAttribute(OracleIndexAttr(), d_oracles.size());
  // we allocate a new oracle, to take ownership
  d_oracles.push_back(std::unique_ptr<Oracle>(new Oracle(o.getFunction())));
  return n;
}

const Oracle& NodeManager::getOracleFor(const Node& n) const
{
  Assert(n.getKind() == kind::ORACLE);
  size_t index = n.getAttribute(OracleIndexAttr());
  Assert(index < d_oracles.size());
  return *d_oracles[index];
}

Node NodeManager::mkVar(const std::string& name, const TypeNode& type)
{
  Node n = NodeBuilder(this, kind::VARIABLE);
  setAttribute(n, TypeAttr(), type);
  setAttribute(n, TypeCheckedAttr(), true);
  setAttribute(n, expr::VarNameAttr(), name);
  return n;
}

Node NodeManager::mkBoundVar(const std::string& name, const TypeNode& type)
{
  Node n = mkBoundVar(type);
  setAttribute(n, expr::VarNameAttr(), name);
  return n;
}

Node NodeManager::getBoundVarListForFunctionType(TypeNode tn)
{
  Assert(tn.isFunction());
  Node bvl = tn.getAttribute(LambdaBoundVarListAttr());
  if (bvl.isNull())
  {
    std::vector<Node> vars;
    for (unsigned i = 0; i < tn.getNumChildren() - 1; i++)
    {
      vars.push_back(mkBoundVar(tn[i]));
    }
    bvl = mkNode(kind::BOUND_VAR_LIST, vars);
    Trace("functions") << "Make standard bound var list " << bvl << " for "
                       << tn << std::endl;
    tn.setAttribute(LambdaBoundVarListAttr(), bvl);
  }
  return bvl;
}

Node NodeManager::mkAssociative(Kind kind, const std::vector<Node>& children)
{
  AlwaysAssert(kind::isAssociative(kind)) << "Illegal kind in mkAssociative";

  const unsigned int max = kind::metakind::getMaxArityForKind(kind);
  size_t numChildren = children.size();

  /* If the number of children is within bounds, then there's nothing to do. */
  if (numChildren <= max)
  {
    return mkNode(kind, children);
  }
  const unsigned int min = kind::metakind::getMinArityForKind(kind);

  std::vector<Node>::const_iterator it = children.begin();
  std::vector<Node>::const_iterator end = children.end();

  /* The new top-level children and the children of each sub node */
  std::vector<Node> newChildren;
  std::vector<Node> subChildren;

  while (it != end && numChildren > max)
  {
    /* Grab the next max children and make a node for them. */
    for (std::vector<Node>::const_iterator next = it + max; it != next;
         ++it, --numChildren)
    {
      subChildren.push_back(*it);
    }
    Node subNode = mkNode(kind, subChildren);
    newChildren.push_back(subNode);

    subChildren.clear();
  }

  // add the leftover children
  if (numChildren > 0)
  {
    for (; it != end; ++it)
    {
      newChildren.push_back(*it);
    }
  }

  /* It would be really weird if this happened (it would require
   * min > 2, for one thing), but let's make sure. */
  AlwaysAssert(newChildren.size() >= min)
      << "Too few new children in mkAssociative";

  // recurse
  return mkAssociative(kind, newChildren);
}

Node NodeManager::mkLeftAssociative(Kind kind,
                                    const std::vector<Node>& children)
{
  Node n = children[0];
  for (size_t i = 1, size = children.size(); i < size; i++)
  {
    n = mkNode(kind, n, children[i]);
  }
  return n;
}

Node NodeManager::mkRightAssociative(Kind kind,
                                     const std::vector<Node>& children)
{
  Node n = children[children.size() - 1];
  for (size_t i = children.size() - 1; i > 0;)
  {
    n = mkNode(kind, children[--i], n);
  }
  return n;
}

Node NodeManager::mkChain(Kind kind, const std::vector<Node>& children)
{
  if (children.size() == 2)
  {
    // if this is the case exactly 1 pair will be generated so the
    // AND is not required
    return mkNode(kind, children[0], children[1]);
  }
  std::vector<Node> cchildren;
  for (size_t i = 0, nargsmo = children.size() - 1; i < nargsmo; i++)
  {
    cchildren.push_back(mkNode(kind, children[i], children[i + 1]));
  }
  return mkNode(kind::AND, cchildren);
}

Node NodeManager::mkVar(const TypeNode& type)
{
  Node n = NodeBuilder(this, kind::VARIABLE);
  setAttribute(n, TypeAttr(), type);
  setAttribute(n, TypeCheckedAttr(), true);
  return n;
}

Node NodeManager::mkBoundVar(const TypeNode& type)
{
  Node n = NodeBuilder(this, kind::BOUND_VARIABLE);
  setAttribute(n, TypeAttr(), type);
  setAttribute(n, TypeCheckedAttr(), true);
  return n;
}

Node NodeManager::mkInstConstant(const TypeNode& type)
{
  Node n = NodeBuilder(this, kind::INST_CONSTANT);
  n.setAttribute(TypeAttr(), type);
  n.setAttribute(TypeCheckedAttr(), true);
  return n;
}

Node NodeManager::mkRawSymbol(const std::string& name, const TypeNode& type)
{
  Node n = NodeBuilder(this, kind::RAW_SYMBOL);
  n.setAttribute(TypeAttr(), type);
  n.setAttribute(TypeCheckedAttr(), true);
  setAttribute(n, expr::VarNameAttr(), name);
  return n;
}

Node NodeManager::mkNullaryOperator(const TypeNode& type, Kind k)
{
  std::map<TypeNode, Node>::iterator it = d_unique_vars[k].find(type);
  if (it == d_unique_vars[k].end())
  {
    Node n = NodeBuilder(this, k).constructNode();
    setAttribute(n, TypeAttr(), type);
    // setAttribute(n, TypeCheckedAttr(), true);
    d_unique_vars[k][type] = n;
    Assert(n.getMetaKind() == kind::metakind::NULLARY_OPERATOR);
    return n;
  }
  else
  {
    return it->second;
  }
}

bool NodeManager::hasOperator(Kind k)
{
  switch (kind::MetaKind mk = kind::metaKindOf(k))
  {
    case kind::metakind::INVALID:
    case kind::metakind::VARIABLE:
    case kind::metakind::NULLARY_OPERATOR: return false;

    case kind::metakind::OPERATOR:
    case kind::metakind::PARAMETERIZED: return true;

    case kind::metakind::CONSTANT: return false;

    default: Unhandled() << mk;
  }
}

TNode NodeManager::operatorOf(Kind k)
{
  AssertArgument(kind::metaKindOf(k) == kind::metakind::OPERATOR,
                 k,
                 "Kind is not an OPERATOR-kinded kind "
                 "in NodeManager::operatorOf()");
  return d_operators[k];
}

template <class NodeClass, class T>
NodeClass NodeManager::mkConstInternal(Kind k, const T& val)
{
  NVStorage<1> nvStorage;
  expr::NodeValue& nvStack = reinterpret_cast<expr::NodeValue&>(nvStorage);

  nvStack.d_id = 0;
  nvStack.d_kind = k;
  nvStack.d_rc = 0;
  nvStack.d_nchildren = 1;

#if defined(__GNUC__) \
    && (__GNUC__ > 4 || (__GNUC__ == 4 && __GNUC_MINOR__ >= 6))
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Warray-bounds"
#pragma GCC diagnostic ignored "-Wzero-length-bounds"
#endif

  nvStack.d_children[0] = const_cast<expr::NodeValue*>(
      reinterpret_cast<const expr::NodeValue*>(&val));
  expr::NodeValue* nv = poolLookup(&nvStack);

#if defined(__GNUC__) \
    && (__GNUC__ > 4 || (__GNUC__ == 4 && __GNUC_MINOR__ >= 6))
#pragma GCC diagnostic pop
#endif

  if (nv != NULL)
  {
    return NodeClass(nv);
  }

  nv = (expr::NodeValue*)std::malloc(sizeof(expr::NodeValue) + sizeof(T));
  if (nv == NULL)
  {
    throw std::bad_alloc();
  }

  nv->d_nchildren = 0;
  nv->d_kind = k;
  nv->d_id = d_nextId++;
  nv->d_rc = 0;

  new (&nv->d_children) T(val);

  poolInsert(nv);
  if (TraceIsOn("gc"))
  {
    Trace("gc") << "creating node value " << nv << " [" << nv->d_id << "]: ";
    nv->printAst(Trace("gc"));
    Trace("gc") << std::endl;
  }

  return NodeClass(nv);
}

Node NodeManager::mkGroundTerm(const TypeNode& tn)
{
  return kind::mkGroundTerm(tn);
}

Node NodeManager::mkGroundValue(const TypeNode& tn)
{
  theory::TypeEnumerator te(tn);
  return *te;
}

bool NodeManager::safeToReclaimZombies() const
{
  // FIXME multithreading
  return !d_inReclaimZombies && !d_attrManager->inGarbageCollection();
}

void NodeManager::deleteAttributes(
    const std::vector<const expr::attr::AttributeUniqueId*>& ids)
{
  d_attrManager->deleteAttributes(ids);
}

Kind NodeManager::getKindForFunction(TNode fun)
{
  TypeNode tn = fun.getType();
  if (tn.isFunction())
  {
    return kind::APPLY_UF;
  }
  else if (tn.isDatatypeConstructor())
  {
    return kind::APPLY_CONSTRUCTOR;
  }
  else if (tn.isDatatypeSelector())
  {
    return kind::APPLY_SELECTOR;
  }
  else if (tn.isDatatypeTester())
  {
    return kind::APPLY_TESTER;
  }
  else if (tn.isDatatypeUpdater())
  {
    return kind::APPLY_UPDATER;
  }
  return kind::UNDEFINED_KIND;
}

Node NodeManager::mkNode(Kind kind, std::initializer_list<TNode> children)
{
  NodeBuilder nb(this, kind);
  nb.append(children.begin(), children.end());
  return nb.constructNode();
}

Node NodeManager::mkNode(TNode opNode, std::initializer_list<TNode> children)
{
  NodeBuilder nb(this, operatorToKind(opNode));
  if (opNode.getKind() != kind::BUILTIN)
  {
    nb << opNode;
  }
  nb.append(children.begin(), children.end());
  return nb.constructNode();
}

Node NodeManager::mkConstReal(const Rational& r)
{
  // works with (r.isIntegral() ? kind::CONST_INTEGER : kind::CONST_RATIONAL)
  return mkConst(kind::CONST_RATIONAL, r);
}

Node NodeManager::mkConstInt(const Rational& r)
{
  Assert(r.isIntegral());
  return mkConst(kind::CONST_INTEGER, r);
}

Node NodeManager::mkConstRealOrInt(const Rational& r)
{
  if (r.isIntegral())
  {
    return mkConstInt(r);
  }
  return mkConstReal(r);
}

Node NodeManager::mkConstRealOrInt(const TypeNode& tn, const Rational& r)
{
  Assert(tn.isRealOrInt()) << "Expected real or int for mkConstRealOrInt, got "
                           << tn;
  if (tn.isInteger())
  {
    return mkConstInt(r);
  }
  return mkConstReal(r);
}

Node NodeManager::mkRealAlgebraicNumber(const RealAlgebraicNumber& ran)
{
  if (ran.isRational())
  {
    // may generate an integer it is it integral
    return mkConstRealOrInt(ran.toRational());
  }
  // Creating this node may refine the ran to the point where isRational returns
  // true
  Node inner = mkConst(Kind::REAL_ALGEBRAIC_NUMBER_OP, ran);

  // Keep doing this until it either is rational or we have a fixed point.
  while (true)
  {
    const RealAlgebraicNumber& cur = inner.getConst<RealAlgebraicNumber>();
    if (cur.isRational())
    {
      // may generate an integer it is it integral
      return mkConstRealOrInt(cur.toRational());
    }
    if (cur == ran) break;
    inner = mkConst(Kind::REAL_ALGEBRAIC_NUMBER_OP, cur);
  }
  return mkNode(Kind::REAL_ALGEBRAIC_NUMBER, inner);
}

}  // namespace cvc5::internal

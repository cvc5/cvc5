/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Clark Barrett, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of theory model buidler class.
 */
#include "theory/theory_model_builder.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "smt/env.h"
#include "theory/rewriter.h"
#include "theory/uf/function_const.h"
#include "theory/uf/theory_uf_model.h"
#include "util/uninterpreted_sort_value.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {

TheoryEngineModelBuilder::TheoryEngineModelBuilder(Env& env) : EnvObj(env) {}

void TheoryEngineModelBuilder::Assigner::initialize(
    TypeNode tn, TypeEnumeratorProperties* tep, const std::vector<Node>& aes)
{
  d_te.reset(new TypeEnumerator(tn, tep));
  d_assignExcSet.insert(d_assignExcSet.end(), aes.begin(), aes.end());
}

Node TheoryEngineModelBuilder::Assigner::getNextAssignment()
{
  Assert(d_te != nullptr);
  Node n;
  bool success = false;
  TypeEnumerator& te = *d_te;
  // Check if we have run out of elements. This should never happen; if it
  // does we assert false and return null.
  if (te.isFinished())
  {
    Assert(false);
    return Node::null();
  }
  // must increment until we find one that is not in the assignment
  // exclusion set
  do
  {
    n = *te;
    success = std::find(d_assignExcSet.begin(), d_assignExcSet.end(), n)
              == d_assignExcSet.end();
    // increment regardless of fail or succeed, to set up the next value
    ++te;
  } while (!success);
  return n;
}

Node TheoryEngineModelBuilder::evaluateEqc(TheoryModel* m, TNode r)
{
  eq::EqClassIterator eqc_i = eq::EqClassIterator(r, m->d_equalityEngine);
  for (; !eqc_i.isFinished(); ++eqc_i)
  {
    Node n = *eqc_i;
    Trace("model-builder-debug") << "Look at term : " << n << std::endl;
    if (!isAssignable(n))
    {
      Trace("model-builder-debug") << "...try to normalize" << std::endl;
      Node normalized = normalize(m, n, true);
      Trace("model-builder-debug")
          << "...return " << normalized
          << ", isValue=" << m->isValue(normalized) << std::endl;
      if (m->isValue(normalized))
      {
        return normalized;
      }
    }
  }
  return Node::null();
}

bool TheoryEngineModelBuilder::isAssignerActive(TheoryModel* tm, Assigner& a)
{
  if (a.d_isActive)
  {
    return true;
  }
  std::vector<Node>& eset = a.d_assignExcSet;
  std::map<Node, Node>::iterator it;
  for (unsigned i = 0, size = eset.size(); i < size; i++)
  {
    // Members of exclusion set must have values, otherwise we are not yet
    // assignable.
    Node er = eset[i];
    if (tm->isValue(er))
    {
      // already processed
      continue;
    }
    // Assignable members of assignment exclusion set should be representatives
    // of their equivalence classes. This ensures we look up the constant
    // representatives for assignable members of assignment exclusion sets.
    Assert(er == tm->getRepresentative(er));
    it = d_constantReps.find(er);
    if (it == d_constantReps.end())
    {
      Trace("model-build-aes")
          << "isAssignerActive: not active due to " << er << std::endl;
      return false;
    }
    // update
    eset[i] = it->second;
  }
  Trace("model-build-aes") << "isAssignerActive: active!" << std::endl;
  a.d_isActive = true;
  return true;
}

bool TheoryEngineModelBuilder::isAssignable(TNode n)
{
  if (n.getKind() == kind::SELECT || n.getKind() == kind::APPLY_SELECTOR
      || n.getKind() == kind::SEQ_NTH)
  {
    // selectors are always assignable (where we guarantee that they are not
    // evaluatable here)
    if (!logicInfo().isHigherOrder())
    {
      Assert(!n.getType().isFunction());
      return true;
    }
    else
    {
      // might be a function field
      return !n.getType().isFunction();
    }
  }
  else if (n.getKind() == kind::FLOATINGPOINT_COMPONENT_SIGN)
  {
    // Extracting the sign of a floating-point number acts similar to a
    // selector on a datatype, i.e. if `(sign x)` wasn't assigned a value, we
    // can pick an arbitrary one. Note that the other components of a
    // floating-point number should always be assigned a value.
    return true;
  }
  else
  {
    // non-function variables, and fully applied functions
    if (!logicInfo().isHigherOrder())
    {
      // no functions exist, all functions are fully applied
      Assert(n.getKind() != kind::HO_APPLY);
      Assert(!n.getType().isFunction());
      return n.isVar() || n.getKind() == kind::APPLY_UF;
    }
    else
    {
      // Assert( n.getKind() != kind::APPLY_UF );
      return (n.isVar() && !n.getType().isFunction())
             || n.getKind() == kind::APPLY_UF
             || (n.getKind() == kind::HO_APPLY
                 && n[0].getType().getNumChildren() == 2);
    }
  }
}

void TheoryEngineModelBuilder::addAssignableSubterms(TNode n,
                                                     TheoryModel* tm,
                                                     NodeSet& cache)
{
  if (n.isClosure())
  {
    return;
  }
  if (cache.find(n) != cache.end())
  {
    return;
  }
  if (isAssignable(n))
  {
    tm->d_equalityEngine->addTerm(n);
  }
  for (TNode::iterator child_it = n.begin(); child_it != n.end(); ++child_it)
  {
    addAssignableSubterms(*child_it, tm, cache);
  }
  cache.insert(n);
}

void TheoryEngineModelBuilder::assignConstantRep(TheoryModel* tm,
                                                 Node eqc,
                                                 Node constRep)
{
  d_constantReps[eqc] = constRep;
  Trace("model-builder") << "    Assign: Setting constant rep of " << eqc
                         << " to " << constRep << endl;
  tm->d_rep_set.setTermForRepresentative(constRep, eqc);
}

bool TheoryEngineModelBuilder::isExcludedCdtValue(
    Node val,
    std::set<Node>* repSet,
    std::map<Node, Node>& assertedReps,
    Node eqc)
{
  Trace("model-builder-debug")
      << "Is " << val << " and excluded codatatype value for " << eqc << "? "
      << std::endl;
  for (set<Node>::iterator i = repSet->begin(); i != repSet->end(); ++i)
  {
    Assert(assertedReps.find(*i) != assertedReps.end());
    Node rep = assertedReps[*i];
    Trace("model-builder-debug") << "  Rep : " << rep << std::endl;
    // check whether it is possible that rep will be assigned the same value
    // as val.
    if (isCdtValueMatch(val, rep))
    {
      return true;
    }
  }
  return false;
}

bool TheoryEngineModelBuilder::isCdtValueMatch(Node v, Node r)
{
  if (r == v)
  {
    // values equal match trivially
    return true;
  }
  else if (v.isConst() && r.isConst())
  {
    // distinct constant values do not match
    return false;
  }
  else if (r.getKind() == kind::APPLY_CONSTRUCTOR)
  {
    if (v.getKind() != kind::APPLY_CONSTRUCTOR)
    {
      Assert(v.getKind() == kind::CODATATYPE_BOUND_VARIABLE);
      // v is the position of a loop. It may be possible to match, we return
      // true, which is an over-approximation of when it is unsafe to use v.
      return true;
    }
    if (v.getOperator() == r.getOperator())
    {
      for (size_t i = 0, nchild = v.getNumChildren(); i < nchild; i++)
      {
        if (!isCdtValueMatch(v[i], r[i]))
        {
          // if one child fails to match, we cannot match
          return false;
        }
      }
      return true;
    }
    // operators do not match
    return false;
  }
  else if (v.getKind() == kind::APPLY_CONSTRUCTOR)
  {
    // v has a constructor in a position that we have yet to fill in r.
    // we are either a finite type in which case this subfield of r can be
    // assigned a default value (or otherwise would have been split on).
    // otherwise we are an infinite type and the subfield of r will be
    // chosen not to clash with the subfield of v.
    return false;
  }
  return true;
}

bool TheoryEngineModelBuilder::involvesUSort(TypeNode tn) const
{
  if (tn.isUninterpretedSort())
  {
    return true;
  }
  else if (tn.isArray())
  {
    return involvesUSort(tn.getArrayIndexType())
           || involvesUSort(tn.getArrayConstituentType());
  }
  else if (tn.isSet())
  {
    return involvesUSort(tn.getSetElementType());
  }
  else if (tn.isDatatype())
  {
    const DType& dt = tn.getDType();
    return dt.involvesUninterpretedType();
  }
  else
  {
    return false;
  }
}

bool TheoryEngineModelBuilder::isExcludedUSortValue(
    std::map<TypeNode, unsigned>& eqc_usort_count,
    Node v,
    std::map<Node, bool>& visited)
{
  Assert(v.isConst());
  if (visited.find(v) == visited.end())
  {
    visited[v] = true;
    TypeNode tn = v.getType();
    if (tn.isUninterpretedSort())
    {
      Trace("model-builder-debug") << "Is excluded usort value : " << v << " "
                                   << tn << std::endl;
      unsigned card = eqc_usort_count[tn];
      Trace("model-builder-debug") << "  Cardinality is " << card << std::endl;
      unsigned index =
          v.getConst<UninterpretedSortValue>().getIndex().toUnsignedInt();
      Trace("model-builder-debug") << "  Index is " << index << std::endl;
      return index > 0 && index >= card;
    }
    for (unsigned i = 0; i < v.getNumChildren(); i++)
    {
      if (isExcludedUSortValue(eqc_usort_count, v[i], visited))
      {
        return true;
      }
    }
  }
  return false;
}

void TheoryEngineModelBuilder::addToTypeList(
    TypeNode tn,
    std::vector<TypeNode>& type_list,
    std::unordered_set<TypeNode>& visiting)
{
  if (std::find(type_list.begin(), type_list.end(), tn) == type_list.end())
  {
    if (visiting.find(tn) == visiting.end())
    {
      visiting.insert(tn);
      /* This must make a recursive call on all types that are subterms of
       * values of the current type.
       * Note that recursive traversal here is over enumerated expressions
       * (very low expression depth). */
      if (tn.isArray())
      {
        addToTypeList(tn.getArrayIndexType(), type_list, visiting);
        addToTypeList(tn.getArrayConstituentType(), type_list, visiting);
      }
      else if (tn.isSet())
      {
        addToTypeList(tn.getSetElementType(), type_list, visiting);
      }
      else if (tn.isDatatype())
      {
        const DType& dt = tn.getDType();
        for (unsigned i = 0; i < dt.getNumConstructors(); i++)
        {
          for (unsigned j = 0; j < dt[i].getNumArgs(); j++)
          {
            TypeNode ctn = dt[i][j].getRangeType();
            addToTypeList(ctn, type_list, visiting);
          }
        }
      }
      Assert(std::find(type_list.begin(), type_list.end(), tn)
             == type_list.end());
      type_list.push_back(tn);
    }
  }
}

bool TheoryEngineModelBuilder::buildModel(TheoryModel* tm)
{
  Trace("model-builder") << "TheoryEngineModelBuilder: buildModel" << std::endl;

  Trace("model-builder")
      << "TheoryEngineModelBuilder: Preprocess build model..." << std::endl;
  // model-builder specific initialization
  if (!preProcessBuildModel(tm))
  {
    Trace("model-builder")
        << "TheoryEngineModelBuilder: fail preprocess build model."
        << std::endl;
    return false;
  }

  Trace("model-builder")
      << "TheoryEngineModelBuilder: Add assignable subterms "
         ", collect representatives and compute assignable information..."
      << std::endl;

  // type enumerator properties
  bool tepFixUSortCard = options().quantifiers.finiteModelFind;
  uint32_t tepStrAlphaCard = options().strings.stringsAlphaCard;
  TypeEnumeratorProperties tep(tepFixUSortCard, tepStrAlphaCard);

  // In the first step of model building, we do a traversal of the
  // equality engine and record the information in the following:

  // The constant representatives, per equivalence class
  d_constantReps.clear();
  // The representatives that have been asserted by theories. This includes
  // non-constant "skeletons" that have been specified by parametric theories.
  std::map<Node, Node> assertedReps;
  // A parition of the set of equivalence classes that have:
  // (1) constant representatives,
  // (2) an assigned representative specified by a theory in collectModelInfo,
  // (3) no assigned representative.
  TypeSet typeConstSet, typeRepSet, typeNoRepSet;
  // An ordered list of types, such that T1 comes before T2 if T1 is a
  // "component type" of T2, e.g. U comes before (Set U). This is only strictly
  // necessary for finite model finding + parametric types instantiated with
  // uninterpreted sorts, but is probably a good idea to do in general since it
  // leads to models with smaller term sizes. -AJR
  std::vector<TypeNode> type_list;
  // The count of equivalence classes per sort (for finite model finding).
  std::map<TypeNode, unsigned> eqc_usort_count;

  // the set of equivalence classes that are "assignable", i.e. those that have
  // an assignable expression in them (see isAssignable), and have not already
  // been assigned a constant.
  std::unordered_set<Node> assignableEqc;
  // The set of equivalence classes that are "evaluable", i.e. those that have
  // an expression in them that is not assignable, and have not already been
  // assigned a constant.
  std::unordered_set<Node> evaluableEqc;
  // Assigner objects for relevant equivalence classes that require special
  // ways of assigning values, e.g. those that take into account assignment
  // exclusion sets.
  std::map<Node, Assigner> eqcToAssigner;
  // A map from equivalence classes to the equivalence class that it shares an
  // assigner object with (all elements in the range of this map are in the
  // domain of eqcToAssigner).
  std::map<Node, Node> eqcToAssignerMaster;

  // Loop through equivalence classes of the equality engine of the model.
  eq::EqualityEngine* ee = tm->d_equalityEngine;
  NodeSet assignableCache;
  std::map<Node, Node>::iterator itm;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  // should we compute assigner objects?
  bool computeAssigners = tm->hasAssignmentExclusionSets();
  // the set of exclusion sets we have processed
  std::unordered_set<Node> processedExcSet;
  for (; !eqcs_i.isFinished(); ++eqcs_i)
  {
    Node eqc = *eqcs_i;
    Trace("model-builder") << "  Processing EQC " << eqc << std::endl;
    // Information computed for each equivalence class

    // The assigned represenative and constant representative
    Node rep, constRep;
    // is constant rep a "base model value" (see TheoryModel::isBaseModelValue)
    bool constRepBaseModelValue = false;
    // A flag set to true if the current equivalence class is assignable (see
    // assignableEqc).
    bool assignable = false;
    // Set to true if the current equivalence class is evaluatable (see
    // evaluableEqc).
    bool evaluable = false;
    // Set to true if a term in the current equivalence class has been given an
    // assignment exclusion set.
    bool hasESet CVC5_UNUSED = false;
    // Set to true if we found that a term in the current equivalence class has
    // been given an assignment exclusion set, and we have not seen this term
    // as part of a previous assignment exclusion group. In other words, when
    // this flag is true we construct a new assigner object with the current
    // equivalence class as its master.
    bool foundESet = false;
    // The assignment exclusion set for the current equivalence class.
    std::vector<Node> eset;
    // The group to which this equivalence class belongs when exclusion sets
    // were assigned (see the argument group of
    // TheoryModel::getAssignmentExclusionSet).
    std::vector<Node> esetGroup;

    // Loop through terms in this EC
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, ee);
    for (; !eqc_i.isFinished(); ++eqc_i)
    {
      Node n = *eqc_i;
      Trace("model-builder") << "    Processing Term: " << n << endl;

      // For each term n in this equivalence class, below we register its
      // assignable subterms, compute whether it is a constant or assigned
      // representative, then if we don't have a constant representative,
      // compute information regarding how we will assign values.

      // (1) Add assignable subterms, which ensures that e.g. models for
      // uninterpreted functions take into account all subterms in the
      // equality engine of the model
      addAssignableSubterms(n, tm, assignableCache);
      // model-specific processing of the term
      tm->addTermInternal(n);

      // compute whether n is assignable
      if (!isAssignable(n))
      {
        // (2) Record constant representative or assign representative, if
        // applicable. We check if n is a value here, e.g. a term for which
        // isConst returns true, or a lambda. The latter is required only for
        // higher-order.
        if (tm->isValue(n))
        {
          // In some cases, there can be multiple terms in the same equivalence
          // class are considered values, e.g., when real algebraic numbers did
          // not simplify to rational values or real.pi was used as a model
          // value. We distinguish three kinds of model values: constants,
          // non-constant base values and non-base values, and we use them in
          // this order of preference.
          // We print a trace message if there is more than one model value in
          // the same equivalence class. We throw a debug failure if there are
          // at least two base model values in the same equivalence class that
          // do not compare equal.
          bool assignConstRep = false;
          bool isBaseValue = tm->isBaseModelValue(n);
          if (constRep.isNull())
          {
            assignConstRep = true;
          }
          else
          {
            // This is currently a trace message, as it often triggers for
            // non-linear arithmetic before the model is refined enough to
            // e.g. show transcendental function apps are not equal to rationals
            Trace("model-warn") << "Model values in the same equivalence class "
                                << constRep << " " << n << std::endl;
            if (!constRepBaseModelValue)
            {
              assignConstRep = isBaseValue;
            }
            else if (isBaseValue)
            {
              Node isEqual = rewrite(constRep.eqNode(n));
              if (isEqual.isConst() && isEqual.getConst<bool>())
              {
                assignConstRep = n.isConst();
              }
              else
              {
                Assert(false) << "Distinct base model values in the same "
                                 "equivalence class "
                              << constRep << " " << n << std::endl;
              }
            }
          }
          if (assignConstRep)
          {
            constRep = n;
            Trace("model-builder") << "    ..ConstRep( " << eqc
                                   << " ) = " << constRep << std::endl;
            constRepBaseModelValue = isBaseValue;
          }
          // if we have a constant representative, nothing else matters
          continue;
        }

        // If we don't have a constant rep, check if this is an assigned rep.
        itm = tm->d_reps.find(n);
        if (itm != tm->d_reps.end())
        {
          // Notice that this equivalence class may contain multiple terms that
          // were specified as being a representative, since e.g. datatypes may
          // assert representative for two constructor terms that are not in the
          // care graph and are merged during collectModeInfo due to equality
          // information from another theory. We overwrite the value of rep in
          // these cases here.
          rep = itm->second;
          Trace("model-builder")
              << "    ..Rep( " << eqc << " ) = " << rep << std::endl;
        }

        // (3) Finally, process assignable information
        evaluable = true;
        // expressions that are not assignable should not be given assignment
        // exclusion sets
        Assert(!tm->getAssignmentExclusionSet(n, esetGroup, eset));
        continue;
      }
      assignable = true;
      if (!computeAssigners)
      {
        // we don't compute assigners, skip
        continue;
      }
      // process the assignment exclusion set for term n
      // was it processed based on a master exclusion group (see
      // eqcToAssignerMaster)?
      if (processedExcSet.find(n) != processedExcSet.end())
      {
        // Should not have two assignment exclusion sets for the same
        // equivalence class
        Assert(!hasESet);
        Assert(eqcToAssignerMaster.find(eqc) != eqcToAssignerMaster.end());
        // already processed as a slave term
        hasESet = true;
        continue;
      }
      // was it assigned one?
      if (tm->getAssignmentExclusionSet(n, esetGroup, eset))
      {
        // Should not have two assignment exclusion sets for the same
        // equivalence class
        Assert(!hasESet);
        foundESet = true;
        hasESet = true;
      }
    }

    // finished traversing the equality engine
    TypeNode eqct = eqc.getType();
    // count the number of equivalence classes of sorts in finite model finding
    if (options().quantifiers.finiteModelFind)
    {
      if (eqct.isUninterpretedSort())
      {
        eqc_usort_count[eqct]++;
      }
    }
    // Assign representative for this equivalence class
    if (!constRep.isNull())
    {
      // Theories should not specify a rep if there is already a constant in the
      // equivalence class. However, it may be the case that the representative
      // specified by a theory may be merged with a constant based on equality
      // information from another class. Thus, rep may be non-null here.
      // Regardless, we assign constRep as the representative here.
      assignConstantRep(tm, eqc, constRep);
      typeConstSet.add(eqct, constRep);
      continue;
    }
    else if (!rep.isNull())
    {
      assertedReps[eqc] = rep;
      typeRepSet.add(eqct, eqc);
      std::unordered_set<TypeNode> visiting;
      addToTypeList(eqct, type_list, visiting);
    }
    else
    {
      typeNoRepSet.add(eqct, eqc);
      std::unordered_set<TypeNode> visiting;
      addToTypeList(eqct, type_list, visiting);
    }

    if (assignable)
    {
      assignableEqc.insert(eqc);
    }
    if (evaluable)
    {
      evaluableEqc.insert(eqc);
    }
    // If we found an assignment exclusion set, we construct a new assigner
    // object.
    if (foundESet)
    {
      // we don't accept assignment exclusion sets for evaluable eqc
      Assert(!evaluable);
      // construct the assigner
      Assigner& a = eqcToAssigner[eqc];
      // Take the representatives of each term in the assignment exclusion
      // set, which ensures we can look up their value in d_constReps later.
      std::vector<Node> aes;
      for (const Node& e : eset)
      {
        // Should only supply terms that occur in the model or constants
        // in assignment exclusion sets.
        Assert(tm->hasTerm(e) || e.isConst());
        Node er = tm->hasTerm(e) ? tm->getRepresentative(e) : e;
        aes.push_back(er);
      }
      // initialize
      a.initialize(eqc.getType(), &tep, aes);
      // all others in the group are slaves of this
      for (const Node& g : esetGroup)
      {
        Assert(isAssignable(g));
        if (!tm->hasTerm(g))
        {
          // Ignore those that aren't in the model, in the case the user
          // has supplied an assignment exclusion set to a variable not in
          // the model.
          continue;
        }
        Node gr = tm->getRepresentative(g);
        if (gr != eqc)
        {
          eqcToAssignerMaster[gr] = eqc;
          // remember that this term has been processed
          processedExcSet.insert(g);
        }
      }
    }
  }

  // Now finished initialization

  // Compute type enumerator properties. This code ensures we do not
  // enumerate terms that have uninterpreted constants that violate the
  // bounds imposed by finite model finding. For example, if finite
  // model finding insists that there are only 2 values { U1, U2 } of type U,
  // then the type enumerator for list of U should enumerate:
  //   nil, (cons U1 nil), (cons U2 nil), (cons U1 (cons U1 nil)), ...
  // instead of enumerating (cons U3 nil).
  if (options().quantifiers.finiteModelFind)
  {
    tep.d_fixed_usort_card = true;
    for (std::map<TypeNode, unsigned>::iterator it = eqc_usort_count.begin();
         it != eqc_usort_count.end();
         ++it)
    {
      Trace("model-builder") << "Fixed bound (#eqc) for " << it->first << " : "
                             << it->second << std::endl;
      tep.d_fixed_card[it->first] = Integer(it->second);
    }
    typeConstSet.setTypeEnumeratorProperties(&tep);
  }

  // Need to ensure that each EC has a constant representative.

  Trace("model-builder") << "Processing EC's..." << std::endl;

  TypeSet::iterator it;
  vector<TypeNode>::iterator type_it;
  set<Node>::iterator i, i2;
  bool changed, unassignedAssignable, assignOne = false;
  set<TypeNode> evaluableSet;

  // Double-fixed-point loop
  // Outer loop handles a special corner case (see code at end of loop for
  // details)
  for (;;)
  {
    // Inner fixed-point loop: we are trying to learn constant values for every
    // EC.  Each time through this loop, we process all of the
    // types by type and may learn some new EC values.  EC's in one type may
    // depend on EC's in another type, so we need a fixed-point loop
    // to ensure that we learn as many EC values as possible
    do
    {
      changed = false;
      unassignedAssignable = false;
      evaluableSet.clear();

      // Iterate over all types we've seen
      for (type_it = type_list.begin(); type_it != type_list.end(); ++type_it)
      {
        TypeNode t = *type_it;
        TypeNode tb = t;
        set<Node>* noRepSet = typeNoRepSet.getSet(t);

        // 1. Try to evaluate the EC's in this type
        if (noRepSet != NULL && !noRepSet->empty())
        {
          Trace("model-builder") << "  Eval phase, working on type: " << t
                                 << endl;
          bool evaluable;
          d_normalizedCache.clear();
          for (i = noRepSet->begin(); i != noRepSet->end();)
          {
            i2 = i;
            ++i;
            Trace("model-builder-debug") << "Look at eqc : " << (*i2)
                                         << std::endl;
            Node normalized;
            // only possible to normalize if we are evaluable
            evaluable = evaluableEqc.find(*i2) != evaluableEqc.end();
            if (evaluable)
            {
              normalized = evaluateEqc(tm, *i2);
            }
            if (!normalized.isNull())
            {
              Assert(tm->isValue(normalized));
              typeConstSet.add(tb, normalized);
              assignConstantRep(tm, *i2, normalized);
              Trace("model-builder") << "    Eval: Setting constant rep of "
                                     << (*i2) << " to " << normalized << endl;
              changed = true;
              noRepSet->erase(i2);
            }
            else
            {
              if (evaluable)
              {
                evaluableSet.insert(tb);
              }
              // If assignable, remember there is an equivalence class that is
              // not assigned and assignable.
              if (assignableEqc.find(*i2) != assignableEqc.end())
              {
                unassignedAssignable = true;
              }
            }
          }
        }

        // 2. Normalize any non-const representative terms for this type
        set<Node>* repSet = typeRepSet.getSet(t);
        if (repSet != NULL && !repSet->empty())
        {
          Trace("model-builder")
              << "  Normalization phase, working on type: " << t << endl;
          d_normalizedCache.clear();
          for (i = repSet->begin(); i != repSet->end();)
          {
            Assert(assertedReps.find(*i) != assertedReps.end());
            Node rep = assertedReps[*i];
            Node normalized = normalize(tm, rep, false);
            Trace("model-builder")
                << "    Normalizing rep (" << rep << "), normalized to ("
                << normalized << ")"
                << ", isValue=" << tm->isValue(normalized) << std::endl;
            if (tm->isValue(normalized))
            {
              changed = true;
              typeConstSet.add(tb, normalized);
              assignConstantRep(tm, *i, normalized);
              assertedReps.erase(*i);
              i2 = i;
              ++i;
              repSet->erase(i2);
            }
            else
            {
              if (normalized != rep)
              {
                assertedReps[*i] = normalized;
                changed = true;
              }
              ++i;
            }
          }
        }
      }
    } while (changed);

    if (!unassignedAssignable)
    {
      break;
    }

    // 3. Assign unassigned assignable EC's using type enumeration - assign a
    // value *different* from all other EC's if the type is infinite
    // Assign first value from type enumerator otherwise - for finite types, we
    // rely on polite framework to ensure that EC's that have to be
    // different are different.

    // Only make assignments on a type if:
    // 1. there are no terms that share the same base type with un-normalized
    // representatives
    // 2. there are no terms that share teh same base type that are unevaluated
    // evaluable terms
    // Alternatively, if 2 or 3 don't hold but we are in a special
    // deadlock-breaking mode where assignOne is true, go ahead and make one
    // assignment
    changed = false;
    // must iterate over the ordered type list to ensure that we do not
    // enumerate values with subterms
    //  having types that we are currently enumerating (when possible)
    //  for example, this ensures we enumerate uninterpreted sort U before (List
    //  of U) and (Array U U)
    //  however, it does not break cyclic type dependencies for mutually
    //  recursive datatypes, but this is handled
    //  by recording all subterms of enumerated values in TypeSet::addSubTerms.
    for (type_it = type_list.begin(); type_it != type_list.end(); ++type_it)
    {
      TypeNode t = *type_it;
      // continue if there are no more equivalence classes of this type to
      // assign
      std::set<Node>* noRepSetPtr = typeNoRepSet.getSet(t);
      if (noRepSetPtr == NULL)
      {
        continue;
      }
      set<Node>& noRepSet = *noRepSetPtr;
      if (noRepSet.empty())
      {
        continue;
      }

      // get properties of this type
      bool isCorecursive = false;
      if (t.isDatatype())
      {
        const DType& dt = t.getDType();
        isCorecursive =
            dt.isCodatatype()
            && (!d_env.isFiniteType(t) || dt.isRecursiveSingleton(t));
      }
#ifdef CVC5_ASSERTIONS
      bool isUSortFiniteRestricted = false;
      if (options().quantifiers.finiteModelFind)
      {
        isUSortFiniteRestricted = !t.isUninterpretedSort() && involvesUSort(t);
      }
#endif

      TypeNode tb = t;
      if (!assignOne)
      {
        set<Node>* repSet = typeRepSet.getSet(tb);
        if (repSet != NULL && !repSet->empty())
        {
          continue;
        }
        if (evaluableSet.find(tb) != evaluableSet.end())
        {
          continue;
        }
      }
      Trace("model-builder") << "  Assign phase, working on type: " << t
                             << endl;
      bool assignable, evaluable CVC5_UNUSED;
      std::map<Node, Assigner>::iterator itAssigner;
      std::map<Node, Node>::iterator itAssignerM;
      set<Node>* repSet = typeRepSet.getSet(t);
      for (i = noRepSet.begin(); i != noRepSet.end();)
      {
        i2 = i;
        ++i;
        // check whether it has an assigner object
        itAssignerM = eqcToAssignerMaster.find(*i2);
        if (itAssignerM != eqcToAssignerMaster.end())
        {
          // Take the master's assigner. Notice we don't care which order
          // equivalence classes are assigned. For instance, the master can
          // be assigned after one of its slaves.
          itAssigner = eqcToAssigner.find(itAssignerM->second);
        }
        else
        {
          itAssigner = eqcToAssigner.find(*i2);
        }
        if (itAssigner != eqcToAssigner.end())
        {
          assignable = isAssignerActive(tm, itAssigner->second);
        }
        else
        {
          assignable = assignableEqc.find(*i2) != assignableEqc.end();
        }
        evaluable = evaluableEqc.find(*i2) != evaluableEqc.end();
        Trace("model-builder-debug")
            << "    eqc " << *i2 << " is assignable=" << assignable
            << ", evaluable=" << evaluable << std::endl;
        if (assignable)
        {
          Assert(!evaluable || assignOne);
          // this assertion ensures that if we are assigning to a term of
          // Boolean type, then the term must be assignable.
          // Note we only assign to terms of Boolean type if the term occurs in
          // a singleton equivalence class; otherwise the term would have been
          // in the equivalence class of true or false and would not need
          // assigning.
          Assert(!t.isBoolean() || isAssignable(*i2));
          Node n;
          if (itAssigner != eqcToAssigner.end())
          {
            Trace("model-builder-debug")
                << "Get value from assigner for finite type..." << std::endl;
            // if it has an assigner, get the value from the assigner.
            n = itAssigner->second.getNextAssignment();
            Assert(!n.isNull());
          }
          else if (t.isUninterpretedSort() || !d_env.isFiniteType(t))
          {
            // If its interpreted as infinite, we get a fresh value that does
            // not occur in the model.
            // Note we also consider uninterpreted sorts to be infinite here
            // regardless of whether the cardinality class of t is
            // CardinalityClass::INTERPRETED_FINITE.
            // This is required because the UF solver does not explicitly
            // assign uninterpreted constants to equivalence classes in its
            // collectModelValues method. Doing so would have the same effect
            // as running the code in this case.
            bool success;
            do
            {
              Trace("model-builder-debug") << "Enumerate term of type " << t
                                           << std::endl;
              n = typeConstSet.nextTypeEnum(t);
              //--- AJR: this code checks whether n is a legal value
              Assert(!n.isNull());
              success = true;
              Trace("model-builder-debug") << "Check if excluded : " << n
                                           << std::endl;
#ifdef CVC5_ASSERTIONS
              if (isUSortFiniteRestricted)
              {
                // must not involve uninterpreted constants beyond cardinality
                // bound (which assumed to coincide with #eqc)
                // this is just an assertion now, since TypeEnumeratorProperties
                // should ensure that only legal values are enumerated wrt this
                // constraint.
                std::map<Node, bool> visited;
                success = !isExcludedUSortValue(eqc_usort_count, n, visited);
                if (!success)
                {
                  Trace("model-builder")
                      << "Excluded value for " << t << " : " << n
                      << " due to out of range uninterpreted constant."
                      << std::endl;
                }
                Assert(success);
              }
#endif
              if (success && isCorecursive)
              {
                if (repSet != NULL && !repSet->empty())
                {
                  // in the case of codatatypes, check if it is in the set of
                  // values that we cannot assign
                  success = !isExcludedCdtValue(n, repSet, assertedReps, *i2);
                  if (!success)
                  {
                    Trace("model-builder")
                        << "Excluded value : " << n
                        << " due to alpha-equivalent codatatype expression."
                        << std::endl;
                  }
                }
              }
              //---
            } while (!success);
            Assert(!n.isNull());
          }
          else
          {
            // Otherwise, we get the first value from the type enumerator.
            Trace("model-builder-debug")
                << "Get first value from finite type..." << std::endl;
            TypeEnumerator te(t);
            n = *te;
          }
          Trace("model-builder-debug") << "...got " << n << std::endl;
          assignConstantRep(tm, *i2, n);
          changed = true;
          noRepSet.erase(i2);
          if (assignOne)
          {
            assignOne = false;
            break;
          }
        }
      }
    }

    // Corner case - I'm not sure this can even happen - but it's theoretically
    // possible to have a cyclical dependency
    // in EC assignment/evaluation, e.g. EC1 = {a, b + 1}; EC2 = {b, a - 1}.  In
    // this case, neither one will get assigned because we are waiting
    // to be able to evaluate.  But we will never be able to evaluate because
    // the variables that need to be assigned are in
    // these same EC's.  In this case, repeat the whole fixed-point computation
    // with the difference that the first EC
    // that has both assignable and evaluable expressions will get assigned.
    if (!changed)
    {
      Assert(!assignOne);  // check for infinite loop!
      assignOne = true;
    }
  }

#ifdef CVC5_ASSERTIONS
  // Assert that all representatives have been converted to constants
  for (it = typeRepSet.begin(); it != typeRepSet.end(); ++it)
  {
    std::set<Node>& repSet = TypeSet::getSet(it);
    if (!repSet.empty())
    {
      Trace("model-builder") << "***Non-empty repSet, size = " << repSet.size()
                             << ", repSet = " << repSet << endl;
      Assert(false);
    }
  }
#endif /* CVC5_ASSERTIONS */

  Trace("model-builder") << "Copy representatives to model..." << std::endl;
  tm->d_reps.clear();
  std::map<Node, Node>::iterator itMap;
  for (itMap = d_constantReps.begin(); itMap != d_constantReps.end(); ++itMap)
  {
    tm->d_reps[itMap->first] = itMap->second;
    tm->d_rep_set.add(itMap->second.getType(), itMap->second);
  }

  Trace("model-builder") << "Make sure ECs have reps..." << std::endl;
  // Make sure every EC has a rep
  for (itMap = assertedReps.begin(); itMap != assertedReps.end(); ++itMap)
  {
    tm->d_reps[itMap->first] = itMap->second;
    tm->d_rep_set.add(itMap->second.getType(), itMap->second);
  }
  for (it = typeNoRepSet.begin(); it != typeNoRepSet.end(); ++it)
  {
    set<Node>& noRepSet = TypeSet::getSet(it);
    for (const Node& node : noRepSet)
    {
      tm->d_reps[node] = node;
      tm->d_rep_set.add(node.getType(), node);
    }
  }

  // modelBuilder-specific initialization
  if (!processBuildModel(tm))
  {
    Trace("model-builder")
        << "TheoryEngineModelBuilder: fail process build model." << std::endl;
    return false;
  }
  Trace("model-builder") << "TheoryEngineModelBuilder: success" << std::endl;
  return true;
}

void TheoryEngineModelBuilder::postProcessModel(bool incomplete, TheoryModel* m)
{
  // if we are incomplete, there is no guarantee on the model.
  // thus, we do not check the model here.
  if (incomplete)
  {
    return;
  }
  Assert(m != nullptr);
  // debug-check the model if the checkModels() is enabled.
  if (options().smt.debugCheckModels)
  {
    debugCheckModel(m);
  }
}

void TheoryEngineModelBuilder::debugCheckModel(TheoryModel* tm)
{
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(tm->d_equalityEngine);
  std::map<Node, Node>::iterator itMap;
  // Check that every term evaluates to its representative in the model
  for (eqcs_i = eq::EqClassesIterator(tm->d_equalityEngine);
       !eqcs_i.isFinished();
       ++eqcs_i)
  {
    // eqc is the equivalence class representative
    Node eqc = (*eqcs_i);
    // get the representative
    Node rep = tm->getRepresentative(eqc);
    if (!rep.isConst() && eqc.getType().isBoolean())
    {
      // if Boolean, it does not necessarily have a constant representative, use
      // get value instead
      rep = tm->getValue(eqc);
      AlwaysAssert(rep.isConst());
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, tm->d_equalityEngine);
    for (; !eqc_i.isFinished(); ++eqc_i)
    {
      Node n = *eqc_i;
      static int repCheckInstance = 0;
      ++repCheckInstance;
      AlwaysAssert(rep.getType() == n.getType())
          << "Representative " << rep << " of " << n
          << " violates type constraints (" << rep.getType() << " and "
          << n.getType() << ")";
      Node val = tm->getValue(n);
      if (val != rep)
      {
        std::stringstream err;
        err << "Failed representative check:" << std::endl
            << "( " << repCheckInstance << ") "
            << "n: " << n << std::endl
            << "getValue(n): " << val << std::endl
            << "rep: " << rep << std::endl;
        if (val.isConst() && rep.isConst())
        {
          AlwaysAssert(val == rep) << err.str();
        }
        else if (rewrite(val) != rewrite(rep))
        {
          // if it does not evaluate, it is just a warning, which may be the
          // case for non-constant values, e.g. lambdas. Furthermore we only
          // throw this warning if rewriting cannot show they are equal.
          warning() << err.str();
        }
      }
    }
  }

  // builder-specific debugging
  debugModel(tm);
}

Node TheoryEngineModelBuilder::normalize(TheoryModel* m, TNode r, bool evalOnly)
{
  std::map<Node, Node>::iterator itMap = d_constantReps.find(r);
  if (itMap != d_constantReps.end())
  {
    return (*itMap).second;
  }
  NodeMap::iterator it = d_normalizedCache.find(r);
  if (it != d_normalizedCache.end())
  {
    return (*it).second;
  }
  Trace("model-builder-debug") << "do normalize on " << r << std::endl;
  Node retNode = r;
  if (r.getNumChildren() > 0)
  {
    std::vector<Node> children;
    if (r.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(r.getOperator());
    }
    for (size_t i = 0, nchild = r.getNumChildren(); i < nchild; ++i)
    {
      Node ri = r[i];
      bool recurse = true;
      if (!ri.isConst())
      {
        if (m->d_equalityEngine->hasTerm(ri))
        {
          itMap =
              d_constantReps.find(m->d_equalityEngine->getRepresentative(ri));
          if (itMap != d_constantReps.end())
          {
            ri = (*itMap).second;
            Trace("model-builder-debug") << i << ": const child " << ri << std::endl;
            recurse = false;
          }
          else if (!evalOnly)
          {
            recurse = false;
            Trace("model-builder-debug") << i << ": keep " << ri << std::endl;
          }
        }
        else
        {
          Trace("model-builder-debug") << i << ": no hasTerm " << ri << std::endl;
        }
        if (recurse)
        {
          ri = normalize(m, ri, evalOnly);
        }
      }
      children.push_back(ri);
    }
    retNode = NodeManager::currentNM()->mkNode(r.getKind(), children);
    retNode = rewrite(retNode);
  }
  d_normalizedCache[r] = retNode;
  return retNode;
}

bool TheoryEngineModelBuilder::preProcessBuildModel(TheoryModel* m)
{
  return true;
}

bool TheoryEngineModelBuilder::processBuildModel(TheoryModel* m)
{
  if (m->areFunctionValuesEnabled())
  {
    assignFunctions(m);
  }
  return true;
}

void TheoryEngineModelBuilder::assignFunction(TheoryModel* m, Node f)
{
  Assert(!logicInfo().isHigherOrder());
  uf::UfModelTree ufmt(f);
  Node default_v;
  for (size_t i = 0; i < m->d_uf_terms[f].size(); i++)
  {
    Node un = m->d_uf_terms[f][i];
    vector<TNode> children;
    children.push_back(f);
    Trace("model-builder-debug") << "  process term : " << un << std::endl;
    for (size_t j = 0; j < un.getNumChildren(); ++j)
    {
      Node rc = m->getRepresentative(un[j]);
      Trace("model-builder-debug2") << "    get rep : " << un[j] << " returned "
                                    << rc << std::endl;
      Assert(rewrite(rc) == rc);
      children.push_back(rc);
    }
    Node simp = NodeManager::currentNM()->mkNode(un.getKind(), children);
    Node v = m->getRepresentative(un);
    Trace("model-builder") << "  Setting (" << simp << ") to (" << v << ")"
                           << endl;
    ufmt.setValue(m, simp, v);
    default_v = v;
  }
  if (default_v.isNull())
  {
    // choose default value from model if none exists
    TypeEnumerator te(f.getType().getRangeType());
    default_v = (*te);
  }
  ufmt.setDefaultValue(m, default_v);
  bool condenseFuncValues = options().theory.condenseFunctionValues;
  if (condenseFuncValues)
  {
    ufmt.simplify();
  }
  std::stringstream ss;
  ss << "_arg_";
  Rewriter* r = condenseFuncValues ? d_env.getRewriter() : nullptr;
  Node val = ufmt.getFunctionValue(ss.str(), r);
  m->assignFunctionDefinition(f, val);
  // ufmt.debugPrint( std::cout, m );
}

void TheoryEngineModelBuilder::assignHoFunction(TheoryModel* m, Node f)
{
  Assert(logicInfo().isHigherOrder());
  TypeNode type = f.getType();
  std::vector<TypeNode> argTypes = type.getArgTypes();
  std::vector<Node> args;
  std::vector<TNode> apply_args;
  for (unsigned i = 0; i < argTypes.size(); i++)
  {
    Node v = NodeManager::currentNM()->mkBoundVar(argTypes[i]);
    args.push_back(v);
    if (i > 0)
    {
      apply_args.push_back(v);
    }
  }
  // start with the base return value (currently we use the same default value
  // for all functions)
  TypeEnumerator te(type.getRangeType());
  Node curr = (*te);
  std::map<Node, std::vector<Node> >::iterator itht = m->d_ho_uf_terms.find(f);
  if (itht != m->d_ho_uf_terms.end())
  {
    for (size_t i = 0; i < itht->second.size(); i++)
    {
      Node hn = itht->second[i];
      Trace("model-builder-debug") << "    process : " << hn << std::endl;
      Assert(hn.getKind() == kind::HO_APPLY);
      Assert(m->areEqual(hn[0], f));
      Node hni = m->getRepresentative(hn[1]);
      Trace("model-builder-debug2") << "      get rep : " << hn[0]
                                    << " returned " << hni << std::endl;
      Assert(hni.getType() == args[0].getType());
      hni = rewrite(args[0].eqNode(hni));
      Node hnv = m->getRepresentative(hn);
      Trace("model-builder-debug2") << "      get rep val : " << hn
                                    << " returned " << hnv << std::endl;
      Assert(hnv.isConst());
      if (!apply_args.empty())
      {
        // Convert to lambda, which is necessary if hnv is a function array
        // constant.
        hnv = uf::FunctionConst::toLambda(hnv);
        Assert(!hnv.isNull() && hnv.getKind() == kind::LAMBDA
               && hnv[0].getNumChildren() + 1 == args.size());
        std::vector<TNode> largs;
        for (unsigned j = 0; j < hnv[0].getNumChildren(); j++)
        {
          largs.push_back(hnv[0][j]);
        }
        Assert(largs.size() == apply_args.size());
        hnv = hnv[1].substitute(
            largs.begin(), largs.end(), apply_args.begin(), apply_args.end());
        hnv = rewrite(hnv);
      }
      Assert(hnv.getType() == curr.getType());
      curr = NodeManager::currentNM()->mkNode(kind::ITE, hni, hnv, curr);
    }
  }
  Node val = NodeManager::currentNM()->mkNode(
      kind::LAMBDA,
      NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args),
      curr);
  m->assignFunctionDefinition(f, val);
}

// This struct is used to sort terms by the "size" of their type
//   The size of the type is the number of nodes in the type, for example
//  size of Int is 1
//  size of Function( Int, Int ) is 3
//  size of Function( Function( Bool, Int ), Int ) is 5
struct sortTypeSize
{
  // stores the size of the type
  std::map<TypeNode, unsigned> d_type_size;
  // get the size of type tn
  unsigned getTypeSize(TypeNode tn)
  {
    std::map<TypeNode, unsigned>::iterator it = d_type_size.find(tn);
    if (it != d_type_size.end())
    {
      return it->second;
    }
    else
    {
      unsigned sum = 1;
      for (unsigned i = 0; i < tn.getNumChildren(); i++)
      {
        sum += getTypeSize(tn[i]);
      }
      d_type_size[tn] = sum;
      return sum;
    }
  }

 public:
  // compares the type size of i and j
  // returns true iff the size of i is less than that of j
  // tiebreaks are determined by node value
  bool operator()(Node i, Node j)
  {
    int si = getTypeSize(i.getType());
    int sj = getTypeSize(j.getType());
    if (si < sj)
    {
      return true;
    }
    else if (si == sj)
    {
      return i < j;
    }
    else
    {
      return false;
    }
  }
};

void TheoryEngineModelBuilder::assignFunctions(TheoryModel* m)
{
  if (!options().theory.assignFunctionValues)
  {
    return;
  }
  Trace("model-builder") << "Assigning function values..." << std::endl;
  std::vector<Node> funcs_to_assign = m->getFunctionsToAssign();

  if (logicInfo().isHigherOrder())
  {
    // sort based on type size if higher-order
    Trace("model-builder") << "Sort functions by type..." << std::endl;
    sortTypeSize sts;
    std::sort(funcs_to_assign.begin(), funcs_to_assign.end(), sts);
  }

  if (TraceIsOn("model-builder"))
  {
    Trace("model-builder") << "...have " << funcs_to_assign.size()
                           << " functions to assign:" << std::endl;
    for (unsigned k = 0; k < funcs_to_assign.size(); k++)
    {
      Node f = funcs_to_assign[k];
      Trace("model-builder") << "  [" << k << "] : " << f << " : "
                             << f.getType() << std::endl;
    }
  }

  // construct function values
  for (unsigned k = 0; k < funcs_to_assign.size(); k++)
  {
    Node f = funcs_to_assign[k];
    Trace("model-builder") << "  Function #" << k << " is " << f << std::endl;
    // std::map< Node, std::vector< Node > >::iterator itht =
    // m->d_ho_uf_terms.find( f );
    if (!logicInfo().isHigherOrder())
    {
      Trace("model-builder") << "  Assign function value for " << f
                             << " based on APPLY_UF" << std::endl;
      assignFunction(m, f);
    }
    else
    {
      Trace("model-builder") << "  Assign function value for " << f
                             << " based on curried HO_APPLY" << std::endl;
      assignHoFunction(m, f);
    }
  }
  Trace("model-builder") << "Finished assigning function values." << std::endl;
}

}  // namespace theory
}  // namespace cvc5::internal

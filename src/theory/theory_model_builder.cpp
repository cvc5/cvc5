/*********************                                                        */
/*! \file theory_model_builder.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Clark Barrett, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of theory model buidler class
 **/
#include "theory/theory_model_builder.h"

#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf_model.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {

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
  // check if we have run out of elements
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

TheoryEngineModelBuilder::TheoryEngineModelBuilder(TheoryEngine* te) : d_te(te)
{
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
      if (normalized.isConst())
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
    if (er.isConst())
    {
      // already processed
      continue;
    }
    // Assignable members of assignment exclusion set should be representatives
    // of their equivalence clases. This ensures we look up the constant
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
  if (n.getKind() == kind::SELECT || n.getKind() == kind::APPLY_SELECTOR_TOTAL)
  {
    // selectors are always assignable (where we guarantee that they are not
    // evaluatable here)
    if (!options::ufHo())
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
    if (!options::ufHo())
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
                                                 Node const_rep)
{
  d_constantReps[eqc] = const_rep;
  Trace("model-builder") << "    Assign: Setting constant rep of " << eqc
                         << " to " << const_rep << endl;
  tm->d_rep_set.setTermForRepresentative(const_rep, eqc);
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
    // check matching val to rep with eqc as a free variable
    Node eqc_m;
    if (isCdtValueMatch(val, rep, eqc, eqc_m))
    {
      Trace("model-builder-debug") << "  ...matches with " << eqc << " -> "
                                   << eqc_m << std::endl;
      if (eqc_m.getKind() == kind::UNINTERPRETED_CONSTANT)
      {
        Trace("model-builder-debug") << "*** " << val
                                     << " is excluded datatype for " << eqc
                                     << std::endl;
        return true;
      }
    }
  }
  return false;
}

bool TheoryEngineModelBuilder::isCdtValueMatch(Node v,
                                               Node r,
                                               Node eqc,
                                               Node& eqc_m)
{
  if (r == v)
  {
    return true;
  }
  else if (r == eqc)
  {
    if (eqc_m.isNull())
    {
      // only if an uninterpreted constant?
      eqc_m = v;
      return true;
    }
    else
    {
      return v == eqc_m;
    }
  }
  else if (v.getKind() == kind::APPLY_CONSTRUCTOR
           && r.getKind() == kind::APPLY_CONSTRUCTOR)
  {
    if (v.getOperator() == r.getOperator())
    {
      for (unsigned i = 0; i < v.getNumChildren(); i++)
      {
        if (!isCdtValueMatch(v[i], r[i], eqc, eqc_m))
        {
          return false;
        }
      }
      return true;
    }
  }
  return false;
}

bool TheoryEngineModelBuilder::involvesUSort(TypeNode tn)
{
  if (tn.isSort())
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
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
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
    if (tn.isSort())
    {
      Trace("model-builder-debug") << "Is excluded usort value : " << v << " "
                                   << tn << std::endl;
      unsigned card = eqc_usort_count[tn];
      Trace("model-builder-debug") << "  Cardinality is " << card << std::endl;
      unsigned index =
          v.getConst<UninterpretedConstant>().getIndex().toUnsignedInt();
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
    std::unordered_set<TypeNode, TypeNodeHashFunction>& visiting)
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
        const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
        for (unsigned i = 0; i < dt.getNumConstructors(); i++)
        {
          for (unsigned j = 0; j < dt[i].getNumArgs(); j++)
          {
            TypeNode ctn = TypeNode::fromType(dt[i][j].getRangeType());
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

bool TheoryEngineModelBuilder::buildModel(Model* m)
{
  Trace("model-builder") << "TheoryEngineModelBuilder: buildModel" << std::endl;
  TheoryModel* tm = (TheoryModel*)m;
  eq::EqualityEngine* ee = tm->d_equalityEngine;

  // buildModel should only be called once per check
  Assert(!tm->isBuilt());

  // Reset model
  tm->reset();

  // mark as built
  tm->d_modelBuilt = true;
  tm->d_modelBuiltSuccess = false;

  // Collect model info from the theories
  Trace("model-builder") << "TheoryEngineModelBuilder: Collect model info..."
                         << std::endl;
  if (!d_te->collectModelInfo(tm))
  {
    return false;
  }

  // model-builder specific initialization
  if (!preProcessBuildModel(tm))
  {
    return false;
  }

  // Loop through all terms and make sure that assignable sub-terms are in the
  // equality engine
  // Also, record #eqc per type (for finite model finding)
  std::map<TypeNode, unsigned> eqc_usort_count;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  {
    NodeSet cache;
    for (; !eqcs_i.isFinished(); ++eqcs_i)
    {
      eq::EqClassIterator eqc_i = eq::EqClassIterator((*eqcs_i), ee);
      for (; !eqc_i.isFinished(); ++eqc_i)
      {
        addAssignableSubterms(*eqc_i, tm, cache);
      }
      TypeNode tn = (*eqcs_i).getType();
      if (tn.isSort())
      {
        if (eqc_usort_count.find(tn) == eqc_usort_count.end())
        {
          eqc_usort_count[tn] = 1;
        }
        else
        {
          eqc_usort_count[tn]++;
        }
      }
    }
  }

  Trace("model-builder") << "Collect representatives..." << std::endl;

  // Process all terms in the equality engine, store representatives for each EC
  d_constantReps.clear();
  std::map<Node, Node> assertedReps;
  TypeSet typeConstSet, typeRepSet, typeNoRepSet;
  TypeEnumeratorProperties tep;
  if (options::finiteModelFind())
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

  // AJR: build ordered list of types that ensures that base types are
  // enumerated first.
  // (I think) this is only strictly necessary for finite model finding +
  // parametric types instantiated with uninterpreted sorts, but is probably
  // a good idea to do in general since it leads to models with smaller term
  // sizes.
  std::vector<TypeNode> type_list;
  eqcs_i = eq::EqClassesIterator(tm->d_equalityEngine);
  for (; !eqcs_i.isFinished(); ++eqcs_i)
  {
    // eqc is the equivalence class representative
    Node eqc = (*eqcs_i);
    Trace("model-builder") << "Processing EC: " << eqc << endl;
    Assert(tm->d_equalityEngine->getRepresentative(eqc) == eqc);
    TypeNode eqct = eqc.getType();
    Assert(assertedReps.find(eqc) == assertedReps.end());
    Assert(d_constantReps.find(eqc) == d_constantReps.end());

    // Loop through terms in this EC
    Node rep, const_rep;
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, tm->d_equalityEngine);
    for (; !eqc_i.isFinished(); ++eqc_i)
    {
      Node n = *eqc_i;
      Trace("model-builder") << "  Processing Term: " << n << endl;
      // Record as rep if this node was specified as a representative
      if (tm->d_reps.find(n) != tm->d_reps.end())
      {
        // AJR: I believe this assertion is too strict,
        // e.g. datatypes may assert representative for two constructor terms
        // that are not in the care graph and are merged during
        // collectModelInfo.
        // Assert(rep.isNull());
        rep = tm->d_reps[n];
        Assert(!rep.isNull());
        Trace("model-builder") << "  Rep( " << eqc << " ) = " << rep
                               << std::endl;
      }
      // Record as const_rep if this node is constant
      if (n.isConst())
      {
        Assert(const_rep.isNull());
        const_rep = n;
        Trace("model-builder") << "  ConstRep( " << eqc << " ) = " << const_rep
                               << std::endl;
      }
      // model-specific processing of the term
      tm->addTermInternal(n);
    }

    // Assign representative for this EC
    if (!const_rep.isNull())
    {
      // Theories should not specify a rep if there is already a constant in the
      // EC
      // AJR: I believe this assertion is too strict, eqc with asserted reps may
      // merge with constant eqc
      // Assert(rep.isNull() || rep == const_rep);
      assignConstantRep(tm, eqc, const_rep);
      typeConstSet.add(eqct.getBaseType(), const_rep);
    }
    else if (!rep.isNull())
    {
      assertedReps[eqc] = rep;
      typeRepSet.add(eqct.getBaseType(), eqc);
      std::unordered_set<TypeNode, TypeNodeHashFunction> visiting;
      addToTypeList(eqct.getBaseType(), type_list, visiting);
    }
    else
    {
      typeNoRepSet.add(eqct, eqc);
      std::unordered_set<TypeNode, TypeNodeHashFunction> visiting;
      addToTypeList(eqct, type_list, visiting);
    }
  }

  Trace("model-builder") << "Compute assignable information..." << std::endl;
  // The set of equivalence classes that are "assignable", i.e. those that
  // have an assignable expression in them (see isAssignable), and
  // have not already been assigned.
  std::unordered_set<Node, NodeHashFunction> assignableEqc;
  // The set of equivalence classes that are "evaluable", i.e. those that
  // have an expression in them that is not assignable, and have not already
  // been assigned.
  std::unordered_set<Node, NodeHashFunction> evaluableEqc;
  // Assigner objects for relevant equivalence classes
  std::map<Node, Assigner> eqcToAssigner;
  // Maps equivalence classes to the equivalence class that maps to its assigner
  // object in the above map.
  std::map<Node, Node> eqcToAssignerMaster;
  // compute the above information
  {
    bool computeAssigners = tm->hasAssignmentExclusionSets();
    std::unordered_set<Node, NodeHashFunction> processed;
    eqcs_i = eq::EqClassesIterator(ee);
    bool assignable = false;
    bool evaluable = false;
    for (; !eqcs_i.isFinished(); ++eqcs_i)
    {
      Node eqc = *eqcs_i;
      if (d_constantReps.find(eqc) != d_constantReps.end())
      {
        // already assigned above, skip
        continue;
      }
      assignable = false;
      evaluable = false;
      // for assignment exclusion sets
      std::vector<Node> group;
      std::vector<Node> eset;
      bool hasESet = false;
      bool foundESet = false;
      eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, ee);
      for (; !eqc_i.isFinished(); ++eqc_i)
      {
        Node n = *eqc_i;
        if (!isAssignable(n))
        {
          evaluable = true;
          if (!computeAssigners)
          {
            if (assignable)
            {
              // both flags set, we are done
              break;
            }
          }
          // expressions that are not assignable should not be given assignment
          // exclusion sets
          Assert(!tm->getAssignmentExclusionSet(n, group, eset));
          continue;
        }
        else
        {
          assignable = true;
          if (!computeAssigners)
          {
            if (evaluable)
            {
              // both flags set, we are done
              break;
            }
            // we don't compute assigners, skip
            continue;
          }
        }
        // process the assignment exclusion set for term n
        // was it processed as a slave of a group?
        if (processed.find(n) != processed.end())
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
        if (tm->getAssignmentExclusionSet(n, group, eset))
        {
          // Should not have two assignment exclusion sets for the same
          // equivalence class
          Assert(!hasESet);
          foundESet = true;
          hasESet = true;
        }
      }
      if (assignable)
      {
        assignableEqc.insert(eqc);
      }
      if (evaluable)
      {
        evaluableEqc.insert(eqc);
      }
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
        for (const Node& g : group)
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
            processed.insert(g);
          }
        }
      }
    }
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
        TypeNode tb = t.getBaseType();
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
              Assert(normalized.isConst());
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
            Trace("model-builder") << "    Normalizing rep (" << rep
                                   << "), normalized to (" << normalized << ")"
                                   << endl;
            if (normalized.isConst())
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
        const Datatype& dt = ((DatatypeType)(t).toType()).getDatatype();
        isCorecursive =
            dt.isCodatatype() && (!dt.isFinite(t.toType())
                                  || dt.isRecursiveSingleton(t.toType()));
      }
#ifdef CVC4_ASSERTIONS
      bool isUSortFiniteRestricted = false;
      if (options::finiteModelFind())
      {
        isUSortFiniteRestricted = !t.isSort() && involvesUSort(t);
      }
#endif

      set<Node>* repSet = typeRepSet.getSet(t);
      TypeNode tb = t.getBaseType();
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
      bool assignable, evaluable CVC4_UNUSED;
      std::map<Node, Assigner>::iterator itAssigner;
      std::map<Node, Node>::iterator itAssignerM;
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
          // Boolean type, then the term is either a variable or an APPLY_UF.
          // Note we only assign to terms of Boolean type if the term occurs in
          // a singleton equivalence class; otherwise the term would have been
          // in the equivalence class of true or false and would not need
          // assigning.
          Assert(!t.isBoolean() || (*i2).isVar()
                 || (*i2).getKind() == kind::APPLY_UF);
          Node n;
          if (itAssigner != eqcToAssigner.end())
          {
            Trace("model-builder-debug")
                << "Get value from assigner for finite type..." << std::endl;
            // if it has an assigner, get the value from the assigner.
            n = itAssigner->second.getNextAssignment();
            Assert(!n.isNull());
          }
          else if (!t.isFinite())
          {
            // if its infinite, we get a fresh value that does not occur in
            // the model.
            bool success;
            do
            {
              Trace("model-builder-debug") << "Enumerate term of type " << t
                                           << std::endl;
              n = typeConstSet.nextTypeEnum(t, true);
              //--- AJR: this code checks whether n is a legal value
              Assert(!n.isNull());
              success = true;
              Trace("model-builder-debug") << "Check if excluded : " << n
                                           << std::endl;
#ifdef CVC4_ASSERTIONS
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
            Trace("model-builder-debug")
                << "Get first value from finite type..." << std::endl;
            // Otherwise, we get the first value from the type enumerator.
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

#ifdef CVC4_ASSERTIONS
  // Assert that all representatives have been converted to constants
  for (it = typeRepSet.begin(); it != typeRepSet.end(); ++it)
  {
    set<Node>& repSet = TypeSet::getSet(it);
    if (!repSet.empty())
    {
      Trace("model-builder") << "***Non-empty repSet, size = " << repSet.size()
                             << ", first = " << *(repSet.begin()) << endl;
      Assert(false);
    }
  }
#endif /* CVC4_ASSERTIONS */

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
    set<Node>::iterator i;
    for (i = noRepSet.begin(); i != noRepSet.end(); ++i)
    {
      tm->d_reps[*i] = *i;
      tm->d_rep_set.add((*i).getType(), *i);
    }
  }

  // modelBuilder-specific initialization
  if (!processBuildModel(tm))
  {
    return false;
  }

  tm->d_modelBuiltSuccess = true;
  return true;
}

void TheoryEngineModelBuilder::postProcessModel(bool incomplete, Model* m)
{
  // if we are incomplete, there is no guarantee on the model.
  // thus, we do not check the model here.
  if (incomplete)
  {
    return;
  }
  TheoryModel* tm = static_cast<TheoryModel*>(m);
  Assert(tm != nullptr);
  // debug-check the model if the checkModels() is enabled.
  if (options::checkModels())
  {
    debugCheckModel(tm);
  }
}

void TheoryEngineModelBuilder::debugCheckModel(TheoryModel* tm)
{
#ifdef CVC4_ASSERTIONS
  Assert(tm->isBuilt());
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
      Assert(rep.isConst());
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, tm->d_equalityEngine);
    for (; !eqc_i.isFinished(); ++eqc_i)
    {
      Node n = *eqc_i;
      static int repCheckInstance = 0;
      ++repCheckInstance;

      // non-linear mult is not necessarily accurate wrt getValue
      if (n.getKind() != kind::NONLINEAR_MULT)
      {
        Debug("check-model::rep-checking") << "( " << repCheckInstance << ") "
                                           << "n: " << n << endl
                                           << "getValue(n): " << tm->getValue(n)
                                           << endl
                                           << "rep: " << rep << endl;
        Assert(tm->getValue(*eqc_i) == rep,
               "run with -d check-model::rep-checking for details");
      }
    }
  }
#endif /* CVC4_ASSERTIONS */

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
    bool childrenConst = true;
    for (size_t i = 0; i < r.getNumChildren(); ++i)
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
            recurse = false;
          }
          else if (!evalOnly)
          {
            recurse = false;
          }
        }
        if (recurse)
        {
          ri = normalize(m, ri, evalOnly);
        }
        if (!ri.isConst())
        {
          childrenConst = false;
        }
      }
      children.push_back(ri);
    }
    retNode = NodeManager::currentNM()->mkNode(r.getKind(), children);
    if (childrenConst)
    {
      retNode = Rewriter::rewrite(retNode);
      Assert(retNode.getKind() == kind::APPLY_UF
             || !retNode.getType().isFirstClass()
             || retNode.isConst());
    }
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
  Assert(!options::ufHo());
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
      Assert(rc.isConst());
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
  bool condenseFuncValues = options::condenseFunctionValues();
  if (condenseFuncValues)
  {
    ufmt.simplify();
  }
  std::stringstream ss;
  ss << "_arg_";
  Node val = ufmt.getFunctionValue(ss.str().c_str(), condenseFuncValues);
  m->assignFunctionDefinition(f, val);
  // ufmt.debugPrint( std::cout, m );
}

void TheoryEngineModelBuilder::assignHoFunction(TheoryModel* m, Node f)
{
  Assert(options::ufHo());
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
      Assert(hni.isConst());
      Assert(hni.getType().isSubtypeOf(args[0].getType()));
      hni = Rewriter::rewrite(args[0].eqNode(hni));
      Node hnv = m->getRepresentative(hn);
      Trace("model-builder-debug2") << "      get rep val : " << hn
                                    << " returned " << hnv << std::endl;
      Assert(hnv.isConst());
      if (!apply_args.empty())
      {
        Assert(hnv.getKind() == kind::LAMBDA
               && hnv[0].getNumChildren() + 1 == args.size());
        std::vector<TNode> largs;
        for (unsigned j = 0; j < hnv[0].getNumChildren(); j++)
        {
          largs.push_back(hnv[0][j]);
        }
        Assert(largs.size() == apply_args.size());
        hnv = hnv[1].substitute(
            largs.begin(), largs.end(), apply_args.begin(), apply_args.end());
        hnv = Rewriter::rewrite(hnv);
      }
      Assert(!TypeNode::leastCommonTypeNode(hnv.getType(), curr.getType())
                  .isNull());
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
  if (!options::assignFunctionValues())
  {
    return;
  }
  Trace("model-builder") << "Assigning function values..." << std::endl;
  std::vector<Node> funcs_to_assign = m->getFunctionsToAssign();

  if (options::ufHo())
  {
    // sort based on type size if higher-order
    Trace("model-builder") << "Sort functions by type..." << std::endl;
    sortTypeSize sts;
    std::sort(funcs_to_assign.begin(), funcs_to_assign.end(), sts);
  }

  if (Trace.isOn("model-builder"))
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
    if (!options::ufHo())
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

} /* namespace CVC4::theory */
} /* namespace CVC4 */

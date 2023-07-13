/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the theory of strings.
 */

#include "theory/strings/theory_strings.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/kind.h"
#include "expr/sequence.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "options/theory_options.h"
#include "printer/smt2/smt2_printer.h"
#include "smt/logic_exception.h"
#include "theory/decision_manager.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/type_enumerator.h"
#include "theory/strings/word.h"
#include "theory/theory_model.h"
#include "theory/valuation.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 * Attribute used for making unique (bound variables) which correspond to
 * unique element values used in sequence models. See use in collectModelValues
 * below.
 */
struct SeqModelVarAttributeId
{
};
using SeqModelVarAttribute = expr::Attribute<SeqModelVarAttributeId, Node>;

TheoryStrings::TheoryStrings(Env& env, OutputChannel& out, Valuation valuation)
    : Theory(THEORY_STRINGS, env, out, valuation),
      d_notify(*this),
      d_statistics(statisticsRegistry()),
      d_state(env, d_valuation),
      d_termReg(env, *this, d_state, d_statistics),
      d_rewriter(env.getRewriter(),
                 &d_statistics.d_rewrites,
                 d_termReg.getAlphabetCardinality()),
      d_eagerSolver(options().strings.stringEagerSolver
                        ? new EagerSolver(env, d_state, d_termReg)
                        : nullptr),
      d_extTheoryCb(),
      d_im(env, *this, d_state, d_termReg, d_extTheory, d_statistics),
      d_extTheory(env, d_extTheoryCb, d_im),
      // the checker depends on the cardinality of the alphabet
      d_checker(d_termReg.getAlphabetCardinality()),
      d_bsolver(env, d_state, d_im, d_termReg),
      d_csolver(env, d_state, d_im, d_termReg, d_bsolver),
      d_esolver(env,
                d_state,
                d_im,
                d_termReg,
                d_rewriter,
                d_bsolver,
                d_csolver,
                d_extTheory,
                d_statistics),
      d_psolver(env, d_state, d_im, d_termReg, d_bsolver, d_csolver),
      d_asolver(env,
                d_state,
                d_im,
                d_termReg,
                d_bsolver,
                d_csolver,
                d_esolver,
                d_extTheory),
      d_rsolver(
          env, d_state, d_im, d_termReg, d_csolver, d_esolver, d_statistics),
      d_regexp_elim(
          env,
          options().strings.regExpElim == options::RegExpElimMode::AGG,
          userContext()),
      d_stringsFmf(env, valuation, d_termReg),
      d_mcd(env, d_state, d_csolver),
      d_strat(d_env),
      d_absModelCounter(0),
      d_strGapModelCounter(0),
      d_cpacb(*this)
{
  d_termReg.finishInit(&d_im);

  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
  d_one = NodeManager::currentNM()->mkConstInt(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConstInt(Rational(-1));
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );

  // set up the extended function callback
  d_extTheoryCb.d_esolver = &d_esolver;

  // use the state object as the official theory state
  d_theoryState = &d_state;
  // use the inference manager as the official inference manager
  d_inferManager = &d_im;
}

TheoryStrings::~TheoryStrings() {

}

TheoryRewriter* TheoryStrings::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryStrings::getProofChecker() { return &d_checker; }

bool TheoryStrings::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::strings::ee";
  esi.d_notifyNewClass = true;
  esi.d_notifyMerge = true;
  esi.d_notifyDisequal = true;
  return true;
}

void TheoryStrings::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  // witness is used to eliminate str.from_code
  d_valuation.setUnevaluatedKind(WITNESS);

  bool eagerEval = options().strings.stringEagerEval;
  // The kinds we are treating as function application in congruence
  d_equalityEngine->addFunctionKind(kind::STRING_LENGTH, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_CONCAT, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_IN_REGEXP, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_TO_CODE, eagerEval);
  d_equalityEngine->addFunctionKind(kind::SEQ_UNIT, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_UNIT, false);
  // `seq.nth` is not always defined, and so we do not evaluate it eagerly.
  d_equalityEngine->addFunctionKind(kind::SEQ_NTH, false);
  // extended functions
  d_equalityEngine->addFunctionKind(kind::STRING_CONTAINS, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_LEQ, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_SUBSTR, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_UPDATE, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_ITOS, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_STOI, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_INDEXOF, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_INDEXOF_RE, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_REPLACE, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_REPLACE_ALL, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_REPLACE_RE, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_REPLACE_RE_ALL, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_REPLACE_ALL, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_TO_LOWER, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_TO_UPPER, eagerEval);
  d_equalityEngine->addFunctionKind(kind::STRING_REV, eagerEval);

  // memberships are not relevant for model building
  d_valuation.setIrrelevantKind(kind::STRING_IN_REGEXP);
  d_valuation.setIrrelevantKind(kind::STRING_LEQ);
  // seq nth doesn't always evaluate
  d_valuation.setUnevaluatedKind(SEQ_NTH);
}

std::string TheoryStrings::identify() const
{
  return std::string("TheoryStrings");
}

bool TheoryStrings::propagateLit(TNode literal)
{
  if (d_state.hasPendingConflict())
  {
    // pending conflict also implies we are done
    return false;
  }
  return d_im.propagateLit(literal);
}

TrustNode TheoryStrings::explain(TNode literal)
{
  Trace("strings-explain") << "explain called on " << literal << std::endl;
  return d_im.explainLit(literal);
}

void TheoryStrings::presolve() {
  Trace("strings-presolve")
      << "TheoryStrings::Presolving : get fmf options "
      << (options().strings.stringFMF ? "true" : "false") << std::endl;
  d_strat.initializeStrategy();

  // if strings fmf is enabled, register the strategy
  if (options().strings.stringFMF)
  {
    d_stringsFmf.presolve();
    // This strategy is local to a check-sat call, since we refresh the strategy
    // on every call to presolve.
    d_im.getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_STRINGS_SUM_LENGTHS,
        d_stringsFmf.getDecisionStrategy(),
        DecisionManager::STRAT_SCOPE_LOCAL_SOLVE);
  }
  Trace("strings-presolve") << "Finished presolve" << std::endl;
}

/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////

bool TheoryStrings::collectModelValues(TheoryModel* m,
                                       const std::set<Node>& termSet)
{
  d_absModelCounter = 0;
  d_strGapModelCounter = 0;
  if (TraceIsOn("strings-debug-model"))
  {
    Trace("strings-debug-model")
        << "TheoryStrings::collectModelValues" << std::endl;
    Trace("strings-debug-model") << "Equivalence classes are:" << std::endl;
    Trace("strings-debug-model") << debugPrintStringsEqc() << std::endl;
    Trace("strings-debug-model") << "Extended functions are:" << std::endl;
    Trace("strings-debug-model") << d_esolver.debugPrintModel() << std::endl;
  }
  Trace("strings-model") << "TheoryStrings::collectModelValues" << std::endl;
  // Collects representatives by types and orders sequence types by how nested
  // they are
  std::map<TypeNode, std::unordered_set<Node>> repSet;
  std::unordered_set<TypeNode> toProcess;
  // Generate model
  ModelCons* mc = d_state.getModelConstructor();
  Assert(mc != nullptr);
  // get the relevant string equivalence classes
  std::vector<Node> auxEq;
  mc->getStringRepresentativesFrom(termSet, toProcess, repSet, auxEq);
  // assert the auxiliary equalities
  for (const Node& aeq : auxEq)
  {
    Assert(aeq.getKind() == EQUAL);
    Trace("strings-model") << "-> auxiliary equality " << aeq << std::endl;
    if (!m->assertEquality(aeq[0], aeq[1], true))
    {
      Unreachable() << "TheoryStrings::collectModelValues: Inconsistent "
                       "auxiliary equality"
                    << std::endl;
      return false;
    }
  }

  while (!toProcess.empty())
  {
    // Pick one of the remaining types to collect model values for
    TypeNode tn = *toProcess.begin();
    if (!collectModelInfoType(tn, toProcess, repSet, m))
    {
      return false;
    }
  }

  return true;
}

/**
 * Object to sort by the value of pairs in the write model returned by the
 * sequences array solver.
 */
struct SortSeqIndex
{
  SortSeqIndex() {}
  /** the comparison */
  bool operator()(const std::pair<Node, Node>& i,
                  const std::pair<Node, Node>& j)
  {
    Assert(i.first.isConst() && i.first.getType().isInteger()
           && j.first.isConst() && j.first.getType().isInteger());
    return i.first.getConst<Rational>() < j.first.getConst<Rational>();
  }
};

bool TheoryStrings::collectModelInfoType(
    TypeNode tn,
    std::unordered_set<TypeNode>& toProcess,
    const std::map<TypeNode, std::unordered_set<Node> >& repSet,
    TheoryModel* m)
{
  // Make sure that the model values for the element type of sequences are
  // computed first
  if (tn.isSequence() && tn.getSequenceElementType().isSequence())
  {
    TypeNode tnElem = tn.getSequenceElementType();
    if (toProcess.find(tnElem) != toProcess.end()
        && !collectModelInfoType(tnElem, toProcess, repSet, m))
    {
      return false;
    }
  }
  toProcess.erase(tn);

  SEnumLenSet sels;
  ModelCons* mc = d_state.getModelConstructor();
  // get partition of strings of equal lengths for the representatives of the
  // current type
  std::vector<std::vector<Node>> col;
  std::vector<Node> lts;
  const std::vector<Node> repVec(repSet.at(tn).begin(), repSet.at(tn).end());
  mc->separateByLength(repVec, col, lts);
  Assert(col.size() == lts.size());
  // indices in col that have lengths that are too big to represent
  std::unordered_set<size_t> oobIndices;

  NodeManager* nm = NodeManager::currentNM();
  std::map< Node, Node > processed;
  //step 1 : get all values for known lengths
  std::vector< Node > lts_values;
  // mapping from lengths used to the index in col that used that length
  std::map<size_t, size_t> values_used;
  // A list of pairs of indices in col that used the same length term. We use
  // this as candidates to add length splitting on below (STRINGS_CMI_SPLIT),
  // which is used as a safeguard when model construction fails unexpectedly
  // by running out of values.
  std::vector<std::pair<size_t, size_t>> len_splits;
  for (size_t i = 0, csize = col.size(); i < csize; i++)
  {
    Trace("strings-model") << "Checking length for { " << col[i];
    Trace("strings-model") << " } (length is " << lts[i] << ")" << std::endl;
    Node len_value = lts[i];
    if (len_value.isNull())
    {
      lts_values.push_back(Node::null());
    }
    else if (len_value.getConst<Rational>() > options().strings.stringsModelMaxLength)
    {
      // note that we give a warning instead of throwing logic exception if we
      // cannot construct the string, these are then assigned witness terms
      // below
      warning() << "The model was computed to have strings of length "
                << len_value << ". Based on the current value of option --strings-model-max-len, we only allow strings up to length "
                << options().strings.stringsModelMaxLength << std::endl;
      oobIndices.insert(i);
      lts_values.push_back(len_value);
    }
    else
    {
      std::size_t lvalue =
          len_value.getConst<Rational>().getNumerator().toUnsignedInt();
      auto itvu = values_used.find(lvalue);
      if (itvu == values_used.end())
      {
        values_used[lvalue] = i;
      }
      else
      {
        len_splits.emplace_back(i, itvu->second);
      }
      lts_values.push_back(len_value);
    }
  }
  ////step 2 : assign arbitrary values for unknown lengths?
  // confirmed by calculus invariant, see paper
  Trace("strings-model") << "Assign to equivalence classes..." << std::endl;
  std::map<Node, Node> pure_eq_assign;
  // if we are using the sequences array solver, get the connected sequences
  const std::map<Node, Node>* conSeq = nullptr;
  std::map<Node, Node>::const_iterator itcs;
  if (options().strings.seqArray != options::SeqArrayMode::NONE)
  {
    conSeq = &d_asolver.getConnectedSequences();
  }
  //step 3 : assign values to equivalence classes that are pure variables
  for (size_t i = 0, csize = col.size(); i < csize; i++)
  {
    bool wasOob = (oobIndices.find(i) != oobIndices.end());
    std::vector< Node > pure_eq;
    Node lenValue = lts_values[i];
    Trace("strings-model") << "Considering " << col[i].size()
                           << " equivalence classes of type " << tn
                           << " for length " << lenValue << std::endl;
    for (const Node& eqc : col[i])
    {
      Trace("strings-model") << "- eqc: " << eqc << std::endl;
      //check if col[i][j] has only variables
      if (eqc.isConst())
      {
        processed[eqc] = eqc;
        // Make sure that constants are asserted to the theory model that we
        // are building. It is possible that new constants were introduced by
        // the eager evaluation in the equality engine. These terms are missing
        // in the term set and, as a result, are skipped when the equality
        // engine is asserted to the theory model.
        m->getEqualityEngine()->addTerm(eqc);

        // For sequences constants, also add the elements (expanding elements
        // as necessary)
        if (eqc.getType().isSequence())
        {
          const std::vector<Node> elems = eqc.getConst<Sequence>().getVec();
          std::vector<TNode> visit(elems.begin(), elems.end());
          for (size_t j = 0; j < visit.size(); j++)
          {
            Node se = visit[j];
            Assert(se.isConst());
            if (se.getType().isSequence())
            {
              const std::vector<Node> selems = se.getConst<Sequence>().getVec();
              visit.insert(visit.end(), selems.begin(), selems.end());
            }
            m->getEqualityEngine()->addTerm(se);
          }
        }

        Trace("strings-model") << "-> constant" << std::endl;
        continue;
      }
      std::vector<Node> nfe = mc->getNormalForm(eqc);
      if (nfe.size() != 1)
      {
        // will be assigned via a concatenation of normal form eqc
        Trace("strings-model")
            << "  -> will be assigned by normal form " << nfe << std::endl;
        continue;
      }
      // check if the length is too big to represent
      if (wasOob)
      {
        processed[eqc] = eqc;
        Assert(!lenValue.isNull() && lenValue.isConst());
        // make the abstract value (witness ((x String)) (= (str.len x)
        // lenValue))
        Node w = utils::mkAbstractStringValueForLength(
            eqc, lenValue, d_absModelCounter);
        d_absModelCounter++;
        Trace("strings-model")
            << "-> length out of bounds, assign abstract " << w << std::endl;
        if (!m->assertEquality(eqc, w, true))
        {
          Unreachable() << "TheoryStrings::collectModelInfoType: Inconsistent "
                           "abstract equality"
                        << std::endl;
          return false;
        }
        continue;
      }
      // ensure we have decided on length value at this point
      if (lenValue.isNull())
      {
        // start with length two (other lengths have special precendence)
        size_t lvalue = 2;
        while (values_used.find(lvalue) != values_used.end())
        {
          lvalue++;
        }
        Trace("strings-model")
            << "*** Decide to make length of " << lvalue << std::endl;
        lenValue = nm->mkConstInt(Rational(lvalue));
        values_used[lvalue] = i;
      }
      // is it an equivalence class with a seq.unit term?
      Node assignedValue;
      if (nfe[0].getKind() == STRING_UNIT)
      {
        // str.unit is applied to integers, where we are guaranteed the model
        // exists. We preempitively get the model value here, so that we
        // avoid repeated model values for strings.
        Node val = d_valuation.getCandidateModelValue(nfe[0][0]);
        assignedValue = utils::mkUnit(eqc.getType(), val);
        assignedValue = rewrite(assignedValue);
        Trace("strings-model")
            << "-> assign via str.unit: " << assignedValue << std::endl;
      }
      else if (nfe[0].getKind() == SEQ_UNIT)
      {
        if (nfe[0][0].getType().isStringLike())
        {
          // By this point, we should have assigned model values for the
          // elements of this sequence type because of the check in the
          // beginning of this method
          Node argVal = m->getRepresentative(nfe[0][0]);
          Assert(nfe[0].getKind() == SEQ_UNIT);
          assignedValue = utils::mkUnit(eqc.getType(), argVal);
        }
        else
        {
          // Otherwise, we use the term itself. We cannot get the model
          // value of this term, since it might not be available yet, as
          // it may belong to a theory that has not built its model yet.
          // Hence, we assign a (non-constant) skeleton (seq.unit argVal).
          assignedValue = nfe[0];
        }
        assignedValue = rewrite(assignedValue);
        Trace("strings-model")
            << "-> assign via seq.unit: " << assignedValue << std::endl;
      }
      else if (d_termReg.hasStringCode() && lenValue == d_one)
      {
        // It has a code and the length of these equivalence classes are one.
        // Note this code is solely for strings, not sequences.
        EqcInfo* eip = d_state.getOrMakeEqcInfo(eqc, false);
        if (eip && !eip->d_codeTerm.get().isNull())
        {
          // its value must be equal to its code
          Node ct = nm->mkNode(kind::STRING_TO_CODE, eip->d_codeTerm.get());
          Node ctv = d_valuation.getCandidateModelValue(ct);
          unsigned cvalue =
              ctv.getConst<Rational>().getNumerator().toUnsignedInt();
          Trace("strings-model") << "(code: " << cvalue << ") ";
          std::vector<unsigned> vec;
          vec.push_back(cvalue);
          assignedValue = nm->mkConst(String(vec));
          Trace("strings-model")
              << "-> assign via str.code: " << assignedValue << std::endl;
        }
      }
      else if (options().strings.seqArray != options::SeqArrayMode::NONE)
      {
        TypeNode eqcType = eqc.getType();
        // determine skeleton based on the write model, if it exists
        const std::map<Node, Node>& writeModel = d_asolver.getWriteModel(eqc);
        if (!writeModel.empty())
        {
          Trace("strings-model") << "Write model for " << eqc << " (type " << tn
                                 << ") is:" << std::endl;
          std::vector<std::pair<Node, Node>> writes;
          std::unordered_set<Node> usedWrites;
          for (const std::pair<const Node, Node>& w : writeModel)
          {
            Trace("strings-model") << "  " << w.first << " -> " << w.second;
            Node ivalue = d_valuation.getCandidateModelValue(w.first);
            Assert(ivalue.isConst() && ivalue.getType().isInteger());
            // ignore if out of bounds
            Rational irat = ivalue.getConst<Rational>();
            if (irat.sgn() == -1 || irat >= lenValue.getConst<Rational>())
            {
              Trace("strings-model")
                  << " (index " << irat << " out of bounds)" << std::endl;
              continue;
            }
            if (usedWrites.find(ivalue) != usedWrites.end())
            {
              Trace("strings-model")
                  << " (index " << irat << " already written)" << std::endl;
              continue;
            }
            Trace("strings-model") << " (index " << irat << ")" << std::endl;
            usedWrites.insert(ivalue);
            Node wsunit = utils::mkUnit(eqcType, w.second);
            writes.emplace_back(ivalue, wsunit);
          }
          // sort based on index value
          SortSeqIndex ssi;
          std::sort(writes.begin(), writes.end(), ssi);
          std::vector<Node> cc;
          uint32_t currIndex = 0;
          for (size_t w = 0, wsize = writes.size(); w <= wsize; w++)
          {
            uint32_t nextIndex;
            if (w == writes.size())
            {
              nextIndex =
                  lenValue.getConst<Rational>().getNumerator().toUnsignedInt();
            }
            else
            {
              Node windex = writes[w].first;
              Assert(windex.getConst<Rational>()
                     <= Rational(String::maxSize()));
              nextIndex =
                  windex.getConst<Rational>().getNumerator().toUnsignedInt();
              Assert(nextIndex >= currIndex);
            }
            if (nextIndex > currIndex)
            {
              Trace("strings-model") << "Make skeleton from " << currIndex
                                     << " ... " << nextIndex << std::endl;
              // allocate arbitrary value to fill gap
              Assert(conSeq != nullptr);
              Node base = eqc;
              itcs = conSeq->find(eqc);
              if (itcs != conSeq->end())
              {
                base = itcs->second;
              }
              // use a skeleton for the gap and not a concrete value, as we
              // do not know how which values from the element type are
              // allowable (i.e. unconstrained) to assign to the gap
              Node cgap = mkSkeletonFromBase(base, currIndex, nextIndex);
              cc.push_back(cgap);
            }
            // then take read
            if (w < wsize)
            {
              cc.push_back(writes[w].second);
            }
            currIndex = nextIndex + 1;
          }
          assignedValue = utils::mkConcat(cc, tn);
          Trace("strings-model")
              << "-> assign via seq.update/nth eqc: " << assignedValue
              << std::endl;
        }
      }
      if (!assignedValue.isNull())
      {
        pure_eq_assign[eqc] = assignedValue;
        m->getEqualityEngine()->addTerm(assignedValue);
      }
      else
      {
        Trace("strings-model") << "-> no assignment" << std::endl;
      }
      pure_eq.push_back(eqc);
    }

    //assign a new length if necessary
    if( !pure_eq.empty() ){
      Trace("strings-model") << "Need to assign values of length " << lenValue
                             << " to equivalence classes ";
      for( unsigned j=0; j<pure_eq.size(); j++ ){
        Trace("strings-model") << pure_eq[j] << " ";
      }
      Trace("strings-model") << std::endl;

      //use type enumerator
      Assert(lenValue.getConst<Rational>() <= Rational(String::maxSize()))
          << "Exceeded UINT32_MAX in string model";
      uint32_t currLen =
          lenValue.getConst<Rational>().getNumerator().toUnsignedInt();
      Trace("strings-model") << "Cardinality of alphabet is "
                             << d_termReg.getAlphabetCardinality() << std::endl;
      SEnumLen* sel = sels.getEnumerator(currLen, tn);
      for (const Node& eqc : pure_eq)
      {
        Node c;
        std::map<Node, Node>::iterator itp = pure_eq_assign.find(eqc);
        if (itp == pure_eq_assign.end())
        {
          do
          {
            if (sel->isFinished())
            {
              // We are in a case where model construction is impossible due to
              // an insufficient number of constants of a given length.

              // Consider an integer equivalence class E whose value is assigned
              // n in the model. Let { S_1, ..., S_m } be the set of string
              // equivalence classes such that len( x ) is a member of E for
              // some member x of each class S1, ...,Sm. Since our calculus is
              // saturated with respect to cardinality inference (see Liang
              // et al, Figure 6, CAV 2014), we have that m <= A^n, where A is
              // the cardinality of our alphabet.

              // Now, consider the case where there exists two integer
              // equivalence classes E1 and E2 that are assigned n, and moreover
              // we did not received notification from arithmetic that E1 = E2.
              // This typically should never happen, but assume in the following
              // that it does.

              // Now, it may be the case that there are string equivalence
              // classes { S_1, ..., S_m1 } whose lengths are in E1,
              // and classes { S'_1, ..., S'_m2 } whose lengths are in E2, where
              // m1 + m2 > A^n. In this case, we have insufficient strings to
              // assign to { S_1, ..., S_m1, S'_1, ..., S'_m2 }. If this
              // happens, we add a split on len( u1 ) = len( u2 ) for some
              // len( u1 ) in E1, len( u2 ) in E2. We do this for each pair of
              // integer equivalence classes that are assigned to the same value
              // in the model.
              AlwaysAssert(!len_splits.empty());
              for (const std::pair<size_t, size_t>& sl : len_splits)
              {
                Node s1 = nm->mkNode(STRING_LENGTH, col[sl.first][0]);
                Node s2 = nm->mkNode(STRING_LENGTH, col[sl.second][0]);
                Node eq = s1.eqNode(s2);
                Node spl = nm->mkNode(OR, eq, eq.negate());
                d_im.lemma(spl, InferenceId::STRINGS_CMI_SPLIT);
                Trace("strings-lemma")
                    << "Strings::CollectModelInfoSplit: " << spl << std::endl;
              }
              // we added a lemma, so can return here
              return false;
            }
            c = sel->getCurrent();
            // if we are a sequence with infinite element type
            if (tn.isSequence()
                && !d_env.isFiniteType(tn.getSequenceElementType()))
            {
              // Make a skeleton instead.
              c = mkSkeletonFor(c);
            }
            // increment
            sel->increment();
          } while (m->hasTerm(c));
        }
        else
        {
          c = itp->second;
        }
        Trace("strings-model") << "*** Assigned constant " << c << " for "
                               << eqc << std::endl;
        processed[eqc] = c;
        if (!m->assertEquality(eqc, c, true))
        {
          // this should never happen due to the model soundness argument
          // for strings
          Unreachable()
              << "TheoryStrings::collectModelInfoType: Inconsistent equality"
              << std::endl;
          return false;
        }
      }
    }
  }
  Trace("strings-model") << "String Model : Pure Assigned." << std::endl;
  //step 4 : assign constants to all other equivalence classes
  for (const Node& rn : repVec)
  {
    if (processed.find(rn) != processed.end())
    {
      continue;
    }

    std::vector<Node> nf = mc->getNormalForm(rn);
    if (TraceIsOn("strings-model"))
    {
      Trace("strings-model")
          << "Construct model for " << rn << " based on normal form ";
      for (unsigned j = 0, size = nf.size(); j < size; j++)
      {
        Node n = nf[j];
        if (j > 0)
        {
          Trace("strings-model") << " ++ ";
        }
        Trace("strings-model") << n;
        Node r = d_state.getRepresentative(n);
        if (!r.isConst() && processed.find(r) == processed.end())
        {
          Trace("strings-model") << "(UNPROCESSED)";
        }
      }
    }
    Trace("strings-model") << std::endl;
    std::vector<Node> nc;
    for (const Node& n : nf)
    {
      Node r = d_state.getRepresentative(n);
      Assert(r.isConst() || processed.find(r) != processed.end());
      nc.push_back(r.isConst() ? r : processed[r]);
    }
    Node cc = d_termReg.mkNConcat(nc, tn);
    Trace("strings-model") << "*** Determined constant " << cc << " for " << rn
                           << std::endl;
    processed[rn] = cc;
    if (!m->assertEquality(rn, cc, true))
    {
      // this should never happen due to the model soundness argument
      // for strings
      Unreachable() << "TheoryStrings::collectModelInfoType: "
                       "Inconsistent equality (unprocessed eqc)"
                    << std::endl;
      return false;
    }
    else if (!cc.isConst())
    {
      // the value may be specified by seq.unit components, ensure this
      // is marked as the skeleton for constructing values in this class.
      m->assertSkeleton(cc);
    }
  }
  //Trace("strings-model") << "String Model : Assigned." << std::endl;
  Trace("strings-model") << "String Model : Finished." << std::endl;
  return true;
}

Node TheoryStrings::mkSkeletonFor(Node c)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  BoundVarManager* bvm = nm->getBoundVarManager();
  TypeNode tn = c.getType();
  Assert(tn.isSequence());
  Assert(c.getKind() == CONST_SEQUENCE);
  const Sequence& sn = c.getConst<Sequence>();
  const std::vector<Node>& snvec = sn.getVec();
  std::vector<Node> skChildren;
  TypeNode etn = tn.getSequenceElementType();
  for (const Node& snv : snvec)
  {
    Assert(snv.getType() == etn);
    Node v = bvm->mkBoundVar<SeqModelVarAttribute>(snv, etn);
    // use a skolem, not a bound variable
    Node kv = sm->mkPurifySkolem(v);
    skChildren.push_back(utils::mkUnit(tn, kv));
  }
  return utils::mkConcat(skChildren, c.getType());
}

Node TheoryStrings::mkSkeletonFromBase(Node r,
                                       size_t currIndex,
                                       size_t nextIndex)
{
  Assert(nextIndex > currIndex);
  Assert(!r.isNull());
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  TypeNode tn = r.getType();
  std::vector<Node> skChildren;
  if (tn.isSequence())
  {
    std::vector<Node> cacheVals(2);
    cacheVals[0] = r;
    TypeNode etn = tn.getSequenceElementType();
    for (size_t i = currIndex; i < nextIndex; i++)
    {
      cacheVals[1] = nm->mkConstInt(Rational(i));
      Node kv = sm->mkSkolemFunction(
          SkolemFunId::SEQ_MODEL_BASE_ELEMENT, etn, cacheVals);
      skChildren.push_back(utils::mkUnit(tn, kv));
    }
  }
  else
  {
    // allocate a unique symbolic (unspecified) string of length one, and
    // repeat it (nextIndex-currIndex) times.
    // Notice that this is guaranteed to be a unique (unspecified) character,
    // since the only existing str.unit terms originate from our reductions,
    // and hence are only applied to non-negative arguments. If the user
    // was able to give arbitrary constraints over str.unit terms, then this
    // construction would require a character not used in the model value of
    // any other string.
    d_strGapModelCounter++;
    Node symChar =
        utils::mkUnit(tn, nm->mkConstInt(-Rational(d_strGapModelCounter)));
    skChildren.resize(nextIndex - currIndex, symChar);
  }
  return utils::mkConcat(skChildren, tn);
}

/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////

void TheoryStrings::preRegisterTerm(TNode n)
{
  Trace("strings-preregister")
      << "TheoryStrings::preRegisterTerm: " << n << std::endl;
  d_termReg.preRegisterTerm(n);
  // Register the term with the extended theory. Notice we do not recurse on
  // this term here since preRegisterTerm is already called recursively on all
  // subterms in preregistered literals.
  d_extTheory.registerTerm(n);
}

bool TheoryStrings::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  if (atom.getKind() == EQUAL)
  {
    // this is only required for internal facts, others are already registered
    if (isInternal)
    {
      // We must ensure these terms are registered. We register eagerly here for
      // performance reasons. Alternatively, terms could be registered at full
      // effort in e.g. BaseSolver::init.
      for (const Node& t : atom)
      {
        d_termReg.registerTerm(t);
      }
    }
    // store disequalities between strings that occur as literals
    if (!pol && atom[0].getType().isStringLike())
    {
      d_state.addDisequality(atom[0], atom[1]);
    }
  }
  return false;
}

void TheoryStrings::notifyFact(TNode atom,
                               bool polarity,
                               TNode fact,
                               bool isInternal)
{
  if (d_eagerSolver)
  {
    d_eagerSolver->notifyFact(atom, polarity, fact, isInternal);
  }
  // process pending conflicts due to reasoning about endpoints
  if (!d_state.isInConflict() && d_state.hasPendingConflict())
  {
    InferInfo iiPendingConf(InferenceId::UNKNOWN);
    d_state.getPendingConflict(iiPendingConf);
    Trace("strings-pending")
        << "Process pending conflict " << iiPendingConf.d_premises << std::endl;
    Trace("strings-conflict")
        << "CONFLICT: Eager : " << iiPendingConf.d_premises << std::endl;
    ++(d_statistics.d_conflictsEager);
    // call the inference manager to send the conflict
    d_im.processConflict(iiPendingConf);
    return;
  }
  // if not doing eager registration, we now register all subterms of the atom
  if (!options().strings.stringEagerReg)
  {
    d_termReg.registerSubterms(atom);
  }
  Trace("strings-pending-debug") << "  Now collect terms" << std::endl;
  Trace("strings-pending-debug") << "  Finished collect terms" << std::endl;
}

void TheoryStrings::postCheck(Effort e)
{
  d_im.doPendingFacts();

  Assert(d_strat.isStrategyInit());
  if (!d_state.isInConflict() && !d_valuation.needCheck()
      && d_strat.hasStrategyEffort(e))
  {
    Trace("strings-check-debug")
        << "Theory of strings " << e << " effort check " << std::endl;
    if (TraceIsOn("strings-eqc"))
    {
      Trace("strings-eqc") << debugPrintStringsEqc() << std::endl;
    }
    // Start the full effort check. This will compute the relevant term set,
    // which is independent of the loop below, which adds internal facts.
    d_termReg.notifyStartFullEffortCheck();
    ++(d_statistics.d_checkRuns);
    bool sentLemma = false;
    bool hadPending = false;
    Trace("strings-check") << "Check at effort " << e << "..." << std::endl;
    do{
      d_im.reset();
      // assume the default model constructor in case we answer sat after this
      // check
      d_state.setModelConstructor(&d_mcd);
      ++(d_statistics.d_strategyRuns);
      Trace("strings-check") << "  * Run strategy..." << std::endl;
      runStrategy(e);
      // remember if we had pending facts or lemmas
      hadPending = d_im.hasPending();
      // Send the facts *and* the lemmas. We send lemmas regardless of whether
      // we send facts since some lemmas cannot be dropped. Other lemmas are
      // otherwise avoided by aborting the strategy when a fact is ready.
      d_im.doPending();
      // Did we successfully send a lemma? Notice that if hasPending = true
      // and sentLemma = false, then the above call may have:
      // (1) had no pending lemmas, but successfully processed pending facts,
      // (2) unsuccessfully processed pending lemmas.
      // In either case, we repeat the strategy if we are not in conflict.
      sentLemma = d_im.hasSentLemma();
      if (TraceIsOn("strings-check"))
      {
        Trace("strings-check") << "  ...finish run strategy: ";
        Trace("strings-check") << (hadPending ? "hadPending " : "");
        Trace("strings-check") << (sentLemma ? "sentLemma " : "");
        Trace("strings-check") << (d_state.isInConflict() ? "conflict " : "");
        if (!hadPending && !sentLemma && !d_state.isInConflict())
        {
          Trace("strings-check") << "(none)";
        }
        Trace("strings-check") << std::endl;
      }
      // repeat if we did not add a lemma or conflict, and we had pending
      // facts or lemmas.
    } while (!d_state.isInConflict() && !sentLemma && hadPending);
    // End the full effort check.
    d_termReg.notifyEndFullEffortCheck();
  }
  Trace("strings-check") << "Theory of strings, done check : " << e << std::endl;
  Assert(!d_im.hasPendingFact());
  Assert(!d_im.hasPendingLemma());
}

bool TheoryStrings::needsCheckLastEffort() {
  if (options().strings.stringModelBasedReduction)
  {
    bool hasExtf = d_esolver.hasExtendedFunctions();
    Trace("strings-process")
        << "needsCheckLastEffort: hasExtf = " << hasExtf << std::endl;
    return hasExtf;
  }
  return false;
}

/** Conflict when merging two constants */
void TheoryStrings::conflict(TNode a, TNode b){
  if (d_state.isInConflict())
  {
    // already in conflict
    return;
  }
  d_im.conflictEqConstantMerge(a, b);
  Trace("strings-conflict") << "CONFLICT: Eq engine conflict" << std::endl;
  ++(d_statistics.d_conflictsEqEngine);
}

void TheoryStrings::eqNotifyNewClass(TNode t){
  Kind k = t.getKind();
  if (k == STRING_LENGTH || k == STRING_TO_CODE)
  {
    Trace("strings-debug") << "New length eqc : " << t << std::endl;

    eq::EqualityEngine* ee = d_state.getEqualityEngine();
    Node r = ee->getRepresentative(t[0]);
    EqcInfo* ei = d_state.getOrMakeEqcInfo(r);
    if (k == STRING_LENGTH)
    {
      ei->d_lengthTerm = t;
    }
    else
    {
      ei->d_codeTerm = t[0];
    }
  }
  if (d_eagerSolver)
  {
    d_eagerSolver->eqNotifyNewClass(t);
  }
}

void TheoryStrings::eqNotifyMerge(TNode t1, TNode t2)
{
  EqcInfo* e2 = d_state.getOrMakeEqcInfo(t2, false);
  if (e2 == nullptr)
  {
    return;
  }
  // always create it if e2 was non-null
  EqcInfo* e1 = d_state.getOrMakeEqcInfo(t1);

  if (d_eagerSolver)
  {
    d_eagerSolver->eqNotifyMerge(e1, t1, e2, t2);
  }

  // add information from e2 to e1
  if (!e2->d_lengthTerm.get().isNull())
  {
    e1->d_lengthTerm.set(e2->d_lengthTerm);
  }
  if (!e2->d_codeTerm.get().isNull())
  {
    e1->d_codeTerm.set(e2->d_codeTerm);
  }
  if (e2->d_cardinalityLemK.get() > e1->d_cardinalityLemK.get())
  {
    e1->d_cardinalityLemK.set(e2->d_cardinalityLemK);
  }
  if (!e2->d_normalizedLength.get().isNull())
  {
    e1->d_normalizedLength.set(e2->d_normalizedLength);
  }
}

void TheoryStrings::computeCareGraph()
{
  //computing the care graph here is probably still necessary, due to operators that take non-string arguments  TODO: verify
  Trace("strings-cg") << "TheoryStrings::computeCareGraph(): Build term indices..." << std::endl;
  // Term index for each (type, operator) pair. We require the operator here
  // since operators are polymorphic, taking strings/sequences.
  std::map<std::pair<TypeNode, Node>, TNodeTrie> index;
  std::map< Node, unsigned > arity;
  const context::CDList<TNode>& fterms = d_termReg.getFunctionTerms();
  size_t functionTerms = fterms.size();
  for (unsigned i = 0; i < functionTerms; ++ i) {
    TNode f1 = fterms[i];
    Trace("strings-cg") << "...build for " << f1 << std::endl;
    Node op = f1.getOperator();
    std::vector< TNode > reps;
    bool has_trigger_arg = false;
    for( unsigned j=0; j<f1.getNumChildren(); j++ ){
      reps.push_back(d_equalityEngine->getRepresentative(f1[j]));
      if (d_equalityEngine->isTriggerTerm(f1[j], THEORY_STRINGS))
      {
        has_trigger_arg = true;
      }
    }
    if( has_trigger_arg ){
      TypeNode ft = utils::getOwnerStringType(f1);
      std::pair<TypeNode, Node> ikey = std::pair<TypeNode, Node>(ft, op);
      index[ikey].addTerm(f1, reps);
      arity[op] = reps.size();
    }
  }
  //for each index
  for (std::pair<const std::pair<TypeNode, Node>, TNodeTrie>& ti : index)
  {
    Trace("strings-cg") << "TheoryStrings::computeCareGraph(): Process index "
                        << ti.first << "..." << std::endl;
    Node op = ti.first.second;
    nodeTriePathPairProcess(&ti.second, arity[op], d_cpacb);
  }
}

void TheoryStrings::notifySharedTerm(TNode n)
{
  // a new shared term causes new terms to be relevant, hence we register
  // them if not doing eager registration.
  if (!options().strings.stringEagerReg)
  {
    d_termReg.registerSubterms(n);
  }
}

TrustNode TheoryStrings::ppRewrite(TNode atom, std::vector<SkolemLemma>& lems)
{
  Trace("strings-ppr") << "TheoryStrings::ppRewrite " << atom << std::endl;
  Kind ak = atom.getKind();
  if (ak == STRING_FROM_CODE)
  {
    // str.from_code(t) ---> ite(0 <= t < |A|, t = str.to_code(k), k = "")
    NodeManager* nm = NodeManager::currentNM();
    SkolemCache* sc = d_termReg.getSkolemCache();
    Node k = sc->mkSkolemCached(atom, SkolemCache::SK_PURIFY, "kFromCode");
    Node t = atom[0];
    Node card = nm->mkConstInt(Rational(d_termReg.getAlphabetCardinality()));
    Node cond =
        nm->mkNode(AND, nm->mkNode(LEQ, d_zero, t), nm->mkNode(LT, t, card));
    Node emp = Word::mkEmptyWord(atom.getType());
    Node pred = nm->mkNode(
        ITE, cond, t.eqNode(nm->mkNode(STRING_TO_CODE, k)), k.eqNode(emp));
    TrustNode tnk = TrustNode::mkTrustLemma(pred);
    lems.push_back(SkolemLemma(tnk, k));
    return TrustNode::mkTrustRewrite(atom, k, nullptr);
  }
  if (options().strings.stringsCodeElim)
  {
    if (ak == STRING_TO_CODE)
    {
      // If we are eliminating code, convert it to nth.
      // str.to_code(t) ---> ite(str.len(t) = 1, str.nth(t,0), -1)
      NodeManager* nm = NodeManager::currentNM();
      Node t = atom[0];
      Node cond = nm->mkNode(EQUAL, nm->mkNode(STRING_LENGTH, t), d_one);
      Node ret =
          nm->mkNode(ITE, cond, nm->mkNode(SEQ_NTH, t, d_zero), d_neg_one);
      return TrustNode::mkTrustRewrite(atom, ret, nullptr);
    }
  }
  else if (ak == SEQ_NTH && atom[0].getType().isString())
  {
    // If we are not eliminating code, we are eliminating nth (over strings);
    // convert it to code.
    // (seq.nth x n) ---> (str.to_code (str.substr x n 1))
    NodeManager* nm = NodeManager::currentNM();
    Node ret = nm->mkNode(
        STRING_TO_CODE,
        nm->mkNode(
            STRING_SUBSTR, atom[0], atom[1], nm->mkConstInt(Rational(1))));
    return TrustNode::mkTrustRewrite(atom, ret, nullptr);
  }
  else if (ak == REGEXP_RANGE)
  {
    for (const Node& nc : atom)
    {
      if (!nc.isConst())
      {
        throw LogicException(
            "expecting a constant string term in regexp range");
      }
      if (nc.getConst<String>().size() != 1)
      {
        throw LogicException(
            "expecting a single constant string term in regexp range");
      }
    }
  }

  TrustNode ret;
  Node atomRet = atom;
  if (options().strings.regExpElim != options::RegExpElimMode::OFF
      && ak == STRING_IN_REGEXP)
  {
    // aggressive elimination of regular expression membership
    ret = d_regexp_elim.eliminateTrusted(atomRet);
    if (!ret.isNull())
    {
      Trace("strings-ppr") << "  rewrote " << atom << " -> " << ret.getNode()
                           << " via regular expression elimination."
                           << std::endl;
      atomRet = ret.getNode();
    }
  }
  if (options().strings.stringFMF)
  {
    // Our decision strategy will minimize the length of this term if it is a
    // variable but not an internally generated Skolem, or a term that does
    // not belong to this theory.
    if (atom.isVar() ? !d_termReg.getSkolemCache()->isSkolem(atom)
                     : kindToTheoryId(ak) != THEORY_STRINGS
                           && atom.getType().isStringLike())
    {
      d_termReg.preRegisterInputVar(atom);
      Trace("strings-preregister") << "input variable: " << atom << std::endl;
    }
  }

  // all characters of constants should fall in the alphabet
  if (atom.isConst() && atom.getType().isString())
  {
    uint32_t alphaCard = d_termReg.getAlphabetCardinality();
    std::vector<unsigned> vec = atom.getConst<String>().getVec();
    for (unsigned u : vec)
    {
      if (u >= alphaCard)
      {
        std::stringstream ss;
        ss << "Characters in string \"" << atom
           << "\" are outside of the given alphabet.";
        throw LogicException(ss.str());
      }
    }
  }
  if (!options().strings.stringExp)
  {
    if (ak == STRING_INDEXOF || ak == STRING_INDEXOF_RE || ak == STRING_ITOS
        || ak == STRING_STOI || ak == STRING_REPLACE || ak == STRING_SUBSTR
        || ak == STRING_REPLACE_ALL || ak == SEQ_NTH || ak == STRING_REPLACE_RE
        || ak == STRING_REPLACE_RE_ALL || ak == STRING_CONTAINS
        || ak == STRING_LEQ || ak == STRING_TO_LOWER || ak == STRING_TO_UPPER
        || ak == STRING_REV || ak == STRING_UPDATE)
    {
      std::stringstream ss;
      ss << "Term of kind " << printer::smt2::Smt2Printer::smtKindStringOf(atom)
         << " not supported in default mode, try --strings-exp";
      throw LogicException(ss.str());
    }
  }
  return ret;
}

TrustNode TheoryStrings::ppStaticRewrite(TNode atom)
{
  Kind ak = atom.getKind();
  if (ak == EQUAL)
  {
    if (atom[0].getType().isRegExp())
    {
      std::stringstream ss;
      ss << "Equality between regular expressions is not supported";
      throw LogicException(ss.str());
    }
    // always apply aggressive equality rewrites here
    Node ret = d_rewriter.rewriteEqualityExt(atom);
    if (ret != atom)
    {
      return TrustNode::mkTrustRewrite(atom, ret, nullptr);
    }
  }
  return TrustNode::null();
}

/** run the given inference step */
void TheoryStrings::runInferStep(InferStep s, Theory::Effort e, int effort)
{
  Trace("strings-process") << "Run " << s;
  if (effort > 0)
  {
    Trace("strings-process") << ", effort = " << effort;
  }
  Trace("strings-process") << "..." << std::endl;
  switch (s)
  {
    case CHECK_INIT: d_bsolver.checkInit(); break;
    case CHECK_CONST_EQC: d_bsolver.checkConstantEquivalenceClasses(); break;
    case CHECK_EXTF_EVAL: d_esolver.checkExtfEval(effort); break;
    case CHECK_CYCLES: d_csolver.checkCycles(); break;
    case CHECK_FLAT_FORMS: d_csolver.checkFlatForms(); break;
    case CHECK_NORMAL_FORMS_EQ_PROP: d_csolver.checkNormalFormsEqProp(); break;
    case CHECK_NORMAL_FORMS_EQ: d_csolver.checkNormalFormsEq(); break;
    case CHECK_NORMAL_FORMS_DEQ: d_csolver.checkNormalFormsDeq(); break;
    case CHECK_CODES: d_psolver.checkCodes(); break;
    case CHECK_LENGTH_EQC: d_csolver.checkLengthsEqc(); break;
    case CHECK_SEQUENCES_ARRAY_CONCAT: d_asolver.checkArrayConcat(); break;
    case CHECK_SEQUENCES_ARRAY: d_asolver.checkArray(); break;
    case CHECK_SEQUENCES_ARRAY_EAGER: d_asolver.checkArrayEager(); break;
    case CHECK_REGISTER_TERMS_NF:
      d_csolver.checkRegisterTermsNormalForms();
      break;
    case CHECK_EXTF_REDUCTION_EAGER:
      d_esolver.checkExtfReductionsEager();
      break;
    case CHECK_EXTF_REDUCTION: d_esolver.checkExtfReductions(e); break;
    case CHECK_MEMBERSHIP_EAGER: d_rsolver.checkMembershipsEager(); break;
    case CHECK_MEMBERSHIP: d_rsolver.checkMemberships(e); break;
    case CHECK_CARDINALITY: d_bsolver.checkCardinality(); break;
    default: Unreachable(); break;
  }
  Trace("strings-process") << "Done " << s
                           << ", addedFact = " << d_im.hasPendingFact()
                           << ", addedLemma = " << d_im.hasPendingLemma()
                           << ", conflict = " << d_state.isInConflict()
                           << std::endl;
}

void TheoryStrings::runStrategy(Theory::Effort e)
{
  std::vector<std::pair<InferStep, int> >::iterator it = d_strat.stepBegin(e);
  std::vector<std::pair<InferStep, int> >::iterator stepEnd =
      d_strat.stepEnd(e);

  Trace("strings-process") << "----check, next round---" << std::endl;
  while (it != stepEnd)
  {
    InferStep curr = it->first;
    int effort = it->second;
    if (curr == BREAK)
    {
      // if we have a pending inference or lemma, we will process it
      if (d_im.hasProcessed())
      {
        break;
      }
    }
    else
    {
      runInferStep(curr, e, effort);
      if (d_state.isInConflict())
      {
        break;
      }
    }
    ++it;
  }
  Trace("strings-process") << "----finished round---" << std::endl;
}

std::string TheoryStrings::debugPrintStringsEqc()
{
  std::stringstream ss;
  for (unsigned t = 0; t < 2; t++)
  {
    eq::EqClassesIterator eqcs2_i = eq::EqClassesIterator(d_equalityEngine);
    ss << (t == 0 ? "STRINGS:" : "OTHER:") << std::endl;
    while (!eqcs2_i.isFinished())
    {
      Node eqc = (*eqcs2_i);
      bool print = (t == 0 && eqc.getType().isStringLike())
                   || (t == 1 && !eqc.getType().isStringLike());
      if (print)
      {
        eq::EqClassIterator eqc2_i = eq::EqClassIterator(eqc, d_equalityEngine);
        ss << "Eqc( " << eqc << " ) : { ";
        while (!eqc2_i.isFinished())
        {
          if ((*eqc2_i) != eqc && (*eqc2_i).getKind() != kind::EQUAL)
          {
            ss << (*eqc2_i) << " ";
          }
          ++eqc2_i;
        }
        ss << " } " << std::endl;
        EqcInfo* ei = d_state.getOrMakeEqcInfo(eqc, false);
        if (ei)
        {
          Trace("strings-eqc-debug")
              << "* Length term : " << ei->d_lengthTerm.get() << std::endl;
          Trace("strings-eqc-debug")
              << "* Cardinality lemma k : " << ei->d_cardinalityLemK.get()
              << std::endl;
          Trace("strings-eqc-debug")
              << "* Normalization length lemma : "
              << ei->d_normalizedLength.get() << std::endl;
        }
      }
      ++eqcs2_i;
    }
    ss << std::endl;
  }
  ss << std::endl;
  return ss.str();
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

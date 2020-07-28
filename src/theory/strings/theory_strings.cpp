/*********************                                                        */
/*! \file theory_strings.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the theory of strings.
 **/

#include "theory/strings/theory_strings.h"

#include "expr/kind.h"
#include "options/strings_options.h"
#include "options/theory_options.h"
#include "smt/logic_exception.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/type_enumerator.h"
#include "theory/strings/word.h"
#include "theory/theory_model.h"
#include "theory/valuation.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

TheoryStrings::TheoryStrings(context::Context* c,
                             context::UserContext* u,
                             OutputChannel& out,
                             Valuation valuation,
                             const LogicInfo& logicInfo,
                             ProofNodeManager* pnm)
    : Theory(THEORY_STRINGS, c, u, out, valuation, logicInfo, pnm),
      d_notify(*this),
      d_statistics(),
      d_equalityEngine(d_notify, c, "theory::strings::ee", true),
      d_state(c, u, d_equalityEngine, d_valuation),
      d_termReg(d_state, d_equalityEngine, out, d_statistics, nullptr),
      d_extTheory(this),
      d_im(c, u, d_state, d_termReg, d_extTheory, out, d_statistics),
      d_rewriter(&d_statistics.d_rewrites),
      d_bsolver(d_state, d_im),
      d_csolver(d_state, d_im, d_termReg, d_bsolver),
      d_esolver(c,
                u,
                d_state,
                d_im,
                d_termReg,
                d_rewriter,
                d_bsolver,
                d_csolver,
                d_extTheory,
                d_statistics),
      d_rsolver(d_state, d_im, d_csolver, d_esolver, d_statistics, c, u),
      d_stringsFmf(c, u, valuation, d_termReg)
{
  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::STRING_LENGTH);
  d_equalityEngine.addFunctionKind(kind::STRING_CONCAT);
  d_equalityEngine.addFunctionKind(kind::STRING_IN_REGEXP);
  d_equalityEngine.addFunctionKind(kind::STRING_TO_CODE);
  d_equalityEngine.addFunctionKind(kind::SEQ_UNIT);

  // extended functions
  d_equalityEngine.addFunctionKind(kind::STRING_STRCTN);
  d_equalityEngine.addFunctionKind(kind::STRING_LEQ);
  d_equalityEngine.addFunctionKind(kind::STRING_SUBSTR);
  d_equalityEngine.addFunctionKind(kind::STRING_UPDATE);
  d_equalityEngine.addFunctionKind(kind::STRING_ITOS);
  d_equalityEngine.addFunctionKind(kind::STRING_STOI);
  d_equalityEngine.addFunctionKind(kind::STRING_STRIDOF);
  d_equalityEngine.addFunctionKind(kind::STRING_STRREPL);
  d_equalityEngine.addFunctionKind(kind::STRING_STRREPLALL);
  d_equalityEngine.addFunctionKind(kind::STRING_REPLACE_RE);
  d_equalityEngine.addFunctionKind(kind::STRING_REPLACE_RE_ALL);
  d_equalityEngine.addFunctionKind(kind::STRING_STRREPLALL);
  d_equalityEngine.addFunctionKind(kind::STRING_TOLOWER);
  d_equalityEngine.addFunctionKind(kind::STRING_TOUPPER);
  d_equalityEngine.addFunctionKind(kind::STRING_REV);

  d_zero = NodeManager::currentNM()->mkConst( Rational( 0 ) );
  d_one = NodeManager::currentNM()->mkConst( Rational( 1 ) );
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );

  d_cardSize = utils::getAlphabetCardinality();
}

TheoryStrings::~TheoryStrings() {

}

TheoryRewriter* TheoryStrings::getTheoryRewriter() { return &d_rewriter; }
std::string TheoryStrings::identify() const
{
  return std::string("TheoryStrings");
}
eq::EqualityEngine* TheoryStrings::getEqualityEngine()
{
  return &d_equalityEngine;
}
void TheoryStrings::finishInit()
{
  TheoryModel* tm = d_valuation.getModel();
  // witness is used to eliminate str.from_code
  tm->setUnevaluatedKind(WITNESS);
}

bool TheoryStrings::areCareDisequal( TNode x, TNode y ) {
  Assert(d_equalityEngine.hasTerm(x));
  Assert(d_equalityEngine.hasTerm(y));
  if( d_equalityEngine.isTriggerTerm(x, THEORY_STRINGS) && d_equalityEngine.isTriggerTerm(y, THEORY_STRINGS) ){
    TNode x_shared = d_equalityEngine.getTriggerTermRepresentative(x, THEORY_STRINGS);
    TNode y_shared = d_equalityEngine.getTriggerTermRepresentative(y, THEORY_STRINGS);
    EqualityStatus eqStatus = d_valuation.getEqualityStatus(x_shared, y_shared);
    if( eqStatus==EQUALITY_FALSE_AND_PROPAGATED || eqStatus==EQUALITY_FALSE || eqStatus==EQUALITY_FALSE_IN_MODEL ){
      return true;
    }
  }
  return false;
}

void TheoryStrings::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

void TheoryStrings::addSharedTerm(TNode t) {
  Debug("strings") << "TheoryStrings::addSharedTerm(): "
                     << t << " " << t.getType().isBoolean() << endl;
  d_equalityEngine.addTriggerTerm(t, THEORY_STRINGS);
  if (options::stringExp())
  {
    d_esolver.addSharedTerm(t);
  }
  Debug("strings") << "TheoryStrings::addSharedTerm() finished" << std::endl;
}

EqualityStatus TheoryStrings::getEqualityStatus(TNode a, TNode b) {
  if( d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b) ){
    if (d_equalityEngine.areEqual(a, b)) {
      // The terms are implied to be equal
      return EQUALITY_TRUE;
    }
    if (d_equalityEngine.areDisequal(a, b, false)) {
      // The terms are implied to be dis-equal
      return EQUALITY_FALSE;
    }
  }
  return EQUALITY_UNKNOWN;
}

void TheoryStrings::propagate(Effort e) {
  // direct propagation now
}

bool TheoryStrings::propagate(TNode literal) {
  Debug("strings-propagate") << "TheoryStrings::propagate(" << literal  << ")" << std::endl;
  // If already in conflict, no more propagation
  if (d_state.isInConflict())
  {
    Debug("strings-propagate") << "TheoryStrings::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }
  // Propagate out
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_state.setConflict();
  }
  return ok;
}

TrustNode TheoryStrings::explain(TNode literal)
{
  Debug("strings-explain") << "explain called on " << literal << std::endl;
  std::vector< TNode > assumptions;
  d_im.explain(literal, assumptions);
  Node ret;
  if( assumptions.empty() ){
    ret = d_true;
  }else if( assumptions.size()==1 ){
    ret = assumptions[0];
  }else{
    ret = NodeManager::currentNM()->mkNode(kind::AND, assumptions);
  }
  return TrustNode::mkTrustPropExp(literal, ret, nullptr);
}

bool TheoryStrings::getCurrentSubstitution( int effort, std::vector< Node >& vars, 
                                            std::vector< Node >& subs, std::map< Node, std::vector< Node > >& exp ) {
  Trace("strings-subs") << "getCurrentSubstitution, effort = " << effort << std::endl;
  for( unsigned i=0; i<vars.size(); i++ ){
    Node n = vars[i];
    Trace("strings-subs") << "  get subs for " << n << "..." << std::endl;
    Node s = d_esolver.getCurrentSubstitutionFor(effort, n, exp[n]);
    subs.push_back(s);
  }
  return true;
}

void TheoryStrings::presolve() {
  Debug("strings-presolve") << "TheoryStrings::Presolving : get fmf options " << (options::stringFMF() ? "true" : "false") << std::endl;
  d_strat.initializeStrategy();

  // if strings fmf is enabled, register the strategy
  if (options::stringFMF())
  {
    d_stringsFmf.presolve();
    // This strategy is local to a check-sat call, since we refresh the strategy
    // on every call to presolve.
    getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_STRINGS_SUM_LENGTHS,
        d_stringsFmf.getDecisionStrategy(),
        DecisionManager::STRAT_SCOPE_LOCAL_SOLVE);
  }
  Debug("strings-presolve") << "Finished presolve" << std::endl;
}


/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////

bool TheoryStrings::collectModelInfo(TheoryModel* m)
{
  Trace("strings-model") << "TheoryStrings : Collect model info" << std::endl;
  Trace("strings-model") << "TheoryStrings : assertEqualityEngine." << std::endl;

  std::set<Node> termSet;

  // Compute terms appearing in assertions and shared terms
  computeRelevantTerms(termSet);
  // assert the (relevant) portion of the equality engine to the model
  if (!m->assertEqualityEngine(&d_equalityEngine, &termSet))
  {
    Unreachable()
        << "TheoryStrings::collectModelInfo: failed to assert equality engine"
        << std::endl;
    return false;
  }

  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> > repSet;
  // Generate model
  // get the relevant string equivalence classes
  for (const Node& s : termSet)
  {
    TypeNode tn = s.getType();
    if (tn.isStringLike())
    {
      Node r = d_state.getRepresentative(s);
      repSet[tn].insert(r);
    }
  }
  for (const std::pair<const TypeNode,
                       std::unordered_set<Node, NodeHashFunction> >& rst :
       repSet)
  {
    // get partition of strings of equal lengths, per type
    std::map<TypeNode, std::vector<std::vector<Node> > > colT;
    std::map<TypeNode, std::vector<Node> > ltsT;
    std::vector<Node> repVec(rst.second.begin(), rst.second.end());
    d_state.separateByLength(repVec, colT, ltsT);
    // now collect model info for the type
    TypeNode st = rst.first;
    if (!collectModelInfoType(st, rst.second, colT[st], ltsT[st], m))
    {
      return false;
    }
  }
  return true;
}

bool TheoryStrings::collectModelInfoType(
    TypeNode tn,
    const std::unordered_set<Node, NodeHashFunction>& repSet,
    std::vector<std::vector<Node> >& col,
    std::vector<Node>& lts,
    TheoryModel* m)
{
  NodeManager* nm = NodeManager::currentNM();
  std::map< Node, Node > processed;
  //step 1 : get all values for known lengths
  std::vector< Node > lts_values;
  std::map<unsigned, Node> values_used;
  std::vector<Node> len_splits;
  for( unsigned i=0; i<col.size(); i++ ) {
    Trace("strings-model") << "Checking length for {";
    for( unsigned j=0; j<col[i].size(); j++ ) {
      if( j>0 ) {
        Trace("strings-model") << ", ";
      }
      Trace("strings-model") << col[i][j];
    }
    Trace("strings-model") << " } (length is " << lts[i] << ")" << std::endl;
    Node len_value;
    if( lts[i].isConst() ) {
      len_value = lts[i];
    }
    else if (!lts[i].isNull())
    {
      // get the model value for lts[i]
      len_value = d_valuation.getModelValue(lts[i]);
    }
    if (len_value.isNull())
    {
      lts_values.push_back(Node::null());
    }
    else
    {
      // must throw logic exception if we cannot construct the string
      if (len_value.getConst<Rational>() > Rational(String::maxSize()))
      {
        std::stringstream ss;
        ss << "Cannot generate model with string whose length exceeds UINT32_MAX";
        throw LogicException(ss.str());
      }
      unsigned lvalue =
          len_value.getConst<Rational>().getNumerator().toUnsignedInt();
      std::map<unsigned, Node>::iterator itvu = values_used.find(lvalue);
      if (itvu == values_used.end())
      {
        values_used[lvalue] = lts[i];
      }
      else
      {
        len_splits.push_back(lts[i].eqNode(itvu->second));
      }
      lts_values.push_back(len_value);
    }
  }
  ////step 2 : assign arbitrary values for unknown lengths?
  // confirmed by calculus invariant, see paper
  Trace("strings-model") << "Assign to equivalence classes..." << std::endl;
  std::map<Node, Node> pure_eq_assign;
  //step 3 : assign values to equivalence classes that are pure variables
  for( unsigned i=0; i<col.size(); i++ ){
    std::vector< Node > pure_eq;
    Trace("strings-model") << "The (" << col[i].size()
                           << ") equivalence classes ";
    for (const Node& eqc : col[i])
    {
      Trace("strings-model") << eqc << " ";
      //check if col[i][j] has only variables
      if (!eqc.isConst())
      {
        NormalForm& nfe = d_csolver.getNormalForm(eqc);
        if (nfe.d_nf.size() == 1)
        {
          // is it an equivalence class with a seq.unit term?
          if (nfe.d_nf[0].getKind() == SEQ_UNIT)
          {
            pure_eq_assign[eqc] = nfe.d_nf[0];
            Trace("strings-model") << "(unit: " << nfe.d_nf[0] << ") ";
          }
          // does it have a code and the length of these equivalence classes are
          // one?
          else if (d_termReg.hasStringCode() && lts_values[i] == d_one)
          {
            EqcInfo* eip = d_state.getOrMakeEqcInfo(eqc, false);
            if (eip && !eip->d_codeTerm.get().isNull())
            {
              // its value must be equal to its code
              Node ct = nm->mkNode(kind::STRING_TO_CODE, eip->d_codeTerm.get());
              Node ctv = d_valuation.getModelValue(ct);
              unsigned cvalue =
                  ctv.getConst<Rational>().getNumerator().toUnsignedInt();
              Trace("strings-model") << "(code: " << cvalue << ") ";
              std::vector<unsigned> vec;
              vec.push_back(cvalue);
              Node mv = nm->mkConst(String(vec));
              pure_eq_assign[eqc] = mv;
              m->getEqualityEngine()->addTerm(mv);
            }
          }
          pure_eq.push_back(eqc);
        }
      }
      else
      {
        processed[eqc] = eqc;
      }
    }
    Trace("strings-model") << "have length " << lts_values[i] << std::endl;

    //assign a new length if necessary
    if( !pure_eq.empty() ){
      if( lts_values[i].isNull() ){
        // start with length two (other lengths have special precendence)
        unsigned lvalue = 2;
        while( values_used.find( lvalue )!=values_used.end() ){
          lvalue++;
        }
        Trace("strings-model") << "*** Decide to make length of " << lvalue << std::endl;
        lts_values[i] = nm->mkConst(Rational(lvalue));
        values_used[lvalue] = Node::null();
      }
      Trace("strings-model") << "Need to assign values of length " << lts_values[i] << " to equivalence classes ";
      for( unsigned j=0; j<pure_eq.size(); j++ ){
        Trace("strings-model") << pure_eq[j] << " ";
      }
      Trace("strings-model") << std::endl;

      //use type enumerator
      Assert(lts_values[i].getConst<Rational>() <= Rational(String::maxSize()))
          << "Exceeded UINT32_MAX in string model";
      uint32_t currLen =
          lts_values[i].getConst<Rational>().getNumerator().toUnsignedInt();
      std::unique_ptr<SEnumLen> sel;
      Trace("strings-model") << "Cardinality of alphabet is "
                             << utils::getAlphabetCardinality() << std::endl;
      if (tn.isString())  // string-only
      {
        sel.reset(new StringEnumLen(
            currLen, currLen, utils::getAlphabetCardinality()));
      }
      else
      {
        sel.reset(new SeqEnumLen(tn, nullptr, currLen, currLen));
      }
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
              for (const Node& sl : len_splits)
              {
                Node spl = nm->mkNode(OR, sl, sl.negate());
                ++(d_statistics.d_lemmasCmiSplit);
                d_out->lemma(spl);
                Trace("strings-lemma")
                    << "Strings::CollectModelInfoSplit: " << spl << std::endl;
              }
              // we added a lemma, so can return here
              return false;
            }
            c = sel->getCurrent();
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
  for (const Node& rn : repSet)
  {
    if (processed.find(rn) == processed.end())
    {
      NormalForm& nf = d_csolver.getNormalForm(rn);
      if (Trace.isOn("strings-model"))
      {
        Trace("strings-model")
            << "Construct model for " << rn << " based on normal form ";
        for (unsigned j = 0, size = nf.d_nf.size(); j < size; j++)
        {
          Node n = nf.d_nf[j];
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
      std::vector< Node > nc;
      for (const Node& n : nf.d_nf)
      {
        Node r = d_state.getRepresentative(n);
        Assert(r.isConst() || processed.find(r) != processed.end());
        nc.push_back(r.isConst() ? r : processed[r]);
      }
      Node cc = utils::mkNConcat(nc, tn);
      Trace("strings-model")
          << "*** Determined constant " << cc << " for " << rn << std::endl;
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
  }
  //Trace("strings-model") << "String Model : Assigned." << std::endl;
  Trace("strings-model") << "String Model : Finished." << std::endl;
  return true;
}

/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////

void TheoryStrings::preRegisterTerm(TNode n)
{
  Trace("strings-preregister")
      << "TheoryStrings::preRegisterTerm: " << n << std::endl;
  d_termReg.preRegisterTerm(n);
}

TrustNode TheoryStrings::expandDefinition(Node node)
{
  Trace("strings-exp-def") << "TheoryStrings::expandDefinition : " << node << std::endl;

  if (node.getKind() == STRING_FROM_CODE)
  {
    // str.from_code(t) --->
    //   witness k. ite(0 <= t < |A|, t = str.to_code(k), k = "")
    NodeManager* nm = NodeManager::currentNM();
    Node t = node[0];
    Node card = nm->mkConst(Rational(utils::getAlphabetCardinality()));
    Node cond =
        nm->mkNode(AND, nm->mkNode(LEQ, d_zero, t), nm->mkNode(LT, t, card));
    Node k = nm->mkBoundVar(nm->stringType());
    Node bvl = nm->mkNode(BOUND_VAR_LIST, k);
    Node emp = Word::mkEmptyWord(node.getType());
    Node ret = nm->mkNode(
        WITNESS,
        bvl,
        nm->mkNode(
            ITE, cond, t.eqNode(nm->mkNode(STRING_TO_CODE, k)), k.eqNode(emp)));
    return TrustNode::mkTrustRewrite(node, ret, nullptr);
  }

  if (node.getKind() == SEQ_NTH)
  {
    // str.nth(s,i) --->
    //   ite(0<=i<=len(s), witness k. 0<=i<=len(s)->unit(k) = seq.at(s,i),
    //   uf(s,i))
    NodeManager* nm = NodeManager::currentNM();
    Node s = node[0];
    Node i = node[1];
    Node len = nm->mkNode(STRING_LENGTH, s);
    Node cond =
        nm->mkNode(AND, nm->mkNode(LEQ, d_zero, i), nm->mkNode(LT, i, len));
    TypeNode elemType = s.getType().getSequenceElementType();
    Node k = nm->mkBoundVar(elemType);
    Node bvl = nm->mkNode(BOUND_VAR_LIST, k);
    std::vector<TypeNode> argTypes;
    argTypes.push_back(s.getType());
    argTypes.push_back(nm->integerType());
    TypeNode ufType = nm->mkFunctionType(argTypes, elemType);
    SkolemCache* sc = d_termReg.getSkolemCache();
    Node uf = sc->mkTypedSkolemCached(
        ufType, Node::null(), Node::null(), SkolemCache::SK_NTH, "Uf");
    Node ret = nm->mkNode(
        ITE,
        cond,
        nm->mkNode(WITNESS,
                   bvl,
                   nm->mkNode(IMPLIES,
                              cond,
                              nm->mkNode(SEQ_UNIT, k)
                                  .eqNode(nm->mkNode(STRING_CHARAT, s, i)))),
        nm->mkNode(APPLY_UF, uf, s, i));
    return TrustNode::mkTrustRewrite(node, ret, nullptr);
  }

  return TrustNode::null();
}

void TheoryStrings::check(Effort e) {
  if (done() && e<EFFORT_FULL) {
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);

  // Trace("strings-process") << "Theory of strings, check : " << e << std::endl;
  Trace("strings-check-debug")
      << "Theory of strings, check : " << e << std::endl;
  while (!done() && !d_state.isInConflict())
  {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.d_assertion;

    Trace("strings-assertion") << "get assertion: " << fact << endl;
    d_im.sendAssumption(fact);
  }
  d_im.doPendingFacts();

  Assert(d_strat.isStrategyInit());
  if (!d_state.isInConflict() && !d_valuation.needCheck()
      && d_strat.hasStrategyEffort(e))
  {
    Trace("strings-check-debug")
        << "Theory of strings " << e << " effort check " << std::endl;
    if(Trace.isOn("strings-eqc")) {
      for( unsigned t=0; t<2; t++ ) {
        eq::EqClassesIterator eqcs2_i = eq::EqClassesIterator( &d_equalityEngine );
        Trace("strings-eqc") << (t==0 ? "STRINGS:" : "OTHER:") << std::endl;
        while( !eqcs2_i.isFinished() ){
          Node eqc = (*eqcs2_i);
          bool print = (t == 0 && eqc.getType().isStringLike())
                       || (t == 1 && !eqc.getType().isStringLike());
          if (print) {
            eq::EqClassIterator eqc2_i = eq::EqClassIterator( eqc, &d_equalityEngine );
            Trace("strings-eqc") << "Eqc( " << eqc << " ) : { ";
            while( !eqc2_i.isFinished() ) {
              if( (*eqc2_i)!=eqc && (*eqc2_i).getKind()!=kind::EQUAL ){
                Trace("strings-eqc") << (*eqc2_i) << " ";
              }
              ++eqc2_i;
            }
            Trace("strings-eqc") << " } " << std::endl;
            EqcInfo* ei = d_state.getOrMakeEqcInfo(eqc, false);
            if( ei ){
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
        Trace("strings-eqc") << std::endl;
      }
      Trace("strings-eqc") << std::endl;
    }
    ++(d_statistics.d_checkRuns);
    bool addedLemma = false;
    bool addedFact;
    Trace("strings-check") << "Full effort check..." << std::endl;
    do{
      ++(d_statistics.d_strategyRuns);
      Trace("strings-check") << "  * Run strategy..." << std::endl;
      runStrategy(e);
      // flush the facts
      addedFact = d_im.hasPendingFact();
      addedLemma = d_im.hasPendingLemma();
      d_im.doPendingFacts();
      d_im.doPendingLemmas();
      if (Trace.isOn("strings-check"))
      {
        Trace("strings-check") << "  ...finish run strategy: ";
        Trace("strings-check") << (addedFact ? "addedFact " : "");
        Trace("strings-check") << (addedLemma ? "addedLemma " : "");
        Trace("strings-check") << (d_state.isInConflict() ? "conflict " : "");
        if (!addedFact && !addedLemma && !d_state.isInConflict())
        {
          Trace("strings-check") << "(none)";
        }
        Trace("strings-check") << std::endl;
      }
      // repeat if we did not add a lemma or conflict
    } while (!d_state.isInConflict() && !addedLemma && addedFact);
  }
  Trace("strings-check") << "Theory of strings, done check : " << e << std::endl;
  Assert(!d_im.hasPendingFact());
  Assert(!d_im.hasPendingLemma());
}

bool TheoryStrings::needsCheckLastEffort() {
  if( options::stringGuessModel() ){
    return d_esolver.hasExtendedFunctions();
  }
  return false;
}

/** Conflict when merging two constants */
void TheoryStrings::conflict(TNode a, TNode b){
  if (!d_state.isInConflict())
  {
    Debug("strings-conflict") << "Making conflict..." << std::endl;
    d_state.setConflict();
    TrustNode conflictNode = explain(a.eqNode(b));
    Trace("strings-conflict")
        << "CONFLICT: Eq engine conflict : " << conflictNode.getNode()
        << std::endl;
    ++(d_statistics.d_conflictsEqEngine);
    d_out->conflict(conflictNode.getNode());
  }
}

void TheoryStrings::eqNotifyNewClass(TNode t){
  Kind k = t.getKind();
  if (k == STRING_LENGTH || k == STRING_TO_CODE)
  {
    Trace("strings-debug") << "New length eqc : " << t << std::endl;
    //we care about the length of this string
    d_termReg.registerTerm(t[0], 1);
  }
  d_state.eqNotifyNewClass(t);
}

void TheoryStrings::addCarePairs(TNodeTrie* t1,
                                 TNodeTrie* t2,
                                 unsigned arity,
                                 unsigned depth)
{
  if( depth==arity ){
    if( t2!=NULL ){
      Node f1 = t1->getData();
      Node f2 = t2->getData();
      if( !d_equalityEngine.areEqual( f1, f2 ) ){
        Trace("strings-cg-debug") << "TheoryStrings::computeCareGraph(): checking function " << f1 << " and " << f2 << std::endl;
        vector< pair<TNode, TNode> > currentPairs;
        for (unsigned k = 0; k < f1.getNumChildren(); ++ k) {
          TNode x = f1[k];
          TNode y = f2[k];
          Assert(d_equalityEngine.hasTerm(x));
          Assert(d_equalityEngine.hasTerm(y));
          Assert(!d_equalityEngine.areDisequal(x, y, false));
          Assert(!areCareDisequal(x, y));
          if( !d_equalityEngine.areEqual( x, y ) ){
            if( d_equalityEngine.isTriggerTerm(x, THEORY_STRINGS) && d_equalityEngine.isTriggerTerm(y, THEORY_STRINGS) ){
              TNode x_shared = d_equalityEngine.getTriggerTermRepresentative(x, THEORY_STRINGS);
              TNode y_shared = d_equalityEngine.getTriggerTermRepresentative(y, THEORY_STRINGS);
              currentPairs.push_back(make_pair(x_shared, y_shared));
            }
          }
        }
        for (unsigned c = 0; c < currentPairs.size(); ++ c) {
          Trace("strings-cg-pair") << "TheoryStrings::computeCareGraph(): pair : " << currentPairs[c].first << " " << currentPairs[c].second << std::endl;
          addCarePair(currentPairs[c].first, currentPairs[c].second);
        }
      }
    }
  }else{
    if( t2==NULL ){
      if( depth<(arity-1) ){
        //add care pairs internal to each child
        for (std::pair<const TNode, TNodeTrie>& tt : t1->d_data)
        {
          addCarePairs(&tt.second, nullptr, arity, depth + 1);
        }
      }
      //add care pairs based on each pair of non-disequal arguments
      for (std::map<TNode, TNodeTrie>::iterator it = t1->d_data.begin();
           it != t1->d_data.end();
           ++it)
      {
        std::map<TNode, TNodeTrie>::iterator it2 = it;
        ++it2;
        for( ; it2 != t1->d_data.end(); ++it2 ){
          if( !d_equalityEngine.areDisequal(it->first, it2->first, false) ){
            if( !areCareDisequal(it->first, it2->first) ){
              addCarePairs( &it->second, &it2->second, arity, depth+1 );
            }
          }
        }
      }
    }else{
      //add care pairs based on product of indices, non-disequal arguments
      for (std::pair<const TNode, TNodeTrie>& tt1 : t1->d_data)
      {
        for (std::pair<const TNode, TNodeTrie>& tt2 : t2->d_data)
        {
          if (!d_equalityEngine.areDisequal(tt1.first, tt2.first, false))
          {
            if (!areCareDisequal(tt1.first, tt2.first))
            {
              addCarePairs(&tt1.second, &tt2.second, arity, depth + 1);
            }
          }
        }
      }
    }
  }
}

void TheoryStrings::computeCareGraph(){
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
      reps.push_back( d_equalityEngine.getRepresentative( f1[j] ) );
      if( d_equalityEngine.isTriggerTerm( f1[j], THEORY_STRINGS ) ){
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
    addCarePairs(&ti.second, nullptr, arity[op], 0);
  }
}

void TheoryStrings::checkRegisterTermsPreNormalForm()
{
  const std::vector<Node>& seqc = d_bsolver.getStringEqc();
  for (const Node& eqc : seqc)
  {
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, &d_equalityEngine);
    while (!eqc_i.isFinished())
    {
      Node n = (*eqc_i);
      if (!d_bsolver.isCongruent(n))
      {
        d_termReg.registerTerm(n, 2);
      }
      ++eqc_i;
    }
  }
}

void TheoryStrings::checkCodes()
{
  // ensure that lemmas regarding str.code been added for each constant string
  // of length one
  if (d_termReg.hasStringCode())
  {
    NodeManager* nm = NodeManager::currentNM();
    // str.code applied to the code term for each equivalence class that has a
    // code term but is not a constant
    std::vector<Node> nconst_codes;
    // str.code applied to the proxy variables for each equivalence classes that
    // are constants of size one
    std::vector<Node> const_codes;
    const std::vector<Node>& seqc = d_bsolver.getStringEqc();
    for (const Node& eqc : seqc)
    {
      NormalForm& nfe = d_csolver.getNormalForm(eqc);
      if (nfe.d_nf.size() == 1 && nfe.d_nf[0].isConst())
      {
        Node c = nfe.d_nf[0];
        Trace("strings-code-debug") << "Get proxy variable for " << c
                                    << std::endl;
        Node cc = nm->mkNode(kind::STRING_TO_CODE, c);
        cc = Rewriter::rewrite(cc);
        Assert(cc.isConst());
        Node cp = d_termReg.getProxyVariableFor(c);
        AlwaysAssert(!cp.isNull());
        Node vc = nm->mkNode(STRING_TO_CODE, cp);
        if (!d_state.areEqual(cc, vc))
        {
          std::vector<Node> emptyVec;
          d_im.sendInference(emptyVec, cc.eqNode(vc), Inference::CODE_PROXY);
        }
        const_codes.push_back(vc);
      }
      else
      {
        EqcInfo* ei = d_state.getOrMakeEqcInfo(eqc, false);
        if (ei && !ei->d_codeTerm.get().isNull())
        {
          Node vc = nm->mkNode(kind::STRING_TO_CODE, ei->d_codeTerm.get());
          nconst_codes.push_back(vc);
        }
      }
    }
    if (d_im.hasProcessed())
    {
      return;
    }
    // now, ensure that str.code is injective
    std::vector<Node> cmps;
    cmps.insert(cmps.end(), const_codes.rbegin(), const_codes.rend());
    cmps.insert(cmps.end(), nconst_codes.rbegin(), nconst_codes.rend());
    for (unsigned i = 0, num_ncc = nconst_codes.size(); i < num_ncc; i++)
    {
      Node c1 = nconst_codes[i];
      cmps.pop_back();
      for (const Node& c2 : cmps)
      {
        Trace("strings-code-debug")
            << "Compare codes : " << c1 << " " << c2 << std::endl;
        if (!d_state.areDisequal(c1, c2) && !d_state.areEqual(c1, d_neg_one))
        {
          Node eq_no = c1.eqNode(d_neg_one);
          Node deq = c1.eqNode(c2).negate();
          Node eqn = c1[0].eqNode(c2[0]);
          // str.code(x)==-1 V str.code(x)!=str.code(y) V x==y
          Node inj_lem = nm->mkNode(kind::OR, eq_no, deq, eqn);
          d_im.sendPhaseRequirement(deq, false);
          std::vector<Node> emptyVec;
          d_im.sendInference(emptyVec, inj_lem, Inference::CODE_INJ);
        }
      }
    }
  }
}

void TheoryStrings::checkRegisterTermsNormalForms()
{
  const std::vector<Node>& seqc = d_bsolver.getStringEqc();
  for (const Node& eqc : seqc)
  {
    NormalForm& nfi = d_csolver.getNormalForm(eqc);
    // check if there is a length term for this equivalence class
    EqcInfo* ei = d_state.getOrMakeEqcInfo(eqc, false);
    Node lt = ei ? ei->d_lengthTerm : Node::null();
    if (lt.isNull())
    {
      Node c = utils::mkNConcat(nfi.d_nf, eqc.getType());
      d_termReg.registerTerm(c, 3);
    }
  }
}

TrustNode TheoryStrings::ppRewrite(TNode atom)
{
  Trace("strings-ppr") << "TheoryStrings::ppRewrite " << atom << std::endl;
  Node atomRet = atom;
  if (options::regExpElim() && atom.getKind() == STRING_IN_REGEXP)
  {
    // aggressive elimination of regular expression membership
    Node atomElim = d_regexp_elim.eliminate(atomRet);
    if (!atomElim.isNull())
    {
      Trace("strings-ppr") << "  rewrote " << atom << " -> " << atomElim
                           << " via regular expression elimination."
                           << std::endl;
      atomRet = atomElim;
    }
  }
  if( !options::stringLazyPreproc() ){
    //eager preprocess here
    std::vector< Node > new_nodes;
    StringsPreprocess* p = d_esolver.getPreprocess();
    Node ret = p->processAssertion(atomRet, new_nodes);
    if (ret != atomRet)
    {
      Trace("strings-ppr") << "  rewrote " << atomRet << " -> " << ret
                           << ", with " << new_nodes.size() << " lemmas."
                           << std::endl;
      for (const Node& lem : new_nodes)
      {
        Trace("strings-ppr") << "    lemma : " << lem << std::endl;
        ++(d_statistics.d_lemmasEagerPreproc);
        d_out->lemma(lem);
      }
      atomRet = ret;
    }else{
      Assert(new_nodes.empty());
    }
  }
  if (atomRet != atom)
  {
    return TrustNode::mkTrustRewrite(atom, atomRet, nullptr);
  }
  return TrustNode::null();
}

/** run the given inference step */
void TheoryStrings::runInferStep(InferStep s, int effort)
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
    case CHECK_REGISTER_TERMS_PRE_NF: checkRegisterTermsPreNormalForm(); break;
    case CHECK_NORMAL_FORMS_EQ: d_csolver.checkNormalFormsEq(); break;
    case CHECK_NORMAL_FORMS_DEQ: d_csolver.checkNormalFormsDeq(); break;
    case CHECK_CODES: checkCodes(); break;
    case CHECK_LENGTH_EQC: d_csolver.checkLengthsEqc(); break;
    case CHECK_REGISTER_TERMS_NF: checkRegisterTermsNormalForms(); break;
    case CHECK_EXTF_REDUCTION: d_esolver.checkExtfReductions(effort); break;
    case CHECK_MEMBERSHIP: d_rsolver.checkMemberships(); break;
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
    if (curr == BREAK)
    {
      if (d_im.hasProcessed())
      {
        break;
      }
    }
    else
    {
      runInferStep(curr, it->second);
      if (d_state.isInConflict())
      {
        break;
      }
    }
    ++it;
  }
  Trace("strings-process") << "----finished round---" << std::endl;
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

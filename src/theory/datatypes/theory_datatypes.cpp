/*********************                                                        */
/*! \file theory_datatypes.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the theory of datatypes
 **
 ** Implementation of the theory of datatypes.
 **/
#include "theory/datatypes/theory_datatypes.h"

#include <map>

#include "base/check.h"
#include "expr/dtype.h"
#include "expr/kind.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/datatypes/theory_datatypes_type_rules.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_model.h"
#include "theory/type_enumerator.h"
#include "theory/valuation.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace datatypes {

TheoryDatatypes::TheoryDatatypes(Context* c,
                                 UserContext* u,
                                 OutputChannel& out,
                                 Valuation valuation,
                                 const LogicInfo& logicInfo,
                                 ProofNodeManager* pnm)
    : Theory(THEORY_DATATYPES, c, u, out, valuation, logicInfo, pnm),
      d_term_sk(u),
      d_labels(c),
      d_selector_apps(c),
      d_collectTermsCache(c),
      d_collectTermsCacheU(u),
      d_functionTerms(c),
      d_singleton_eq(u),
      d_lemmas_produced_c(u),
      d_sygusExtension(nullptr),
      d_state(c, u, valuation),
      d_im(*this, d_state, pnm),
      d_notify(d_im, *this)
{

  d_true = NodeManager::currentNM()->mkConst( true );
  d_zero = NodeManager::currentNM()->mkConst( Rational(0) );
  d_dtfCounter = 0;

  // indicate we are using the default theory state object
  d_theoryState = &d_state;
  d_inferManager = &d_im;

  ProofChecker* pc = pnm != nullptr ? pnm->getChecker() : nullptr;
  if (pc != nullptr)
  {
    // add checkers
    d_pchecker.registerTo(pc);
  }
}

TheoryDatatypes::~TheoryDatatypes() {
  for(std::map< Node, EqcInfo* >::iterator i = d_eqc_info.begin(), iend = d_eqc_info.end();
      i != iend; ++i){
    EqcInfo* current = (*i).second;
    Assert(current != NULL);
    delete current;
  }
}

TheoryRewriter* TheoryDatatypes::getTheoryRewriter() { return &d_rewriter; }

bool TheoryDatatypes::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::datatypes::ee";
  return true;
}

void TheoryDatatypes::finishInit()
{
  Assert(d_equalityEngine != nullptr);
  // The kinds we are treating as function application in congruence
  d_equalityEngine->addFunctionKind(kind::APPLY_CONSTRUCTOR);
  d_equalityEngine->addFunctionKind(kind::APPLY_SELECTOR_TOTAL);
  d_equalityEngine->addFunctionKind(kind::APPLY_TESTER);
  // We could but don't do congruence for DT_SIZE and DT_HEIGHT_BOUND here.
  // It also could make sense in practice to do congruence for APPLY_UF, but
  // this is not done.
  if (getQuantifiersEngine() && options::sygus())
  {
    d_sygusExtension.reset(
        new SygusExtension(this, getQuantifiersEngine(), getSatContext()));
    // do congruence on evaluation functions
    d_equalityEngine->addFunctionKind(kind::DT_SYGUS_EVAL);
  }
  // testers are not relevant for model building
  d_valuation.setIrrelevantKind(APPLY_TESTER);
}

TheoryDatatypes::EqcInfo* TheoryDatatypes::getOrMakeEqcInfo( TNode n, bool doMake ){
  if( !hasEqcInfo( n ) ){
    if( doMake ){
      //add to labels
      d_labels[ n ] = 0;

      std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( n );
      EqcInfo* ei;
      if( eqc_i != d_eqc_info.end() ){
        ei = eqc_i->second;
      }else{
        ei = new EqcInfo( getSatContext() );
        d_eqc_info[n] = ei;
      }
      if( n.getKind()==APPLY_CONSTRUCTOR ){
        ei->d_constructor = n;
      }
      
      //add to selectors
      d_selector_apps[n] = 0;
      
      return ei;
    }else{
      return NULL;
    }
  }else{
    std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( n );
    return (*eqc_i).second;
  }
}

TNode TheoryDatatypes::getEqcConstructor( TNode r ) {
  if( r.getKind()==APPLY_CONSTRUCTOR ){
    return r;
  }else{
    EqcInfo * ei = getOrMakeEqcInfo( r, false );
    if( ei && !ei->d_constructor.get().isNull() ){
      return ei->d_constructor.get();
    }else{
      return r;
    }
  }
}

bool TheoryDatatypes::preCheck(Effort level)
{
  d_im.reset();
  d_im.clearPending();
  return false;
}

void TheoryDatatypes::postCheck(Effort level)
{
  // Apply any last pending inferences, which may occur if the last processed
  // fact was an internal one and triggered further internal inferences.
  d_im.process();
  if (level == EFFORT_LAST_CALL)
  {
    Assert(d_sygusExtension != nullptr);
    std::vector<Node> lemmas;
    d_sygusExtension->check(lemmas);
    d_im.sendLemmas(lemmas);
    return;
  }
  else if (level == EFFORT_FULL && !d_state.isInConflict()
           && !d_im.hasSentLemma() && !d_valuation.needCheck())
  {
    //check for cycles
    Assert(!d_im.hasPendingFact());
    do {
      d_im.reset();
      Trace("datatypes-proc") << "Check cycles..." << std::endl;
      checkCycles();
      Trace("datatypes-proc") << "...finish check cycles" << std::endl;
      d_im.process();
      if (d_state.isInConflict() || d_im.hasSentLemma())
      {
        return;
      }
    } while (d_im.hasSentFact());

    //check for splits
    Trace("datatypes-debug") << "Check for splits " << endl;
    do {
      d_im.reset();
      std::map< TypeNode, Node > rec_singletons;
      eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
      while( !eqcs_i.isFinished() ){
        Node n = (*eqcs_i);
        //TODO : avoid irrelevant (pre-registered but not asserted) terms here?
        TypeNode tn = n.getType();
        if( tn.isDatatype() ){
          Trace("datatypes-debug") << "Process equivalence class " << n << std::endl;
          EqcInfo* eqc = getOrMakeEqcInfo( n );
          //if there are more than 1 possible constructors for eqc
          if( !hasLabel( eqc, n ) ){
            Trace("datatypes-debug") << "No constructor..." << std::endl;
            TypeNode tt = tn;
            const DType& dt = tt.getDType();
            Trace("datatypes-debug")
                << "Datatype " << dt.getName() << " is "
                << dt.isInterpretedFinite(tt) << " "
                << dt.isRecursiveSingleton(tt) << std::endl;
            bool continueProc = true;
            if( dt.isRecursiveSingleton( tt ) ){
              Trace("datatypes-debug") << "Check recursive singleton..." << std::endl;
              //handle recursive singleton case
              std::map< TypeNode, Node >::iterator itrs = rec_singletons.find( tn );
              if( itrs!=rec_singletons.end() ){
                Node eq = n.eqNode( itrs->second );
                if( d_singleton_eq.find( eq )==d_singleton_eq.end() ){
                  d_singleton_eq[eq] = true;
                  // get assumptions
                  bool success = true;
                  std::vector< Node > assumptions;
                  //if there is at least one uninterpreted sort occurring within the datatype and the logic is not quantified, add lemmas ensuring cardinality is more than one,
                  //  do not infer the equality if at least one sort was processed.
                  //otherwise, if the logic is quantified, under the assumption that all uninterpreted sorts have cardinality one,
                  //  infer the equality.
                  for( unsigned i=0; i<dt.getNumRecursiveSingletonArgTypes( tt ); i++ ){
                    TypeNode type = dt.getRecursiveSingletonArgType(tt, i);
                    if( getQuantifiersEngine() ){
                      // under the assumption that the cardinality of this type is one
                      Node a = getSingletonLemma(type, true);
                      assumptions.push_back( a.negate() );
                    }else{
                      success = false;
                      // assert that the cardinality of this type is more than one
                      getSingletonLemma(type, false);
                    }
                  }
                  if( success ){
                    Node assumption = n.eqNode(itrs->second);
                    assumptions.push_back(assumption);
                    Node lemma = assumptions.size()==1 ? assumptions[0] : NodeManager::currentNM()->mkNode( OR, assumptions );
                    Trace("dt-singleton") << "*************Singleton equality lemma " << lemma << std::endl;
                    d_im.lemma(lemma);
                  }
                }
              }else{
                rec_singletons[tn] = n;
              }
              //do splitting for quantified logics (incomplete anyways)
              continueProc = ( getQuantifiersEngine()!=NULL );
            }
            if( continueProc ){
              Trace("datatypes-debug") << "Get possible cons..." << std::endl;
              //all other cases
              std::vector< bool > pcons;
              getPossibleCons( eqc, n, pcons );
              //check if we do not need to resolve the constructor type for this equivalence class.
              // this is if there are no selectors for this equivalence class, and its possible values are infinite,
              //  then do not split.
              int consIndex = -1;
              int fconsIndex = -1;
              bool needSplit = true;
              for( unsigned int j=0; j<pcons.size(); j++ ) {
                if( pcons[j] ) {
                  if( consIndex==-1 ){
                    consIndex = j;
                  }
                  Trace("datatypes-debug") << j << " compute finite..."
                                           << std::endl;
                  bool ifin = dt[j].isInterpretedFinite(tt);
                  Trace("datatypes-debug") << "...returned " << ifin
                                           << std::endl;
                  if (!ifin)
                  {
                    if( !eqc || !eqc->d_selectors ){
                      needSplit = false;
                    }
                  }else{
                    if( fconsIndex==-1 ){
                      fconsIndex = j;
                    }
                  }
                }
              }
              //if we want to force an assignment of constructors to all ground eqc
              //d_dtfCounter++;
              if( !needSplit && options::dtForceAssignment() && d_dtfCounter%2==0 ){
                Trace("datatypes-force-assign") << "Force assignment for " << n << std::endl;
                needSplit = true;
                consIndex = fconsIndex!=-1 ? fconsIndex : consIndex;
              }

              if( needSplit ) {
                if( dt.getNumConstructors()==1 ){
                  //this may not be necessary?
                  //if only one constructor, then this term must be this constructor
                  Node t = utils::mkTester(n, 0, dt);
                  d_im.addPendingInference(t, d_true, false, InferId::SPLIT);
                  Trace("datatypes-infer") << "DtInfer : 1-cons (full) : " << t << std::endl;
                }else{
                  Assert(consIndex != -1 || dt.isSygus());
                  if( options::dtBinarySplit() && consIndex!=-1 ){
                    Node test = utils::mkTester(n, consIndex, dt);
                    Trace("dt-split") << "*************Split for possible constructor " << dt[consIndex] << " for " << n << endl;
                    test = Rewriter::rewrite( test );
                    NodeBuilder<> nb(kind::OR);
                    nb << test << test.notNode();
                    Node lemma = nb;
                    d_im.lemma(lemma);
                    d_out->requirePhase( test, true );
                  }else{
                    Trace("dt-split") << "*************Split for constructors on " << n <<  endl;
                    Node lemma = utils::mkSplit(n, dt);
                    Trace("dt-split-debug") << "Split lemma is : " << lemma << std::endl;
                    d_im.sendDtLemma(lemma,
                                     InferId::SPLIT,
                                     LemmaProperty::SEND_ATOMS,
                                     false);
                  }
                  if( !options::dtBlastSplits() ){
                    break;
                  }
                }
              }else{
                Trace("dt-split-debug") << "Do not split constructor for " << n << " : " << n.getType() << " " << dt.getNumConstructors() << std::endl;
              }
            }
          }else{
            Trace("datatypes-debug") << "Has constructor " << eqc->d_constructor.get() << std::endl;
          }
        }
        ++eqcs_i;
      }
      if (d_im.hasSentLemma())
      {
        // clear pending facts: we added a lemma, so internal inferences are
        // no longer necessary
        d_im.clearPendingFacts();
      }
      else
      {
        // we did not add a lemma, process internal inferences. This loop
        // will repeat.
        Trace("datatypes-debug") << "Flush pending facts..." << std::endl;
        d_im.process();
      }
    } while (!d_state.isInConflict() && !d_im.hasSentLemma()
             && d_im.hasSentFact());
    Trace("datatypes-debug")
        << "Finished, conflict=" << d_state.isInConflict()
        << ", lemmas=" << d_im.hasSentLemma() << std::endl;
    if (!d_state.isInConflict())
    {
      Trace("dt-model-debug") << std::endl;
      printModelDebug("dt-model-debug");
    }
  }

  Trace("datatypes-check") << "Finished check effort " << level << std::endl;
  if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") ) {
    Notice() << "TheoryDatatypes::check(): done" << endl;
  }
}

bool TheoryDatatypes::needsCheckLastEffort() {
  return d_sygusExtension != nullptr;
}

void TheoryDatatypes::notifyFact(TNode atom,
                                 bool polarity,
                                 TNode fact,
                                 bool isInternal)
{
  Trace("datatypes-debug") << "TheoryDatatypes::assertFact : " << fact
                           << ", isInternal = " << isInternal << std::endl;
  // could be sygus-specific
  if (d_sygusExtension)
  {
    std::vector< Node > lemmas;
    d_sygusExtension->assertFact(atom, polarity, lemmas);
    d_im.sendLemmas(lemmas);
  }
  //add to tester if applicable
  Node t_arg;
  int tindex = utils::isTester(atom, t_arg);
  if (tindex >= 0)
  {
    Trace("dt-tester") << "Assert tester : " << atom << " for " << t_arg << std::endl;
    Node rep = getRepresentative( t_arg );
    EqcInfo* eqc = getOrMakeEqcInfo( rep, true );
    Node tst =
        isInternal ? (polarity ? Node(atom) : atom.notNode()) : Node(fact);
    addTester(tindex, tst, eqc, rep, t_arg);
    Trace("dt-tester") << "Done assert tester." << std::endl;
    Trace("dt-tester") << "Done pending merges." << std::endl;
    if (!d_state.isInConflict() && polarity)
    {
      if (d_sygusExtension)
      {
        Trace("dt-tester") << "Assert tester to sygus : " << atom << std::endl;
        std::vector< Node > lemmas;
        d_sygusExtension->assertTester(tindex, t_arg, atom, lemmas);
        Trace("dt-tester") << "Done assert tester to sygus." << std::endl;
        d_im.sendLemmas(lemmas);
      }
    }
  }else{
    Trace("dt-tester-debug") << "Assert (non-tester) : " << atom << std::endl;
  }
  Trace("datatypes-debug") << "TheoryDatatypes::assertFact : finished " << fact << std::endl;
  // now, flush pending facts if this wasn't an internal call
  if (!isInternal)
  {
    d_im.process();
  }
}

void TheoryDatatypes::preRegisterTerm(TNode n)
{
  Trace("datatypes-prereg")
      << "TheoryDatatypes::preRegisterTerm() " << n << endl;
  // external selectors should be preprocessed away by now
  Assert(n.getKind() != APPLY_SELECTOR);
  // must ensure the type is well founded and has no nested recursion if
  // the option dtNestedRec is not set to true.
  TypeNode tn = n.getType();
  if (tn.isDatatype())
  {
    const DType& dt = tn.getDType();
    Trace("dt-expand") << "Check properties of " << dt.getName() << std::endl;
    if (!dt.isWellFounded())
    {
      std::stringstream ss;
      ss << "Cannot handle non-well-founded datatype " << dt.getName();
      throw LogicException(ss.str());
    }
    Trace("dt-expand") << "...well-founded ok" << std::endl;
    if (!options::dtNestedRec())
    {
      if (dt.hasNestedRecursion())
      {
        std::stringstream ss;
        ss << "Cannot handle nested-recursive datatype " << dt.getName();
        throw LogicException(ss.str());
      }
      Trace("dt-expand") << "...nested recursion ok" << std::endl;
    }
  }
  collectTerms( n );
  switch (n.getKind()) {
  case kind::EQUAL:
  case kind::APPLY_TESTER:
    // add predicate trigger for testers and equalities
    // Get triggered for both equal and dis-equal
    d_equalityEngine->addTriggerPredicate(n);
    break;
  default:
    // Function applications/predicates
    d_equalityEngine->addTerm(n);
    if (d_sygusExtension)
    {
      std::vector< Node > lemmas;
      d_sygusExtension->preRegisterTerm(n, lemmas);
      d_im.sendLemmas(lemmas);
    }
    break;
  }
  d_im.process();
}

TrustNode TheoryDatatypes::expandDefinition(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode tn = n.getType();
  Node ret;
  switch (n.getKind())
  {
    case kind::APPLY_SELECTOR:
    {
      Node selector = n.getOperator();
      // APPLY_SELECTOR always applies to an external selector, cindexOf is
      // legal here
      size_t cindex = utils::cindexOf(selector);
      const DType& dt = utils::datatypeOf(selector);
      const DTypeConstructor& c = dt[cindex];
      Node selector_use;
      TypeNode ndt = n[0].getType();
      if (options::dtSharedSelectors())
      {
        size_t selectorIndex = utils::indexOf(selector);
        Trace("dt-expand") << "...selector index = " << selectorIndex
                           << std::endl;
        Assert(selectorIndex < c.getNumArgs());
        selector_use = c.getSelectorInternal(ndt, selectorIndex);
      }else{
        selector_use = selector;
      }
      Node sel = nm->mkNode(kind::APPLY_SELECTOR_TOTAL, selector_use, n[0]);
      if (options::dtRewriteErrorSel())
      {
        ret = sel;
      }
      else
      {
        Node tester = c.getTester();
        Node tst = nm->mkNode(APPLY_TESTER, tester, n[0]);
        tst = Rewriter::rewrite(tst);
        if (tst == d_true)
        {
          ret = sel;
        }else{
          mkExpDefSkolem(selector, ndt, n.getType());
          Node sk =
              nm->mkNode(kind::APPLY_UF, d_exp_def_skolem[ndt][selector], n[0]);
          if (tst == nm->mkConst(false))
          {
            ret = sk;
          }
          else
          {
            ret = nm->mkNode(kind::ITE, tst, sel, sk);
          }
        }
        Trace("dt-expand") << "Expand def : " << n << " to " << ret
                           << std::endl;
      }
    }
    break;
    case TUPLE_UPDATE:
    case RECORD_UPDATE:
    {
      Assert(tn.isDatatype());
      const DType& dt = tn.getDType();
      NodeBuilder<> b(APPLY_CONSTRUCTOR);
      b << dt[0].getConstructor();
      size_t size, updateIndex;
      if (n.getKind() == TUPLE_UPDATE)
      {
        Assert(tn.isTuple());
        size = tn.getTupleLength();
        updateIndex = n.getOperator().getConst<TupleUpdate>().getIndex();
      }
      else
      {
        Assert(tn.isRecord());
        const DTypeConstructor& recCons = dt[0];
        size = recCons.getNumArgs();
        // get the index for the name
        updateIndex = recCons.getSelectorIndexForName(
            n.getOperator().getConst<RecordUpdate>().getField());
      }
      Debug("tuprec") << "expr is " << n << std::endl;
      Debug("tuprec") << "updateIndex is " << updateIndex << std::endl;
      Debug("tuprec") << "t is " << tn << std::endl;
      Debug("tuprec") << "t has arity " << size << std::endl;
      for (size_t i = 0; i < size; ++i)
      {
        if (i == updateIndex)
        {
          b << n[1];
          Debug("tuprec") << "arg " << i << " gets updated to " << n[1]
                          << std::endl;
        }
        else
        {
          b << nm->mkNode(
              APPLY_SELECTOR_TOTAL, dt[0].getSelectorInternal(tn, i), n[0]);
          Debug("tuprec") << "arg " << i << " copies "
                          << b[b.getNumChildren() - 1] << std::endl;
        }
      }
      ret = b;
      Debug("tuprec") << "return " << ret << std::endl;
    }
    break;
    default: break;
  }
  if (!ret.isNull() && n != ret)
  {
    return TrustNode::mkTrustRewrite(n, ret, nullptr);
  }
  return TrustNode::null();
}

TrustNode TheoryDatatypes::ppRewrite(TNode in)
{
  Debug("tuprec") << "TheoryDatatypes::ppRewrite(" << in << ")" << endl;
  // first, see if we need to expand definitions
  TrustNode texp = expandDefinition(in);
  if (!texp.isNull())
  {
    return texp;
  }
  if( in.getKind()==EQUAL ){
    Node nn;
    std::vector< Node > rew;
    if (utils::checkClash(in[0], in[1], rew))
    {
      nn = NodeManager::currentNM()->mkConst(false);
    }
    else
    {
      nn = rew.size()==0 ? d_true :
                ( rew.size()==1 ? rew[0] : NodeManager::currentNM()->mkNode( kind::AND, rew ) );
    }
    if (in != nn)
    {
      return TrustNode::mkTrustRewrite(in, nn, nullptr);
    }
  }

  // nothing to do
  return TrustNode::null();
}

TrustNode TheoryDatatypes::explain(TNode literal)
{
  return d_im.explainLit(literal);
}

/** called when a new equivalance class is created */
void TheoryDatatypes::eqNotifyNewClass(TNode t){
  if( t.getKind()==APPLY_CONSTRUCTOR ){
    getOrMakeEqcInfo( t, true );
  }
}

/** called when two equivalance classes have merged */
void TheoryDatatypes::eqNotifyMerge(TNode t1, TNode t2)
{
  if( t1.getType().isDatatype() ){
    Trace("datatypes-debug")
        << "NotifyMerge : " << t1 << " " << t2 << std::endl;
    merge(t1,t2);
  }
}

void TheoryDatatypes::merge( Node t1, Node t2 ){
  if (!d_state.isInConflict())
  {
    TNode trep1 = t1;
    TNode trep2 = t2;
    Trace("datatypes-debug") << "Merge " << t1 << " " << t2 << std::endl;
    EqcInfo* eqc2 = getOrMakeEqcInfo( t2 );
    if( eqc2 ){
      bool checkInst = false;
      if( !eqc2->d_constructor.get().isNull() ){
        trep2 = eqc2->d_constructor.get();
      }
      EqcInfo* eqc1 = getOrMakeEqcInfo( t1 );
      if( eqc1 ){
        Trace("datatypes-debug") << "  merge eqc info " << eqc2 << " into " << eqc1 << std::endl;
        if( !eqc1->d_constructor.get().isNull() ){
          trep1 = eqc1->d_constructor.get();
        }
        //check for clash
        TNode cons1 = eqc1->d_constructor.get();
        TNode cons2 = eqc2->d_constructor.get();
        //if both have constructor, then either clash or unification
        if( !cons1.isNull() && !cons2.isNull() ){
          Trace("datatypes-debug") << "  constructors : " << cons1 << " " << cons2 << std::endl;
          Node unifEq = cons1.eqNode( cons2 );
          std::vector< Node > rew;
          if (utils::checkClash(cons1, cons2, rew))
          {
            std::vector<Node> conf;
            conf.push_back(unifEq);
            Trace("dt-conflict")
                << "CONFLICT: Clash conflict : " << conf << std::endl;
            d_im.sendDtConflict(conf, InferId::CLASH_CONFLICT);
            return;
          }
          else
          {
            //do unification
            for( int i=0; i<(int)cons1.getNumChildren(); i++ ) {
              if( !areEqual( cons1[i], cons2[i] ) ){
                Node eq = cons1[i].eqNode( cons2[i] );
                d_im.addPendingInference(eq, unifEq, false, InferId::UNIF);
                Trace("datatypes-infer") << "DtInfer : cons-inj : " << eq << " by " << unifEq << std::endl;
              }
            }
          }
        }
        Trace("datatypes-debug") << "  instantiated : " << eqc1->d_inst << " " << eqc2->d_inst << std::endl;
        eqc1->d_inst = eqc1->d_inst || eqc2->d_inst;
        if( !cons2.isNull() ){
          if( cons1.isNull() ){
            Trace("datatypes-debug") << "  must check if it is okay to set the constructor." << std::endl;
            checkInst = true;
            addConstructor( eqc2->d_constructor.get(), eqc1, t1 );
            if (d_state.isInConflict())
            {
              return;
            }
          }
        }
      }else{
        Trace("datatypes-debug") << "  no eqc info for " << t1 << ", must create" << std::endl;
        //just copy the equivalence class information
        eqc1 = getOrMakeEqcInfo( t1, true );
        eqc1->d_inst.set( eqc2->d_inst );
        eqc1->d_constructor.set( eqc2->d_constructor );
        eqc1->d_selectors.set( eqc2->d_selectors );
      }


      //merge labels
      NodeUIntMap::iterator lbl_i = d_labels.find(t2);
      if( lbl_i != d_labels.end() ){
        Trace("datatypes-debug") << "  merge labels from " << eqc2 << " " << t2 << std::endl;
        size_t n_label = (*lbl_i).second;
        for (size_t i = 0; i < n_label; i++)
        {
          Assert(i < d_labels_data[t2].size());
          Node t = d_labels_data[ t2 ][i];
          Node t_arg = d_labels_args[t2][i];
          unsigned tindex = d_labels_tindex[t2][i];
          addTester( tindex, t, eqc1, t1, t_arg );
          if (d_state.isInConflict())
          {
            Trace("datatypes-debug") << "  conflict!" << std::endl;
            return;
          }
        }

      }
      //merge selectors
      if( !eqc1->d_selectors && eqc2->d_selectors ){
        eqc1->d_selectors = true;
        checkInst = true;
      }
      NodeUIntMap::iterator sel_i = d_selector_apps.find(t2);
      if( sel_i != d_selector_apps.end() ){
        Trace("datatypes-debug") << "  merge selectors from " << eqc2 << " " << t2 << std::endl;
        size_t n_sel = (*sel_i).second;
        for (size_t j = 0; j < n_sel; j++)
        {
          addSelector( d_selector_apps_data[t2][j], eqc1, t1, eqc2->d_constructor.get().isNull() );
        }
      }
      if( checkInst ){
        Trace("datatypes-debug") << "  checking instantiate" << std::endl;
        instantiate( eqc1, t1 );
        if (d_state.isInConflict())
        {
          return;
        }
      }
    }
    Trace("datatypes-debug") << "Finished Merge " << t1 << " " << t2 << std::endl;
  }
}

TheoryDatatypes::EqcInfo::EqcInfo( context::Context* c )
    : d_inst( c, false )
    , d_constructor( c, Node::null() )
    , d_selectors( c, false )
{}

bool TheoryDatatypes::hasLabel( EqcInfo* eqc, Node n ){
  return ( eqc && !eqc->d_constructor.get().isNull() ) || !getLabel( n ).isNull();
}

Node TheoryDatatypes::getLabel( Node n ) {
  NodeUIntMap::iterator lbl_i = d_labels.find(n);
  if( lbl_i != d_labels.end() ){
    size_t n_lbl = (*lbl_i).second;
    if( n_lbl>0 && d_labels_data[n][ n_lbl-1 ].getKind()!=kind::NOT ){
      return d_labels_data[n][ n_lbl-1 ];
    }
  }
  return Node::null();
}

int TheoryDatatypes::getLabelIndex( EqcInfo* eqc, Node n ){
  if( eqc && !eqc->d_constructor.get().isNull() ){
    return utils::indexOf(eqc->d_constructor.get().getOperator());
  }else{
    Node lbl = getLabel( n );
    if( lbl.isNull() ){
      return -1;
    }else{
      int tindex = utils::isTester(lbl);
      Trace("datatypes-debug") << "Label of " << n << " is " << lbl
                               << " with tindex " << tindex << std::endl;
      Assert(tindex != -1);
      return tindex;
    }
  }
}

bool TheoryDatatypes::hasTester( Node n ) {
  NodeUIntMap::iterator lbl_i = d_labels.find(n);
  if( lbl_i != d_labels.end() ){
    return (*lbl_i).second>0;
  }else{
    return false;
  }
}

void TheoryDatatypes::getPossibleCons( EqcInfo* eqc, Node n, std::vector< bool >& pcons ){
  TypeNode tn = n.getType();
  const DType& dt = tn.getDType();
  int lindex = getLabelIndex( eqc, n );
  pcons.resize( dt.getNumConstructors(), lindex==-1 );
  if( lindex!=-1 ){
    pcons[ lindex ] = true;
  }else{
    NodeUIntMap::iterator lbl_i = d_labels.find(n);
    if( lbl_i != d_labels.end() ){
      size_t n_lbl = (*lbl_i).second;
      for (size_t i = 0; i < n_lbl; i++)
      {
        Assert(d_labels_data[n][i].getKind() == NOT);
        unsigned tindex = d_labels_tindex[n][i];
        pcons[ tindex ] = false;
      }
    }
  }
}

void TheoryDatatypes::mkExpDefSkolem( Node sel, TypeNode dt, TypeNode rt ) {
  if( d_exp_def_skolem[dt].find( sel )==d_exp_def_skolem[dt].end() ){
    std::stringstream ss;
    ss << sel << "_uf";
    d_exp_def_skolem[dt][ sel ] = NodeManager::currentNM()->mkSkolem( ss.str().c_str(),
                                  NodeManager::currentNM()->mkFunctionType( dt, rt ) );
  }
}

Node TheoryDatatypes::getTermSkolemFor( Node n ) {
  if( n.getKind()==APPLY_CONSTRUCTOR ){
    NodeMap::const_iterator it = d_term_sk.find( n );
    if( it==d_term_sk.end() ){
      //add purification unit lemma ( k = n )
      Node k = NodeManager::currentNM()->mkSkolem( "k", n.getType(), "reference skolem for datatypes" );
      d_term_sk[n] = k;
      Node eq = k.eqNode( n );
      Trace("datatypes-infer") << "DtInfer : ref : " << eq << std::endl;
      d_im.addPendingLemma(eq);
      return k;
    }else{
      return (*it).second;
    }
  }else{
    return n;
  }
}

void TheoryDatatypes::addTester(
    unsigned ttindex, Node t, EqcInfo* eqc, Node n, Node t_arg)
{
  Trace("datatypes-debug") << "Add tester : " << t << " to eqc(" << n << ")" << std::endl;
  Debug("datatypes-labels") << "Add tester " << t << " " << n << " " << eqc << std::endl;
  bool tpolarity = t.getKind()!=NOT;
  Assert((tpolarity ? t : t[0]).getKind() == APPLY_TESTER);
  Node j, jt;
  bool makeConflict = false;
  int prevTIndex = getLabelIndex(eqc, n);
  if (prevTIndex >= 0)
  {
    unsigned ptu = static_cast<unsigned>(prevTIndex);
    //if we already know the constructor type, check whether it is in conflict or redundant
    if ((ptu == ttindex) != tpolarity)
    {
      if( !eqc->d_constructor.get().isNull() ){
        //conflict because equivalence class contains a constructor
        std::vector<Node> conf;
        conf.push_back(t);
        conf.push_back(t_arg.eqNode(eqc->d_constructor.get()));
        Trace("dt-conflict")
            << "CONFLICT: Tester eq conflict " << conf << std::endl;
        d_im.sendDtConflict(conf, InferId::TESTER_CONFLICT);
        return;
      }else{
        makeConflict = true;
        //conflict because the existing label is contradictory
        j = getLabel( n );
        jt = j;
      }
    }else{
      return;
    }
  }else{
    //otherwise, scan list of labels
    NodeUIntMap::iterator lbl_i = d_labels.find(n);
    Assert(lbl_i != d_labels.end());
    size_t n_lbl = (*lbl_i).second;
    std::map< int, bool > neg_testers;
    for (size_t i = 0; i < n_lbl; i++)
    {
      Assert(d_labels_data[n][i].getKind() == NOT);
      unsigned jtindex = d_labels_tindex[n][i];
      if( jtindex==ttindex ){
        if( tpolarity ){  //we are in conflict
          j = d_labels_data[n][i];
          jt = j[0];
          makeConflict = true;
          break;
        }else{            //it is redundant
          return;
        }
      }else{
        neg_testers[jtindex] = true;
      }
    }
    if( !makeConflict ){
      Debug("datatypes-labels") << "Add to labels " << t << std::endl;
      d_labels[n] = n_lbl + 1;
      if (n_lbl < d_labels_data[n].size())
      {
        // reuse spot in the vector
        d_labels_data[n][n_lbl] = t;
        d_labels_args[n][n_lbl] = t_arg;
        d_labels_tindex[n][n_lbl] = ttindex;
      }else{
        d_labels_data[n].push_back(t);
        d_labels_args[n].push_back(t_arg);
        d_labels_tindex[n].push_back(ttindex);
      }
      n_lbl++;

      const DType& dt = t_arg.getType().getDType();
      Debug("datatypes-labels") << "Labels at " << n_lbl << " / " << dt.getNumConstructors() << std::endl;
      if( tpolarity ){
        instantiate( eqc, n );
        // We could propagate is-C1(x) => not is-C2(x) here for all other
        // constructors, but empirically this hurts performance.
      }else{
        //check if we have reached the maximum number of testers
        // in this case, add the positive tester
        if (n_lbl == dt.getNumConstructors() - 1)
        {
          std::vector< bool > pcons;
          getPossibleCons( eqc, n, pcons );
          int testerIndex = -1;
          for( unsigned i=0; i<pcons.size(); i++ ) {
            if( pcons[i] ){
              testerIndex = i;
              break;
            }
          }
          Assert(testerIndex != -1);
          //we must explain why each term in the set of testers for this equivalence class is equal
          std::vector< Node > eq_terms;
          NodeBuilder<> nb(kind::AND);
          for (unsigned i = 0; i < n_lbl; i++)
          {
            Node ti = d_labels_data[n][i];
            nb << ti;
            Assert(ti.getKind() == NOT);
            Node t_arg2 = d_labels_args[n][i];
            if( std::find( eq_terms.begin(), eq_terms.end(), t_arg2 )==eq_terms.end() ){
              eq_terms.push_back( t_arg2 );
              if( t_arg2!=t_arg ){
                nb << t_arg2.eqNode( t_arg );
              }
            }
          }
          Node t_concl = testerIndex == -1
                             ? NodeManager::currentNM()->mkConst(false)
                             : utils::mkTester(t_arg, testerIndex, dt);
          Node t_concl_exp = ( nb.getNumChildren() == 1 ) ? nb.getChild( 0 ) : nb;
          d_im.addPendingInference(
              t_concl, t_concl_exp, false, InferId::LABEL_EXH);
          Trace("datatypes-infer") << "DtInfer : label : " << t_concl << " by " << t_concl_exp << std::endl;
          return;
        }
      }
    }
  }
  if( makeConflict ){
    Debug("datatypes-labels") << "Explain " << j << " " << t << std::endl;
    std::vector<Node> conf;
    conf.push_back(j);
    conf.push_back(t);
    conf.push_back(jt[0].eqNode(t_arg));
    Trace("dt-conflict") << "CONFLICT: Tester conflict : " << conf << std::endl;
    d_im.sendDtConflict(conf, InferId::TESTER_MERGE_CONFLICT);
  }
}

void TheoryDatatypes::addSelector( Node s, EqcInfo* eqc, Node n, bool assertFacts ) {
  Trace("dt-collapse-sel") << "Add selector : " << s << " to eqc(" << n << ")" << std::endl;
  //check to see if it is redundant
  NodeUIntMap::iterator sel_i = d_selector_apps.find(n);
  Assert(sel_i != d_selector_apps.end());
  if( sel_i != d_selector_apps.end() ){
    size_t n_sel = (*sel_i).second;
    for (size_t j = 0; j < n_sel; j++)
    {
      Node ss = d_selector_apps_data[n][j];
      if( s.getOperator()==ss.getOperator() && ( s.getKind()!=DT_HEIGHT_BOUND || s[1]==ss[1] ) ){
        Trace("dt-collapse-sel") << "...redundant." << std::endl;
        return;
      }
    }
    //add it to the vector
    //sel->push_back( s );
    d_selector_apps[n] = n_sel + 1;
    if (n_sel < d_selector_apps_data[n].size())
    {
      d_selector_apps_data[n][n_sel] = s;
    }else{
      d_selector_apps_data[n].push_back( s );
    }
  
    eqc->d_selectors = true;
  }
  if( assertFacts && !eqc->d_constructor.get().isNull() ){
    //conclude the collapsed merge
    collapseSelector( s, eqc->d_constructor.get() );
  }
}

void TheoryDatatypes::addConstructor( Node c, EqcInfo* eqc, Node n ){
  Trace("datatypes-debug") << "Add constructor : " << c << " to eqc(" << n << ")" << std::endl;
  Assert(eqc->d_constructor.get().isNull());
  //check labels
  NodeUIntMap::iterator lbl_i = d_labels.find(n);
  if( lbl_i != d_labels.end() ){
    size_t constructorIndex = utils::indexOf(c.getOperator());
    size_t n_lbl = (*lbl_i).second;
    for (size_t i = 0; i < n_lbl; i++)
    {
      Node t = d_labels_data[n][i];
      if (d_labels_data[n][i].getKind() == NOT)
      {
        unsigned tindex = d_labels_tindex[n][i];
        if (tindex == constructorIndex)
        {
          std::vector<Node> conf;
          conf.push_back(t);
          conf.push_back(t[0][0].eqNode(c));
          Trace("dt-conflict")
              << "CONFLICT: Tester merge eq conflict : " << conf << std::endl;
          d_im.sendDtConflict(conf, InferId::TESTER_CONFLICT);
          return;
        }
      }
    }
  }
  //check selectors
  NodeUIntMap::iterator sel_i = d_selector_apps.find(n);
  if( sel_i != d_selector_apps.end() ){
    size_t n_sel = (*sel_i).second;
    for (size_t j = 0; j < n_sel; j++)
    {
      Node s = d_selector_apps_data[n][j];
      //collapse the selector
      collapseSelector( s, c );
    }
  }
  eqc->d_constructor.set( c );
}

void TheoryDatatypes::collapseSelector( Node s, Node c ) {
  Assert(c.getKind() == APPLY_CONSTRUCTOR);
  Trace("dt-collapse-sel") << "collapse selector : " << s << " " << c << std::endl;
  Node r;
  bool wrong = false;
  Node eq_exp = s[0].eqNode(c);
  if( s.getKind()==kind::APPLY_SELECTOR_TOTAL ){
    Node selector = s.getOperator();
    size_t constructorIndex = utils::indexOf(c.getOperator());
    const DType& dt = utils::datatypeOf(selector);
    const DTypeConstructor& dtc = dt[constructorIndex];
    int selectorIndex = dtc.getSelectorIndexInternal(selector);
    wrong = selectorIndex<0;
    r = NodeManager::currentNM()->mkNode( kind::APPLY_SELECTOR_TOTAL, s.getOperator(), c );
  }
  if( !r.isNull() ){
    Node rrs;
    if (wrong)
    {
      // Must use make ground term here instead of the rewriter, since we
      // do not want to introduce arbitrary values. This is important so that
      // we avoid constants for types that are not "closed enumerable", e.g.
      // uninterpreted sorts and arrays, where the solver does not fully
      // handle values of the sort. The call to mkGroundTerm does not introduce
      // values for these sorts.
      rrs = r.getType().mkGroundTerm();
      Trace("datatypes-wrong-sel")
          << "Bad apply " << r << " term = " << rrs
          << ", value = " << r.getType().mkGroundValue() << std::endl;
    }
    else
    {
      rrs = Rewriter::rewrite(r);
    }
    if (s != rrs)
    {
      Node eq = s.eqNode(rrs);
      // Since collapsing selectors may generate new terms, we must send
      // this out as a lemma if it is of an external type, or otherwise we
      // may ask for the equality status of terms that only datatypes knows
      // about, see issue #5344.
      bool forceLemma = !s.getType().isDatatype();
      Trace("datatypes-infer") << "DtInfer : collapse sel";
      Trace("datatypes-infer") << " : " << eq << " by " << eq_exp << std::endl;
      d_im.addPendingInference(eq, eq_exp, forceLemma, InferId::COLLAPSE_SEL);
    }
  }
}

EqualityStatus TheoryDatatypes::getEqualityStatus(TNode a, TNode b){
  Assert(d_equalityEngine->hasTerm(a) && d_equalityEngine->hasTerm(b));
  if (d_equalityEngine->areEqual(a, b))
  {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }
  if (d_equalityEngine->areDisequal(a, b, false))
  {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }
  return EQUALITY_FALSE_IN_MODEL;
}

void TheoryDatatypes::addCarePairs(TNodeTrie* t1,
                                   TNodeTrie* t2,
                                   unsigned arity,
                                   unsigned depth,
                                   unsigned& n_pairs)
{
  if( depth==arity ){
    if( t2!=NULL ){
      Node f1 = t1->getData();
      Node f2 = t2->getData();
      if( !areEqual( f1, f2 ) ){
        Trace("dt-cg") << "Check " << f1 << " and " << f2 << std::endl;
        vector< pair<TNode, TNode> > currentPairs;
        for (unsigned k = 0; k < f1.getNumChildren(); ++ k) {
          TNode x = f1[k];
          TNode y = f2[k];
          Assert(d_equalityEngine->hasTerm(x));
          Assert(d_equalityEngine->hasTerm(y));
          Assert(!areDisequal(x, y));
          Assert(!areCareDisequal(x, y));
          if (!d_equalityEngine->areEqual(x, y))
          {
            Trace("dt-cg") << "Arg #" << k << " is " << x << " " << y << std::endl;
            if (d_equalityEngine->isTriggerTerm(x, THEORY_DATATYPES)
                && d_equalityEngine->isTriggerTerm(y, THEORY_DATATYPES))
            {
              TNode x_shared = d_equalityEngine->getTriggerTermRepresentative(
                  x, THEORY_DATATYPES);
              TNode y_shared = d_equalityEngine->getTriggerTermRepresentative(
                  y, THEORY_DATATYPES);
              currentPairs.push_back(make_pair(x_shared, y_shared));
            }
          }
        }
        for (unsigned c = 0; c < currentPairs.size(); ++ c) {
          Trace("dt-cg-pair") << "Pair : " << currentPairs[c].first << " " << currentPairs[c].second << std::endl;
          addCarePair(currentPairs[c].first, currentPairs[c].second);
          n_pairs++;
        }
      }
    }
  }else{
    if( t2==NULL ){
      if( depth<(arity-1) ){
        //add care pairs internal to each child
        for (std::pair<const TNode, TNodeTrie>& tt : t1->d_data)
        {
          addCarePairs(&tt.second, nullptr, arity, depth + 1, n_pairs);
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
          if (!d_equalityEngine->areDisequal(it->first, it2->first, false))
          {
            if( !areCareDisequal(it->first, it2->first) ){
              addCarePairs( &it->second, &it2->second, arity, depth+1, n_pairs );
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
          if (!d_equalityEngine->areDisequal(tt1.first, tt2.first, false))
          {
            if (!areCareDisequal(tt1.first, tt2.first))
            {
              addCarePairs(&tt1.second, &tt2.second, arity, depth + 1, n_pairs);
            }
          }
        }
      }
    }
  }
}

void TheoryDatatypes::computeCareGraph(){
  unsigned n_pairs = 0;
  Trace("dt-cg-summary") << "Compute graph for dt..." << d_functionTerms.size() << " " << d_sharedTerms.size() << std::endl;
  Trace("dt-cg") << "Build indices..." << std::endl;
  std::map<TypeNode, std::map<Node, TNodeTrie> > index;
  std::map< Node, unsigned > arity;
  //populate indices
  unsigned functionTerms = d_functionTerms.size();
  for( unsigned i=0; i<functionTerms; i++ ){
    TNode f1 = d_functionTerms[i];
    Assert(d_equalityEngine->hasTerm(f1));
    Trace("dt-cg-debug") << "...build for " << f1 << std::endl;
    //break into index based on operator, and type of first argument (since some operators are parametric)
    Node op = f1.getOperator();
    TypeNode tn = f1[0].getType();
    std::vector< TNode > reps;
    bool has_trigger_arg = false;
    for( unsigned j=0; j<f1.getNumChildren(); j++ ){
      reps.push_back(d_equalityEngine->getRepresentative(f1[j]));
      if (d_equalityEngine->isTriggerTerm(f1[j], THEORY_DATATYPES))
      {
        has_trigger_arg = true;
      }
    }
    //only may contribute to care pairs if has at least one trigger argument
    if( has_trigger_arg ){
      index[tn][op].addTerm( f1, reps );
      arity[op] = reps.size();
    }
  }
  //for each index
  for (std::pair<const TypeNode, std::map<Node, TNodeTrie> >& tt : index)
  {
    for (std::pair<const Node, TNodeTrie>& t : tt.second)
    {
      Trace("dt-cg") << "Process index " << tt.first << ", " << t.first << "..."
                     << std::endl;
      addCarePairs(&t.second, nullptr, arity[t.first], 0, n_pairs);
    }
  }
  Trace("dt-cg-summary") << "...done, # pairs = " << n_pairs << std::endl;
}

bool TheoryDatatypes::collectModelValues(TheoryModel* m,
                                         const std::set<Node>& termSet)
{
  Trace("dt-cmi") << "Datatypes : Collect model values "
                  << d_equalityEngine->consistent() << std::endl;
  Trace("dt-model") << std::endl;
  printModelDebug( "dt-model" );
  Trace("dt-model") << std::endl;

  //get all constructors
  eq::EqClassesIterator eqccs_i = eq::EqClassesIterator(d_equalityEngine);
  std::vector< Node > cons;
  std::vector< Node > nodes;
  std::map< Node, Node > eqc_cons;
  while( !eqccs_i.isFinished() ){
    Node eqc = (*eqccs_i);
    //for all equivalence classes that are datatypes
    //if( termSet.find( eqc )==termSet.end() ){
    //  Trace("dt-cmi-debug") << "Irrelevant eqc : " << eqc << std::endl;
    //}
    if( eqc.getType().isDatatype() ){
      EqcInfo* ei = getOrMakeEqcInfo( eqc );
      if( ei && !ei->d_constructor.get().isNull() ){
        Node c = ei->d_constructor.get();
        cons.push_back( c );
        eqc_cons[ eqc ] = c;
      }else{
        //if eqc contains a symbol known to datatypes (a selector), then we must assign
        //should assign constructors to EQC if they have a selector or a tester
        bool shouldConsider = ( ei && ei->d_selectors ) || hasTester( eqc );
        if( shouldConsider ){
          nodes.push_back( eqc );
        }
      }
    }
    //}
    ++eqccs_i;
  }

  //unsigned orig_size = nodes.size();
  std::map< TypeNode, int > typ_enum_map;
  std::vector< TypeEnumerator > typ_enum;
  unsigned index = 0;
  while( index<nodes.size() ){
    Node eqc = nodes[index];
    Node neqc;
    bool addCons = false;
    TypeNode tt = eqc.getType();
    const DType& dt = tt.getDType();
    if (!d_equalityEngine->hasTerm(eqc))
    {
      Assert(false);
    }else{
      Trace("dt-cmi") << "NOTICE : Datatypes: no constructor in equivalence class " << eqc << std::endl;
      Trace("dt-cmi") << "   Type : " << eqc.getType() << std::endl;
      EqcInfo* ei = getOrMakeEqcInfo( eqc );
      std::vector< bool > pcons;
      getPossibleCons( ei, eqc, pcons );
      Trace("dt-cmi") << "Possible constructors : ";
      for( unsigned i=0; i<pcons.size(); i++ ){
        Trace("dt-cmi") << pcons[i] << " ";
      }
      Trace("dt-cmi") << std::endl;
      for( unsigned r=0; r<2; r++ ){
        if( neqc.isNull() ){
          for( unsigned i=0; i<pcons.size(); i++ ){
            //must try the infinite ones first
            bool cfinite = dt[ i ].isInterpretedFinite( tt );
            if( pcons[i] && (r==1)==cfinite ){
              neqc = utils::getInstCons(eqc, dt, i);
              break;
            }
          }
        }
      }
      addCons = true;
    }
    if( !neqc.isNull() ){
      Trace("dt-cmi") << "Assign : " << neqc << std::endl;
      if (!m->assertEquality(eqc, neqc, true))
      {
        return false;
      }
      eqc_cons[ eqc ] = neqc;
    }
    if( addCons ){
      cons.push_back( neqc );
    }
    ++index;
  }

  for( std::map< Node, Node >::iterator it = eqc_cons.begin(); it != eqc_cons.end(); ++it ){
    Node eqc = it->first;
    if( eqc.getType().isCodatatype() ){
      //until models are implemented for codatatypes
      //throw Exception("Models for codatatypes are not supported in this version.");
      //must proactive expand to avoid looping behavior in model builder
      if( !it->second.isNull() ){
        std::map< Node, int > vmap;
        Node v = getCodatatypesValue( it->first, eqc_cons, vmap, 0 );
        Trace("dt-cmi") << "  EQC(" << it->first << "), constructor is " << it->second << ", value is " << v << ", const = " << v.isConst() << std::endl;
        if (!m->assertEquality(eqc, v, true))
        {
          return false;
        }
        m->assertSkeleton(v);
      }
    }else{
      Trace("dt-cmi") << "Datatypes : assert representative " << it->second << " for " << it->first << std::endl;
      m->assertSkeleton(it->second);
    }
  }
  return true;
}


Node TheoryDatatypes::getCodatatypesValue( Node n, std::map< Node, Node >& eqc_cons, std::map< Node, int >& vmap, int depth ){
  std::map< Node, int >::iterator itv = vmap.find( n );
  if( itv!=vmap.end() ){
    int debruijn = depth - 1 - itv->second;
    return NodeManager::currentNM()->mkConst(
        UninterpretedConstant(n.getType(), debruijn));
  }else if( n.getType().isDatatype() ){
    Node nc = eqc_cons[n];
    if( !nc.isNull() ){
      vmap[n] = depth;
      Trace("dt-cmi-cdt-debug") << "    map " << n << " -> " << depth << std::endl;
      Assert(nc.getKind() == APPLY_CONSTRUCTOR);
      std::vector< Node > children;
      children.push_back( nc.getOperator() );
      for( unsigned i=0; i<nc.getNumChildren(); i++ ){
        Node r = getRepresentative( nc[i] );
        Node rv = getCodatatypesValue( r, eqc_cons, vmap, depth+1 );
        children.push_back( rv );
      }
      vmap.erase( n );
      return NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
    }
  }
  return n;
}

Node TheoryDatatypes::getSingletonLemma( TypeNode tn, bool pol ) {
  int index = pol ? 0 : 1;
  std::map< TypeNode, Node >::iterator it = d_singleton_lemma[index].find( tn );
  if( it==d_singleton_lemma[index].end() ){
    Node a;
    if( pol ){
      Node v1 = NodeManager::currentNM()->mkBoundVar( tn );
      Node v2 = NodeManager::currentNM()->mkBoundVar( tn );
      a = NodeManager::currentNM()->mkNode( FORALL, NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, v1, v2 ), v1.eqNode( v2 ) );
    }else{
      Node v1 = NodeManager::currentNM()->mkSkolem( "k1", tn );
      Node v2 = NodeManager::currentNM()->mkSkolem( "k2", tn );
      a = v1.eqNode( v2 ).negate();
      //send out immediately as lemma
      d_im.lemma(a);
      Trace("dt-singleton") << "******** assert " << a << " to avoid singleton cardinality for type " << tn << std::endl;
    }
    d_singleton_lemma[index][tn] = a;
    return a;
  }else{
    return it->second;
  }
}

void TheoryDatatypes::collectTerms( Node n ) {
  if (d_collectTermsCache.find(n) != d_collectTermsCache.end())
  {
    // already processed
    return;
  }
  d_collectTermsCache[n] = true;
  Kind nk = n.getKind();
  if (nk == APPLY_CONSTRUCTOR)
  {
    Debug("datatypes") << "  Found constructor " << n << endl;
    if (n.getNumChildren() > 0)
    {
      d_functionTerms.push_back(n);
    }
    return;
  }
  if (nk == APPLY_SELECTOR_TOTAL || nk == DT_SIZE || nk == DT_HEIGHT_BOUND)
  {
    d_functionTerms.push_back(n);
    // we must also record which selectors exist
    Trace("dt-collapse-sel") << "  Found selector " << n << endl;
    Node rep = getRepresentative(n[0]);
    // record it in the selectors
    EqcInfo* eqc = getOrMakeEqcInfo(rep, true);
    // add it to the eqc info
    addSelector(n, eqc, rep);
  }

  // now, do user-context-dependent lemmas
  if (nk != DT_SIZE && nk != DT_HEIGHT_BOUND)
  {
    // if not one of these kinds, there are no lemmas
    return;
  }
  if (d_collectTermsCacheU.find(n) != d_collectTermsCacheU.end())
  {
    return;
  }
  d_collectTermsCacheU[n] = true;

  NodeManager* nm = NodeManager::currentNM();

  if (nk == DT_SIZE)
  {
    Node lem = nm->mkNode(LEQ, d_zero, n);
    Trace("datatypes-infer")
        << "DtInfer : size geq zero : " << lem << std::endl;
    d_im.addPendingLemma(lem);
  }
  else if (nk == DT_HEIGHT_BOUND && n[1].getConst<Rational>().isZero())
  {
    std::vector<Node> children;
    const DType& dt = n[0].getType().getDType();
    for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      if (utils::isNullaryConstructor(dt[i]))
      {
        Node test = utils::mkTester(n[0], i, dt);
        children.push_back(test);
      }
    }
    Node lem;
    if (children.empty())
    {
      lem = n.negate();
    }
    else
    {
      lem = n.eqNode(children.size() == 1 ? children[0]
                                          : nm->mkNode(OR, children));
    }
    Trace("datatypes-infer") << "DtInfer : zero height : " << lem << std::endl;
    d_im.addPendingLemma(lem);
  }
}

Node TheoryDatatypes::getInstantiateCons(Node n, const DType& dt, int index)
{
  if( n.getKind()==APPLY_CONSTRUCTOR && n.getNumChildren()==0 ){
    return n;
  }
  //add constructor to equivalence class
  Node k = getTermSkolemFor( n );
  Node n_ic = utils::getInstCons(k, dt, index);
  n_ic = Rewriter::rewrite( n_ic );
  // it may be a new term, so we collect terms and add it to the equality engine
  collectTerms( n_ic );
  d_equalityEngine->addTerm(n_ic);
  Debug("dt-enum") << "Made instantiate cons " << n_ic << std::endl;
  return n_ic;
}

void TheoryDatatypes::instantiate( EqcInfo* eqc, Node n ){
  Trace("datatypes-debug") << "Instantiate: " << n << std::endl;
  //add constructor to equivalence class if not done so already
  int index = getLabelIndex( eqc, n );
  if (index == -1 || eqc->d_inst)
  {
    return;
  }
  Node exp;
  Node tt;
  if (!eqc->d_constructor.get().isNull())
  {
    exp = d_true;
    tt = eqc->d_constructor;
  }
  else
  {
    exp = getLabel(n);
    tt = exp[0];
  }
  TypeNode ttn = tt.getType();
  const DType& dt = ttn.getDType();
  // instantiate this equivalence class
  eqc->d_inst = true;
  Node tt_cons = getInstantiateCons(tt, dt, index);
  Node eq;
  if (tt == tt_cons)
  {
    return;
  }
  eq = tt.eqNode(tt_cons);
  // Determine if the equality must be sent out as a lemma. Notice that
  // we  keep new equalities from the instantiate rule internal
  // as long as they are for datatype constructors that have no arguments that
  // have finite external type, which corresponds to:
  //   forceLemma = dt[index].hasFiniteExternalArgType(ttn);
  // Such equalities must be sent because they introduce selector terms that
  // may contribute to conflicts due to cardinality (good examples of this are
  // regress0/datatypes/dt-param-card4-bool-sat.smt2 and
  // regress0/datatypes/list-bool.smt2).
  bool forceLemma = true;
  if (options::dtPoliteOptimize())
  {
    forceLemma = dt[index].hasFiniteExternalArgType(ttn);
  }
  Trace("datatypes-infer-debug") << "DtInstantiate : " << eqc << " " << eq
                                 << " forceLemma = " << forceLemma << std::endl;
  d_im.addPendingInference(eq, exp, forceLemma, InferId::INST);
  Trace("datatypes-infer") << "DtInfer : instantiate : " << eq << " by " << exp
                           << std::endl;
}

void TheoryDatatypes::checkCycles() {
  Trace("datatypes-cycle-check") << "Check acyclicity" << std::endl;
  std::vector< Node > cdt_eqc;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    TypeNode tn = eqc.getType();
    if( tn.isDatatype() ) {
      if( !tn.isCodatatype() ){
        if( options::dtCyclic() ){
          //do cycle checks
          std::map< TNode, bool > visited;
          std::map< TNode, bool > proc;
          std::vector<Node> expl;
          Trace("datatypes-cycle-check") << "...search for cycle starting at " << eqc << std::endl;
          Node cn = searchForCycle( eqc, eqc, visited, proc, expl );
          Trace("datatypes-cycle-check") << "...finish." << std::endl;
          //if we discovered a different cycle while searching this one
          if( !cn.isNull() && cn!=eqc ){
            visited.clear();
            proc.clear();
            expl.clear();
            Node prev = cn;
            cn = searchForCycle( cn, cn, visited, proc, expl );
            Assert(prev == cn);
          }

          if( !cn.isNull() ) {
            Assert(expl.size() > 0);
            Trace("dt-conflict")
                << "CONFLICT: Cycle conflict : " << expl << std::endl;
            d_im.sendDtConflict(expl, InferId::CYCLE);
            return;
          }
        }
      }else{
        //indexing
        cdt_eqc.push_back( eqc );
      }
    }
    ++eqcs_i;
  }
  Trace("datatypes-cycle-check") << "Check uniqueness" << std::endl;
  //process codatatypes
  if( cdt_eqc.size()>1 && options::cdtBisimilar() ){
    printModelDebug("dt-cdt-debug");
    Trace("dt-cdt-debug") << "Process " << cdt_eqc.size() << " co-datatypes" << std::endl;
    std::vector< std::vector< Node > > part_out;
    std::vector<Node> exp;
    std::map< Node, Node > cn;
    std::map< Node, std::map< Node, int > > dni;
    for( unsigned i=0; i<cdt_eqc.size(); i++ ){
      cn[cdt_eqc[i]] = cdt_eqc[i];
    }
    separateBisimilar( cdt_eqc, part_out, exp, cn, dni, 0, false );
    Trace("dt-cdt-debug") << "Done separate bisimilar." << std::endl;
    if( !part_out.empty() ){
      Trace("dt-cdt-debug") << "Process partition size " << part_out.size() << std::endl;
      for( unsigned i=0; i<part_out.size(); i++ ){
        std::vector< Node > part;
        part.push_back( part_out[i][0] );
        for( unsigned j=1; j<part_out[i].size(); j++ ){
          Trace("dt-cdt") << "Codatatypes : " << part_out[i][0] << " and " << part_out[i][j] << " must be equal!!" << std::endl;
          part.push_back( part_out[i][j] );
          std::vector< std::vector< Node > > tpart_out;
          exp.clear();
          cn.clear();
          cn[part_out[i][0]] = part_out[i][0];
          cn[part_out[i][j]] = part_out[i][j];
          dni.clear();
          separateBisimilar( part, tpart_out, exp, cn, dni, 0, true );
          Assert(tpart_out.size() == 1 && tpart_out[0].size() == 2);
          part.pop_back();
          //merge based on explanation
          Trace("dt-cdt") << "  exp is : ";
          for( unsigned k=0; k<exp.size(); k++ ){
            Trace("dt-cdt") << exp[k] << " ";
          }
          Trace("dt-cdt") << std::endl;
          Node eq = part_out[i][0].eqNode( part_out[i][j] );
          Node eqExp = NodeManager::currentNM()->mkAnd(exp);
          d_im.addPendingInference(eq, eqExp, false, InferId::BISIMILAR);
          Trace("datatypes-infer") << "DtInfer : cdt-bisimilar : " << eq << " by " << eqExp << std::endl;
        }
      }
    }
  }
}

//everything is in terms of representatives
void TheoryDatatypes::separateBisimilar(
    std::vector<Node>& part,
    std::vector<std::vector<Node> >& part_out,
    std::vector<Node>& exp,
    std::map<Node, Node>& cn,
    std::map<Node, std::map<Node, int> >& dni,
    int dniLvl,
    bool mkExp)
{
  if( !mkExp ){
    Trace("dt-cdt-debug") << "Separate bisimilar : " << std::endl;
    for( unsigned i=0; i<part.size(); i++ ){
      Trace("dt-cdt-debug") << "   " << part[i] << ", current = " << cn[part[i]] << std::endl;
    }
  }
  Assert(part.size() > 1);
  std::map< Node, std::vector< Node > > new_part;
  std::map< Node, std::vector< Node > > new_part_c;
  std::map< int, std::vector< Node > > new_part_rec;

  std::map< Node, Node > cn_cons;
  for( unsigned j=0; j<part.size(); j++ ){
    Node c = cn[part[j]];
    std::map< Node, int >::iterator it_rec = dni[part[j]].find( c );
    if( it_rec!=dni[part[j]].end() ){
      //looped
      if( !mkExp ){ Trace("dt-cdt-debug") << "  - " << part[j] << " is looping at index " << it_rec->second << std::endl; }
      new_part_rec[ it_rec->second ].push_back( part[j] );
    }else{
      if( c.getType().isDatatype() ){
        Node ncons = getEqcConstructor( c );
        if( ncons.getKind()==APPLY_CONSTRUCTOR ) {
          Node cc = ncons.getOperator();
          cn_cons[part[j]] = ncons;
          if (mkExp && c != ncons)
          {
            exp.push_back(c.eqNode(ncons));
          }
          new_part[cc].push_back( part[j] );
          if( !mkExp ){ Trace("dt-cdt-debug") << "  - " << part[j] << " is datatype " << ncons << "." << std::endl; }
        }else{
          new_part_c[c].push_back( part[j] );
          if( !mkExp ){ Trace("dt-cdt-debug") << "  - " << part[j] << " is unspecified datatype." << std::endl; }
        }
      }else{
        //add equivalences
        if( !mkExp ){ Trace("dt-cdt-debug") << "  - " << part[j] << " is term " << c << "." << std::endl; }
        new_part_c[c].push_back( part[j] );
      }
    }
  }
  //direct add for constants
  for( std::map< Node, std::vector< Node > >::iterator it = new_part_c.begin(); it != new_part_c.end(); ++it ){
    if( it->second.size()>1 ){
      std::vector< Node > vec;
      vec.insert( vec.begin(), it->second.begin(), it->second.end() );
      part_out.push_back( vec );
    }
  }
  //direct add for recursive
  for( std::map< int, std::vector< Node > >::iterator it = new_part_rec.begin(); it != new_part_rec.end(); ++it ){
    if( it->second.size()>1 ){
      std::vector< Node > vec;
      vec.insert( vec.begin(), it->second.begin(), it->second.end() );
      part_out.push_back( vec );
    }else{
      //add back : could match a datatype?
    }
  }
  //recurse for the datatypes
  for( std::map< Node, std::vector< Node > >::iterator it = new_part.begin(); it != new_part.end(); ++it ){
    if( it->second.size()>1 ){
      //set dni to check for loops
      std::map< Node, Node > dni_rem;
      for( unsigned i=0; i<it->second.size(); i++ ){
        Node n = it->second[i];
        dni[n][cn[n]] = dniLvl;
        dni_rem[n] = cn[n];
      }

      //we will split based on the arguments of the datatype
      std::vector< std::vector< Node > > split_new_part;
      split_new_part.push_back( it->second );

      unsigned nChildren = cn_cons[it->second[0]].getNumChildren();
      //for each child of constructor
      unsigned cindex = 0;
      while( cindex<nChildren && !split_new_part.empty() ){
        if( !mkExp ){ Trace("dt-cdt-debug") << "Split argument #" << cindex << " of " << it->first << "..." << std::endl; }
        std::vector< std::vector< Node > > next_split_new_part;
        for( unsigned j=0; j<split_new_part.size(); j++ ){
          //set current node
          for( unsigned k=0; k<split_new_part[j].size(); k++ ){
            Node n = split_new_part[j][k];
            Node cnc = cn_cons[n][cindex];
            Node nr = getRepresentative(cnc);
            cn[n] = nr;
            if (mkExp && cnc != nr)
            {
              exp.push_back(nr.eqNode(cnc));
            }
          }
          std::vector< std::vector< Node > > c_part_out;
          separateBisimilar( split_new_part[j], c_part_out, exp, cn, dni, dniLvl+1, mkExp );
          next_split_new_part.insert( next_split_new_part.end(), c_part_out.begin(), c_part_out.end() );
        }
        split_new_part.clear();
        split_new_part.insert( split_new_part.end(), next_split_new_part.begin(), next_split_new_part.end() );
        cindex++;
      }
      part_out.insert( part_out.end(), split_new_part.begin(), split_new_part.end() );

      for( std::map< Node, Node >::iterator it2 = dni_rem.begin(); it2 != dni_rem.end(); ++it2 ){
        dni[it2->first].erase( it2->second );
      }
    }
  }
}

//postcondition: if cycle detected, explanation is why n is a subterm of on
Node TheoryDatatypes::searchForCycle(TNode n,
                                     TNode on,
                                     std::map<TNode, bool>& visited,
                                     std::map<TNode, bool>& proc,
                                     std::vector<Node>& explanation,
                                     bool firstTime)
{
  Trace("datatypes-cycle-check2") << "Search for cycle " << n << " " << on << endl;
  TNode ncons;
  TNode nn;
  if( !firstTime ){
    nn = getRepresentative( n );
    if( nn==on ){
      if (n != nn)
      {
        explanation.push_back(n.eqNode(nn));
      }
      return on;
    }
  }else{
    nn = getRepresentative( n );
  }
  if( proc.find( nn )!=proc.end() ){
    return Node::null();
  }
  Trace("datatypes-cycle-check2") << "...representative : " << nn << " " << ( visited.find( nn ) == visited.end() ) << " " << visited.size() << std::endl;
  if( visited.find( nn ) == visited.end() ) {
    Trace("datatypes-cycle-check2") << "  visit : " << nn << std::endl;
    visited[nn] = true;
    TNode nncons = getEqcConstructor(nn);
    if (nncons.getKind() == APPLY_CONSTRUCTOR)
    {
      for (unsigned i = 0; i < nncons.getNumChildren(); i++)
      {
        TNode cn =
            searchForCycle(nncons[i], on, visited, proc, explanation, false);
        if( cn==on ) {
          //add explanation for why the constructor is connected
          if (n != nncons)
          {
            explanation.push_back(n.eqNode(nncons));
          }
          return on;
        }else if( !cn.isNull() ){
          return cn;
        }
      }
    }
    Trace("datatypes-cycle-check2") << "  unvisit : " << nn << std::endl;
    proc[nn] = true;
    visited.erase( nn );
    return Node::null();
  }else{
    TypeNode tn = nn.getType();
    if( tn.isDatatype() ) {
      if( !tn.isCodatatype() ){
        return nn;
      }
    }
    return Node::null();
  }
}

bool TheoryDatatypes::hasTerm(TNode a) { return d_equalityEngine->hasTerm(a); }

bool TheoryDatatypes::areEqual( TNode a, TNode b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine->areEqual(a, b);
  }else{
    return false;
  }
}

bool TheoryDatatypes::areDisequal( TNode a, TNode b ){
  if( a==b ){
    return false;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine->areDisequal(a, b, false);
  }else{
    //TODO : constants here?
    return false;
  }
}

bool TheoryDatatypes::areCareDisequal( TNode x, TNode y ) {
  Trace("datatypes-cg") << "areCareDisequal: " << x << " " << y << std::endl;
  Assert(d_equalityEngine->hasTerm(x));
  Assert(d_equalityEngine->hasTerm(y));
  if (d_equalityEngine->isTriggerTerm(x, THEORY_DATATYPES)
      && d_equalityEngine->isTriggerTerm(y, THEORY_DATATYPES))
  {
    TNode x_shared =
        d_equalityEngine->getTriggerTermRepresentative(x, THEORY_DATATYPES);
    TNode y_shared =
        d_equalityEngine->getTriggerTermRepresentative(y, THEORY_DATATYPES);
    EqualityStatus eqStatus = d_valuation.getEqualityStatus(x_shared, y_shared);
    if( eqStatus==EQUALITY_FALSE_AND_PROPAGATED || eqStatus==EQUALITY_FALSE || eqStatus==EQUALITY_FALSE_IN_MODEL ){
      return true;
    }
  }
  return false;
}

TNode TheoryDatatypes::getRepresentative( TNode a ){
  if( hasTerm( a ) ){
    return d_equalityEngine->getRepresentative(a);
  }else{
    return a;
  }
}

void TheoryDatatypes::printModelDebug( const char* c ){
  if(! (Trace.isOn(c))) {
    return;
  }

  Trace( c ) << "Datatypes model : " << std::endl;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    //if( !eqc.getType().isBoolean() ){
      if( eqc.getType().isDatatype() ){
        Trace( c ) << "DATATYPE : ";
      }
      Trace( c ) << eqc << " : " << eqc.getType() << " : " << std::endl;
      Trace( c ) << "   { ";
      //add terms to model
      eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, d_equalityEngine);
      while( !eqc_i.isFinished() ){
        if( (*eqc_i)!=eqc ){
          Trace( c ) << (*eqc_i) << " ";
        }
        ++eqc_i;
      }
      Trace( c ) << "}" << std::endl;
      if( eqc.getType().isDatatype() ){
        EqcInfo* ei = getOrMakeEqcInfo( eqc );
        if( ei ){
          Trace( c ) << "   Instantiated : " << ei->d_inst.get() << std::endl;
          Trace( c ) << "   Constructor : ";
          if( !ei->d_constructor.get().isNull() ){
            Trace( c )<< ei->d_constructor.get();
          }
          Trace( c ) << std::endl << "   Labels : ";
          if( hasLabel( ei, eqc ) ){
            Trace( c ) << getLabel( eqc );
          }else{
            NodeUIntMap::iterator lbl_i = d_labels.find(eqc);
            if( lbl_i != d_labels.end() ){
              for (size_t j = 0; j < (*lbl_i).second; j++)
              {
                Trace( c ) << d_labels_data[eqc][j] << " ";
              }
            }
          }
          Trace( c ) << std::endl;
          Trace( c ) << "   Selectors : " << ( ei->d_selectors ? "yes, " : "no " );
          NodeUIntMap::iterator sel_i = d_selector_apps.find(eqc);
          if( sel_i != d_selector_apps.end() ){
            for (size_t j = 0; j < (*sel_i).second; j++)
            {
              Trace( c ) << d_selector_apps_data[eqc][j] << " ";
            }
          }
          Trace( c ) << std::endl;
        }
      }
    //}
    ++eqcs_i;
  }
}

void TheoryDatatypes::computeRelevantTerms(std::set<Node>& termSet)
{
  Trace("dt-cmi") << "Have " << termSet.size() << " relevant terms..."
                  << std::endl;

  //also include non-singleton equivalence classes  TODO : revisit this
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  while( !eqcs_i.isFinished() ){
    TNode r = (*eqcs_i);
    bool addedFirst = false;
    Node first;
    TypeNode rtn = r.getType();
    if (!rtn.isBoolean())
    {
      eq::EqClassIterator eqc_i = eq::EqClassIterator(r, d_equalityEngine);
      while (!eqc_i.isFinished())
      {
        TNode n = (*eqc_i);
        if (first.isNull())
        {
          first = n;
          // always include all datatypes
          if (rtn.isDatatype())
          {
            addedFirst = true;
            termSet.insert(n);
          }
        }
        else
        {
          if (!addedFirst)
          {
            addedFirst = true;
            termSet.insert(first);
          }
          termSet.insert(n);
        }
        ++eqc_i;
      }
    }
    ++eqcs_i;
  }
}

std::pair<bool, Node> TheoryDatatypes::entailmentCheck(TNode lit)
{
  Trace("dt-entail") << "Check entailed : " << lit << std::endl;
  Node atom = lit.getKind()==NOT ? lit[0] : lit;
  bool pol = lit.getKind()!=NOT;
  if( atom.getKind()==APPLY_TESTER ){
    Node n = atom[0];
    if( hasTerm( n ) ){
      Node r = d_equalityEngine->getRepresentative(n);
      EqcInfo * ei = getOrMakeEqcInfo( r, false );
      int l_index = getLabelIndex( ei, r );
      int t_index = static_cast<int>(utils::indexOf(atom.getOperator()));
      Trace("dt-entail") << "  Tester indices are " << t_index << " and " << l_index << std::endl;
      if( l_index!=-1 && (l_index==t_index)==pol ){
        std::vector< TNode > exp_c;
        Node eqToExplain;
        if( ei && !ei->d_constructor.get().isNull() ){
          eqToExplain = n.eqNode(ei->d_constructor.get());
        }else{
          Node lbl = getLabel( n );
          Assert(!lbl.isNull());
          exp_c.push_back( lbl );
          Assert(areEqual(n, lbl[0]));
          eqToExplain = n.eqNode(lbl[0]);
        }
        d_equalityEngine->explainLit(eqToExplain, exp_c);
        Node exp = NodeManager::currentNM()->mkAnd(exp_c);
        Trace("dt-entail") << "  entailed, explanation is " << exp << std::endl;
        return make_pair(true, exp);
      }
    }
  }
  return make_pair(false, Node::null());
}

} /* namepsace CVC4::theory::datatypes */
} /* namepsace CVC4::theory */
} /* namepsace CVC4 */

/*********************                                                        */
/*! \file theory_rewriterules.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Francois Bobot
 ** Minor contributors (to current version): Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Deals with rewrite rules ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/rewriterules/theory_rewriterules.h"
#include "theory/rewriterules/theory_rewriterules_rules.h"
#include "theory/rewriterules/theory_rewriterules_params.h"

#include "theory/rewriterules/theory_rewriterules_preprocess.h"
#include "theory/rewriter.h"
#include "theory/rewriterules/options.h"


using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::rewriterules;
using namespace CVC4::theory::rrinst;


namespace CVC4 {
namespace theory {
namespace rewriterules {


inline std::ostream& operator <<(std::ostream& stream, const RuleInst& ri) {
  ri.toStream(stream);
  return stream;
}

static const RuleInst* RULEINST_TRUE = (RuleInst*) 1;
static const RuleInst* RULEINST_FALSE = (RuleInst*) 2;

  /** Rule an instantiation with the given match */
RuleInst::RuleInst(TheoryRewriteRules & re, const RewriteRule * r,
                   std::vector<Node> & inst_subst,
                   Node matched):
  rule(r), d_matched(matched)
{
  Assert(r != NULL);
  Assert(!r->directrr || !d_matched.isNull());
  subst.swap(inst_subst);
};

Node RuleInst::substNode(const TheoryRewriteRules & re, TNode r,
                         TCache cache ) const {
  Assert(this != RULEINST_TRUE && this != RULEINST_FALSE);
  return r.substitute (rule->free_vars.begin(),rule->free_vars.end(),
                       subst.begin(),subst.end(),cache);
};
size_t RuleInst::findGuard(TheoryRewriteRules & re, size_t start)const{
  TCache cache;
  Assert(this != RULEINST_TRUE && this != RULEINST_FALSE);
  while (start < (rule->guards).size()){
    Node g = substNode(re,rule->guards[start],cache);
    switch(re.addWatchIfDontKnow(g,this,start)){
    case ATRUE:
      Debug("rewriterules::guards") << g << "is true" << std::endl;
      ++start;
      continue;
    case AFALSE:
      Debug("rewriterules::guards") << g << "is false" << std::endl;
      return -1;
    case ADONTKNOW:
      Debug("rewriterules::guards") << g << "is unknown" << std::endl;
      return start;
    }
  }
  /** All the guards are verified */
  re.propagateRule(this,cache);
  return start;
};

bool RuleInst::alreadyRewritten(TheoryRewriteRules & re) const{
  Assert(this != RULEINST_TRUE && this != RULEINST_FALSE);
  static NoMatchAttribute rewrittenNodeAttribute;
  TCache cache;
  for(std::vector<Node>::const_iterator
        iter = rule->to_remove.begin();
      iter != rule->to_remove.end(); ++iter){
    if (substNode(re,*iter,cache).getAttribute(rewrittenNodeAttribute))
      return true;
  };
  return false;
}

void RuleInst::toStream(std::ostream& out) const{
  if(this == RULEINST_TRUE){ out << "TRUE"; return;};
  if(this == RULEINST_FALSE){ out << "FALSE"; return;};
  out << "(" << *rule << ") ";
  for(std::vector<Node>::const_iterator
        iter = subst.begin(); iter != subst.end(); ++iter){
    out << *iter << " ";
  };
}


void Guarded::nextGuard(TheoryRewriteRules & re)const{
  Assert(inst != RULEINST_TRUE && inst != RULEINST_FALSE);
  if(simulateRewritting && inst->alreadyRewritten(re)) return;
  inst->findGuard(re,d_guard+1);
};

/** start indicate the first guard which is not true */
Guarded::Guarded(const RuleInst* ri, const size_t start) :
  d_guard(start),inst(ri) {};
Guarded::Guarded(const Guarded & g) :
  d_guard(g.d_guard),inst(g.inst) {};
Guarded::Guarded() :
  //dumb value
  d_guard(-1),inst(RULEINST_TRUE) {};

TheoryRewriteRules::TheoryRewriteRules(context::Context* c,
                                       context::UserContext* u,
                                       OutputChannel& out,
                                       Valuation valuation,
                                       const LogicInfo& logicInfo) :
  Theory(THEORY_REWRITERULES, c, u, out, valuation, logicInfo),
  d_rules(c), d_ruleinsts(c), d_guardeds(c), d_checkLevel(c,0),
  d_explanations(c), d_ruleinsts_to_add(), d_ppAssert_on(false)
{
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);
}

void TheoryRewriteRules::addMatchRuleTrigger(const RewriteRule * r,
                                             rrinst::InstMatch & im,
                                             bool delay){
  ++r->nb_matched;
  ++d_statistics.d_match_found;
  if(rewrite_instantiation) im.applyRewrite();
  if(representative_instantiation)
    im.makeRepresentative( getQuantifiersEngine() );

  if(!cache_match || !r->inCache(*this,im)){
    ++r->nb_applied;
    ++d_statistics.d_cache_miss;
    std::vector<Node> subst;
    //AJR: replaced computeTermVec with this
    for( size_t i=0; i<r->inst_vars.size(); i++ ){
      Node n = im.getValue( r->inst_vars[i] );
      Assert( !n.isNull() );
      subst.push_back( n );
    }
    RuleInst * ri = new RuleInst(*this,r,subst,
                                 r->directrr ? im.d_matched : Node::null());
    Debug("rewriterules::matching") << "One matching found"
                                    << (delay? "(delayed)":"")
                                    << ":" << *ri << std::endl;
    // Find the first non verified guard, don't save the rule if the
    // rule can already be fired In fact I save it otherwise strange
    // things append.
    Assert(ri->rule != NULL);
    if(delay) d_ruleinsts_to_add.push_back(ri);
    else{
      if(simulateRewritting && ri->alreadyRewritten(*this)) return;
      if(ri->findGuard(*this, 0) != (r->guards).size())
        d_ruleinsts.push_back(ri);
      else delete(ri);
    };
  }else{
    ++d_statistics.d_cache_hit;
  };
}

void TheoryRewriteRules::check(Effort level) {
  CodeTimer codeTimer(d_theoryTime);

  Assert(d_ruleinsts_to_add.empty());

  while(!done()) {
    // Get all the assertions
    // TODO: Test that it have already been ppAsserted

    //if we are here and ppAssert has not been done
    // that means that ppAssert is off so we need to assert now
    if(!d_ppAssert_on) addRewriteRule(get());
    else get();
    // Assertion assertion = get();
    // TNode fact = assertion.assertion;

    // Debug("rewriterules") << "TheoryRewriteRules::check(): processing " << fact << std::endl;
    //   if (getValuation().getDecisionLevel()>0)
    //     Unhandled(getValuation().getDecisionLevel());
    //   addRewriteRule(fact);

    };

  Debug("rewriterules::check") << "RewriteRules::Check start " << d_checkLevel << (level==EFFORT_FULL? " EFFORT_FULL":"") << std::endl;

  /** Test each rewrite rule */
  for(size_t rid = 0, end = d_rules.size(); rid < end; ++rid) {
    RewriteRule * r = d_rules[rid];
    if (level!=EFFORT_FULL && r->d_split) continue;
    Debug("rewriterules::check") << "RewriteRules::Check  rule: " << *r << std::endl;
    Trigger & tr = r->trigger;
    //reset instantiation round for trigger (set up match production)
    tr.resetInstantiationRound();

    /** Test the possible matching one by one */
    while(tr.getNextMatch()){
      rrinst::InstMatch im = tr.getInstMatch();
      addMatchRuleTrigger(r, im, true);
    }
  }

  const bool do_notification = d_checkLevel == 0 || level==EFFORT_FULL;
  bool polldone = false;

  if(level==EFFORT_FULL) ++d_statistics.d_full_check;
  else ++d_statistics.d_check;

  GuardedMap::const_iterator p = d_guardeds.begin();
  do{


    //dequeue instantiated rules
    for(; !d_ruleinsts_to_add.empty();){
      RuleInst * ri = d_ruleinsts_to_add.back(); d_ruleinsts_to_add.pop_back();
      if(simulateRewritting && ri->alreadyRewritten(*this)) continue;
      if(ri->findGuard(*this, 0) != ri->rule->guards.size())
        d_ruleinsts.push_back(ri);
      else delete(ri);
    };

    if(do_notification)
    /** Temporary way. Poll value */
    for (; p != d_guardeds.end(); ++p){
      TNode g = (*p).first;
      const GList * const l = (*p).second;
      const Guarded & glast = l->back();
      // Notice() << "Polled?:" << g << std::endl;
      if(glast.inst == RULEINST_TRUE||glast.inst == RULEINST_FALSE) continue;
      // Notice() << "Polled!:" << g << "->" << (glast.inst == RULEINST_TRUE||glast.inst == RULEINST_FALSE) << std::endl;
      bool value;
      if(getValuation().hasSatValue(g,value)){
        if(value) polldone = true; //One guard is true so pass n check
        Debug("rewriterules::guards") << "Poll value:" << g
                             << " is " << (value ? "true" : "false") << std::endl;
        notification(g,value);
        //const Guarded & glast2 = (*l)[l->size()-1];
        // Notice() << "Polled!!:" << g << "->" << (glast2.inst == RULEINST_TRUE||glast2.inst == RULEINST_FALSE) << std::endl;
      };
    };

  }while(!d_ruleinsts_to_add.empty() ||
         (p != d_guardeds.end() && do_notification));

  if(polldone) d_checkLevel = checkSlowdown;
  else d_checkLevel = d_checkLevel > 0 ? (d_checkLevel - 1) : 0;

  /** Narrowing by splitting on the guards */
  /** Perhaps only when no notification? */
  if(narrowing_full_effort && level==EFFORT_FULL){
    for (GuardedMap::const_iterator p = d_guardeds.begin();
         p != d_guardeds.end(); ++p){
      TNode g = (*p).first;
      const GList * const l = (*p).second;
      const Guarded & glast = (*l)[l->size()-1];
      if(glast.inst == RULEINST_TRUE||glast.inst == RULEINST_FALSE)
        continue;
      // If it has a value it should already has been notified
      bool value CVC4_UNUSED;
      Assert(!getValuation().hasSatValue(g,value));
      Debug("rewriterules::check") << "RewriteRules::Check Narrowing on:" << g << std::endl;
      /** Can split on already rewritten instrule... but... */
      getOutputChannel().split(g);
    }
  }

  Assert(d_ruleinsts_to_add.empty());
  Debug("rewriterules::check") << "RewriteRules::Check done " << d_checkLevel << std::endl;

};

void TheoryRewriteRules::registerQuantifier( Node n ){};

Trigger TheoryRewriteRules::createTrigger( TNode n, std::vector<Node> & pattern ) {
  //  Debug("rewriterules") << "createTrigger:";
  getQuantifiersEngine()->registerPattern(pattern);
  return *Trigger::mkTrigger(getQuantifiersEngine(),n,pattern,
                             options::efficientEMatching()?
                             Trigger::MATCH_GEN_EFFICIENT_E_MATCH :
                             Trigger::MATCH_GEN_DEFAULT,
                             true,
                             Trigger::TR_MAKE_NEW,
                             false);
  //                             options::smartMultiTriggers());
};

bool TheoryRewriteRules::notifyIfKnown(const GList * const ltested,
                                        GList * const lpropa) {
    Assert(ltested->size() > 0);
    const Guarded & glast = (*ltested)[ltested->size()-1];
    if(glast.inst == RULEINST_TRUE || glast.inst == RULEINST_FALSE){
      notification(lpropa,glast.inst == RULEINST_TRUE);
      return true;
    };
    return false;
};

void TheoryRewriteRules::notification(GList * const lpropa, bool b){
  if (b){
    for(size_t ig = 0;
        ig != lpropa->size(); ++ig) {
      (*lpropa)[ig].nextGuard(*this);
    };
    lpropa->push_back(Guarded(RULEINST_TRUE,0));
  }else{
    lpropa->push_back(Guarded(RULEINST_FALSE,0));
  };
  Assert(lpropa->back().inst == RULEINST_TRUE ||
         lpropa->back().inst == RULEINST_FALSE);
};



Answer TheoryRewriteRules::addWatchIfDontKnow(Node g0, const RuleInst* ri,
                                              const size_t gid){
  /** Currently create a node with a literal */
  Node g = getValuation().ensureLiteral(g0);
  GuardedMap::iterator l_i = d_guardeds.find(g);
  GList* l;
  if( l_i == d_guardeds.end() ) {
    /** Normally Not watched so IDONTNOW but since we poll, we can poll now */
    bool value;
    if(getValuation().hasSatValue(g,value)){
      if(value) return ATRUE;
      else      return AFALSE;
    };
    //Not watched so IDONTNOW
    l = new(getSatContext()->getCMM())
      GList(true, getSatContext());//,
            //ContextMemoryAllocator<Guarded>(getContext()->getCMM()));
    d_guardeds.insert(g ,l);//.insertDataFromContextMemory(g, l);
    /* TODO Add register propagation */
  } else {
    l = (*l_i).second;
    Assert(l->size() > 0);
    const Guarded & glast = (*l)[l->size()-1];
    if(glast.inst == RULEINST_TRUE) return ATRUE;
    if(glast.inst == RULEINST_FALSE) return AFALSE;

  };
  /** I DONT KNOW because not watched or because not true nor false */
  l->push_back(Guarded(ri,gid));
  return ADONTKNOW;
};

void TheoryRewriteRules::notification(Node g, bool b){
  GuardedMap::const_iterator l = d_guardeds.find(g);
  /** Should be a propagated node already known */
  Assert(l != d_guardeds.end());
  notification((*l).second,b);
}


void TheoryRewriteRules::notifyEq(TNode lhs, TNode rhs) {
  GuardedMap::const_iterator ilhs = d_guardeds.find(lhs);
  GuardedMap::const_iterator irhs = d_guardeds.find(rhs);
  /** Should be a propagated node already known */
  Assert(ilhs != d_guardeds.end());
  if( irhs == d_guardeds.end() ) {
    /** Not watched so points to the list directly */
    d_guardeds.insertDataFromContextMemory(rhs, (*ilhs).second);
  } else {
    GList * const llhs = (*ilhs).second;
    GList * const lrhs = (*irhs).second;
    if(!(notifyIfKnown(llhs,lrhs) || notifyIfKnown(lrhs,llhs))){
      /** If none of the two is known */
      for(GList::const_iterator g = llhs->begin(); g != llhs->end(); ++g){
        lrhs->push_back(*g);
      };
    };
  };
};


Node TheoryRewriteRules::normalizeConjunction(NodeBuilder<> & conjunction){
  Assert(conjunction.getKind() == kind::AND);
  switch(conjunction.getNumChildren()){
  case 0:
    return d_true;
  case 1:
    return conjunction[0];
  default:
    return conjunction;
  }

}

void explainInstantiation(const RuleInst *inst, TNode substHead, NodeBuilder<> & conjunction ){
  TypeNode booleanType = NodeManager::currentNM()->booleanType();
  // if the rule is directly applied by the rewriter,
  // we should take care to use the representative that can't be directly rewritable:
  // If "car(a)" is somewhere and we know that "a = cons(x,l)" we shouldn't
  // add the constraint car(cons(x,l) = x because it is rewritten to x = x.
  // But we should say cons(a) = x
  Assert(!inst->d_matched.isNull());
  Assert( inst->d_matched.getKind() == kind::APPLY_UF);
  Assert( substHead.getKind() == kind::APPLY_UF );
  Assert( inst->d_matched.getOperator() == substHead.getOperator() );
  Assert(conjunction.getKind() == kind::AND);
  // replace the left hand side by the term really matched
  NodeBuilder<2> nb;
  for(size_t i = 0,
        iend = inst->d_matched.getNumChildren(); i < iend; ++i){
    nb.clear( inst->d_matched[i].getType(false) == booleanType ?
              kind::IFF : kind::EQUAL );
    nb << inst->d_matched[i] << substHead[i];
    conjunction << static_cast<Node>(nb);
  }
}

Node skolemizeBody( Node f ){
  /*TODO skolemize the subformula of s with constant or skolemize
    directly in the body of the rewrite rule with an uninterpreted
    function.
   */
  if ( f.getKind()!=EXISTS ) return f;
  std::vector< Node > vars;
  std::vector< Node > csts;
  for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
    csts.push_back( NodeManager::currentNM()->mkSkolem( "skolem_$$", f[0][i].getType(), "is from skolemizing the body of a rewrite rule" ) );
    vars.push_back( f[0][i] );
  }
  return f[ 1 ].substitute( vars.begin(), vars.end(),
                            csts.begin(), csts.end() );
}


void TheoryRewriteRules::propagateRule(const RuleInst * inst, TCache cache){
  //   Debug("rewriterules") << "A rewrite rules is verified. Add lemma:";
  Debug("rewriterules::propagate") << "propagateRule" << *inst << std::endl;
  const RewriteRule * rule = inst->rule;
  ++rule->nb_applied;
  // Can be more something else than an equality in fact (eg. propagation rule)
  Node equality = skolemizeBody(inst->substNode(*this,rule->body,cache));
  if(propagate_as_lemma){
    Node lemma = equality;
    if(rule->directrr){
      NodeBuilder<> conjunction(kind::AND);
      explainInstantiation(inst,
                           rule->guards.size() > 0?
                           inst->substNode(*this,rule->guards[0],cache) : equality[0],
                           conjunction);
      Debug("rewriterules-directrr") << "lemma:" << lemma << " :: " << inst->d_matched;
      //rewrite rule
      TypeNode booleanType = NodeManager::currentNM()->booleanType();
      if(equality[1].getType(false) == booleanType)
        equality = inst->d_matched.iffNode(equality[1]);
      else equality = inst->d_matched.eqNode(equality[1]);
      lemma = normalizeConjunction(conjunction).impNode(equality);
      Debug("rewriterules-directrr") << " -> " << lemma << std::endl;
    }
    else if(rule->guards.size() > 0){
      // We can use implication for reduction rules since the head is known
      // to be true
      NodeBuilder<> conjunction(kind::AND);
      substGuards(inst,cache,conjunction);
      lemma = normalizeConjunction(conjunction).impNode(equality);
    }
    Debug("rewriterules::propagate") << "propagated " << lemma << std::endl;
    getOutputChannel().lemma(lemma);
  }else{
    Node lemma_lit = equality;
    if(rule->directrr && rule->guards.size() == 0)
      lemma_lit = inst->d_matched.eqNode(equality[1]); // rewrite rules
    lemma_lit = getValuation().ensureLiteral(lemma_lit);
    ExplanationMap::const_iterator p = d_explanations.find(lemma_lit);
    if(p!=d_explanations.end()) return; //Already propagated
    bool value;
    if(getValuation().hasSatValue(lemma_lit,value)){
      /* Already assigned */
      if (!value){
        NodeBuilder<> conflict(kind::AND);

        if(rule->directrr){
          explainInstantiation(inst,
                               rule->guards.size() > 0?
                               inst->substNode(*this,rule->guards[0],cache) : equality[0],
                               conflict);
          if(rule->guards.size() > 0){
            //reduction rule
            Assert(rule->guards.size() == 1);
            conflict << inst->d_matched; //this one will be two times
          }
        }
        substGuards(inst,cache,conflict);
        conflict << lemma_lit;
        getOutputChannel().conflict(normalizeConjunction(conflict));
      };
    }else{
      getOutputChannel().propagate(lemma_lit);
      d_explanations.insert(lemma_lit, *inst);
   };
  };

  if(simulateRewritting){
    static NoMatchAttribute rewrittenNodeAttribute;
    // Tag the rewritted terms
    // for(std::vector<Node>::iterator i = rule->to_remove.begin();
    //     i == rule->to_remove.end(); ++i){
    //   (*i).setAttribute(rewrittenNodeAttribute,true);
    // };
    for(size_t i = 0; i < rule->to_remove.size(); ++i){
      Node rewritten = inst->substNode(*this,rule->to_remove[i],cache);
      Debug("rewriterules::simulateRewriting") << "tag " << rewritten << " as rewritten" << std::endl;
      rewritten.setAttribute(rewrittenNodeAttribute,true);
    };

  };

  if ( compute_opt && !rule->body_match.empty() ){

    uf::TheoryUF* uf = static_cast<uf::TheoryUF *>(getQuantifiersEngine()->getTheoryEngine()->theoryOf( theory::THEORY_UF ));
    eq::EqualityEngine* ee =
      static_cast<eq::EqualityEngine*>(uf->getEqualityEngine());

    //Verify that this instantiation can't immediately fire another rule
    for(RewriteRule::BodyMatch::const_iterator p = rule->body_match.begin();
        p != rule->body_match.end(); ++p){
      RewriteRule * r = (*p).second;
      // Use trigger2 since we can be in check
      ApplyMatcher * tr = r->trigger_for_body_match;
      Assert(tr != NULL);
      tr->resetInstantiationRound(getQuantifiersEngine());
      rrinst::InstMatch im;
      TNode m = inst->substNode(*this,(*p).first, cache);
      Assert( m.getKind() == kind::APPLY_UF );
      ee->addTerm(m);
      if( tr->reset(m,im,getQuantifiersEngine()) ){
        im.d_matched = m;
        Debug("rewriterules::matching") << "SimulatedRewrite: " << std::endl;
        addMatchRuleTrigger(r, im);
      }
    }

  }
};

void TheoryRewriteRules::substGuards(const RuleInst *inst,
                                     TCache cache,
                                     NodeBuilder<> & conjunction){
  const RewriteRule * r = inst->rule;
  /** Guards */ /* TODO remove the duplicate with a set like in uf? */
  for(std::vector<Node>::const_iterator p = r->guards.begin();
      p != r->guards.end(); ++p) {
    Assert(!p->isNull());
    conjunction << inst->substNode(*this,*p,cache);
  };
}

Node TheoryRewriteRules::explain(TNode n){
  ExplanationMap::const_iterator p = d_explanations.find(n);
  Assert(p!=d_explanations.end(),"I forget the explanation...");
  RuleInst inst = (*p).second;
  const RewriteRule * rule = inst.rule;
  TCache cache;
  NodeBuilder<> explanation(kind::AND);
  if(rule->directrr){
    explainInstantiation(&inst,
                         rule->guards.size() > 0?
                         inst.substNode(*this,rule->guards[0],cache):
                         inst.substNode(*this,rule->body[0]  ,cache),
                         explanation);
    if(rule->guards.size() > 0){
      //reduction rule
      Assert(rule->guards.size() == 1);
      explanation << inst.d_matched; //this one will be two times
    }
  };
  substGuards(&inst, cache ,explanation);
  return normalizeConjunction(explanation);
}

void TheoryRewriteRules::collectModelInfo( TheoryModel* m, bool fullModel ){

}

Theory::PPAssertStatus TheoryRewriteRules::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  //TODO: here add only to the rewriterules database for ppRewrite,
  //and not for the general one. Otherwise rewriting that occur latter
  //on this rewriterules will be lost. But if the rewriting of the
  //body is not done in "in", will it be done latter after
  //substitution? Perhaps we should add the rewriterules to the
  //database for ppRewrite also after the subtitution at the levvel of check

  // addRewriteRule(in);
  // d_ppAssert_on = true;
  return PP_ASSERT_STATUS_UNSOLVED;
}

TheoryRewriteRules::Statistics::Statistics():
  d_num_rewriterules("TheoryRewriteRules::Num_RewriteRules", 0),
  d_check("TheoryRewriteRules::Check", 0),
  d_full_check("TheoryRewriteRules::FullCheck", 0),
  d_poll("TheoryRewriteRules::Poll", 0),
  d_match_found("TheoryRewriteRules::MatchFound", 0),
  d_cache_hit("TheoryRewriteRules::CacheHit", 0),
  d_cache_miss("TheoryRewriteRules::CacheMiss", 0)
{
  StatisticsRegistry::registerStat(&d_num_rewriterules);
  StatisticsRegistry::registerStat(&d_check);
  StatisticsRegistry::registerStat(&d_full_check);
  StatisticsRegistry::registerStat(&d_poll);
  StatisticsRegistry::registerStat(&d_match_found);
  StatisticsRegistry::registerStat(&d_cache_hit);
  StatisticsRegistry::registerStat(&d_cache_miss);
}

TheoryRewriteRules::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_num_rewriterules);
  StatisticsRegistry::unregisterStat(&d_check);
  StatisticsRegistry::unregisterStat(&d_full_check);
  StatisticsRegistry::unregisterStat(&d_poll);
  StatisticsRegistry::unregisterStat(&d_match_found);
  StatisticsRegistry::unregisterStat(&d_cache_hit);
  StatisticsRegistry::unregisterStat(&d_cache_miss);
}


}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

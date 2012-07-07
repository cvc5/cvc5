/*********************                                                        */
/*! \file theory_rewriterules.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: bobot
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::rewriterules;


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
      Debug("rewriterules") << g << "is true" << std::endl;
      ++start;
      continue;
    case AFALSE:
      Debug("rewriterules") << g << "is false" << std::endl;
      return -1;
    case ADONTKNOW:
      Debug("rewriterules") << g << "is unknown" << std::endl;
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
                                       const LogicInfo& logicInfo,
                                       QuantifiersEngine* qe) :
  Theory(THEORY_REWRITERULES, c, u, out, valuation, logicInfo, qe),
  d_rules(c), d_ruleinsts(c), d_guardeds(c), d_checkLevel(c,0),
  d_explanations(c), d_ruleinsts_to_add()
  {
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);
  Debug("rewriterules") << Node::setdepth(-1);
  Debug("rewriterules-rewrite") << Node::setdepth(-1);
}

void TheoryRewriteRules::addMatchRuleTrigger(const RewriteRule * r,
                                             InstMatch & im,
                                             bool delay){
  ++r->nb_matched;
  if(rewrite_instantiation) im.applyRewrite();
  if(representative_instantiation)
    im.makeRepresentative( getQuantifiersEngine() );

  if(!cache_match || !r->inCache(*this,im)){
    ++r->nb_applied;
    std::vector<Node> subst;
    im.computeTermVec(getQuantifiersEngine(), r->inst_vars , subst);
    RuleInst * ri = new RuleInst(*this,r,subst,
                                 r->directrr ? im.d_matched : Node::null());
    Debug("rewriterules") << "One matching found"
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
  };
}

void TheoryRewriteRules::check(Effort level) {
  CodeTimer codeTimer(d_theoryTime);

  Assert(d_ruleinsts_to_add.empty());

  while(!done()) {
    // Get all the assertions
    // TODO: Test that it have already been ppAsserted
    get();
    // Assertion assertion = get();
    // TNode fact = assertion.assertion;

    // Debug("rewriterules") << "TheoryRewriteRules::check(): processing " << fact << std::endl;
    //   if (getValuation().getDecisionLevel()>0)
    //     Unhandled(getValuation().getDecisionLevel());
    //   addRewriteRule(fact);

    };

  Debug("rewriterules") << "Check:" << d_checkLevel << (level==EFFORT_FULL? " EFFORT_FULL":"") << std::endl;

  /** Test each rewrite rule */
  for(size_t rid = 0, end = d_rules.size(); rid < end; ++rid) {
    RewriteRule * r = d_rules[rid];
    if (level!=EFFORT_FULL && r->d_split) continue;
    Debug("rewriterules") << "  rule: " << r << std::endl;
    Trigger & tr = r->trigger;
    //reset instantiation round for trigger (set up match production)
    tr.resetInstantiationRound();
    //begin iterating from the first match produced by the trigger
    tr.reset( Node::null() );

    /** Test the possible matching one by one */
    InstMatch im;
    while(tr.getNextMatch( im )){
      addMatchRuleTrigger(r, im, true);
      im.clear();
    }
  }

  const bool do_notification = d_checkLevel == 0 || level==EFFORT_FULL;
  bool polldone = false;

  GuardedMap::const_iterator p = d_guardeds.begin();
  do{


    //dequeue instantiated rules
    for(; !d_ruleinsts_to_add.empty();){
      RuleInst * ri = d_ruleinsts_to_add.back(); d_ruleinsts_to_add.pop_back();
      if(simulateRewritting && ri->alreadyRewritten(*this)) break;
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
        Debug("rewriterules") << "Poll value:" << g
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
      bool value; value = value; // avoiding the warning in non debug mode
      Assert(!getValuation().hasSatValue(g,value));
      Debug("rewriterules") << "Narrowing on:" << g << std::endl;
      /** Can split on already rewritten instrule... but... */
      getOutputChannel().split(g);
    }
  }

  Assert(d_ruleinsts_to_add.empty());
  Debug("rewriterules") << "Check done:" << d_checkLevel << std::endl;

};

void TheoryRewriteRules::registerQuantifier( Node n ){};

Trigger TheoryRewriteRules::createTrigger( TNode n, std::vector<Node> & pattern ) {
  //  Debug("rewriterules") << "createTrigger:";
  getQuantifiersEngine()->registerPattern(pattern);
  return *Trigger::mkTrigger(getQuantifiersEngine(),n,pattern,
                             match_gen_kind, true);
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
    for(GList::const_iterator g = lpropa->begin();
        g != lpropa->end(); ++g) {
      (*g).nextGuard(*this);
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
  /** TODO: Should use the representative of g, but should I keep the
      mapping for myself? */
  /* If it false in one model (current valuation) it's false for all */
  if (useCurrentModel){
    Node val = getValuation().getValue(g0);
    Debug("rewriterules") << "getValue:" << g0 << " = "
                          << val << " is " << (val == d_false) << std::endl;
    if (val == d_false) return AFALSE;
  };
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


void TheoryRewriteRules::propagateRule(const RuleInst * inst, TCache cache){
  //   Debug("rewriterules") << "A rewrite rules is verified. Add lemma:";
  Debug("rewriterules") << "propagateRule" << *inst << std::endl;
  const RewriteRule * rule = inst->rule;
  ++rule->nb_applied;
  // Can be more something else than an equality in fact (eg. propagation rule)
  Node equality = inst->substNode(*this,rule->body,cache);
  if(propagate_as_lemma){
    Node lemma = equality;
    if(rule->guards.size() > 0){
      // TODO: problem with reduction rule => instead of <=>
      lemma = substGuards(inst, cache).impNode(equality);
    };
    if(rule->directrr){
      TypeNode booleanType = NodeManager::currentNM()->booleanType();
      // if the rule is directly applied by the rewriter,
      // we should take care to use the representative that can't be directly rewritable:
      // If "car(a)" is somewhere and we know that "a = cons(x,l)" we shouldn't
      // add the constraint car(cons(x,l) = x because it is rewritten to x = x.
      // But we should say cons(a) = x
      Assert(lemma.getKind() == kind::EQUAL ||
             lemma.getKind() == kind::IMPLIES);
      Assert(!inst->d_matched.isNull());
      Assert( inst->d_matched.getOperator() == lemma[0].getOperator() );
      // replace the left hand side by the term really matched
      Debug("rewriterules-directrr") << "lemma:" << lemma << " :: " << inst->d_matched;
      Node hyp;
      NodeBuilder<2> nb;
      if(inst->d_matched.getNumChildren() == 1){
        nb.clear( inst->d_matched[0].getType(false) == booleanType ?
                  kind::IFF : kind::EQUAL );
        nb << inst->d_matched[0] << lemma[0][0];
        hyp = nb;
      }else{
        NodeBuilder<> andb(kind::AND);
        for(size_t i = 0,
              iend = inst->d_matched.getNumChildren(); i < iend; ++i){
          nb.clear( inst->d_matched[i].getType(false) == booleanType ?
                    kind::IFF : kind::EQUAL );
          nb << inst->d_matched[i] << lemma[0][i];
          andb << static_cast<Node>(nb);
        }
        hyp = andb;
      };
      nb.clear(lemma.getKind());
      nb << inst->d_matched << lemma[1];
      lemma = hyp.impNode(static_cast<Node>(nb));
      Debug("rewriterules-directrr") << " -> " << lemma << std::endl;
    };
    // Debug("rewriterules") << "lemma:" << lemma << std::endl;
    getOutputChannel().lemma(lemma);
  }else{
    Assert(!direct_rewrite);
    Node lemma_lit = getValuation().ensureLiteral(equality);
    ExplanationMap::const_iterator p = d_explanations.find(lemma_lit);
    if(p!=d_explanations.end()) return; //Already propagated
    bool value;
    if(getValuation().hasSatValue(lemma_lit,value)){
      /* Already assigned */
      if (!value){
        Node conflict = substGuards(inst,cache,lemma_lit);
        getOutputChannel().conflict(conflict);
      };
    }else{
      getOutputChannel().propagate(lemma_lit);
      d_explanations.insert(lemma_lit, *inst);
   };
  };

  if(simulateRewritting){
    static NoMatchAttribute rewrittenNodeAttribute;
    // Tag the rewritted terms
    for(std::vector<Node>::iterator i = rule->to_remove.begin();
        i == rule->to_remove.end(); ++i){
      (*i).setAttribute(rewrittenNodeAttribute,true);
    };
  };

  //Verify that this instantiation can't immediately fire another rule
  for(RewriteRule::BodyMatch::const_iterator p = rule->body_match.begin();
      p != rule->body_match.end(); ++p){
    RewriteRule * r = (*p).second;
    // Debug("rewriterules") << "  rule: " << r << std::endl;
    // Use trigger2 since we can be in check
    Trigger & tr = r->trigger_for_body_match;
    InstMatch im;
    TNode m = inst->substNode(*this,(*p).first, cache);
    tr.getMatch(m,im);
    if(!im.empty()){
      im.d_matched = m;
      addMatchRuleTrigger(r, im);
    }
  }
};


Node TheoryRewriteRules::substGuards(const RuleInst *inst,
                                     TCache cache,
                                     /* Already substituted */
                                     Node last){
  const RewriteRule * r = inst->rule;
  /** No guards */
  const size_t size = r->guards.size();
  if(size == 0) return (last.isNull()?d_true:last);
  /** One guard */
  if(size == 1 && last.isNull()) return inst->substNode(*this,r->guards[0],cache);
  /** Guards */ /* TODO remove the duplicate with a set like in uf? */
  NodeBuilder<> conjunction(kind::AND);
  for(std::vector<Node>::const_iterator p = r->guards.begin();
      p != r->guards.end(); ++p) {
    Assert(!p->isNull());
    conjunction << inst->substNode(*this,*p,cache);
  };
  if (!last.isNull()) conjunction << last;
  return conjunction;
}

Node TheoryRewriteRules::explain(TNode n){
  ExplanationMap::const_iterator p = d_explanations.find(n);
  Assert(p!=d_explanations.end(),"I forget the explanation...");
  RuleInst i = (*p).second;
  //Notice() << n << "<-" << *(i.rule) << std::endl;
  return substGuards(&i, TCache ());
}

Theory::PPAssertStatus TheoryRewriteRules::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  addRewriteRule(in);
  return PP_ASSERT_STATUS_UNSOLVED;
}

}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
